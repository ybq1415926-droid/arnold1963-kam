#!/usr/bin/env python3
"""Build and audit this project using an existing Lake installation (Python 3.9+)."""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

PACKAGE = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
CONFIGS = ["lean-toolchain", "lakefile.toml", "lake-manifest.json"]
AUDIT = "KamProject/Arnold1963/Audit/W10.lean"
ENTRY = "KamProject/Arnold1963/Audit/W10Entry.lean"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project-root", type=Path, default=PACKAGE)
    parser.add_argument("--lake", default="lake", help="Lake executable; no installation is performed")
    parser.add_argument("--all", action="store_true", help="Build every project Lean module")
    parser.add_argument("--check-only", action="store_true", help="Only scan sources and local imports")
    parser.add_argument("--check-snapshot", action="store_true", help="Also check the recorded release hashes")
    parser.add_argument("--output", type=Path, help="Defaults to PROJECT/.audit-output")
    args = parser.parse_args()
    root = args.project_root.resolve()
    output = (args.output or root / ".audit-output").resolve()
    output.mkdir(parents=True, exist_ok=True)
    report = {"started_utc": datetime.now(timezone.utc).isoformat(), "passed": False,
              "mode": "scan" if args.check_only else ("all-modules" if args.all else "main-and-audits"),
              "commands": []}

    def portable(text):
        for spelling in {str(root), str(root).replace("\\", "/")}:
            text = text.replace(spelling, "<project>")
        return re.sub(r"[A-Za-z]:[\\/][^\s\"'<>]+", "<local-path>", text)

    try:
        sources = sorted([root / "KamProject.lean", *(root / "KamProject").rglob("*.lean")])
        rels = [path.relative_to(root).as_posix() for path in sources]
        report["source_count"] = len(sources)
        hashes = {p: sha256(root / p) for p in rels + CONFIGS}
        write_json(output / "source-sha256.json", hashes)
        if args.check_snapshot:
            expected = json.loads((PACKAGE / "verification/source-sha256.json").read_text(encoding="utf-8"))
            if hashes != expected:
                changed = sorted(k for k in hashes.keys() | expected.keys() if hashes.get(k) != expected.get(k))
                raise ValueError("Snapshot differs: " + ", ".join(changed))
            report["snapshot_hashes_match"] = True
        markers, missing_imports = [], []
        modules = {p[:-5].replace("/", ".") for p in rels}
        for path, rel in zip(sources, rels):
            content = path.read_text(encoding="utf-8-sig")
            for number, line in enumerate(content.splitlines(), 1):
                # Deliberately conservative: comments are scanned too; this is not a Lean parser.
                if re.search(r"\b(sorry|admit|native_decide|axiom)\b", line):
                    markers.append({"path": rel, "line": number})
                if re.match(r"^\s*import\s", line):
                    for name in line.split("--", 1)[0].split()[1:]:
                        if name.startswith("KamProject") and name not in modules:
                            missing_imports.append({"path": rel, "import": name})
        report.update(proof_marker_matches=markers, missing_local_imports=missing_imports)
        if markers or missing_imports:
            raise ValueError("Source scan or local import closure failed; inspect report.json")

        def run(name, arguments):
            print("Running " + name + " ...", flush=True)
            started = time.monotonic()
            env = os.environ.copy()
            env.setdefault("LEAN_NUM_THREADS", "1")
            result = subprocess.run([args.lake, *arguments], cwd=root, env=env,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                    text=True, encoding="utf-8", errors="replace")
            log = portable(result.stdout)
            (output / (name + ".txt")).write_text(log, encoding="utf-8")
            report["commands"].append({"name": name, "arguments": arguments,
                                       "exit_code": result.returncode,
                                       "seconds": round(time.monotonic() - started, 2)})
            if result.returncode:
                raise ValueError(name + " failed; see its log")
            if re.search(r"\bsorryAx\b|\berror:|\bwarning:", log, flags=re.IGNORECASE):
                raise ValueError(name + " contains a diagnostic; see its log")
            return log

        if not args.check_only:
            version = run("version", ["env", "lean", "--version"])
            expected_version = (root / "lean-toolchain").read_text().strip().split(":v")[-1]
            if not re.search(r"version\s+" + re.escape(expected_version) + r"\b", version):
                raise ValueError("Lean version does not match lean-toolchain")
            report["lean_version_output"] = version.strip()
            targets = sorted(modules) if args.all else []
            run("build", ["--no-cache", "build", *targets])
            run("audit-build", ["--no-cache", "build", AUDIT[:-5].replace("/", "."),
                                ENTRY[:-5].replace("/", ".")])
            axioms_output = run("axioms", ["env", "lean", AUDIT])
            audit_source = (root / AUDIT).read_text(encoding="utf-8-sig")
            names = re.findall(r"^#print axioms (\S+)\s*$", audit_source, flags=re.MULTILINE)
            expected_names = ["KamProject.Arnold1963." + n for n in names]
            records = [{"declaration": n, "axioms": [a.strip() for a in aa.split(",") if a.strip()]}
                       for n, aa in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", axioms_output)]
            actual_names = [r["declaration"] for r in records]
            if not expected_names or Counter(expected_names) != Counter(actual_names):
                raise ValueError("Axiom output declarations do not match the audit commands")
            if len(set(actual_names)) != len(actual_names):
                raise ValueError("Duplicate axiom output declaration")
            unexpected = [r for r in records if set(r["axioms"]) - ALLOWED_AXIOMS]
            if unexpected:
                raise ValueError("Nonstandard axioms in " + repr(unexpected))
            report["axiom_declaration_count"] = len(records)
            report["axioms_used"] = sorted({a for r in records for a in r["axioms"]})
            write_json(output / "axioms.json", records)
            run("entry", ["env", "lean", ENTRY])
        # Refuse to certify a moving source tree.
        current_sources = sorted([root / "KamProject.lean", *(root / "KamProject").rglob("*.lean")])
        if current_sources != sources or any(sha256(root / p) != h for p, h in hashes.items()):
            raise ValueError("Project sources changed during verification")
        report["passed"] = True
    except (OSError, ValueError) as exc:
        report["failure"] = portable(str(exc))
        print(report["failure"], file=sys.stderr)
    finally:
        report["finished_utc"] = datetime.now(timezone.utc).isoformat()
        write_json(output / "report.json", report)
    print("PASS" if report["passed"] else "FAIL", flush=True)
    return 0 if report["passed"] else 1


if __name__ == "__main__":
    sys.exit(main())
