# Reproducing the formal checks

The snapshot fixes Lean to `leanprover/lean4:v4.33.1` and mathlib to tag
`v4.33.1`, commit `0df444a360eaa60ab8c11dca51a86af692955474`.
Preserve `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`.

## Environment and commands

Use an existing installation of the stated Lean toolchain, or follow the
[Lean installation instructions](https://lean-lang.org/install/). A new clone
needs its locked dependencies and, ordinarily, the mathlib cache:

```text
lake exe cache get
lake build
lake env lean KamProject/Arnold1963/Audit/W10.lean
lake env lean KamProject/Arnold1963/Audit/W10Entry.lean
```

Dependency/cache retrieval may require internet access and substantial disk
space. Do not run `lake update` as part of reproducing this fixed snapshot.
For constrained Windows machines, set `$env:LEAN_NUM_THREADS = '1'` in
PowerShell before building. The verification script also defaults to one thread
unless the environment already sets a value.

With Python 3.9 or newer, the portable script needs only the standard library:

```text
python scripts/verify.py --all
```

It builds every project module, builds the W10 audits, invokes Lean on both
audit entries, compares printed axiom declaration names with the commands in
`Audit/W10.lean`, rejects duplicate or missing entries and nonstandard axioms,
and checks source markers and local imports. It rejects build warnings or
errors and verifies that the source tree did not change during the run.
Output goes to ignored directory `.audit-output/`; no dependency update or
toolchain installation is explicitly invoked by the script. Lake or an elan
launcher can still retrieve missing locked components when the environment is
not prepared.

Without `--all`, it builds the default project target and the two W10 audit
targets. For a source-only check of the original archived snapshot:

```text
python scripts/verify.py --check-only --check-snapshot
```

`--check-snapshot` compares the 191 Lean files and three version files with
[`source-sha256.json`](../verification/source-sha256.json). It intentionally
fails after source changes; ordinary development CI omits this flag. The manifest
is a reproducibility record, not a signature or an independent timestamp.
`--lake` accepts an existing executable path. `--project-root` supports checking
another checkout with the same source snapshot.

## Included evidence and its limits

The `verification/2026-10-04-*` records originate from the pre-publication local
validation: all 191 project modules built, and 32 audited declarations used only
`propext`, `Classical.choice` and `Quot.sound`. The printed axiom output is
included. Historical command summaries refer to original log names; not all
verbose build logs are bundled, because they include machine-specific paths.
Those summaries are author-supplied records, not an independent reproduction.

The public candidate's sources and version files match that historical baseline
byte for byte. On 2026-10-07, the default build, W10 audit build and both direct
Lean audit invocations passed again in the existing Windows working checkout,
using its installed toolchain and dependencies. The candidate copy separately
passed source-hash and import checks. This was not a fresh dependency download
or an independent build on another machine. See
[`2026-10-07-report.json`](../verification/2026-10-07-report.json); its `mode`
is `main-and-audits`, not `all-modules`.

The GitHub workflow sets up the pinned Lean environment, obtains the mathlib
cache, and runs the all-module script. A green remote CI result must be obtained
after upload; a workflow file alone is not a successful remote run.

A text scan is conservative and is not a Lean parser. The 32-declaration axiom
audit follows dependencies recursively from those declarations; it is not an
enumeration of every declaration in every file. Compilation establishes the
formal statements under their formal assumptions. The mathematical scope and
pending semantic review are stated in [Scope](SCOPE.md).
