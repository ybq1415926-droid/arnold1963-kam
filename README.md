# Arnold 1963 KAM in Lean 4

The author has completed the main semantic self-review against the explicit theorem statement. Review of the audit examples remains pending. This is not an independent review or peer-review certification.

**Archived release:** [v0.1.0 — DOI: 10.5281/zenodo.23201478](https://doi.org/10.5281/zenodo.23201478),
published 7 October 2026. For reproducible citation, use this version DOI.
The [all-versions DOI](https://doi.org/10.5281/zenodo.23201477) resolves to the latest archived version.

This project formalizes a version of the basic nondegenerate analytic Hamiltonian KAM theorem in Lean 4 and mathlib, developed with reference to Arnold (1963). The theorem uses the explicit hypotheses and conclusions stated in the current Lean interface; equivalence with the full scope of Arnold's original statement is not claimed. The development constructs the iteration, analytic invariant tori, trajectories of the original Hamiltonian, and a large-measure conclusion.

See the [English theorem statement](docs/Arnold1963_Main_Theorem_Code_Aligned_EN.tex) and [Scope and assumptions](docs/SCOPE.md).

**Author:** Bingqi Yu, Jilin University —
[ORCID](https://orcid.org/0009-0000-4646-1791) ·
[GitHub](https://github.com/ybq1415926-droid).
The development used AI assistance; see [Provenance](docs/PROVENANCE.md).

[中文说明](README.zh-CN.md) · [Build and audit](docs/REPRODUCIBILITY.md) ·
[Release notes](docs/RELEASE_NOTES.md) · [Citation metadata](CITATION.cff)

## Main result

Start with [Main/Theorem1.lean](KamProject/Arnold1963/Main/Theorem1.lean).
In namespace `KamProject.Arnold1963`, the principal declaration is `theorem1`:

```lean
theorem theorem1 {n : ℕ} {H₀ : ComplexSpace n → ℂ} {G : Set (ComplexSpace n)}
    (h : GlobalHamiltonianData n H₀ G) {ρ : ℝ≥0} {κ : ℝ}
    (hρ : 0 < ρ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ f : AnalyticPhaseFunction n G ρ,
      f.uniformNorm ≤ M → Nonempty (Theorem1Result n H₀ G ρ κ f)
```

The positive threshold is chosen before the perturbation. It may depend on the fixed unperturbed Hamiltonian and domain data, the prescribed complex angle width ρ, and the prescribed measure tolerance κ, but not on the perturbation. The output contains a compact positive-measure good set, a measurable small complement, pairwise disjoint analytic invariant tori, and trajectories satisfying the original perturbed Hamiltonian equation for every real time. A globally injective frequency map is not assumed. The final torus interface asserts the absence of nonzero integer relations; no additional quantitative Diophantine bound or Lagrangian property is claimed here.

Read these definitions together with the theorem:

| Definition | Source |
| --- | --- |
| Unperturbed Hamiltonian and domain hypotheses | [GlobalHamiltonianData](KamProject/Arnold1963/Geometry/LocalizationCover.lean) |
| Analytic, periodic, real-compatible bounded perturbation | [AnalyticPhaseFunction](KamProject/Arnold1963/Basic/Functions.lean) |
| Analytic torus, frequency, displacement and orbit specification | [KAMTorus](KamProject/Arnold1963/Main/TorusResult.lean) |
| Global partition and measure specification | [Theorem1Result](KamProject/Arnold1963/Main/Theorem1.lean) |
| Public import and example uses | [W10](KamProject/Arnold1963/W10.lean), [W10Entry](KamProject/Arnold1963/Audit/W10Entry.lean) |

## Reproduce

The versions are fixed: **Lean 4.33.1**, **mathlib v4.33.1**.
The dependency commits are recorded in `lake-manifest.json`.
With the toolchain and dependencies available, run from the repository root:

```text
lake build
lake env lean KamProject/Arnold1963/Audit/W10.lean
lake env lean KamProject/Arnold1963/Audit/W10Entry.lean
```

For all 191 project modules, source scanning and the 32-declaration axiom audit:

```text
python scripts/verify.py --all
```

Use `python3` on systems where that is the Python executable name. Setup,
snapshot hashes, exact checks and their limits are described in
[Reproducibility](docs/REPRODUCIBILITY.md). The 2026-10-04 records show a successful
191-module build. The public candidate preserves all 191 Lean files and the three
version configuration files byte for byte against that baseline.

On 2026-10-07, the default project build and W10 audits passed again in the existing Windows checkout. The copied candidate passed hash and import checks. The GitHub Actions build and axiom audit also passed for the initial public source commit 0e1151b. These are validation records for that source snapshot; subsequent commits should be checked through their own workflow runs.

The 32 audited declarations recursively depend only on `propext`,
`Classical.choice` and `Quot.sound`. The source scan finds no `sorry`, `admit`,
`native_decide` or explicit `axiom` token. These checks concern the formal
statements; they do not by themselves certify correspondence with the paper.

## Layout and review

`KamProject/Arnold1963/` contains the formal development, with `Basic`,
`Arithmetic`, `Analysis`, `Geometry`, `Step`, `Iteration`, `Convergence`,
`Dynamics`, `Measure`, `Tori`, `Main` and `Audit` modules. The W0–W10 reading
order is in [Scope](docs/SCOPE.md). The small training and test modules are
retained to preserve the checked source tree and imports.

Reports about assumptions, mathematical correspondence, estimates, or build
reproducibility are welcome. Please identify the declaration and the relevant
source passage. The original proof paper and working reference PDFs are not
bundled. This snapshot makes no claim of worldwide priority or completed peer
review.

## Reference and license

V. I. Arnol'd, *Proof of a theorem of A. N. Kolmogorov on the invariance of
quasi-periodic motions under small perturbations of the Hamiltonian*,
Russian Mathematical Surveys **18**(5), 9–36 (1963).
[DOI](https://doi.org/10.1070/RM1963v018n05ABEH004130).

Original project code and repository documentation: [Apache-2.0](LICENSE).
Dependencies retain their own licenses. Please cite the exact version used via
[CITATION.cff](CITATION.cff). Citation for the archived release:

Bingqi Yu. (2026). *Arnold 1963 KAM in Lean 4* (v0.1.0) [Computer software].
Zenodo. https://doi.org/10.5281/zenodo.23201478
