# Review status and evidence

## Author review

Bingqi Yu has completed semantic self-review of the explicitly stated theorem,
including the audit examples. The acceptance target is the
[mathematical statement](Arnold1963_Main_Theorem_Code_Aligned_EN.pdf), not
equivalence with every assumption or auxiliary result in Arnold's original paper.

AI-assisted source analysis and local Lean checks supported the review. This is
author self-review, not independent human review or peer-review certification.

## Audit example

The example uses one degree of freedom:

- `H₀(p) = p³/3`.
- The complex action domain is the union of disks of radius `1/4` centered at
  `+1` and `−1`.
- The real slice is the closure of two nonempty open intervals, with null boundary.
- The Hessian is `2p` and is nonzero on the required real open set.
- The frequency map is `p²`, so it is not globally injective.
- A positive threshold is obtained before choosing a nonconstant, centered cosine
  perturbation satisfying the norm bound.
- With tolerance `κ = 1/2`, the strict good-set estimate forces good points in
  both equal-volume branches.
- Each torus is connected and stays in one branch. Consequently there are at
  least two nonempty disjoint tori.

The specific output uses the same `FiniteLocalization.theorem1Result` construction
as the general theorem. The separate `original_data_threshold` declaration
directly invokes `theorem1`.

Sources: [W9Example](../KamProject/Arnold1963/Audit/W9Example.lean),
[W10Example](../KamProject/Arnold1963/Audit/W10Example.lean),
[W10Branches](../KamProject/Arnold1963/Audit/W10Branches.lean).

The example does not claim exactly two tori, equal perturbed frequencies, a
numerical value of the existence threshold, or a higher-dimensional small-divisor
demonstration.

## Machine checks on 2026-10-08

Using the existing Lean 4.33.1 installation:

- The W9Example, W10Example, W10Branches, W10 and W10Entry build targets passed,
  including cached dependencies.
- A direct W10 audit invocation passed.
- All 32 expected declarations matched the printed axiom output, without
  duplicates or omissions.
- The only reported axioms were `propext`, `Classical.choice` and `Quot.sound`.
- A direct W9Example check passed on retry. The first attempt encountered a
  toolchain-file read failure; the file existed, and no reinstallation was performed.

These checks were not a clean rebuild from downloaded dependencies. The v1.0.0
source commit `7985c9b` subsequently passed its GitHub Actions workflow and was
archived on 2026-10-08 at [DOI 10.5281/zenodo.23232025](https://doi.org/10.5281/zenodo.23232025).
The prior archived checks remain in [verification](../verification/).

## Novelty scope

As of the search on 2026-10-08, no earlier completed public Lean formalization of
a general basic nondegenerate analytic Hamiltonian KAM theorem with invariant
tori and a large-measure conclusion was identified. This is a limited public-web
literature search, not proof of worldwide priority or an exhaustive repository search.

Related work must be distinguished:

- The [Lean evaluation problem on KAM invariant curves](https://lean-lang.org/eval/problems/kam_invariant_curve/)
  displays a theorem statement whose shown proof contains `sorry`. That displayed
  statement is not a completed formal proof; the dynamic submission leaderboard
  was not verified in this search.
- [Rigorous computer-assisted applications of KAM theory](https://arxiv.org/abs/1601.00084)
  predate this project. Validated numerical applications are distinct from a
  complete proof-assistant formalization of a general theorem.

Earlier comparable formalizations and corrections to the novelty assessment
are welcome.
