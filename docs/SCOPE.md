# Mathematical scope and review map

The target is the basic nondegenerate analytic Hamiltonian KAM theorem in
Arnold (1963), §§2–4. This is a preliminary formalization snapshot with final
human semantic review pending. The Lean definitions below specify precisely
what is proved, including the adopted domain regularity conditions.

## Inputs

[`GlobalHamiltonianData`](../KamProject/Arnold1963/Geometry/LocalizationCover.lean)
requires:

- A positive finite dimension `n`, a compact complex action set `G` invariant
  under conjugation, and `H₀` analytic on a neighborhood of `G` and compatible
  with conjugation there.
- A nonempty open real set `U` whose closure is exactly `realSlice G`, with
  `volume (frontier U) = 0`.
- Every complexified point of `U` lies in the interior of `G`.
- The complex Hessian determinant of `H₀` is nonzero at those real interior
  points. Global injectivity of its frequency map is not an input.

Compactness implies finite real action volume; the nonempty open subset implies
positive real action volume. These are derived consequences. This interface does
not claim that arbitrary open domains or arbitrary compact sets automatically
satisfy these conditions. The compact-domain convention follows §4.5; the
explicit real-slice regularity conditions are adopted from the project's
revised working proof, and are visible in the formal statement.

[`AnalyticPhaseFunction`](../KamProject/Arnold1963/Basic/Functions.lean)
requires analyticity on neighborhoods of the specified phase domain,
`2π` angle periodicity, conjugation compatibility and boundedness on that domain.
Its `uniformNorm` is the supremum norm on the domain, not on the entire ambient
space. In `theorem1`, `ρ > 0` and `κ > 0`; a positive threshold `M` is chosen
before the arbitrary perturbation with `uniformNorm ≤ M`.

## Outputs

[`Theorem1Result`](../KamProject/Arnold1963/Main/Theorem1.lean) provides a partition
of `realSlice G × RealTorus n` into a compact good set and a measurable bad set.
The good set has positive volume and volume strictly greater than
`(1 − κ)` times the initial physical phase volume. The bad set has volume
strictly less than `κ` times that volume. The informative relative-measure
regime is `0 < κ < 1`, although the formal interface accepts all `κ > 0`.

The good set is the union of a pairwise disjoint family of actual torus sets.
Each [`KAMTorus`](../KamProject/Arnold1963/Main/TorusResult.lean) has a complex
angle-analytic lift, a closed embedding of the real `2π` torus, injective
derivative, and an angle projection with a homeomorphism and locally analytic
inverse. Its frequency has no nonzero integer relation and equals the original
unperturbed frequency at an output center. Both displacement blocks are `< κ`.
For every real time, the lifted linear motion solves the original perturbed
Hamiltonian equation and remains on the torus.

The common positive analytic width is an output bounded by the input width;
it is not asserted to equal the original width. Analyticity is in the angle
variables for each surviving torus, not in an open neighborhood of all surviving
action labels. Across different local frequency charts, intersecting tori are
proved equal; the family of actual sets removes duplicates.

## Conventions to audit

| Object | Convention |
| --- | --- |
| Real and complex coordinate vectors | Coordinate maximum norm |
| Phase vectors `(p,q)` | Product maximum norm |
| Linear maps | Induced operator norm over the stated scalar field; norm changes require explicit bounds |
| Fourier indices | Integer vectors with `ℓ¹` length `indexLength` |
| Low modes | Strict cutoff `0 < indexLength k < N` |
| Angles and physical phase measure | Period `2π`; total angle volume `(2π)^n` |
| Unit torus used in density arguments | Period `1` internally, transferred to the physical `2π` torus |
| Hamiltonian vector field in `(p,q)` order | `(-∂q H, ∂p H)`; signs must be read with this coordinate order |

Indexing is deliberately mixed by mathematical role: code parameters
`delta δ₁ s`, `beta δ₁ s`, `gamma n δ₁ s`, `perturbation n δ₁ s` and
`cutoff n δ₁ s` refer to paper step `s+1`. The transformation at code `s` is
`B_{s+1}`. In contrast, `state s`, `phase s` and `actionDomain s` refer to
`H^(s)`, `F_s` and `G_s`; `cumulative 0 = id` and `cumulative s = S_s`.
There is no universal instruction to shift every index by one.

## Reading order

Paths in this table are relative to `KamProject/Arnold1963/`.

| Stage | Mathematical role | Principal source locations |
| --- | --- | --- |
| W0–W1 | Statement, domains, norms, arithmetic and estimates | `Basic/`, `Arithmetic/`, `Analysis/` |
| W2 | Actual Fourier coefficients, reconstruction and tails | `Analysis/FourierCoefficients.lean`, `FourierSeries.lean`, `FourierTail.lean` |
| W3 | Implicit generating maps, uniqueness, inverse and symplectic structure | `Geometry/GeneratingImplicit.lean` through `GeneratingTorus.lean` |
| W4 | Homological equation and fundamental lemma | `Step/Homological.lean`, `Step/Fundamental.lean`, `Step.lean` |
| W5a–W5b | Domain loss, frequency charts, measure and inductive step | `W5a.lean`, `W5b.lean`, `Step/Inductive.lean` |
| W6 | Infinite iteration, quantitative budgets and theorem 2 | `Iteration/`, `Main/Theorem2.lean`, `W6.lean` |
| W7 | Limits, joint angle analyticity, dynamics and volume | `Convergence/`, `Dynamics/`, `Measure/`, `W7.lean` |
| W8 | Analytic embeddings and the local KAM result | `Tori/`, `Main/LocalKAM.lean`, `W8.lean` |
| W9 | Finite localization and global measure coverage | `Geometry/LocalizationCover.lean`, `Main/GlobalCover.lean`, `W9.lean` |
| W10 | Cross-chart equality, disjoint family and main theorem | `Tori/CrossChart.lean`, `Main/TorusResult.lean`, `Main/Theorem1.lean`, `W10.lean` |

Not every auxiliary theorem in the paper is reproduced in its full original
generality: some are replaced by specialized results sufficient for this proof.
The isoenergetic extension, degenerate cases and the rigid-body application in
§5 are outside this snapshot's claims.

## Review requests

Priority review points are the exact domain assumptions, the original-to-formal
statement correspondence, norm conversions, indexing and tail budgets,
physical volume normalization, and the scope of the analytic torus output.
For a finding, record the declaration, expected natural-language statement,
source section, and whether it concerns the hypotheses, conclusion or proof.

The nonconstant two-branch example in
[`Audit/W10Branches.lean`](../KamProject/Arnold1963/Audit/W10Branches.lean)
provides an instantiated output with two nonempty disjoint tori. It is a useful
nonvacuity check, not a replacement for review of the general theorem.
