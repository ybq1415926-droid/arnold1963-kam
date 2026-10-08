# Release notes

## v1.0.0 — 2026-10-08

Archived source commit: `7985c9b`.
Version DOI: [10.5281/zenodo.23232025](https://doi.org/10.5281/zenodo.23232025).

This version documents the author's completed semantic self-review of the
explicitly stated KAM theorem, including the audit examples.

- Added the English mathematical statement as PDF and LaTeX source.
- Clarified the domain assumptions and the relationship to Arnold (1963).
- Clarified that the threshold may depend on the prescribed width and measure
  tolerance, but not on the perturbation.
- Recorded the nonresonance conclusion and limits of the torus specification.
- Documented the nonconstant one-dimensional, two-branch example and its limits.
- Recorded the 2026-10-08 local example checks and 32-declaration axiom audit.
- Added a qualified novelty assessment distinguishing complete formal proofs
  from unproved statements and computer-assisted numerical applications.

No Lean statements, proofs, toolchain versions or dependency versions were
changed. The review status is author self-review, not independent review or
peer-review certification. The release commit passed GitHub Actions before
publication. DOI and publication-status updates on the main branch do not alter
the archived v1.0.0 source snapshot.

## v0.1.0 — historical preparation record

The following describes the preparation state of v0.1.0. That version was
subsequently published on 2026-10-07 and archived at
[DOI 10.5281/zenodo.23201478](https://doi.org/10.5281/zenodo.23201478).

Prepared on 2026-10-07 for public review; this preparation date is not an asserted
publication date. Final human semantic review is pending.

The candidate contains 191 Lean source files and the locked Lean 4.33.1 / mathlib
v4.33.1 configuration, preserving their bytes from the 2026-10-04 validation
baseline. The development includes the basic and inductive lemmas, quantitative
iteration, theorem 2, analytic torus construction, finite localization,
cross-chart disjointness and the main theorem under `GlobalHamiltonianData`.
It includes a nonconstant perturbation example with two actual disjoint tori.

Publication preparation adds English and Chinese entry documents, precise scope
and provenance notes, citation metadata, Apache-2.0 licensing, portable
verification, source hashes and a build-and-audit GitHub workflow. It does not
change any Lean statement, proof, toolchain or dependency version.

Review is requested on statement correspondence and the explicit assumptions.
The archived software version is not a claim of peer-reviewed correctness,
coverage of all KAM variants, or worldwide priority.
