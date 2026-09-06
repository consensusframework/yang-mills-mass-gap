# Finite-Volume Lattice Gauge Theory in Lean 4 — A Formalization Program Around the Yang–Mills Mass Gap

> **Status:** exploratory formalization research. This repository is **not a
> proof, partial proof or claimed solution** of the Yang–Mills Existence and
> Mass Gap Millennium Problem. Every verified result is a finite-lattice
> statement in the small-β (strong-coupling) regime.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22305341.svg)](https://doi.org/10.5281/zenodo.22305341)
[![Lean CI (Phase 3)](https://github.com/consensusframework/yang-mills-mass-gap/actions/workflows/lean-ci.yml/badge.svg?branch=main)](https://github.com/consensusframework/yang-mills-mass-gap/actions/workflows/lean-ci.yml)

## What this is

A Lean 4 / Mathlib library, `LatticeGauge` (`Phase3/`), for finite-volume
lattice gauge theory: Wilson action, Gibbs measure and expectation, gauge and
translation invariance, Haar probability on `U(n)`, the β = 0 product state,
and a polymer / cluster expansion of Kotecký–Preiss type with explicit
constants. Everything is machine-checked by the Lean 4 kernel; principal
declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.

## What this is not

The project does **not** construct continuum Yang–Mills theory or its
measure, does not construct a thermodynamic limit or any infinite-volume
object, does not prove a continuum limit or a general spatial-mixing result,
does not prove a mass gap, and does not prove the continuum Yang–Mills
existence or mass-gap statement required by the Clay Millennium Problem. The
finite-volume bounds below have local prefactors, but they are theorems about
finite lattices only. A lattice mass-gap target (`HasLatticeMassGap`) is
stated and explicitly marked open. Nothing here should be cited as a solution
or partial solution of the Clay problem.

## Verified state

| | |
|---|---|
| Library | `Phase3/LatticeGauge`, 105 modules, > 30,000 Lean lines, ≈ 1,150 declarations |
| `sorry` | 0 |
| Project-specific scientific axioms | 0 (kernel axioms only: `propext`, `Classical.choice`, `Quot.sound`) |
| Toolchain | Lean 4.15.0, Mathlib `v4.15.0` (pinned in `Phase3/lakefile.toml`) |
| CI | single job `build-phase3`: clean build of `Phase3/` + `#print axioms` of the three capstones, green on `main` |
| Frozen release | tag `zenodo-v51`, Version 51 DOI [10.5281/zenodo.22305341](https://doi.org/10.5281/zenodo.22305341) |

Detailed records: [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md),
[`RELEASE_NOTES_PEDRA51.md`](RELEASE_NOTES_PEDRA51.md),
[`formalization.yaml`](formalization.yaml) (mathlib-initiative schema v0.4).

## Principal results

All three hold in finite volume for `0 ≤ β ≤ 1/40000` (Wilson convention:
small β is strong coupling) on a finite periodic four-dimensional lattice,
for a probability base measure and a bounded measurable function `χ` with
`|χ| ≤ 1`. "Distance" is walk separation in the plaquette graph, not
Euclidean distance.

1. **Version 49 — cluster-expansion identity for the log partition function.**
   `LatticeGauge.logPartition_eq_tsum_unrooted`
   (`Phase3/LatticeGauge/KPLogPartition.lean`):
   `log Z_β = Σ'ₙ Bₙ(w_β)`, with the signed unrooted Ursell series absolutely
   convergent and `Z_β > 0` obtained as a corollary of the expansion.

2. **Version 50 — exponential covariance decay of two local observables.**
   `LatticeGauge.abs_gibbsCovariance_le_local_exp_decay`
   (`Phase3/LatticeGauge/CovarianceDecay.lean`): for bounded observables
   `f, g` with disjoint finite link supports, walk-barrier-separated at scale
   `n`, `|Cov_β(f, g)| ≤ 3·Cf·Cg·exp(6·D/113)·exp(−n/2)`, where `D` is the sum
   of the support-link cardinalities. The prefactor depends only on the local
   supports, not on the ambient volume.

3. **Version 51 — exponential stability under remote polymer-activity
   restriction.**
   `LatticeGauge.abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`
   (`Phase3/LatticeGauge/ActivityRestrictionStability.lean`): for a bounded
   measurable observable `f` depending only on the links of `s` with
   `|f| ≤ Cf`, and a remote region `r` with `WalkBarrierSeparated s r n`,

   ```
   |gibbsExpectation f − activityRestrictedExpectation f s r|
       ≤ 2 · Cf · exp(8 · D_s / 113) · exp(−n / 2),      D_s = card(supportLinkFinset s).
   ```

   `activityRestrictedExpectation` is the normalized polymer functional
   obtained by suppressing the activities of every polymer touching `r`; it
   is not a second Gibbs measure, a boundary condition or a spatial-mixing
   statement. The right-hand side has no separate dependence on the ambient
   volume or on the size of `r`; the remote region affects the estimate through
   the walk-separation scale `n`.

Kernel certificate of all three (checked on every CI run): `[propext, Classical.choice, Quot.sound]`.

## Reproduce

```sh
git clone https://github.com/consensusframework/yang-mills-mass-gap
cd yang-mills-mass-gap/Phase3
lake update            # resolves the pinned Mathlib (v4.15.0)
lake exe cache get     # optional: Mathlib build cache
lake build             # 105 modules; ~7–8 min on 2 vCPU with the cache
```

The CI step `Kernel certificates` (`.github/workflows/lean-ci.yml`) re-checks the three `#print axioms` certificates with `lake env lean`.

## Repository layout

```
Phase3/LatticeGauge/            the verified library (namespace LatticeGauge)
Phase3/lakefile.toml            Lake project, pinned Mathlib
Phase3/lean-toolchain           Lean toolchain pin
formalization.yaml              mathlib-initiative metadata (v0.4)
VERIFICATION_STATUS.md          verification record
RELEASE_NOTES_PEDRA51.md        release notes of Version 51
LICENSE, LICENSE-DOCUMENTATION  Apache-2.0 (code) / CC BY 4.0 (documentation)
.github/workflows/lean-ci.yml   CI (job build-phase3)
```

## History and archive

The project went through three stages: exploratory formalization (Phase 1),
conditional formalization with explicit assumptions and axioms (Phase 2), and
the finite-lattice library without project-specific scientific axioms (Phase 3). Phases 1 and 2 are legacy:
they do not establish their assumptions, are not in the Phase 3 dependency
tree, and were removed from the active tree after Version 51.

The complete historical tree is preserved, byte for byte, at the tag
[`zenodo-v51`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v51)
(commit `27dde3ffdfd63b052a63680ad85232512959456b`) and at the branch
[`archive/zenodo-v51-full-tree`](https://github.com/consensusframework/yang-mills-mass-gap/tree/archive/zenodo-v51-full-tree).
Previous versions: Version 50 — [10.5281/zenodo.22162464](https://doi.org/10.5281/zenodo.22162464)
(tag `zenodo-v50`); Version 49 — [10.5281/zenodo.22050763](https://doi.org/10.5281/zenodo.22050763)
(tag `zenodo-v49`); concept DOI (all versions) — [10.5281/zenodo.17397622](https://doi.org/10.5281/zenodo.17397622).

## Methodology

The project is coordinated by **Jucelha Carvalho** (Smart Tour Brasil,
[ORCID 0009-0004-6047-2306](https://orcid.org/0009-0004-6047-2306)) under the
**Consensus Framework**, a human-led method for coordinating several AI
models in separate roles (architecture and specification, Lean
implementation, reproduction, adversarial review, custody audit), with the
human coordinator holding credentials, integration and release. For Versions
49–51 every accepted gate went through written specification → Lean
implementation → verifiable git bundle → reproduction on a pinned bench →
GitHub Actions CI → integration by merge commit → post-merge CI on `main`.
The Consensus Framework was the winner of the UN Tourism Global Artificial
Intelligence Challenge 2025; that recognition concerns the methodology and is
not a review or endorsement of the mathematics here, which rests solely on
the Lean 4 kernel and CI.

AI cross-validation is not a substitute for mathematical peer review. A
machine-checked proof shows that a formal conclusion follows from its formal
definitions and hypotheses, not that the formalization captures every aspect
of the physical Yang–Mills problem.

## Authors

Authorship is collective, human–AI: every AI model that contributed
materially is a coauthor, identified as an AI model; developer companies are
not authors, participants or affiliations. Jucelha Carvalho is the human
author, coordinator, release custodian and responsible party, not the sole
author. Roles are not rankings; the repository exists because they were
cumulative.

- **Jucelha Carvalho (Smart Tour Brasil)** — coordination, scope and epistemological decisions, provenance, custody, integration supervision, release authorization.
- **GPT-5.6 "Sol" (AI model)** — theorem and stone architecture, formal specifications, scope control, mathematical review, audit methodology.
- **Claude Fable 5 (AI model)** — Lean 4 implementation and debugging of the Phase 3 stones through 50, CI integration, initial Stone 51 iterations.
- **Claude Fable 5.1 (AI model)** — Lean implementation of Stone 51, publication and integration operations, hygiene audits, post-51 reorganization.
- **Kimi 3 (AI model)** — external adversarial mathematical review of Stones 47–51 (audits, not build reproductions).
- **Manus AI 1.6 (AI model)** — DevOps and operations; reproducibility and release reviews of Stones 48–50; reproduction of gate 51-A.
- **Codex v2 (AI model)** — custody, reproduction and reading audit of Stone 51, independent from the Lean implementer but not from the architect's model family; not a human peer review.
- **Claude Opus 4.5 (AI model)**, **Claude Opus 4.6 (AI model)**, **Claude Opus 4.7 (AI model)** — formal-verification work, incomplete-proof reduction, historical-code recovery, forensic inventory, dependency mapping.
- **Claude Opus 5 (AI model)** — technical review of the Stone 50 reproduction path (not a completed or artifact-verified reproduction).
- **GPT-5.2 (AI model)** — early axiom reformulation, conditional-theorem design, strategic planning.
- **Gemini 3 Pro (AI model)** — early conceptual exploration, drafts, hypothesis exploration, historical architecture.
- **Grok 4.5 (AI model)** — additional independent external audit of the Stone 49 chain and scope.
- **Grok 4.6 (AI model)** — additional reported Linux reproduction of the frozen Stone 50 candidate (reported corroboration, not artifact-verified).

Formal verification: Lean 4 kernel and GitHub Actions — verification
instances, not authors. Scientific coauthorship and legal copyright ownership
are distinct records.

## Community feedback and acknowledgments

We thank Michael R Douglas, Colin Bundschu, Jack McCarthy and Ron Nissim for
comments, critical feedback and references shared during public discussions
of the project in the Lean community; the feedback contributed to the
terminology correction and to the repository reorganization. These
acknowledgments recognize public feedback and pointers to related work; they
do not imply coauthorship, endorsement of the results or participation in the
Lean proofs.

## License

Code and configuration (Lean sources, lakefiles, toolchain pins, workflows)
are licensed under the Apache License 2.0 — see [`LICENSE`](LICENSE).
Documentation and textual materials (README, release notes, Markdown files)
are licensed under Creative Commons Attribution 4.0 International — see
[`LICENSE-DOCUMENTATION`](LICENSE-DOCUMENTATION). Comments inside `.lean`
files follow the license of the code. Version 50 remains licensed as
published on Zenodo (CC BY 4.0).

## Citation

Please cite this repository as an exploratory Lean 4 formalization project,
not as progress establishing the Millennium Problem.

```text
Carvalho, Jucelha (Smart Tour Brasil, ORCID 0009-0004-6047-2306);
GPT-5.6 "Sol" (AI model); Claude Fable 5 (AI model);
Claude Fable 5.1 (AI model); Kimi 3 (AI model); Manus AI 1.6 (AI model);
Codex v2 (AI model); Claude Opus 4.5 (AI model);
Claude Opus 4.6 (AI model); Claude Opus 4.7 (AI model);
Claude Opus 5 (AI model); GPT-5.2 (AI model); Gemini 3 Pro (AI model);
Grok 4.5 (AI model); Grok 4.6 (AI model) (2026).
A Lean 4 Formalization Program Around the Yang–Mills Mass Gap — Version 51:
Finite-Volume Exponential Stability Under Remote Polymer-Activity
Restriction. Zenodo.
https://doi.org/10.5281/zenodo.22305341
```

## Contact

Jucelha Carvalho — jucelha@smarttourbrasil.com.br —
<https://orcid.org/0009-0004-6047-2306>
