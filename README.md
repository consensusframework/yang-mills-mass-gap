# Finite-Volume Lattice Gauge Theory in Lean 4 — A Formalization Program Around the Yang–Mills Mass Gap

We are building and publishing, step by step, a formal, verifiable research
program directed at the Yang–Mills existence and mass-gap problem. Its
currently proved results concern finite-volume lattice gauge theory in the
small-β (strong-coupling, Wilson convention) regime; the most recent, Stone 53,
establishes Lipschitz stability, in the damping parameter, of the normalized
polymer functional under continuous remote polymer-activity damping.

> **Scope.** Every verified result is a finite-lattice theorem. The repository
> is **not a proof, partial proof or claimed solution** of the Yang–Mills
> Existence and Mass Gap Millennium Problem; see "What this is not".

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22738731.svg)](https://doi.org/10.5281/zenodo.22738731)
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
| Library | `Phase3/LatticeGauge`, 113 modules, 34,585 Lean source lines; 1,665 top-level declaration lines by a textual count (`grep -cE` of lines beginning with `theorem`, `lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or `class` followed by a space, at commit `a7ae1c0…`; 1,636 at the Version 52 commit `f4015c5…`), not an exhaustive inventory of the declarations elaborated by Lean |
| `sorry` | 0 |
| Project-specific scientific axioms | 0 (kernel axioms only: `propext`, `Classical.choice`, `Quot.sound`) |
| Toolchain | Lean 4.15.0, Mathlib `v4.15.0` (pinned in `Phase3/lakefile.toml`) |
| CI | single job `build-phase3`: clean build of `Phase3/` + a dedicated `#print axioms` check of the three capstones of Versions 49–51, green on `main` at `a7ae1c0…` (run 484); the seven certificates of the Stone 52 capstone module and the 29 certificates of the two Stone 53 modules are emitted during the build and visible in the CI log |
| Frozen release | tag `zenodo-v52` (→ commit `f4015c5c8e7376a924c3ec3ab3dc7c00097e6085`), Version 52 DOI [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731) — the most recent deposited version; it contains Stone 52 and not Stone 53 |
| Integrated, not deposited | Stone 53 on `main` since merge commit `a7ae1c0cb81aa8829c056482afc74f9629485fd6` (PR #28); no tag, release or Zenodo record — see [`docs/stone53/RESULTS.md`](docs/stone53/RESULTS.md) |

Detailed records: [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md),
[`RELEASE_NOTES_PEDRA51.md`](RELEASE_NOTES_PEDRA51.md),
[`docs/stone52/RESULTS.md`](docs/stone52/RESULTS.md) (Stone 52 and its
provenance), [`docs/audits/stone52/`](docs/audits/stone52/README.md) (the
seven Stone 52 stage audits and the Kimi 3 review),
[`docs/stone53/RESULTS.md`](docs/stone53/RESULTS.md) (Stone 53),
[`docs/audits/stone53/`](docs/audits/stone53/README.md) (the Stone 53 QA1
reproduction, the Kimi 3 review and the publication record),
[`formalization.yaml`](formalization.yaml) (mathlib-initiative schema v0.4).
The release notes of Version 52 are an asset of the GitHub Release
[`zenodo-v52`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v52),
external to the tree.

## Principal results

All five hold in finite volume for `0 ≤ β ≤ 1/40000` (Wilson convention:
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

4. **Version 52 — exponential stability under continuous remote
   polymer-activity damping.**
   `LatticeGauge.abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay`
   (`Phase3/LatticeGauge/ActivityDampingStability.lean`): under the hypotheses
   of Version 51 and a damping parameter `0 ≤ θ ≤ 1`,

   ```
   |gibbsExpectation f − activityDampedExpectation f s r θ|
       ≤ (1 − θ) · (2 · Cf) · exp(8 · D_s / 113) · exp(−n / 2),
   ```

   through the sharper two-term form
   `(1 − θ) · Cf · exp(−n/2) · [exp(8·D_s/113) + exp(4·D_s/113)]`.
   `activityDampedExpectation` is the normalized polymer functional in which
   the activity of every polymer touching `r` is multiplied by `θ` (activities
   outside `r` unchanged); it is not a second Gibbs measure, a modified action
   or a boundary condition. `θ = 0` recovers the Version 51 estimate with the
   same constant and rate; `θ = 1` and `r = ∅` are exact identities with the
   Gibbs expectation. `0 ≤ Cf` is derived, not assumed. The theorem bounds the
   deviation for one `θ`; it does not assert monotonicity in `θ` or any
   infinite-volume statement. Details, endpoints, the six gates and the
   CI/merge record: [`docs/stone52/RESULTS.md`](docs/stone52/RESULTS.md).

5. **Stone 53 (integrated on `main`, not deposited) — Lipschitz stability of
   the damped functional in the damping parameter.**
   `LatticeGauge.abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay`
   (`Phase3/LatticeGauge/ActivityDampingLipschitz.lean`): for
   `F(θ) = activityDampedExpectation f s r θ` and two damping parameters
   `θ, θ′ ∈ [0, 1]`,

   ```
   |F(θ) − F(θ′)|
       ≤ |θ − θ′| · Cf · exp(−n/2) · [exp(8·D_s/113) + exp(4·D_s/113)]
       ≤ |θ − θ′| · (2 · Cf) · exp(8 · D_s / 113) · exp(−n / 2),
   ```

   the same constant as Version 52, now as a Lipschitz constant uniform in
   `θ`, `θ′` and `r`. Hypotheses: the small-β regime, `χ` bounded and
   measurable, `f` measurable with `|f| ≤ Cf` (`0 ≤ Cf` derived), and
   `WalkBarrierSeparated s r n`; **no `DependsOnlyOn f s`** is needed between
   the two functionals (without it, `s` is a parameter of the functional, not
   asserted to be a support of `f`); the exact ledger behind the estimate needs
   neither measurability, nor a majorant, nor separation; `DependsOnlyOn f s`
   enters only when `F(1)` is identified with the Gibbs expectation (endpoint
   `θ′ = 1`, which recovers the Version 52 estimate). Endpoints: `θ = θ′`
   (difference 0), `θ′ = 0` (distance to the Version 51 functional with the
   factor `θ`), `r = ∅` (exact identity for all real `θ, θ′`). Not asserted:
   monotonicity in `θ`, a derivative in `θ`, a second Gibbs measure, or any
   infinite-volume statement. Details, the two modules and the CI/merge record:
   [`docs/stone53/RESULTS.md`](docs/stone53/RESULTS.md).

Kernel certificates: the three capstones of Versions 49–51 are re-checked by a
dedicated CI step on every run; the seven declarations of the Stone 52 capstone
module and the 29 declarations of the two Stone 53 modules carry in-file
`#print axioms` certificates emitted during the build. All report
`[propext, Classical.choice, Quot.sound]`.

## Reproduce

```sh
git clone https://github.com/consensusframework/yang-mills-mass-gap
cd yang-mills-mass-gap/Phase3
lake update            # resolves the pinned Mathlib (v4.15.0)
lake exe cache get     # optional: Mathlib build cache
lake build             # 113 modules; ~8–9 min on 2 vCPU with the cache
```

The CI step `Kernel certificates` (`.github/workflows/lean-ci.yml`) re-checks
the three `#print axioms` certificates of Versions 49–51 with `lake env lean`;
the Stone 52 and Stone 53 certificates are printed by `lake build` itself
(modules `LatticeGauge.ActivityDampingStability`,
`LatticeGauge.ActivityDampingLipschitzInfrastructure` and
`LatticeGauge.ActivityDampingLipschitz`).

## Repository layout

```
Phase3/LatticeGauge/            the verified library (namespace LatticeGauge)
Phase3/lakefile.toml            Lake project, pinned Mathlib
Phase3/lean-toolchain           Lean toolchain pin
formalization.yaml              mathlib-initiative metadata (v0.4)
VERIFICATION_STATUS.md          verification record
RELEASE_NOTES_PEDRA51.md        release notes of Version 51
docs/stone52/RESULTS.md         Stone 52: statement, endpoints, gates, CI and merge record
docs/audits/stone52/            the seven Stone 52 stage-audit packages, reports and the Kimi 3 review
docs/stone53/RESULTS.md         Stone 53: statement, hypotheses, endpoints, modules, CI and merge record
docs/audits/stone53/            Stone 53: QA1 reproduction package, Kimi 3 review, publication record
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
The most recent deposited version is Version 52 — [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731),
tag [`zenodo-v52`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v52)
(a simple tag pointing to commit `f4015c5c8e7376a924c3ec3ab3dc7c00097e6085`,
root tree `9087e69d…`, `Phase3/` tree `bf2fae8c…`; GitHub Release with four
assets: the snapshot ZIP, `RELEASE_NOTES_PEDRA52.md`, `MANIFEST_v52.txt` and
`SHA256SUMS.3.txt`, published by the coordinator). Previous versions:
Version 51 — [10.5281/zenodo.22305341](https://doi.org/10.5281/zenodo.22305341)
(tag `zenodo-v51`); Version 50 — [10.5281/zenodo.22162464](https://doi.org/10.5281/zenodo.22162464)
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
GitHub Actions CI → integration by merge commit → post-merge CI on `main`,
with the publication steps executed through the coordinator's machine. For
Stone 52 the same chain was kept, with two changes of process: each gate was
audited, before publication, by a separate Claude Fable 5.1 instance on its
own bench (seven stage audits, preserved in
[`docs/audits/stone52/`](docs/audits/stone52/README.md); after integration,
one final adversarial review by Kimi 3, a different model family, by reading
and without Lean execution, with two corrective addenda), and the publication
steps (push of the audited bundle, pull request, merge after green CI) were
executed by a Claude Fable 5.1 instance in Claude Code under written per-gate
authorization, with repository access granted by the coordinator, who holds
the credentials, the branch ruleset and the release decisions. For Stone 53
(scientific architecture by GPT Astra) the two modules were built and, after
the audit, published by one Claude Fable 5.1 instance in Claude Code with an
executable Lean bench; the candidate was reproduced by execution by a separate
Claude Fable 5.1 instance on its own bench (QA1, same model, not blind) and
reviewed adversarially by reading by Kimi 3, a different model family,
without Lean execution (one review with one errata); both records are
preserved in [`docs/audits/stone53/`](docs/audits/stone53/README.md).
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
- **GPT-5.6 "Sol" (AI model)** — theorem and stone architecture, formal specifications, scope control, mathematical review, audit methodology (including the scientific architecture of Stone 52).
- **GPT Astra (AI model)** — review of the Stone 52 integration, custody checks on GitHub, architecture and review of the Stone 52 documentary consolidation; scientific architecture of Stone 53 (feasibility, construction, publication and consolidation tapes) and review of its sources, Git objects and evidence, without a Lean build of its own; review of the Version 52 release package.
- **Claude Fable 5 (AI model)** — Lean 4 implementation and debugging of the Phase 3 stones through 50, CI integration, initial Stone 51 iterations.
- **Claude Fable 5.1 (AI model)** — Lean implementation of Stones 51, 52 and 53, publication and integration operations, hygiene audits, post-51 reorganization; for Stone 52, also the seven stage audits (a separate instance from the implementer, same model) and the publication operations in Claude Code; for Stone 53, construction and publication in one Claude Code instance with an executable Lean bench, the QA1 reproduction by a separate instance (same model, not blind), the documentary consolidations, and the packaging of the Version 52 release assets.
- **Kimi 3 (AI model)** — external adversarial mathematical review of Stones 47–51 (audits, not build reproductions); for Stone 52, the final adversarial mathematical and code review of the integrated state `00600e0…` with two corrective addenda (reading only, no Lean execution), preserved in `docs/audits/stone52/kimi/`; for Stone 53, the final adversarial review of the candidate `abad166…` with one errata (reading only, no Lean execution, not blind), preserved in `docs/audits/stone53/kimi/`.
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
files follow the license of the code. Earlier versions remain licensed as
published on Zenodo (Version 50: CC BY 4.0).

## Citation

Please cite this repository as an exploratory Lean 4 formalization project,
not as progress establishing the Millennium Problem. The citation below is the
**deposited** Version 52 record (commit `f4015c5c…`); Stone 53 is integrated on
`main` (commit
[`a7ae1c0cb81aa8829c056482afc74f9629485fd6`](https://github.com/consensusframework/yang-mills-mass-gap/commit/a7ae1c0cb81aa8829c056482afc74f9629485fd6))
and has no Zenodo record; to refer to it, cite the commit. The Version 51
citation (DOI [10.5281/zenodo.22305341](https://doi.org/10.5281/zenodo.22305341))
remains valid for that deposited record.

```text
Carvalho, Jucelha (Smart Tour Brasil, ORCID 0009-0004-6047-2306);
GPT-5.6 "Sol" (AI model); GPT Astra (AI model); Claude Fable 5 (AI model);
Claude Fable 5.1 (AI model); Kimi 3 (AI model); Manus AI 1.6 (AI model);
Codex v2 (AI model); Claude Opus 4.5 (AI model);
Claude Opus 4.6 (AI model); Claude Opus 4.7 (AI model);
Claude Opus 5 (AI model); GPT-5.2 (AI model); Gemini 3 Pro (AI model);
Grok 4.5 (AI model); Grok 4.6 (AI model) (2026).
A Lean 4 Formalization Program Around the Yang–Mills Mass Gap — Version 52:
Finite-Volume Exponential Stability Under Remote Polymer-Activity
Damping. Zenodo.
https://doi.org/10.5281/zenodo.22738731
```

## Contact

Jucelha Carvalho — jucelha@smarttourbrasil.com.br —
<https://orcid.org/0009-0004-6047-2306>
