# Finite-Volume Lattice Gauge Theory in Lean 4 — A Formalization Program Around the Yang–Mills Mass Gap

We are building and publishing, step by step, a formal, verifiable research
program directed at the Yang–Mills existence and mass-gap problem. Its
currently proved results concern finite-volume lattice gauge theory in the
small-β (strong-coupling, Wilson convention) regime; the most recent, Stones
53, 54 and 55, establish Lipschitz stability, in the damping parameter, of the
normalized polymer functional under continuous remote polymer-activity
damping, with the constant refined in Stone 54 and, in Stone 55, the scalar
damping parameter replaced by a profile of factors, one per polymer, with the
same constant.

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
| Library | `Phase3/LatticeGauge`, 116 modules, 37,030 Lean source lines; 1,756 top-level declaration lines by a textual count (`grep -cE` of lines beginning with `theorem`, `lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or `class` followed by a space, at commit `d6ce3d7…`; 1,678 at the Version 54 commit `9358faa…` and at `9c0f6fd…`, 1,665 at the Version 53 commit `571b83a…`, 1,636 at the Version 52 commit `f4015c5…`), not an exhaustive inventory of the declarations elaborated by Lean and not a count of theorems; 247 in-file `#print axioms` commands (179 at Version 54, 166 at Version 53), which certify the declarations they name, not every declaration of the library |
| `sorry` | 0 |
| Project-specific scientific axioms | 0 (kernel axioms only: `propext`, `Classical.choice`, `Quot.sound`) |
| Toolchain | Lean 4.15.0, Mathlib `v4.15.0` (pinned in `Phase3/lakefile.toml`); dependency manifest `Phase3/lake-manifest.json` (SHA-256 `c376bbe9…1227`, Mathlib at `9837ca9d…`, the commit of the tag `v4.15.0`) committed by the maintenance after the Version 54 snapshot — see [Reproduce](#reproduce) |
| CI | single job `build-phase3`: clean build of `Phase3/` + a dedicated `#print axioms` check of the three capstones of Versions 49–51, green on `main` at the Stone 55 merge `d6ce3d7…` (run 494; previously at the Version 54 commit `9358faa…`, run 490); from the maintenance commit after `9358faa…`, the job resolves dependencies from the committed manifest instead of running `lake update`, and checks the manifest byte-identical before and after the build; the seven certificates of the Stone 52 capstone module, the 29 certificates of the two Stone 53 modules, the 13 certificates of the Stone 54 module and the 68 certificates of the two Stone 55 modules are emitted during the build and visible in the CI log |
| Deposited | Version 54: tag `zenodo-v54` (→ commit `9358faa27b44ce24b3b9fe035cba94a68448e034`, the Stone 54 snapshot with its documentation; Stone 54 itself integrated at `9c0f6fde…`, PR #30), GitHub Release with four assets published by the coordinator on 2026-09-15, and Zenodo record DOI [10.5281/zenodo.22767474](https://doi.org/10.5281/zenodo.22767474) published on Zenodo on 2026-09-15 (confirmed by the coordinator and by a capture of the record page; the consolidating session could not reach Zenodo itself) — the most recent Zenodo deposit; it contains Stones 52–54 and not `Phase3/lake-manifest.json`, added afterwards by the maintenance commit, nor Stone 55 — see [`docs/stone54/RESULTS.md`](docs/stone54/RESULTS.md) |
| Deposited | Version 52: tag `zenodo-v52` (→ commit `f4015c5c8e7376a924c3ec3ab3dc7c00097e6085`), DOI [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731); it contains Stone 52 and not Stones 53–55 |
| GitHub Release | Version 53: tag `zenodo-v53` (→ commit `571b83aadb53838eb8257c015b7c02d3e57d30ad`, the Stone 53 snapshot with its documentation), GitHub Release published by the coordinator; DOI 10.5281/zenodo.22750453 reserved for the Zenodo record — its publication on Zenodo is not confirmed here |
| Integrated, not deposited | Stone 55: integrated on `main` at `d6ce3d7232f08b5f975dfa8c6f43ec5031937e10` (PR #33, 2026-09-17), audited (QA1 reproduction; Kimi 3 review with one errata) and CI-verified (run 494); no tag, Release, deposit or DOI of its own — cite the commit. The documentary consolidation of Stone 55 is the candidate snapshot of a future Version 55 — see [`docs/stone55/RESULTS.md`](docs/stone55/RESULTS.md) |

Detailed records: [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md),
[`RELEASE_NOTES_PEDRA51.md`](RELEASE_NOTES_PEDRA51.md),
[`docs/stone52/RESULTS.md`](docs/stone52/RESULTS.md) (Stone 52 and its
provenance), [`docs/audits/stone52/`](docs/audits/stone52/README.md) (the
seven Stone 52 stage audits and the Kimi 3 review),
[`docs/stone53/RESULTS.md`](docs/stone53/RESULTS.md) (Stone 53),
[`docs/audits/stone53/`](docs/audits/stone53/README.md) (the Stone 53 QA1
reproduction, the Kimi 3 review and the publication record),
[`docs/stone54/RESULTS.md`](docs/stone54/RESULTS.md) (Stone 54),
[`docs/audits/stone54/`](docs/audits/stone54/README.md) (the Stone 54 QA1
reproduction, the Kimi 3 review and the publication record),
[`docs/stone55/RESULTS.md`](docs/stone55/RESULTS.md) (Stone 55),
[`docs/audits/stone55/`](docs/audits/stone55/README.md) (the Stone 55 QA1
reproduction, the Kimi 3 review with its errata and the publication record),
[`formalization.yaml`](formalization.yaml) (mathlib-initiative schema v0.4).
The release notes of Version 52 are an asset of the GitHub Release
[`zenodo-v52`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v52),
external to the tree.

## Principal results

All seven hold in finite volume for `0 ≤ β ≤ 1/40000` (Wilson convention:
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

6. **Stone 54 (Version 54, GitHub Release `zenodo-v54`, Zenodo DOI 10.5281/zenodo.22767474) — the same Lipschitz
   stability with the connector column at κ = 2.**
   `LatticeGauge.abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined`
   (`Phase3/LatticeGauge/ActivityDampingLipschitzRefined.lean`): under exactly
   the hypotheses, interval and rate of Stone 53,

   ```
   |F(θ) − F(θ′)|
       ≤ |θ − θ′| · Cf · exp(−n/2) · [exp(6·D_s/113) + exp(4·D_s/113)]
       ≤ |θ − θ′| · (2 · Cf) · exp(6 · D_s / 113) · exp(−n / 2),
   ```

   the prefactor of the first exponential going from `exp(8·D_s/113)` to
   `exp(6·D_s/113)`: the scalar bound `|e^x − e^y| ≤ e^q·|x − y|` for
   `x, y ≤ q` (from Mathlib's `Real.add_one_le_exp`) closes the connector
   column through the budget (1/2, 2), admissible since 1/2 + 16/113 ≤ 1,
   while the ledger and the bridge column of Stone 53 are reused intact. The
   Stone 53 estimate is recovered from the refined one as a corollary. No
   optimality or priority is claimed for the constant; the comparison of the
   constants is a comparison of bounds, not of the actual deviation
   (equality of the complete constants when `Cf = 0` or `D_s = 0`). Details,
   the module, the review records and the CI/merge record:
   [`docs/stone54/RESULTS.md`](docs/stone54/RESULTS.md).

7. **Stone 55 (integrated on `main` at `d6ce3d72…`, not deposited) — the same
   stability under a profile of activity factors, one per polymer.**
   `LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_local_exp_decay`
   (`Phase3/LatticeGauge/ActivityProfileDampingStability.lean`): the scalar
   `θ` of Stones 52–54 is replaced by a profile `a : Polymer N → ℝ`, the
   activity of a polymer touching `r` being multiplied by `a η` and the
   others left unchanged (values of `a` outside `r` are never read). For two
   profiles `a, a′` with values in `[0, 1]` and a majorant `δ ≥ 0` of
   `|a η − a′ η|` on the polymers touching `r`, under the hypotheses, rate and
   regime of Stone 54,

   ```
   |F(a) − F(a′)|
       ≤ δ · Cf · exp(−n/2) · [exp(6·D_s/113) + exp(4·D_s/113)]
       ≤ δ · (2 · Cf) · exp(6 · D_s / 113) · exp(−n / 2),
   ```

   with `δ` in the place of `|θ − θ′|`, no `δ ≤ 1`, no `DependsOnlyOn f s` in
   the comparison of two profiles, `0 ≤ Cf` derived, and nothing divided by
   `δ`. The route is that of Stone 54: the product weights of the profile in
   place of the powers of `θ` (a telescoping lemma in `[0, 1]` gives the count
   bounds, tuple repetitions counted by position), the exact two-profile
   ledger with the plus sign on the bridges, the barrier bound of the exponent,
   the κ = 2 control on the connector column (budget (1/2, 2)) and the κ = 1
   bridge column (budget (7/8, 1)), erosion by the natural truncated
   subtraction. Constant profiles give back the Stone 54 estimate as an
   application, without circularity; the zero profile is the Stone 51
   restricted functional with no hypothesis, the unit profile is the Gibbs
   expectation under `DependsOnlyOn f s`, and `r = ∅` gives `F(a) = F(a′)` for
   arbitrary real profiles. Not asserted: a new Gibbs measure, a boundary
   condition, a per-link profile, monotonicity or differentiability in the
   profile, optimality or priority, or any infinite-volume statement.
   Details, the two modules, the audit records and the CI/merge record:
   [`docs/stone55/RESULTS.md`](docs/stone55/RESULTS.md).

Kernel certificates: the three capstones of Versions 49–51 are re-checked by a
dedicated CI step on every run; the seven declarations of the Stone 52 capstone
module, the 29 declarations of the two Stone 53 modules, the 13 declarations
of the Stone 54 module and the 68 theorems of the two Stone 55 modules carry
in-file `#print axioms` certificates emitted during the build. All report
`[propext, Classical.choice, Quot.sound]`.

## Reproduce

```sh
git clone https://github.com/consensusframework/yang-mills-mass-gap
cd yang-mills-mass-gap/Phase3
lake env true          # materializes the dependencies at the revisions of lake-manifest.json (no `lake update`)
lake exe cache get     # optional: Mathlib build cache
lake build             # 116 modules; ~9 min on 2 vCPU with the cache
sha256sum lake-manifest.json   # c376bbe9…1227 before and after: the manifest is not rewritten
```

**Dependency manifest.** `Phase3/lake-manifest.json` (SHA-256
`c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`) pins
Mathlib at `9837ca9d65d9de6fad1ef4381750ca688774e608` (the commit of the tag
`v4.15.0`, `inputRev` `v4.15.0`) and its eight transitive dependencies
(batteries `e8dc5fc1…`, aesop `2689851f…`, Qq `f0c584bc…`, proofwidgets
`2b000e02…` at `v0.0.48`, importGraph `9a0b533c…`, LeanSearchClient
`003ff459…`, plausible `2c57364e…`, Cli `0c8ea32a…`). It is the manifest
resolved by `lake update` from the pins of `Phase3/lakefile.toml` on the
constructor's bench, and the one whose SHA-256 the independent QA1
reproductions of Stones 52, 53 and 54 recorded before and after their builds
(`docs/audits/stone52/reports/RELATORIO_52-A0-QA1.md`,
`docs/audits/stone53/packages/QA1_53_evidence.zip` and
`docs/audits/stone54/packages/QA1_54_evidence.zip`, files
`manifest_pre_build.sha256` / `manifest_post_build.sha256`). It was committed
after the Version 54 snapshot `9358faa2…` (which does not contain it) by the
maintenance commit that also changed the CI to resolve dependencies from it
instead of running `lake update`; the CI checks that every dependency is
checked out at the recorded revision and that the manifest is byte-identical
before and after the build. Do not run `lake update`: it re-resolves the
dependencies and rewrites the manifest.

The CI step `Kernel certificates` (`.github/workflows/lean-ci.yml`) re-checks
the three `#print axioms` certificates of Versions 49–51 with `lake env lean`;
the Stone 52, 53, 54 and 55 certificates are printed by `lake build` itself
(modules `LatticeGauge.ActivityDampingStability`,
`LatticeGauge.ActivityDampingLipschitzInfrastructure`,
`LatticeGauge.ActivityDampingLipschitz`,
`LatticeGauge.ActivityDampingLipschitzRefined`,
`LatticeGauge.ActivityProfileDamping` and
`LatticeGauge.ActivityProfileDampingStability`).

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
docs/stone54/RESULTS.md         Stone 54: refined constant, route, review records, CI and merge record
docs/audits/stone54/            Stone 54: QA1 reproduction package, Kimi 3 review, publication record
docs/stone55/RESULTS.md         Stone 55: profile damping, statement, route, endpoints, audit records, CI and merge record
docs/audits/stone55/            Stone 55: QA1 reproduction package, Kimi 3 review with errata, publication record
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
Version 53 has the GitHub Release
[`zenodo-v53`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v53)
(a simple tag pointing to commit `571b83aadb53838eb8257c015b7c02d3e57d30ad`,
root tree `98bed2c3…`, `Phase3/` tree `99758dfc…`; four assets prepared for
the Zenodo record with the reserved DOI 10.5281/zenodo.22750453, whose
publication is not confirmed in this repository). The most recent Zenodo
deposit confirmed here is Version 52 — [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731),
tag [`zenodo-v52`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v52)
(a simple tag pointing to commit `f4015c5c8e7376a924c3ec3ab3dc7c00097e6085`,
root tree `9087e69d…`, `Phase3/` tree `bf2fae8c…`; GitHub Release with four
assets: the snapshot ZIP, `RELEASE_NOTES_PEDRA52.md`, `MANIFEST_v52.txt` and
`SHA256SUMS.3.txt`, published by the coordinator). Version 54 has the GitHub
Release [`zenodo-v54`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v54)
(a simple tag pointing to commit `9358faa27b44ce24b3b9fe035cba94a68448e034`,
root tree `e378c15e…`, `Phase3/` tree `7d8373f6…`; four assets — the snapshot
ZIP, `RELEASE_NOTES_PEDRA54.md`, `MANIFEST_v54.txt` and `SHA256SUMS.txt` —
published by the coordinator on 2026-09-15; Zenodo record DOI
[10.5281/zenodo.22767474](https://doi.org/10.5281/zenodo.22767474), published
on 2026-09-15 as confirmed by the coordinator and by a capture of the record
page — the current deposited version). Stone 55, integrated later at
`d6ce3d72…`, has no release or deposit of its own. Previous versions:
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
preserved in [`docs/audits/stone53/`](docs/audits/stone53/README.md). Stone 54
(scientific architecture and review by GPT Astra, from a proposal in section
E.3 of an antecedents research report on Stone 53) followed the same chain:
construction and publication by the same Claude Fable 5.1 instance, one QA1
reproduction by execution by a separate instance (same model, not blind), one
adversarial review by reading by Kimi 3 (no Lean execution, not blind), all
preserved in [`docs/audits/stone54/`](docs/audits/stone54/README.md). Stone 55
(scientific architecture and review by GPT Astra: feasibility, construction,
publication and consolidation tapes) followed the same chain: construction
and publication by the same Claude Fable 5.1 instance, one QA1 reproduction by
execution by a separate instance (same model, not blind), one adversarial
review by reading by Kimi 3 (no Lean execution, not blind) with one errata on
the attribution of the tests, all preserved in
[`docs/audits/stone55/`](docs/audits/stone55/README.md).
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
- **GPT Astra (AI model)** — review of the Stone 52 integration, custody checks on GitHub, architecture and review of the Stone 52 documentary consolidation; scientific architecture of Stones 53, 54 and 55 (feasibility, construction, publication and consolidation tapes) and review of their sources, Git objects and evidence, without a Lean build of its own; review of the Version 52, 53 and 54 release packages.
- **Claude Fable 5 (AI model)** — Lean 4 implementation and debugging of the Phase 3 stones through 50, CI integration, initial Stone 51 iterations.
- **Claude Fable 5.1 (AI model)** — Lean implementation of Stones 51, 52 and 53, publication and integration operations, hygiene audits, post-51 reorganization; for Stone 52, also the seven stage audits (a separate instance from the implementer, same model) and the publication operations in Claude Code; for Stones 53, 54 and 55, construction and publication in one Claude Code instance with an executable Lean bench, the QA1 reproductions by a separate instance (same model, not blind), the documentary consolidations, the maintenance after the Version 54 snapshot, and the packaging of the Version 52, 53 and 54 release assets.
- **Kimi 3 (AI model)** — external adversarial mathematical review of Stones 47–51 (audits, not build reproductions); for Stone 52, the final adversarial mathematical and code review of the integrated state `00600e0…` with two corrective addenda (reading only, no Lean execution), preserved in `docs/audits/stone52/kimi/`; for Stone 53, the final adversarial review of the candidate `abad166…` with one errata (reading only, no Lean execution, not blind), preserved in `docs/audits/stone53/kimi/`; for Stone 54, the adversarial review of the scientific merge `9c0f6fd…` (reading and mathematical analysis, no Lean execution, not blind), preserved in `docs/audits/stone54/kimi/`; for Stone 55, the adversarial review of the candidate `0c50b6d…` and the scientific merge `d6ce3d7…` with one errata on the attribution of the tests (reading and mathematical analysis, no Lean execution, not blind), preserved in `docs/audits/stone55/kimi/`.
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
**published** Version 54 record (commit
[`9358faa27b44ce24b3b9fe035cba94a68448e034`](https://github.com/consensusframework/yang-mills-mass-gap/commit/9358faa27b44ce24b3b9fe035cba94a68448e034),
GitHub Release `zenodo-v54`, Zenodo DOI 10.5281/zenodo.22767474, published on
2026-09-15; concept DOI 10.5281/zenodo.17397622 for all versions). Stone 55
(integrated at commit `d6ce3d72…`) has no deposit of its own: cite the commit.
Version 53 (commit `571b83aa…`, GitHub Release `zenodo-v53`, reserved DOI
10.5281/zenodo.22750453) may be cited by its DOI once its Zenodo record is
confirmed published; until then, cite the commit. The Version 52 citation
(DOI [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731)) and
the Version 51 citation
(DOI [10.5281/zenodo.22305341](https://doi.org/10.5281/zenodo.22305341))
remain valid for those deposited records.

```text
Carvalho, Jucelha (Smart Tour Brasil, ORCID 0009-0004-6047-2306);
GPT-5.6 "Sol" (AI model); GPT Astra (AI model); Claude Fable 5 (AI model);
Claude Fable 5.1 (AI model); Kimi 3 (AI model); Manus AI 1.6 (AI model);
Codex v2 (AI model); Claude Opus 4.5 (AI model);
Claude Opus 4.6 (AI model); Claude Opus 4.7 (AI model);
Claude Opus 5 (AI model); GPT-5.2 (AI model); Gemini 3 Pro (AI model);
Grok 4.5 (AI model); Grok 4.6 (AI model) (2026).
A Lean 4 Formalization Program Around the Yang–Mills Mass Gap — Version 54:
Refined Finite-Volume Lipschitz Stability Under Remote Polymer-Activity
Damping. Zenodo.
https://doi.org/10.5281/zenodo.22767474
```

## Contact

Jucelha Carvalho — jucelha@smarttourbrasil.com.br —
<https://orcid.org/0009-0004-6047-2306>
