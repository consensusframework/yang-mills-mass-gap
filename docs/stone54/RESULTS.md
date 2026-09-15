# Stone 54 — refined Lipschitz stability of the damped functional: the connector column at κ = 2

Integrated state of `main` at commit
[`9c0f6fdecee5c8628a2434d032e421edc78bb722`](https://github.com/consensusframework/yang-mills-mass-gap/commit/9c0f6fdecee5c8628a2434d032e421edc78bb722)
(merge of [PR #30](https://github.com/consensusframework/yang-mills-mass-gap/pull/30);
root tree `eaffdb1355a515bb7686831d07c767c39739f2bb`, `Phase3/` tree
`7d8373f682a10a70e4db6f701e08fb7c1dbb6908`). At consolidation time
(2026-09-14) Stone 54 was integrated on `main`, audited and CI-verified, but
not part of any release: the most recent GitHub Release was `zenodo-v53`
(commit `571b83aa…`, Version 53, with a reserved DOI) and the most recent
Zenodo deposit confirmed by this repository's records was Version 52 (DOI
[10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731)). Since
then the consolidated state was frozen as **Version 54** at commit
`9358faa27b44ce24b3b9fe035cba94a68448e034` (merge of PR #31), tag
`zenodo-v54`, with a GitHub Release published by the coordinator on 2026-09-15
and the DOI 10.5281/zenodo.22767474 reserved for its Zenodo record; see §8,
added by the maintenance after that snapshot. The most recent Zenodo deposit
confirmed by this repository's records remains Version 52.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. Nothing here asserts monotonicity or differentiability of
> the damped functional in θ, a second Gibbs measure, a boundary condition or a
> spatial-mixing theorem; no optimality, sharpness or bibliographic priority is
> claimed for the constant.

## 1. The statement

Principal declaration:
`LatticeGauge.abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_refined`
([`Phase3/LatticeGauge/ActivityDampingLipschitzRefined.lean`](../../Phase3/LatticeGauge/ActivityDampingLipschitzRefined.lean)).

Write `F(θ) = activityDampedExpectation μm β χ f s r θ` (the normalized polymer
functional of Stone 52, in which the activity of every polymer touching the
region `r` is multiplied by `θ`) and `D_s = card (supportLinkFinset s)`. For
`θ, θ′ ∈ [0, 1]`:

```
|F(θ) − F(θ′)|
    ≤ |θ − θ′| · Cf · exp(−n / 2) · [exp(6 · D_s / 113) + exp(4 · D_s / 113)]
    ≤ |θ − θ′| · (2 · Cf) · exp(6 · D_s / 113) · exp(−n / 2).
```

The first line is the refined two-term estimate
(`abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms_refined`);
the capstone follows from `exp(4·D_s/113) ≤ exp(6·D_s/113)` (`D_s ≥ 0`). Compared
with Stone 53, the prefactor of the first exponential goes from
`exp(8·D_s/113)` to `exp(6·D_s/113)`; **the hypotheses, the interval
`[0, 1]` and the rate `exp(−n/2)` are exactly those of the Stone 53 capstone.**
Nothing is divided by `|θ − θ′|`.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`.

| Hypothesis | Meaning |
|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | `χ : G → ℝ` is a bounded measurable real function (the capstone does not require `χ` to be a representation character) |
| `mf : Measurable f`, `hCf : ∀ U, \|f U\| ≤ Cf` | measurability and an absolute majorant of the observable; `0 ≤ Cf` is **derived** (`nonneg_of_abs_le_of_config`, 52-E), not assumed |
| `hsep : WalkBarrierSeparated s r n` | walk-barrier separation of the set `s` from the damped region `r` at scale `n` |
| `h0 h1 h0' h1' : 0 ≤ θ ≤ 1, 0 ≤ θ′ ≤ 1` | the two damping parameters |

`DependsOnlyOn f s` is **not** a hypothesis of the capstone between the two
functionals (without it, `s` is a parameter of the functional, not asserted to
be a support of `f`); it enters only where `F(1)` is identified with the Gibbs
expectation (endpoint θ′ = 1). No sign condition on activities or exponents
is used.

## 2. The route

- **Direct comparison of two parameters.** The exact two-parameter ledger of
  Stone 53 (`activityDampedExpectation_sub_eq_two_column_lipschitz_ledger`,
  bridge column with a **plus** sign) is reused intact; the difference of the
  two functionals is never routed through the Gibbs expectation.
- **Connector column at κ = 2.** Both exponents `E_T(θ), E_T(θ′)` are bounded
  above by `q_T = card(barrierLinkFinset T s)·(2/113)` (Stone 53,
  `abs_dampedActivityCoreExponent_le_barrier`). The scalar bound
  `|e^x − e^y| ≤ e^q·|x − y|` for real `x, y ≤ q`
  (`abs_exp_sub_exp_le_exp_mul_abs_sub`, proved from Mathlib's
  `Real.add_one_le_exp` — not by the mean-value theorem — with no sign
  condition on `x, y` and no exponential of `|x − y|`) gives
  `|e^{E_T(θ)} − e^{E_T(θ′)}| ≤ e^{q_T}·|E_T(θ) − E_T(θ′)|`; the exponent
  difference is the connector difference (Stone 53), eroded:
  `|E_T(θ) − E_T(θ′)| ≤ |θ − θ′|·e^{−((n − m_T : ℕ))/2}·q_T`; then `q_T ≤ e^{q_T}`
  (`le_exp_self`) and the repurchased erosion give
  `|e^{E_T(θ)} − e^{E_T(θ′)}| ≤ |θ − θ′|·e^{−n/2}·e^{m_T/2 + 2·q_T}` — two
  barrier exponentials instead of the three of Stone 53. The core weight is
  bounded without exponential (`|W_T| ≤ Cf·Π M`) and `0 ≤ θ′^t ≤ 1`.
- **Budget (1/2, 2).** The column closes through the generic budget
  `coreLocalBudget` at `λ = 1/2, κ = 2` (`sum_halfTilt_two_le`, a wrapper of
  `coreLocalBudget_connector`), admissible because
  `1/2 + 2·(8/113) = 145/226 ≤ 1`, with prefactor `exp((2+1)·D_s·(2/113)) = exp(6·D_s/113)`.
- **Bridge column reused.** The bridge column of Stone 53 is consumed intact
  (`abs_sum_lipschitzBridgeColumn_le`: κ = 1, tilt 7/8, prefactor
  `exp(4·D_s/113)`).
- **Erosion with the natural truncated subtraction.** `n − m_T` is computed in
  ℕ before the cast: when the core mass `m_T` exceeds `n` the erosion factor is
  `1`, never an explosion; when `q_T = 0` the bound degenerates coherently.
- **Refined ⇒ Stone 53, without circularity.** `refined_constant_le_published_constant`
  (`2·Cf·e^{6 D_s/113}·e^{−n/2} ≤ 2·Cf·e^{8 D_s/113}·e^{−n/2}` for `0 ≤ Cf`) and
  `…_le_local_exp_decay_of_refined` re-derive the Stone 53 capstone from the
  refined one. The Stone 53 capstone is not used in any Stone 54 proof (it
  appears only in a docstring); Stone 54 imports Stone 53 and the published
  modules are untouched.

## 3. Endpoints and the comparison of constants

| Endpoint | Declaration | Content |
|---|---|---|
| θ = θ′ | (capstone applied) | the right-hand side vanishes because nothing was divided by `\|θ − θ′\|`; exercised by the auditor's test V4a and the constructor's test T2 |
| θ′ = 1 | `abs_activityDampedExpectation_sub_gibbsExpectation_le_refined` | with `DependsOnlyOn f s`, `F(1)` is the Gibbs expectation (52-A): `\|F(θ) − gibbs\| ≤ (1 − θ)·2·Cf·e^{6 D_s/113}·e^{−n/2}` — the Stone 52 statement with the smaller prefactor |
| θ′ = 0 | `abs_activityDampedExpectation_sub_activityRestrictedExpectation_le_refined` | the distance to the Stone 51 functional with the factor `θ`; no `DependsOnlyOn f s` |
| r = ∅ | (Stone 53 identity reused) | `F(θ) = F(θ′)` exactly for all real θ, θ′; the refined capstone is not extrapolated outside `[0, 1]` |

**Precise comparison of the constants (record D1 of the 54-QA1 audit,
confirmed by the Kimi 3 review).** The declaration
`refined_constant_le_published_constant` states only the inequality
`2·Cf·e^{6 D_s/113}·e^{−n/2} ≤ 2·Cf·e^{8 D_s/113}·e^{−n/2}` under `0 ≤ Cf`, and
it is correct. Its docstring says the two constants "agree exactly when
`D_s = 0`", which omits the case `Cf = 0`: under `Cf ≥ 0`, the complete
constants coincide exactly when `Cf = 0` or `D_s = 0`; a strict improvement
requires `Cf > 0` and `D_s > 0`. In the complete right-hand sides, θ = θ′ also
produces equality at zero. This compares **bounds**; it says nothing about a
decrease of the actual deviation `|F(θ) − F(θ′)|`. The docstring is left as
committed (the scientific module is not edited by the documentary
consolidation); this note is the record of the precision, with reference to
the original declaration.

## 4. The module

One new module (523 Lean lines; 13 top-level declaration lines, a textual
count by `grep -cE` of lines beginning with `theorem`, `lemma`, `def`,
`abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or `class`
followed by a space, at commit `410bde81…` — all 13 are `theorem`; 13 in-file
`#print axioms` certificates), a leaf over Stone 53; no pre-existing module was
modified; the only change outside the new file is its glob in
`Phase3/lakefile.toml` (113 → 114 modules).

| Gate | Module | Lines / decls / certs | Content |
|---|---|---|---|
| 54-A | `ActivityDampingLipschitzRefined.lean` | 523 / 13 / 13 | the scalar bounds `exp_sub_exp_le_exp_mul_abs_sub` (one-sided, `x ≤ q` only), `abs_exp_sub_exp_le_exp_mul_abs_sub` (two-sided, `x, y ≤ q`), `le_exp_self`; the refined exponential control `abs_exp_dampedActivityCoreExponent_sub_le_decay_refined` (κ = 2); the refined connector column (`abs_refinedConnectorColumnTerm_le`, `sum_abs_refinedConnectorColumn_le`, `abs_sum_refinedConnectorColumn_le`, budget (1/2, 2)); the refined two-term estimate; the refined capstone; `refined_constant_le_published_constant`; the Stone 53 capstone re-derived (`…_of_refined`); the endpoints θ′ = 1 and θ′ = 0 |

Imports: `LatticeGauge.ActivityDampingLipschitz` (Stone 53) and
`LatticeGauge.CovarianceDecay` (Stone 50, gate 50-A19c, per the header of that
source), the latter only for the one-line wrapper `sum_halfTilt_two_le`
(record I1: avoidable, legitimate, preserved; no decay result of that module
is consumed).

Origin of the proposal: section E.3 of the antecedents-and-originality
research report on Stone 53 received by the coordinator ("κ = 3 is not a
demonstrated necessity"), followed by the architectural review of GPT Astra.
The report does not name the researching model; no identity is invented. No
optimality, priority or exclusivity of the route is claimed.

## 5. Kernel certificates and CI

- Every one of the 13 declarations carries an in-file `#print axioms`
  certificate; each reports `[propext, Classical.choice, Quot.sound]`. They are
  emitted during `lake build` and are visible in the CI logs of runs 487 and
  488; the dedicated CI step `Kernel certificates` still checks the three
  capstones of Versions 49–51 and was not extended.
- Hygiene in the module: 0 `sorry`, 0 `admit`, 0 scientific `axiom`,
  0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`; 114 inherited build
  warnings (unchanged since Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`,
  delivered as a verifiable git bundle; the QA1 audit before publication; push
  of the audited commit, a non-draft pull request, `build-phase3` green on the
  pull-request head, a normal merge with the expected head SHA locked (no
  squash, no rebase), and `build-phase3` green again on `main` at the merge
  commit; then the adversarial review of the integrated state.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `410bde8146e8f14b698a03387da395a79f81f9eb` | [#30](https://github.com/consensusframework/yang-mills-mass-gap/pull/30) | [487](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34875314038) (id 34875314038) | `9c0f6fdecee5c8628a2434d032e421edc78bb722` | [488](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34876420216) (id 34876420216) |

Custody note: the pull-request run 487 is associated with the head
`410bde81…`, but its effective checkout was the provisional merge commit
`9a9c9eb` ("Merge 410bde81… into 571b83aa…"), as recorded in the job log read
by the publishing instance (`docs/audits/stone54/publication/RELATORIO_54-P.md`);
run 488 compiled the definitive merge `9c0f6fde…` itself (job log read by the
same instance). The run metadata alone do not prove the effective checkout;
the attribution is to the log reading. The merge commit has parents
`571b83aa…` (the base, the Version 53 commit) and `410bde81…`, and its tree
`eaffdb13…` is the tree of the candidate; both runs report `Build completed
successfully`, 114 `LatticeGauge` modules built, 0 replayed, 0 errors, no
`sorryAx`, 114 inherited warnings and none in the new module, and the 13
certificates as above.

Toolchain at `9c0f6fde…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`); the library has 114 modules and 35,108 Lean source
lines. The resolved dependency manifest (`lake-manifest.json`, SHA-256
`c376bbe9…1227`, Mathlib `9837ca9d…`) was not in the tree at `9c0f6fde…` nor
at the Version 54 snapshot; it was committed by the later maintenance (§8).

## 6. Relation to Stone 53

Stone 53 proved the Lipschitz estimate with the constant
`2·Cf·exp(8·D_s/113)·exp(−n/2)`, closing the connector column at κ = 3 through
the factorization `e^{E(θ)} − e^{E(θ′)} = e^{E(θ′)}·(e^{Δ} − 1)`. Stone 54 keeps
the same ledger, bridge column, hypotheses, interval and rate, and closes the
connector column at κ = 2 through the scalar bound of the exponential, giving
`exp(6·D_s/113)`. The Stone 53 capstone remains published and valid, and is a
corollary of the refined one.

## 7. Audits and reviews

Recorded, with hashes and provenance, in
[`docs/audits/stone54/`](../audits/stone54/README.md):

- **54-QA1** — reproduction by execution of the candidate `410bde81…` by a
  separate instance of Claude Fable 5.1 on its own bench (`.lake/build`
  deleted; 114 modules built, 0 replayed, exit 0; 13/13 own certificates
  standard, 0 `sorryAx`; inherited warnings identical to the baseline in full
  text, none in the new module; own tests V0–V5). Same model as the
  constructor, distinct instance and bench; not blind. Verdict `PASS` with a
  documentary observation (D1); no mathematical defect.
- **54-K-ADV** — adversarial review by Luan / Kimi 3, a different model
  family, by reading and mathematical analysis, without Lean execution, with
  declared prior exposure (not blind), of the scientific merge `9c0f6fde…`.
  Verdict `PASS NO ESCOPO`; no new finding; D1/D2/I1 confirmed. The review
  does not extend to any later scientific change.
- **54-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).
- **GPT Astra** — scientific architecture and review: reading of the module
  and of the reports, checks of the evidence, Git objects and publication
  metadata; no Lean build of its own.

These are audits and reviews by AI models with human coordination; no
specialized human mathematical review of the proofs is documented at this
stage.

## 8. Version 54: consolidation, release and later maintenance

Record added by the maintenance after the Version 54 snapshot; nothing in
this section is inside the deposited Version 54 files.

| Step | Record |
|---|---|
| Documentary consolidation | [PR #31](https://github.com/consensusframework/yang-mills-mass-gap/pull/31), head `c9f687c27f3b955ba681f54d1cc7f8f658ff1ada` over `9c0f6fde…`; `build-phase3` run [489](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34899248490) (id 34899248490, job 104160931797; effective checkout the provisional merge `dd17f45e…`); merge commit `9358faa27b44ce24b3b9fe035cba94a68448e034` (parents `9c0f6fde…` and `c9f687c2…`; root tree `e378c15e…`, `Phase3/` tree `7d8373f6…` unchanged); run [490](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34900254096) (id 34900254096) on `main` at `9358faa2…` itself. Both runs: success, 114 modules built, 0 replayed, 0 errors, no `sorryAx` |
| Version 54 | tag `zenodo-v54` (simple tag → `9358faa2…`); GitHub Release [`zenodo-v54`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v54) published by the coordinator on 2026-09-15 with four assets: `yang-mills-mass-gap-zenodo-v54.zip` (1,050,139 bytes; `git archive` of `9358faa2…`, 167 tracked files), `RELEASE_NOTES_PEDRA54.md`, `MANIFEST_v54.txt`, `SHA256SUMS.txt` |
| DOI | 10.5281/zenodo.22767474 reserved for the Zenodo record of Version 54 (concept DOI 10.5281/zenodo.17397622). Its publication on Zenodo could not be verified from the maintenance session (Zenodo and doi.org unreachable from it); it is recorded as reserved, not as published. The reserved DOI and the GitHub Release are not evidence of a published deposit |
| Maintenance after the snapshot | `Phase3/lake-manifest.json` (SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`; Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608` = tag `v4.15.0`, `inputRev` `v4.15.0`, plus the eight transitive dependencies) committed from the constructor's bench; it is the manifest whose SHA-256 the QA1 reproductions of Stones 52, 53 and 54 recorded before and after their builds (`manifest_pre_build.sha256` / `manifest_post_build.sha256` in the QA1 packages; `RELATORIO_52-A0-QA1.md`). The CI step `lake update` was replaced by a resolution from the committed manifest (`lake env true`), with a check that every dependency is checked out at the recorded revision and that the manifest is byte-identical before and after the build. No `.lean` file, pin, proof or audit record was changed |
