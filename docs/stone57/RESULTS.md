# Stone 57 — finite-volume multi-region Lipschitz stability for polymer-activity profiles

Integrated state of `main` at commit
[`b66c255c83bba02dc8d53158279296bbf7ea005c`](https://github.com/consensusframework/yang-mills-mass-gap/commit/b66c255c83bba02dc8d53158279296bbf7ea005c)
(merge of [PR #39](https://github.com/consensusframework/yang-mills-mass-gap/pull/39);
parents `95091fdd07398a7b42901829ad61e4e2c26d5aaa` and
`c936d4617f3e6f35ea1431c2fa9496b235940f5a`; root tree
`47e843190b38159fcc408340313bda77de0f46e7`, `Phase3/` tree
`cc1bfb261610266372745473fb54ad86f1077fae`). Four states are to be kept
apart: the **candidate** `c936d461…` (the audited commit, single parent
`95091fdd…`), the **scientific integration** `b66c255c…` (the merge above,
whose tree is the candidate's), the **documentary consolidation** (this
document and the audit records, merged after it) and the **deposit**. At
consolidation time (2026-10-09) Stone 57 was integrated on `main`, audited,
reviewed, re-executed and CI-verified, but not part of any release and
without a deposit of its own: the most recent version is **Version 56**
(commit `95091fdd07398a7b42901829ad61e4e2c26d5aaa`, tag `zenodo-v56`, GitHub
Release published on 2026-10-01, Zenodo record DOI
[10.5281/zenodo.22949184](https://doi.org/10.5281/zenodo.22949184), whose
publication is confirmed by the coordinator; see §8). Stone 57 is later than
the Version 56 snapshot and is not in that deposit; it is cited by its
commit. No DOI is reserved or recorded for a future Version 57 in this
document.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. The object is the normalized polymer functional of
> Stones 55–56 with the damping region kept everywhere: no new Gibbs measure,
> boundary condition, modified action, per-link profile or physical switch-off
> is constructed or claimed; nothing asserts monotonicity or differentiability
> in the profile, a spatial-mixing theorem, an optimal owner or an optimal
> sum, a Euclidean distance or a restriction on the number or size of the
> regions; no optimality, sharpness or bibliographic priority is claimed for
> the constant or the route. Stone 57 is a **finite composition derived from
> Stone 56**: the published Stone 56 two-term estimate is consumed at every
> step, and nothing of its cluster, erosion or budget chain is reopened.

## 1. The statement

Principal declarations (module
[`Phase3/LatticeGauge/ActivityProfileDampingMultiRegion.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingMultiRegion.lean),
blob `818048c4b849658c3e3dbcbdeca6a2b45b5b0dc4`):

```
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_multiregion
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_multiregion
LatticeGauge.profileExpectation_eq_of_cover_empty_family
```

Objects of Stones 55–56, unchanged: the damping region `R` stays in the
definition of the functional, the weights, the activities and the exponents,

```
F_R(a) = profileExpectation μm β χ f s R a,
b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
D_s    = card (supportLinkFinset s).
```

A **finite family of change regions**, indexed by `i : Fin m` (`m = 0`
included), with its own separation scale and intensity majorant per region:

```
r : Fin m → Set (Link N),   n : Fin m → ℕ,   δ : Fin m → ℝ,
B = ∑ i : Fin m, δ i · exp(−(n i : ℝ) / 2).
```

For profiles `a, a′` with values in `[0, 1]`, under the hypotheses of the
table below:

```
|F_R(a) − F_R(a′)|
    ≤ Cf · [exp(6 · D_s / 113) + exp(4 · D_s / 113)] · B      (two-term form)
    ≤ (2 · Cf) · exp(6 · D_s / 113) · B.                      (capstone)
```

The constant, the rate `exp(−n/2)` per region and the regime are those of
Stones 54–56; the single cost `δ·exp(−n/2)` of Stone 56 is replaced by the
finite sum `B` of the individual costs of the regions. Nothing is divided by
any amplitude or factor; no `δ i ≤ 1` is required; no factor of `m`, of the
volume, of `card R` or of `card (r i)` enters outside the sum — the number of
regions participates only through `B`.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`.

| Hypothesis | Meaning |
|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | `χ : G → ℝ` is a bounded measurable real function |
| `R : Set (Link N)` | the damping region, explicit and arbitrary |
| `mf : Measurable f`, `hCf : ∀ U, \|f U\| ≤ Cf` | measurability and an absolute majorant of the observable; `0 ≤ Cf` is **derived** (`nonneg_of_abs_le_of_config`, 52-E), not assumed |
| `{m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}` | the finite family; `m = 0` admitted |
| `hδ0 : ∀ i, 0 ≤ δ i` | the majorants are non-negative; no upper bound on any `δ i` |
| `hsep : ∀ i, WalkBarrierSeparated s (r i) (n i)` | walk-barrier separation of the set `s` from each change region `r i` at its own scale `n i` |
| `h0 h1 h0' h1' : ∀ η, 0 ≤ a η ≤ 1, 0 ≤ a′ η ≤ 1` | the two profiles take values in `[0, 1]` (the absence of an upper bound on `δ i` does not remove this hypothesis) |
| `hcover : ∀ η, touchFactor R a η ≠ touchFactor R a′ η → ∃ i : Fin m, typedTouchesSupport η (r i) ∧ \|touchFactor R a η − touchFactor R a′ η\| ≤ δ i` | **cover of the effective changes by polymers**: every polymer whose effective factor changes is assigned at least one region `i` that it touches **and** whose majorant `δ i` pays its change — one and the same index for the contact and the budget |

`hcover` is a hypothesis about polymers with an effective difference, not an
inclusion of regions of links, not a cover of `R` by the union of the `r i`,
and not two independent existentials (one for the contact, one for the
budget). The regions may overlap; a polymer touching several regions is
covered by any one of them that pays its change.

Not required by the public signatures: an `owner` (the assignment is built
inside the proof); `m > 0`; disjointness of the regions; `r i ⊆ R`; a
separation of `s` from `R`; a unit background outside the regions; `δ i ≤ 1`;
a sign condition on activities or exponents; `DependsOnlyOn f s` in the
comparison of the two functionals. `s` is the regional parameter of the
functional (the set whose touching cores index the polymer representation);
it is asserted to be a support of `f` only where `DependsOnlyOn f s` is
present, which is not the case here. `R` stays the damping region of both
functionals and may carry a common, non-unit background near `s`. The bound
is uniform in the admissible background; this does not mean that the
functional is independent of the background, and a non-unit common background
is not identified with the original Gibbs expectation.

### Algebraic auxiliaries versus analytic capstones

The auxiliaries of the namespace `LatticeGauge.ActivityProfileMultiRegion`
(the selection and endpoint identities, the step obligations) carry no
interval, no regime, no separation and no bound on `f`; the interval and the
regime enter only through the Stone 56 estimate consumed by the composition,
and the analytic hypotheses above belong to the capstones. The `m = 0`
interface is algebraic (it omits the four measure instances); the one-region
interface is analytic.

## 2. The route, as formalized

The chain promoted from the feasibility file (gate 57-A) to the module (gate
57-L), with the Stone 56 two-term estimate as the only analytic input.

- **The owner.** `owner : Polymer N → Option (Fin m)` assigns to each polymer
  at most one index. Three obligations: `howner_none` — `owner η = none` only
  where `b(η) = b′(η)`; `howner_touch` — `owner η = some i` only on polymers
  touching `r i`; `howner_bound` — there, `|b(η) − b′(η)| ≤ δ i`. Overlapping
  regions are resolved by assigning each polymer to a single step. The public
  capstones build the owner from `hcover` by classical choice
  (`coverOwner`: `some (Classical.choose (hcover η h))` where
  `h : b(η) ≠ b′(η)`, `none` otherwise; `coverOwner_none`, `coverOwner_touch`,
  `coverOwner_bound`); the user supplies no owner, and no optimality of the
  choice or of `B` is required or claimed.
- **Intermediate profiles by coordinate substitution.** `moved owner k η :=
  ∃ i, owner η = some i ∧ i.val < k`; `stepProfile owner a a′ k η := if
  moved owner k η then a′ η else a η` — the second profile on the coordinates
  owned by an index `< k`, the first profile elsewhere (a definition by
  cases: when `a η = a′ η` the value coincides with `a′ η` also before the
  coordinate is moved). `p_0 = a` as profiles (`stepProfile_zero`); each
  `p_k` stays in `[0, 1]` (`stepProfile_mem`); the effective factor of `p_k`
  selects, by the same condition, `b′(η)` or `b(η)`
  (`touchFactor_stepProfile`, an identity of definitions with `R` kept).
- **The Stone 56 hypotheses at every step.** `moved` is monotone in the
  stage (`moved_mono`); a coordinate that switches exactly at stage `i.val`
  is owned by `i` (`owner_eq_of_moved_succ`, by `Fin.ext` and `omega`).
  Hence, at step `i`: outside `r i` the effective factors of `p_i` and
  `p_(i+1)` agree (`step_same`, from `howner_touch` only — a coordinate
  switches only at the step of its owner, even when it touches other
  regions, so no disjointness is presupposed); on `r i` they differ by at
  most `δ i` (`step_bound`: `howner_bound` on the coordinates owned by `i`,
  a zero difference paid by `0 ≤ δ i` elsewhere — overlapping regions are
  never charged twice within a step).
- **The last profile.** `p_m` has the effective factors of `a′`
  (`touchFactor_stepProfile_last`, from `howner_none` only): an equality of
  **effective** factors, not of raw profiles — values never read outside `R`
  may still differ. The functionals then agree exactly by the Stone 56
  identity `profileExpectation_eq_of_touchFactor_eq`.
- **Composition.** `abs_telescope` (`|g 0 − g k| ≤ ∑_{j<k} |g j − g (j+1)|`,
  by induction) and, at each step, the **published two-term estimate of
  Stone 56** (`abs_profileExpectation_sub_profileExpectation_le_two_terms_localized`)
  with `r i, n i, δ i` and the profiles `p_i, p_(i+1)`
  (`ActivityProfileMultiRegion.abs_profileExpectation_sub_le_of_owner`, in the
  native form `exp(3·D_s·(2/113)) + exp(2·D_s·(2/113))`); `Finset.sum_range`,
  `Finset.sum_le_sum` and `Finset.mul_sum` reorganize the sum into
  `Cf·(E6 + E4)·B`. The exponents are rewritten `6·D_s/113`, `4·D_s/113` in
  the public two-term theorem; `0 ≤ Cf` (derived), `B ≥ 0` (`budget_nonneg`)
  and `exp(4·D_s/113) ≤ exp(6·D_s/113)` (`D_s ≥ 0`) give the capstone.

This is not an independent re-derivation of the Stone 56 estimate: Stone 56
is the input of the general construction.

## 3. The module and its declarations

One new module (527 Lean lines; 22 top-level declaration lines by the
textual count of the README — `grep -cE` of lines beginning with `theorem`,
`lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`,
`inductive` or `class` followed by a space — at the candidate `c936d461…`:
19 `theorem`, 1 `def` and 2 `noncomputable def`; 22 in-file `#print axioms`
certificates, one per named declaration, definitions included), a leaf over
Stone 56; no pre-existing module was modified; the only change outside the
new file is its glob in `Phase3/lakefile.toml` (117 → 118 modules; blob
`11de6e17d9e7bf208d16ce322a757a39e1f97683`, previously `ae8438d4…`).

| Namespace | Declarations | Content |
|---|---|---|
| `LatticeGauge.ActivityProfileMultiRegion` (auxiliaries) | `moved` (def), `stepProfile`, `coverOwner` (noncomputable defs); `not_moved_zero`, `stepProfile_zero`, `stepProfile_mem`, `touchFactor_stepProfile`, `moved_mono`, `owner_eq_of_moved_succ`, `step_same`, `step_bound`, `touchFactor_stepProfile_last`, `abs_telescope`, `budget_nonneg`, `abs_profileExpectation_sub_le_of_owner`, `coverOwner_none`, `coverOwner_touch`, `coverOwner_bound` | coordinate substitution with a unique owner; the Stone 56 hypotheses at every step; finite telescoping; the composition with an explicit owner; the owner from the cover |
| `LatticeGauge` (public) | `abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms`, `abs_profileExpectation_sub_profileExpectation_le_multiregion`, `abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_multiregion`, `profileExpectation_eq_of_cover_empty_family` | the two estimates under `hcover`; the two interfaces |

Imports: `Mathlib` and `LatticeGauge.ActivityProfileDampingLocality`
(Stone 56). From Stone 56 the module consumes the two-term estimate (one
use) and `profileExpectation_eq_of_touchFactor_eq` (two uses); from Stone 52-E
`nonneg_of_abs_le_of_config`; the Stone 56 capstone itself is not used.
Hygiene: 0 `sorry`, `admit`, `native_decide`, scientific `axiom`,
`set_option`, `maxHeartbeats` (the word "admitted" occurs once, in a
docstring); linters active.

Origin of the proposal: the scientific architecture of GPT Astra / Can
(feasibility tape 57-A; construction tape 57-L); the feasibility file
`T57A_multiregion_tests.lean` (27 theorems and 3 definitions in a disposable
file, 17 of the theorems in the chain and 10 in its tests T1–T7, plus the
expected failure T8x) was promoted to this module, whose definitive
scientific count is 19 theorems and 3 definitions.

## 4. Interfaces, control cases and limits

| Case | Declaration or test | Content |
|---|---|---|
| one region | `abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_multiregion` | the Stone 56 hypotheses (`hsame`, `hδ` for one region) give `hcover` with `m = 1` (`hsame` by contraposition gives the touch), and the capstone returns the Stone 56 bound, the sum over `Fin 1` on the **right-hand side** reducing to `δ·exp(−n/2)`; its type is the type of the Stone 56 capstone (checked by `exact` in both directions, constructor's tests W1/W1′, auditor's Q1). A compatibility test of the composition, not a proof of Stone 56 |
| no region | `profileExpectation_eq_of_cover_empty_family` | `m = 0`: `hcover` forces the equality of all effective factors (there is no index), hence `F_R(a) = F_R(a′)` exactly, with no analytic hypothesis; the analytic capstone also accepts `m = 0`, with `B = 0` (W2b, Q2) |
| overlapping regions | W3, Q3 | a polymer touching `r 0` and `r 1` and owned by `0` switches at stage 0 and never again; the step-1 obligations hold at it although it touches `r 1`: the unique assignment, not a geometric exclusivity, decides the step (see the reading precision D1 in the audit index) |
| zero cost | W5a, Q2 | `δ ≡ 0` gives the bound `0` and equality by application of the capstone; nothing divided |
| `δ > 1` | W5b, Q6 | `δ ≡ 7` is admissible (merely loose); with `Cf = 0` the bound is `0` whatever the regions, so no strict improvement is attributed to it |
| zero factors, common background `1/2`, ignored raw values | W4, Q4 | a factor `0` against `1/2` on a polymer touching `R` and `r 0` (owner `0`, effective difference `1/2`); a common factor `1/2` on a polymer with owner `none`, kept at every stage; raw values `3/10` vs `9/10` on a polymer that does not touch `R`: effective factors `1 = 1`, the last profile keeps the raw value of `a` while its effective factor is that of `a′` (equality of effective factors without equality of raw profiles). A raw change `0 → 1/2` is effective only on a polymer touching `R`; the tests prove the general application and assume no geometry (precision Q4d) |
| two-step composition by hand | W9 (constructor), Q5 (auditor, with its own intermediate profile and step hypotheses) | the Stone 56 two-term estimate applied directly to `p_0 → p_1 → p_2` and closed by the triangle inequality, without the new capstones |
| expected failure | W8x (constructor), Q8x (auditor) | an owner that leaves an effective change at `none`: the last-step obligation is open (goal `1 = 1/2`, resp. `False`) — an application failure by the missing cover, not a counterexample |

The sum can improve a coarse comparison when costs and separations are
favorable (W6, Q6: amplitudes `1/4, 1` at scales `0, 4` give
`B = 1/4 + exp(−2) < 1`, an exact scalar comparison, strict for the full
bounds only under `Cf > 0`); there is no universal gain for an arbitrary
cover (W7, Q7: two equal regions give two equal terms, and a duplicated
family costs twice), and neither the chosen owner nor the sum is claimed
optimal. The geometric tests are parameterized by `typedTouchesSupport`
hypotheses; no concrete lattice instance is constructed. The result is of
finite volume, in the declared regime, on periodic four-dimensional
lattices; it does not construct a thermodynamic or continuum limit or a mass
gap, does not prove the Clay problem, and claims no bibliographic priority,
monotonicity, differentiability, new Gibbs measure or boundary condition.

## 5. Kernel certificates and CI

- Every one of the 22 named declarations of the module (19 theorems and 3
  definitions) carries an in-file `#print axioms` certificate; each reports
  `[propext, Classical.choice, Quot.sound]`. The library carries 291 in-file
  `#print axioms` commands at `c936d461…` and at `b66c255c…` (269 + 22);
  these are certificate commands, not a count of theorems and not a global
  inventory of the axioms of every declaration.
- The CI runs emit **294 axiom outputs = 291 of the build + 3 of the workflow
  step** on the Version 49–51 capstones, for **292 distinct names**: two of
  the three workflow outputs repeat names already certified by the build,
  and the third, `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name to
  the list emitted by the build (the Version 49 capstone has no in-file
  `#print axioms`); it is not a new theorem added by the workflow. In runs 505
  and 506, 75 of the 294 lists are printed across more than one line; the
  reading recomposes each list up to its closing bracket and accepts names
  with apostrophes (`activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`).
- Hygiene in the module: 114 inherited build warnings (unchanged since
  Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`
  (the Version 56 snapshot `95091fdd…`), delivered as a verifiable git
  bundle; the QA1 audit before publication; push of the audited commit, a
  non-draft pull request, `build-phase3` green on the pull-request head, a
  normal merge with the expected head SHA locked (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit; then the
  adversarial review and the complementary execution of the integrated
  state.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `c936d4617f3e6f35ea1431c2fa9496b235940f5a` | [#39](https://github.com/consensusframework/yang-mills-mass-gap/pull/39) | [505](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/37955736915) (id 37955736915, job 113905659491) | `b66c255c83bba02dc8d53158279296bbf7ea005c` | [506](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/37957117948) (id 37957117948, job 113910337460) |

Custody note: the pull-request run 505 is associated with the head
`c936d461…`, but its effective checkout was the provisional merge commit
`3214768b020b661fe052ec8ff697f15023eb942f` ("Merge c936d461… into
95091fdd…"), as recorded in the job log read by the publishing instance
(`docs/audits/stone57/publication/RELATORIO_57-P.md`); run 506 compiled the
definitive merge `b66c255c…` itself. The run metadata alone do not prove the
effective checkout; the attribution is to the log reading. Both runs: `Build
completed successfully`; the dependency manifest `c376bbe9…1227` recorded and
verified after the resolution and after the build, the nine dependencies
checked out at the recorded revisions, no `lake update`; **118 `LatticeGauge`
modules built, 0 replayed** (dependencies: 9 built, 0 replayed on the runner
— a cache of the CI, not a recompilation of the dependencies); 0 errors; 114
warnings, all in `LatticeGauge/`, none in the new module, none from
dependencies, the full warning blocks identical as a multiset to the QA1
baseline; 294 axiom outputs, all standard, the 22 of the new module included;
no `sorryAx`.

Toolchain at `b66c255c…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 118
modules, 38,521 Lean source lines and 1,802 top-level declaration lines by
the textual count (1,780 at Version 56 plus the 22 of this module) — 1,802
is not a number of theorems.

## 6. Relation to Stone 56

Stone 56 proved the localized stability with one change region `r`, one
separation `n` and one majorant `δ`, the damping region `R` kept in the
functional. Stone 57 composes it over a finite family of change regions,
each with its own separation and majorant, under a cover of the effective
changes by polymers; the constant and the regime are unchanged and the single
cost becomes the finite sum `B`. The Stone 56 two-term estimate is consumed at
every step; the Stone 56 statement is recovered by the one-region interface
as an application, which is a compatibility check of the composition and not
a circularity, since Stone 56 is the input of the general construction.

## 7. Audits, review and complementary execution

Recorded, with hashes and provenance, in
[`docs/audits/stone57/`](../audits/stone57/README.md). Four kinds of evidence
with distinct scopes; none is specialized human mathematical review.

- **57-QA1** — reproduction by execution of the candidate `c936d461…` by a
  separate instance of Claude Fable 5.1 on a fresh bench (same model as the
  constructor; prior exposure declared, not blind; the constructor's report
  read before the execution to identify the target, the constructor's logs
  and tests opened only in a second pass after the auditor's own
  conclusions). Dependencies from the Mathlib community cache at the nine
  manifest revisions, no `lake update` (0 built / 0 replayed of dependencies
  and no dependency diagnostics in that log — a reuse, not a rebuild of the
  dependencies); clean build 2026-10-09, 794 s, exit 0, **118 modules built,
  0 replayed**, 0 errors, 291 certificates standard, 0 `sorryAx`; 114
  inherited warning blocks identical to the Stone 56 baseline, none in the
  new module; own tests Q0–Q7 pass, Q8x fails on the expected `howner_none`
  obligation; 34 warnings in the auditor's own disposable tests (Q1: 28, Q4:
  4, Q6: 2), separate from the 114 of the project. The constructor's tests
  W1–W9/W8x were re-executed by the auditor in the second pass; the re-execution
  does not transfer their authorship. Verdict `PASS NO ESCOPO` (custody,
  execution, mathematics, documentation PASS). No errata was issued by the
  auditor; three reading precisions of the coordination (D1–D3) and the
  precision on Q4d qualify the audit's descriptions, not its code, and are
  recorded in the audit index.
- **57-K-ADV** — adversarial review by **Kimi K3**, as the review identifies
  itself (the historical credits say "Kimi 3"; no new technical identity is
  inferred), a different model family, by reading and mathematical analysis,
  with own custody checks (hashes, bundle, diff, trees, Git objects of the
  base, the candidate and the merge) and own parsing of the clean logs,
  **without Lean execution**; not blind (the tape disclosed the target and
  the earlier results). Verdict `PASS NO ESCOPO`; no mathematical defect, no
  hidden hypothesis, no insufficient cover, no double charge, no loss of the
  common background; D1–D3 and Q4d confirmed as precisions; no errata. Its
  declared limits: the standalone 57-P report was not received, the full CI
  logs of runs 505/506 were not downloaded (its 294/292 check is structural,
  from the workflow and the clean logs), Zenodo and the Release were not
  consulted.
- **57-MANUS-EXEC** — complementary execution, on the declared platform
  **Manus Sandbox** (the model identifier was not exposed; nothing is inferred
  from the platform name), of the QA1 tests on the integrated state
  `b66c255c…`: a disposable checkout of the fixed SHA with the push URL
  disabled, Lean 4.15.0 / Lake 5.0.0, the nine dependencies at the manifest
  revisions, no `lake update`; `lake build LatticeGauge.ActivityProfileDampingMultiRegion`
  (exit 0, 1,083 s): **104 `LatticeGauge` modules built / 0 replayed** —
  exactly the import chain of the module, **not a full rebuild of the 118**;
  the 22 certificates of the module re-executed by Q0, all standard, no
  `sorryAx`; Q3/Q4/Q5 exit 0 (Q4 with four test warnings; Q5 with two
  certificates of its own test theorems, not new declarations of the
  project); Q8x exit 1 on the open `False` obligation under the owner `none`
  with differing effective factors; `#check` of the two capstones confirms
  the explicit `hcover` and the absence of a public `owner`; 102 warnings in
  43 imported pre-existing modules, zero in the new module — exactly the
  corresponding subset of the QA1 baseline blocks, no new warning; module,
  manifest and pins preserved, tracked diff empty. Verdict of the executor:
  **EXECUÇÃO CONCLUÍDA NO ESCOPO**. The test sources are byte-identical copies
  of the QA1 tests: the contribution is their re-execution on another bench,
  not new tests or an independent re-derivation; it is not counted as an
  additional independent mathematical audit. One qualification by the
  coordination (M1, in the audit index) concerns the pre-build inventory
  path; the positive evidence stands on the fresh clone and the build log.
- **57-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).
- **GPT Astra / Can** — scientific architecture and review: the feasibility,
  construction, integration and consolidation tapes; reading of the module,
  the reports, the packages and the logs; no Lean build of its own.

## 8. Version records

| Step | Record |
|---|---|
| Version 56 (the current version) | commit `95091fdd07398a7b42901829ad61e4e2c26d5aaa` (merge of PR #38, the documentary consolidation of Stone 56), tag `zenodo-v56` (simple tag), GitHub Release [`zenodo-v56`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v56) published on 2026-10-01 (`draft = false`, 2026-10-01T22:47:39Z, read through the GitHub API by the consolidating session) with four assets (`yang-mills-mass-gap-zenodo-v56.zip`, 1,308,511 bytes; `RELEASE_NOTES_PEDRA56.md`, 34,578 bytes, the notes revised by the coordinator before the upload; `MANIFEST_v56.txt`; the checksum file, named `SHA256SUMS.8.txt` on the Release); Zenodo record DOI [10.5281/zenodo.22949184](https://doi.org/10.5281/zenodo.22949184) (concept DOI 10.5281/zenodo.17397622), **published**, as confirmed by the coordinator — the exact Zenodo publication date was not established by the materials of this consolidation and is not inferred from the Release date; the consolidating session did not consult Zenodo. The deposit contains Stones 52–56 and the committed dependency manifest, and not Stone 57 |
| Stone 57 | integrated on `main` at `b66c255c…` (2026-10-09, PR #39), audited (QA1 2026-10-09), reviewed (Kimi K3, received 2026-10-09), re-executed (Manus Sandbox, 2026-10-09) and CI-verified (runs 505 and 506); **no tag, no Release, no deposit and no reserved DOI of its own recorded here**. It is cited by its commit. The future Version 57, if deposited, will be packaged from the definitive documentary merge in a step of its own |
