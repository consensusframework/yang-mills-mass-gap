# Stone 55 — stability of the damped functional under a profile of activity factors

Integrated state of `main` at commit
[`d6ce3d7232f08b5f975dfa8c6f43ec5031937e10`](https://github.com/consensusframework/yang-mills-mass-gap/commit/d6ce3d7232f08b5f975dfa8c6f43ec5031937e10)
(merge of [PR #33](https://github.com/consensusframework/yang-mills-mass-gap/pull/33);
parents `bd2f6c1b0ad600b0282b4776859bb917466152ea` and
`0c50b6d5e23915f13d6f36d560a58ba6f24ae97b`; root tree
`e69c0fe94d18b83f0664fdc42642358ef4f8e867`, `Phase3/` tree
`20ffea86201c8a35d62479b2c0038f8c3e592de5`). At consolidation time
(2026-09-19) Stone 55 was integrated on `main`, audited and CI-verified, but
not part of any release and without a deposit of its own: the most recent
version is **Version 54** (commit `9358faa27b44ce24b3b9fe035cba94a68448e034`,
tag `zenodo-v54`, GitHub Release, Zenodo record DOI
[10.5281/zenodo.22767474](https://doi.org/10.5281/zenodo.22767474), published
on 2026-09-15 as confirmed by the coordinator and by a capture of the record
page; see §8). The maintenance after that snapshot (the committed dependency
manifest and the CI change, PR #32) and Stone 55 itself are later than the
Version 54 snapshot and are not in that deposit.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. The object is a normalized polymer functional of a
> profile-damped activity, exactly as in Stone 52 with a profile in place of a
> scalar: no new Gibbs measure, boundary condition, modified action, per-link
> profile or physical switch-off is constructed or claimed; nothing asserts
> monotonicity or differentiability in the profile, a spatial-mixing theorem, or
> any restriction on the size of the region; no optimality, sharpness or
> bibliographic priority is claimed for the constant or the route.

## 1. The statement

Principal declaration:
`LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_local_exp_decay`
([`Phase3/LatticeGauge/ActivityProfileDampingStability.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingStability.lean)).

Stones 52–54 damp the activity of every polymer touching a remote region `r`
by one scalar `θ ∈ [0, 1]`. Stone 55 replaces the scalar by a **profile**
`a : Polymer N → ℝ`, one factor per polymer:

```
profileDampedActivity z r a η = if typedTouchesSupport η r then a η * z η else z η
```

(`ActivityProfileDamping.lean`). The values of `a` on polymers that do not
touch `r` are never read: the remote character is built into the definition,
with no side hypothesis. Write `F(a) = profileExpectation μm β χ f s r a` (the
normalized polymer functional of the profile-damped activity) and
`D_s = card (supportLinkFinset s)`. For two profiles `a, a′` with values in
`[0, 1]` and a majorant `δ ≥ 0` of `|a η − a′ η|` on every polymer `η`
touching `r`:

```
|F(a) − F(a′)|
    ≤ δ · Cf · exp(−n / 2) · [exp(6 · D_s / 113) + exp(4 · D_s / 113)]
    ≤ δ · (2 · Cf) · exp(6 · D_s / 113) · exp(−n / 2).
```

The first line is the two-term estimate
(`abs_profileExpectation_sub_profileExpectation_le_two_terms`); the capstone
follows from `exp(4·D_s/113) ≤ exp(6·D_s/113)` (`D_s ≥ 0`). **The constant,
the rate `exp(−n/2)`, the interval `[0, 1]` and the regime are those of the
Stone 54 capstone, with `δ` in the place of `|θ − θ′|.** Nothing is divided
by `δ`; no `δ ≤ 1` is required anywhere.

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
| `hδ0 : 0 ≤ δ` | the majorant is non-negative; there is no upper bound on `δ` (δ = 7 is admissible, the bound is then merely loose) |
| `h0 h1 h0' h1' : ∀ η, 0 ≤ a η ≤ 1, 0 ≤ a′ η ≤ 1` | the two profiles take values in `[0, 1]` on every polymer (values outside `r` are never read by the functional, but the hypotheses are stated for all `η`) |
| `hδ : ∀ η, typedTouchesSupport η r → \|a η − a′ η\| ≤ δ` | the majorant of the profile difference, required only on the polymers touching `r` |

`DependsOnlyOn f s` is **not** a hypothesis of the capstone between the two
functionals; it enters only where `F(1)` (the unit profile) is identified with
the Gibbs expectation. No sign condition on activities or exponents is used.

**Two kinds of hypotheses.** The algebraic identities of Stone 55 — the
weight identities `∏ z_a = A_Γ · ∏ z`, the constant-profile specializations,
the endpoint identities for the unit profile, the zero profile and the empty
region, and the exact two-profile ledger
(`profileExpectation_sub_eq_two_column_ledger`) — are stated with no
hypothesis on `f`, no majorant and no separation; the ledger needs only the
KP regime (`hβ`, `hsmall`, `mχ`, `hχabs`) for the exponential representation,
and the empty-region identities need nothing at all and hold for arbitrary
real profiles. The analytic bounds — the eroded connector bound, the
exponential control, the two columns, the two-term estimate and the capstone —
add the profile hypotheses (`[0, 1]`, `δ ≥ 0`, the majorant on the touching
polymers) and, from the columns onwards, `mf`, `hCf` and `hsep`. The table
above is the capstone's list; the declaration matrices in
[`docs/audits/stone55/`](../audits/stone55/README.md) record the list of each
declaration.

## 2. The route

- **Weights.** Where Stone 52 has the count weight `θ^{touchCount r Γ}`,
  Stone 55 has the product weight `A_Γ = profileWeight r a Γ = ∏_{η ∈ Γ}
  touchFactor r a η`, with `touchFactor r a η = if typedTouchesSupport η r
  then a η else 1`; for tuples, `tupleProfileWeight` multiplies over the
  positions, so repetitions are counted by position (`![η, η]` has weight
  `a η ^ 2` and touch count 2). For `0 ≤ a ≤ 1`: `0 ≤ A_Γ ≤ 1`, `A_Γ = 1` on
  families avoiding `r` (in particular on the allowed cores), and
  `|z_a| ≤ |z|`, so the abstract Kotecký–Preiss hypothesis is transported by
  monotonicity (`abstractKP_profileDampedActivity`, via `abstractKP_mono`;
  Stones 46/50 are not redone).
- **Telescoping in `[0, 1]`.** `abs_prod_sub_prod_le_sum_abs_sub`:
  `|∏ x_i − ∏ y_i| ≤ Σ |x_i − y_i|` for factors in `[0, 1]`, by induction on
  the finset with the identity `x·P − y·Q = x·(P − Q) + (x − y)·Q`. Hence
  `|A_Γ − A′_Γ| ≤ touchCount r Γ · δ` and, for tuples,
  `|A_δ − A′_δ| ≤ tupleTouchCount r δ · δ ≤ k · δ` whenever
  `|a η − a′ η| ≤ δ` on the polymers touching `r` — the profile analogue of
  `|θ^j − θ′^j| ≤ j·|θ − θ′|`, which is recovered as a corollary
  (`abs_pow_sub_pow_le_of_prod`). The lemma fails outside `[0, 1]`; this is
  why the interval hypotheses are present along the whole chain.
- **Representation and the exact ledger.** The profile gas is
  `exp(Σ′ coefficients)` and hence positive (`profilePolymerGas_eq_exp`,
  `profilePolymerGas_pos`: the KP criterion is established by
  `abstractKP_of_beta_le_one_div_40000` and transported, and positivity is a
  consequence of the exponential representation); the ratio identity uses the
  published `typedPolymerGas_ratio_eq_exp_sub`, without cancelling a
  denominator. The marked gas is fibered over the touching cores with the
  product split `A_Γ = A_T · A_R` in place of the count split of 52-A.F, giving
  the exponential form `F(a) = Σ_T A_T · W_T · e^{E_T(a)}` and the **exact
  two-profile ledger**, an identity with no hypothesis on `f`:
  `F(a) − F(a′) = Σ_{T touching} A′_T · W_T · (e^{E_T(a)} − e^{E_T(a′)})
  + Σ_{T bridge} (A_T − A′_T) · W_T · e^{E_T(a)}` — the second profile's
  weight on the connector column, the first profile's exponent on the bridge
  column, **plus** sign on the bridges (the correction vanishes on the allowed
  cores, where `A_T = A′_T = 1`). The difference of the two functionals is
  never routed through the Gibbs expectation.
- **Profile connector and erosion.** The connector coefficient carries the
  weight `1 − A_δ` on the tuples hitting both barriers; its inclusion–exclusion
  (`kpProfileConnector_inclusion_exclusion`) inserts the regional filter only
  through the implication `TupleAllowed (regionAllowed r) → tupleTouchCount = 0
  → A_δ = 1`, without converse and without any hypothesis on `a`. The series
  identities `E_T(a) − E_T(full) = C(a)` and `E_T(a) − E_T(a′) = C(a) − C(a′)`
  keep the orientation of 51-C/52-C; the domination
  `|c_k(a) − c_k(a′)| ≤ δ · k · A_k(|z|)` counts tuple positions, and
  summability comes from the 52-A0 first moment through the domination
  against the unit profile. The eroded bound
  `|C(a) − C(a′)| ≤ δ · e^{−((n − m_T : ℕ))/2} · q_T` uses the natural
  truncated subtraction before the cast: when the core mass `m_T` exceeds `n`
  the erosion factor is `1`, never an explosion; no `8/(3e)`.
- **Barrier bound of the exponent and κ = 2.** `|E_T(a)| ≤ q_T =
  card(barrierLinkFinset T s) · (2/113)` (`abs_profileCoreExponent_le_barrier`,
  route 53-A, the κ = 1 cost). The bilateral scalar bound of Stone 54,
  `|e^x − e^y| ≤ e^q · |x − y|` for `x, y ≤ q`
  (`abs_exp_sub_exp_le_exp_mul_abs_sub`, from `Real.add_one_le_exp`), applied
  with both exponents `≤ q_T`, then `q_T ≤ e^{q_T}` (`le_exp_self`) and the
  repurchased erosion give `|e^{E_T(a)} − e^{E_T(a′)}| ≤ δ · e^{−n/2} ·
  e^{m_T/2 + 2·q_T}` (`abs_exp_profileCoreExponent_sub_le_decay_refined`,
  κ = 2). No `δ ≤ 1` is used at any point: only `0 ≤ δ`.
- **Connector column, budget (1/2, 2).** `0 ≤ A′_T ≤ 1`, the Mayer majorant
  `|W_T| ≤ Cf · ∏ M` without exponential, and the κ = 2 control; the sum over
  touching families closes through `sum_halfTilt_two_le` (the generic
  `coreLocalBudget` at `λ = 1/2, κ = 2`, admissible because
  `1/2 + 2·(8/113) = 145/226 ≤ 1`), prefactor `exp(6·D_s/113)`.
- **Bridge column, κ = 1, budget (7/8, 1).** `|A_T − A′_T| ≤ card T · δ`; the
  first moment `card T · |W_T · e^{E_T(a)}|` is paid by `card T ≤ m_T ≤
  e^{3 m_T/8}`, by the bridge geometry `n ≤ m_T` and by the fusion
  `e^{m_T/2} · e^{3 m_T/8} = e^{7 m_T/8}` absorbed in the tilt 7/8; the sum is
  extended from the bridges to the touching families (non-negative terms) and
  closed by `sum_sevenEighthsTilt_one_le`, prefactor `exp(4·D_s/113)`.
- **Closure.** Ledger, triangle inequality and the two columns give the
  two-term estimate; the capstone follows with `e^{4 D_s/113} ≤ e^{6 D_s/113}`
  and `0 ≤ Cf` derived.
- **Stone 54 recovered by application, without circularity.** The constant
  profiles `a ≡ θ`, `a′ ≡ θ′` with `δ = |θ − θ′|` satisfy the hypotheses; the
  capstone applied to them, rewritten by `profileExpectation_const`, is the
  Stone 54 capstone
  (`abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay_of_profile`).
  The direction is 55 ⇒ 54: the Stone 54 capstone is not used in any Stone 55
  proof (it appears only in a docstring); Stone 55 imports Stone 54 and the
  published modules are untouched. The constant-profile specializations
  include cases by `rfl` (`profileDampedActivity_const`,
  `profilePolymerGas_const`, `profileCoreExponent_const`: the constant profile
  *is* the scalar damping, definitionally) and cases by rewriting
  (`profileWeight_const`, `tupleProfileWeight_const`, `profileMarkedGas_const`,
  `profileExpectation_const`); the header of the 55-A module calls them
  "definitional identities" in bloc (record D3 in the audits).

## 3. Endpoints

| Endpoint | Declaration | Content |
|---|---|---|
| δ = 0 | (capstone applied); `profile_bound_self` | the right-hand side vanishes because nothing was divided by `δ`; `profile_bound_self` is only the algebra of the right-hand side at δ = 0 (record D1); the effective application of the capstone with δ = 0 is exercised by the constructor's test V3 and the auditor's tests W4a/W4b (profiles equal on the touching polymers and different elsewhere give `F(a) = F(a′)`, also by the literal equality of the activities) |
| constant profiles | `…_le_local_exp_decay_of_profile` | the Stone 54 capstone, recovered as an application (§2) |
| unit profile | `abs_profileExpectation_sub_gibbsExpectation_le` | with `DependsOnlyOn f s`, `F(1)` is the Gibbs expectation (`profileExpectation_one`); for `1 − a ≤ δ` on the touching polymers, `\|F(a) − gibbs\| ≤ δ·2·Cf·e^{6 D_s/113}·e^{−n/2}` |
| zero profile | `abs_profileExpectation_sub_activityRestrictedExpectation_le` | `F(0)` is the Stone 51 restricted functional with **no** hypothesis (`profileExpectation_zero`); for `a ≤ δ` on the touching polymers, the same bound against `activityRestrictedExpectation`, without `DependsOnlyOn f s` (record D5: the asymmetry is real, only the unit side must identify the functional with Gibbs) |
| r = ∅ | `profileExpectation_sub_profileExpectation_empty_region` | `F(a) = F(a′)` exactly for **all** real profiles, outside `[0, 1]` included, because no factor is read; the capstone is not extrapolated outside `[0, 1]` |
| a profile with a value outside `[0, 1]` | (no declaration) | the capstone does not apply (the auditor's test W5x, expected to fail: an application failure by a missing hypothesis, not evidence of falsity nor of indispensability) |

## 4. The modules

Two new modules (923 + 999 = 1,922 Lean lines; 78 top-level declaration
lines, a textual count by `grep -cE` of lines beginning with `theorem`,
`lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`,
`inductive` or `class` followed by a space — 68 `theorem` and 10
`noncomputable def`; 68 in-file `#print axioms` certificates, one per
theorem), forming a chain over Stone 54; no pre-existing module was modified;
the only change outside the two new files is their two globs in
`Phase3/lakefile.toml` (114 → 116 modules).

| Gate | Module | Lines / decls / certs | Content |
|---|---|---|---|
| 55-A | `ActivityProfileDamping.lean` (blob `dc85622b…`) | 923 / 8 defs + 43 thms / 43 | `touchFactor`, `profileDampedActivity`, `profileWeight`, `tupleProfileWeight`; the constant-profile, unit, zero and empty-region specializations; domination and KP transport; the weight identities `∏ z_a = A_Γ·∏ z` (families and tuples), `0 ≤ A_Γ ≤ 1`, `A_Γ = 1` on families avoiding `r`; the telescoping lemma in `[0, 1]` and the count bounds (`touchCount·δ`, `tupleTouchCount·δ ≤ k·δ`, `card·δ`), with the Stone 53 power lemma as corollary; the profile gases, the normalized functional `profileExpectation` and the profile core exponent; gas = exp(cluster sum) > 0, the ratio identity, `\|E_T(a)\| ≤ q_T`; the fibering of the marked gas, the exponential form and the exact two-profile ledger |
| 55-B | `ActivityProfileDampingStability.lean` (blob `6f12d160…`) | 999 / 2 defs + 25 thms / 25 | `kpProfileConnectorUnrootedCoeff`, `profileConnector`; the inclusion–exclusion, the domination `δ·k·A_k`, summability and the series identities; the eroded two-profile bound; the bilateral exponential control at κ = 2; the connector column (budget (1/2, 2)) and the bridge column (κ = 1, tilt 7/8, budget (7/8, 1)); the two-term estimate; the capstone; `profile_bound_self`; the Stone 54 capstone as an application; the endpoints against the unit profile (Gibbs, with `DependsOnlyOn`) and the zero profile (Stone 51, without it) |

Imports: 55-A imports `Mathlib` and `LatticeGauge.ActivityDampingLipschitzRefined`
(Stone 54); 55-B imports `Mathlib` and 55-A; 55-B is a leaf, no cycle. From
Stone 54 only the scalar helpers `abs_exp_sub_exp_le_exp_mul_abs_sub` and
`le_exp_self` are consumed (and, through Stone 54, the one-line wrapper
`sum_halfTilt_two_le` of `LatticeGauge.CovarianceDecay`, Stone 50 — record I1
of the Stone 54 audit, inherited, legitimate and avoidable; nothing new). The
generic barrier route of 53-A, the first moments of 52-A0, the damped objects
of 52-A/C, the erosion of 51-D and the gas identities of Stone 50 are consumed
as published.

Origin of the proposal: the scientific architecture and review of GPT Astra
(feasibility tape 55-A, construction 55-L). No optimality, priority or
exclusivity of the route is claimed.

## 5. Kernel certificates and CI

- Every one of the 68 theorems carries an in-file `#print axioms`
  certificate; each reports `[propext, Classical.choice, Quot.sound]`. They are
  emitted during `lake build` and are visible in the CI logs of runs 493 and
  494; the dedicated CI step `Kernel certificates` still checks the three
  capstones of Versions 49–51 and was not extended. The library carries 247
  in-file `#print axioms` commands at `d6ce3d72…` (179 + 68; the CI logs show
  250 axiom outputs = 247 + the 3 of the workflow step); these are certificate
  commands, not a count of theorems.
- Hygiene in the modules: 0 `sorry`, 0 `admit`, 0 scientific `axiom`,
  0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`, no division by `δ`;
  114 inherited build warnings (unchanged since Version 50), none in the new
  modules.
- Publication protocol: one candidate commit over the then-current `main`
  (the maintenance commit `bd2f6c1b…`, PR #32), delivered as a verifiable git
  bundle; the QA1 audit before publication; push of the audited commit, a
  non-draft pull request, `build-phase3` green on the pull-request head, a
  normal merge with the expected head SHA locked (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit; then the
  adversarial review of the integrated state.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `0c50b6d5e23915f13d6f36d560a58ba6f24ae97b` | [#33](https://github.com/consensusframework/yang-mills-mass-gap/pull/33) | [493](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/35262236671) (id 35262236671, job 105340563324) | `d6ce3d7232f08b5f975dfa8c6f43ec5031937e10` | [494](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/35263497257) (id 35263497257, job 105344775356) |

Custody note: the pull-request run 493 is associated with the head
`0c50b6d5…`, but its effective checkout was the provisional merge commit
`acf4f9d` ("Merge 0c50b6d5… into bd2f6c1b…"), as recorded in the job log read
by the publishing instance (`docs/audits/stone55/publication/RELATORIO_55-P.md`);
run 494 compiled the definitive merge `d6ce3d72…` itself (job log read by the
same instance). The run metadata alone do not prove the effective checkout;
the attribution is to the log reading. The merge commit has parents
`bd2f6c1b…` (the base) and `0c50b6d5…`, and its tree `e69c0fe9…` is the tree
of the candidate. Both runs: `Build completed successfully`; the dependency
manifest `c376bbe9…1227` recorded and verified after the resolution and after
the build, the nine dependencies checked out at the recorded revisions, no
`lake update`; 116 `LatticeGauge` modules built, 0 replayed (dependencies: 9
built, 0 replayed — the cache executable and the like); 0 errors; 114
warnings, all in `LatticeGauge/`, none in the new modules, none from
dependencies; 250 axiom outputs, all standard, the 68 of the new modules
included; no `sorryAx`.

Toolchain at `d6ce3d72…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 116
modules and 37,030 Lean source lines.

## 6. Relation to Stone 54

Stone 54 proved the Lipschitz estimate in one scalar,
`|F(θ) − F(θ′)| ≤ |θ − θ′|·2·Cf·exp(6·D_s/113)·exp(−n/2)`, closing the
connector column at κ = 2. Stone 55 keeps the same route — the Stone 54
scalar bound of the exponential with the count bounds of 55-A in the place of
the power lemma — and the same constant, rate, interval and regime, for a
profile of factors per polymer with `δ` in the place of `|θ − θ′|`. The Stone
54 capstone remains published and valid, and is an application of the new
one.

## 7. Audits and reviews

Recorded, with hashes and provenance, in
[`docs/audits/stone55/`](../audits/stone55/README.md):

- **55-QA1** — reproduction by execution of the candidate `0c50b6d5…` by a
  separate instance of Claude Fable 5.1 on its own bench (dependencies
  materialized from the committed manifest, no `lake update`; `.lake/build`
  deleted; 116 modules built, 0 replayed, exit 0, 644 s; 68/68 own certificates
  standard, 0 `sorryAx`; inherited warnings identical to the baseline in full
  text, none in the new modules; own tests W0–W5x, the ledger and the closure
  re-derived by independent routes). Same model as the constructor, distinct
  instance and bench; prior exposure declared, not blind. Verdict `PASS NO
  ESCOPO` with documentary observations (D1–D5, I1); no mathematical defect.
- **55-K-ADV** — adversarial review by Luan / Kimi 3, a different model
  family, by reading and mathematical analysis, without Lean execution, with
  declared prior exposure (not blind), of the candidate sources and of the
  scientific merge `d6ce3d72…`. Verdict `PASS NO ESCOPO`; no new finding;
  D1–D5 and I1 confirmed. One errata (C1) corrects the attribution of the
  tests in the review: V1–V4 are the constructor's tests, W0–W5x are the
  auditor's; the verdict is unchanged. The review and the errata are one
  review with one errata, to be read together, C1 prevailing on the
  attribution.
- **55-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).
- **GPT Astra** — scientific architecture and review: the feasibility,
  construction, publication and consolidation tapes; reading of the modules
  and of the reports, checks of the evidence, Git objects and publication
  metadata; no Lean build of its own.

These are audits and reviews by AI models with human coordination; no
specialized human mathematical review of the proofs is documented at this
stage.

## 8. Version records

| Step | Record |
|---|---|
| Version 54 (the current version) | commit `9358faa27b44ce24b3b9fe035cba94a68448e034` (merge of PR #31), tag `zenodo-v54`, GitHub Release [`zenodo-v54`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v54) published 2026-09-15; Zenodo record DOI [10.5281/zenodo.22767474](https://doi.org/10.5281/zenodo.22767474) (concept DOI 10.5281/zenodo.17397622), **published on Zenodo on 2026-09-15**, as confirmed by the coordinator and by a capture of the record page ("Published September 15, 2026 \| Version 54"); the consolidating session could not reach Zenodo or doi.org itself, so the confirmation is attributed to the coordination and the capture, not to a direct consultation. The deposit contains Stones 52–54 and not `Phase3/lake-manifest.json` |
| Maintenance after the snapshot | PR #32 (merge `bd2f6c1b0ad600b0282b4776859bb917466152ea`): the dependency manifest committed and the CI resolution from it; later than the Version 54 snapshot, not in the deposit (see `docs/stone54/RESULTS.md`, §8) |
| Stone 55 | integrated on `main` at `d6ce3d72…` (2026-09-17, PR #33), audited (QA1 2026-09-17; Kimi 3 review and errata 2026-09-19) and CI-verified; **no tag, no Release, no deposit and no DOI of its own**. It is cited by its commit. This documentary consolidation is the candidate snapshot of a future Version 55, which is not created here |
