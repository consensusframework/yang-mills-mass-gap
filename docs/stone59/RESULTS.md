# Stone 59 — attained optimal budgets for fixed additive covers

Integrated state of `main` at commit
[`1dab07ab9da3052c7b957f858ccaf084501ecf4d`](https://github.com/consensusframework/yang-mills-mass-gap/commit/1dab07ab9da3052c7b957f858ccaf084501ecf4d)
(merge of [PR #44](https://github.com/consensusframework/yang-mills-mass-gap/pull/44);
parents `52cc0915547a13c0b738b0b506d572d00b011a12` and
`dcd6e6b18a909914dd789667d9830bff106bc762`; root tree
`1b4729f397e7db3dfb44c56f4c0193636fe30513`, `Phase3/` tree
`c3157cb9d428b74f73bf789588a3ab2f48d429e7`, `Phase3/LatticeGauge/` tree
`7b2da34274831bae6124cd154c58d09d0ba397c6`). Four states are to be kept
apart: the **candidate** `dcd6e6b1…` (the audited commit, single parent
`52cc0915…`, whose root tree is the merge's), the **scientific integration**
`1dab07ab…` (the merge above), the **documentary consolidation** (this
document and the audit records, merged after it) and the **deposit**. At
consolidation time (2026-10-22) Stone 59 was integrated on `main`, audited,
reviewed and CI-verified, but not part of any release and without a deposit
of its own: the most recent version is **Version 58** (commit
`52cc0915547a13c0b738b0b506d572d00b011a12`, tag `zenodo-v58`, GitHub Release
published on 2026-10-18, Zenodo record DOI
[10.5281/zenodo.23439473](https://doi.org/10.5281/zenodo.23439473), whose
publication is confirmed by the coordinator; see §8). Stone 59 is later than
the Version 58 snapshot and is not in that deposit; it is cited by its
commit. No DOI is reserved or recorded for a future Version 59 in this
document.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. The object is the normalized polymer functional of
> Stones 55–58 with the damping region kept everywhere: no new Gibbs measure,
> boundary condition, modified action, per-link profile or physical switch-off
> is constructed or claimed. Stone 59 optimizes the **cost of the budgets**
> of the Stone 58 additive cover for a **fixed** finite family of regions and
> **fixed** separation scales; it does not optimize the geometry of the
> regions, the scales, the order of any construction, the actual deviation
> of the functional or a universal constant. The minimum is obtained by
> classical choice: it is an existence statement, not a numerical algorithm,
> and no linear-programming duality is formalized. The minimum **value** is
> unique; the minimizing **vector** is not claimed unique (it is not, in
> general). The bound with the optimal cost is at most the bound of every
> admissible budget; strict improvements are exhibited on particular
> witnesses and no universal strict improvement, optimal constant,
> monotonicity of the functional or bibliographic priority is claimed. The
> two published Stone 58 estimates are consumed; nothing of the chain
> 56–57–58 is reopened.

## 1. The statement

Principal declarations (module
[`Phase3/LatticeGauge/ActivityProfileDampingOptimalCover.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingOptimalCover.lean),
blob `292602ddfc1ae915a7b4bf0a6095a4d5eaa754ba`, SHA-256
`61dde0c961ef126dd813c04a869da5fd4f60ec08395f84a2fb3ad18016704cee`,
36,696 bytes, 646 lines):

```
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_optimal_cover
LatticeGauge.optimal_two_terms_le_additive_two_terms
LatticeGauge.optimal_compact_le_additive_compact
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms_of_optimal
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_additive_cover_of_optimal
LatticeGauge.profileExpectation_eq_of_minCost_eq_zero
LatticeGauge.profileExpectation_eq_of_reaches_fin_zero
```

Objects of Stones 55–58, unchanged: the damping region `R` stays in the
definition of the functional, the weights, the activities and the exponents,

```
F_R(a) = profileExpectation μm β χ f s R a,
b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
D_s    = card (supportLinkFinset s).
```

The effective factor `b(η)` is the profile value `a η` when the polymer `η`
touches `R` and `1` otherwise; raw values of the profiles off `R` are never
read. A **fixed finite family of change regions** with its own separation
scale per region:

```
r : Fin m → Set (Link N),   n : Fin m → ℕ        (m = 0 included).
```

A **budget** is a vector `δ : Fin m → ℝ`. It is **admissible**
(`ActivityProfileOptimalCover.Admissible R r a a′ δ`) when its coordinates
are non-negative and it is an **additive cover** of the effective changes
(`AdditiveCover`): for every polymer `η`,

```
|b(η) − b′(η)| ≤ ∑ i : Fin m, if typedTouchesSupport η (r i) then δ i else 0,
```

exactly the Stone 58 hypothesis `hadd`. Its **cost** is the Stone 58 budget
sum, and the **optimal cost** is its minimum over the admissible budgets:

```
B(δ) = ∑ i, δ i · exp(−(n i : ℝ) / 2)                  (ActivityProfileOptimalCover.budget)
B*   = min { B(δ) : Admissible R r a a′ δ }             (ActivityProfileOptimalCover.minCost)
```

`Reaches R r a a′` (every polymer whose effective factor changes touches some
region `r i`) is the condition under which an admissible budget exists. For
profiles `a, a′` with values in `[0, 1]` and `hreach : Reaches R r a a′`,
under the hypotheses of the table below:

```
|F_R(a) − F_R(a′)|
    ≤ Cf · [exp(6 · D_s / 113) + exp(4 · D_s / 113)] · B*      (two-term form)
    ≤ (2 · Cf) · exp(6 · D_s / 113) · B*.                      (capstone)
```

Exactly the constant, the rate `exp(−n/2)` per region and the regime of
Stones 54–58. What changes is the cost: Stone 58 gives the bound with `B(δ)`
for **any** admissible budget `δ` supplied by the user; Stone 59 gives it
with the **smallest** such cost, `B* ≤ B(δ)` for every admissible `δ`
(including budgets with coordinates greater than `1`), and shows that the
minimum is **attained**. Nothing is divided by any budget, cost, capacity or
difference of profiles (there are divisions by the fixed non-zero constants
`2`, `113` and `40000` in the exponents and the regime, as in the earlier
stones); no `δ i ≤ 1` is required of the budgets compared; no factor of `m`,
of the volume, of `card R` or of `card (r i)` enters outside the sum.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`.

| Hypothesis | Meaning |
|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | `χ : G → ℝ` is a bounded measurable real function; no group-character hypothesis |
| `R : Set (Link N)` | the damping region, explicit and arbitrary |
| `mf : Measurable f`, `hCf : ∀ U, \|f U\| ≤ Cf` | measurability and an absolute majorant of the observable; `0 ≤ Cf` is **derived** (`nonneg_of_abs_le_of_config`, 52-E), not assumed |
| `(r : Fin m → Set (Link N)) (n : Fin m → ℕ)` | the fixed finite family and its scales; `m = 0` admitted; overlaps and repetitions allowed |
| `hsep : ∀ i, WalkBarrierSeparated s (r i) (n i)` | walk-barrier separation of the set `s` from each change region `r i` at its own scale `n i` |
| `h0 h1 h0' h1' : ∀ η, 0 ≤ a η ≤ 1, 0 ≤ a′ η ≤ 1` | the two profiles take values in `[0, 1]`; through `abs_touchFactor_sub_le_one` this bounds every effective change by `1` — the hypothesis under which the unit budget is admissible and the clipping preserves admissibility |
| `hreach : Reaches R r a a′` | every polymer whose effective factors differ touches some `r i`; equivalent, under the profile bounds, to the existence of an admissible budget (`reaches_iff_exists_admissible`) |

No budget `δ` appears in the signatures of the two estimates: the budget is
chosen inside (`optimalBudget`), and `B*` is its cost. Not required by the
public signatures: a minimizer, a budget or a decomposition supplied by the
user; `m > 0`; disjointness of the regions; `r i ⊆ R`; a separation of `s`
from `R`; a unit background outside the regions; `δ i ≤ 1` on the budgets
compared; a sign condition on activities or exponents; `DependsOnlyOn f s`
in the comparison of the two functionals; positivity of `Cf`, of the
optimal cost or of any capacity. `s` is the regional parameter of the
functional; it is asserted to be a support of `f` only where
`DependsOnlyOn f s` is present, which is not the case here.

### What the definition of `B*` carries

`exists_optimal` is proved first (existence of an admissible budget in
`[0, 1]^m` whose cost is at most the cost of every admissible budget);
`optimalBudget R r n h0 h1 h0' h1' hreach` is `Classical.choose` of that
existential and `minCost … := budget n (optimalBudget …)`. The four profile
bounds and `hreach` are **arguments of the definitions**: `B*` is defined
only where a minimizer exists; there is no conventional value for an empty
feasible set, and no infimum is taken without a minimizer. The value is
independent of the minimizer chosen (`minCost_eq_budget_of_isMin`: for any
admissible `δ*` whose cost is at most the cost of every admissible budget,
`minCost … = budget n δ*`; `budget_eq_of_isMin`: two such budgets have equal
costs). Two invocations of `optimalBudget` that differ only in the proof
terms of the hypotheses are definitionally equal by proof irrelevance; that
says nothing about the uniqueness of the minimizing vector, which fails in
general (§4).

### Algebraic auxiliaries versus analytic capstones

The optimization (§§59-L.1–59-L.6 of the module, namespace
`LatticeGauge.ActivityProfileOptimalCover`) involves no `β`, no measure, no
integration and no separation: it is about real vectors, the effective
factors and finite sums. The profile bounds enter the optimization only
through `abs_touchFactor_sub_le_one` (admissibility of the unit budget;
preservation of admissibility by the clipping). The analytic hypotheses
belong to the two capstones through the two published Stone 58 estimates
consumed there. The two comparisons of right-hand sides
(`optimal_two_terms_le_additive_two_terms`,
`optimal_compact_le_additive_compact`) are real inequalities and are stated
with `omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in`; the
two recoveries keep the full context; the two exact identities
(`profileExpectation_eq_of_minCost_eq_zero`,
`profileExpectation_eq_of_reaches_fin_zero`) are stated with
`omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in`,
keeping only what the type of `profileExpectation` needs. These `omit`s are
those of the source and are not to be generalized to the other theorems.

## 2. The route, as formalized

The chain promoted from the feasibility file (gate 59-A,
`T59A_optimal_cover_tests.lean`, four elaboration attempts, the fourth clean
with its tests) to the module (gate 59-L), with the two published Stone 58
estimates as the only analytic input. No hypothesis was added at any step
of the chain; in particular no positivity of a move parameter was needed
(there is no `move` in this stone: the optimization does not construct
intermediate profiles).

- **Feasibility.** `abs_touchFactor_sub_le_one`: under the profile bounds,
  `|b(η) − b′(η)| ≤ 1` for every polymer (`touchFactor_nonneg`,
  `touchFactor_le_one` of Stone 55). `admissible_one_of_reaches`: under
  `hreach` the unit budget `δ ≡ 1` is admissible — a polymer with no
  effective change is covered by the non-negative sum (`coverSum_nonneg`);
  a polymer with an effective change touches some `r i`, whose unit term
  alone dominates the change (`Finset.single_le_sum`).
  `reaches_of_admissible`: conversely, if some admissible budget exists, a
  polymer with an effective change must touch some region, since otherwise
  its cover sum is `0` (this direction uses no profile bound).
  `reaches_iff_exists_admissible` records the equivalence.
- **Clipping at one.** `clip δ i := min (δ i) 1`, with `clip_nonneg`,
  `clip_le_one`, `clip_le`. `admissible_clip`: the clipped budget of an
  admissible budget is admissible — for each polymer, either some touched
  region has `δ i ≥ 1`, and then its clipped term `1` alone covers the change
  (bounded by `1` through the profile bounds), or every touched region has
  `δ j < 1` and the touched terms are unchanged. Budgets of untouched regions
  contribute `0` before and after the clipping. `budget_clip_le`: the cost
  does not increase, the weights `exp(−n i/2)` being positive.
- **Compactness and the attained minimum.** `feasibleBox R r a a′ :=
  Set.Icc 0 1 ∩ {δ | AdditiveCover R r a a′ δ}`. `isClosed_additiveCover`
  (stated with `_root_.IsClosed`, the library having its own
  `LatticeGauge.IsClosed` for loops): the cover set is the intersection, over
  **all** polymers (no `Fintype (Polymer N)`), of the closed sets
  `{δ | |b(η) − b′(η)| ≤ ∑ i, if … then δ i else 0}`
  (`isClosed_iInter`, `isClosed_le continuous_const (continuous_finset_sum …)`).
  `isCompact_feasibleBox`: `isCompact_Icc` on `Fin m → ℝ` intersected with a
  closed set (`IsCompact.inter_right`), for every `m`, `m = 0` included.
  `feasibleBox_nonempty`: the unit budget under `hreach`.
  `continuous_budget`: a finite sum of coordinates times constants.
  `exists_optimal`: `IsCompact.exists_isMinOn` gives a minimizer `δs` on the
  box; for any admissible `δ` (no upper bound), `clip δ` is in the box, so
  `budget n δs ≤ budget n (clip δ) ≤ budget n δ` — the minimum on the box is
  the minimum over **all** admissible budgets. The unrestricted admissible
  set is not declared compact (when non-empty and `m ≥ 1` it is unbounded);
  only the box is used.
- **The optimal budget and its cost.** `optimalBudget`, `minCost` by
  classical choice (above); `optimalBudget_admissible`,
  `optimalBudget_le_one` (its coordinates are at most `1`),
  `minCost_le_budget` (`B* ≤ B(δ)` for every admissible `δ`),
  `minCost_nonneg` (`budget_nonneg'`), `budget_eq_of_isMin`,
  `minCost_eq_budget_of_isMin` (uniqueness of the value).
- **Zero cost and the degenerate cases.** `minCost_eq_zero_iff`: `B* = 0`
  iff `b(η) = b′(η)` for every polymer — with a cost `0`, every term of the
  non-negative sum vanishes (`Finset.sum_eq_zero_iff_of_nonneg`) and the
  positive weights force `optimalBudget … ≡ 0`, whose cover sums are `0`;
  conversely equal effective factors make the zero budget admissible
  (`admissible_zero_of_touchFactor_eq`, `budget_zero`), so `B* ≤ 0`.
  `touchFactor_eq_of_reaches_fin_zero`: with `m = 0`, `hreach` forces equal
  effective factors (no index exists); `budget_fin_zero`: every cost over
  `Fin 0` is `0`; `reaches_empty_region`: with `R = ∅` all effective factors
  are `1` (`not_blockTouchesSupport_empty`), so `hreach` holds for arbitrary
  real profiles.
- **Closure.** The two capstones apply the two published Stone 58 estimates
  (`abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms`,
  `…_le_additive_cover`) to `optimalBudget …`, whose admissibility supplies
  `hδ0` and `hadd`; the Stone 58 conclusion with the explicit sum is
  definitionally `minCost …`. `optimal_two_terms_le_additive_two_terms` and
  `optimal_compact_le_additive_compact`: for every admissible `δ`, the
  right-hand side with `B*` is at most the right-hand side with `B(δ)` —
  `minCost_le_budget` multiplied by the non-negative prefactor
  (`0 ≤ Cf` derived, exponentials positive; `mul_le_mul_of_nonneg_left`).
  `…_le_additive_cover_two_terms_of_optimal` and
  `…_le_additive_cover_of_optimal`: from `hδ0` and `hadd`,
  `reaches_of_admissible` gives `hreach`, the optimal estimate applies and
  the comparison closes — the two Stone 58 statements, with their types,
  recovered from the optimal ones. `profileExpectation_eq_of_minCost_eq_zero`
  and `profileExpectation_eq_of_reaches_fin_zero`: exact equality of the
  functionals from `B* = 0` or from `m = 0` through the Stone 56 identity
  `profileExpectation_eq_of_touchFactor_eq`.

The dependency **58 → 59 → recovery of 58** is intentional: the two Stone 58
estimates are the input of the two optimal estimates, and the recoveries
are compatibility checks of the interface, not an independent proof of
Stone 58. Nothing of Stones 56–58 is re-derived.

## 3. The module and its declarations

One new module (646 Lean lines; 44 top-level declaration lines by the
textual count of the README — `grep -cE` of lines beginning with `theorem`,
`lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`,
`inductive` or `class` followed by a space — at the candidate `dcd6e6b1…`
and at the merge `1dab07ab…`: 36 `theorem`, 4 `noncomputable def` and 4
`def`; 44 in-file `#print axioms` commands, one per declaration), a leaf
over Stone 58; no pre-existing module was modified; the only change outside
the new file is its glob in `Phase3/lakefile.toml` (119 → 120 modules; blob
`cd461108aaecf1760d02806410226c94642dfd90`, previously `9ad914d0…`). The
diff from the base is exactly these two paths, +647/−1.

| Line | Kind | Declaration | Content |
|---|---|---|---|
| 117 | `def` | `AdditiveCover` | the Stone 58 cover condition on a budget |
| 123 | `def` | `Admissible` | non-negative coordinates and `AdditiveCover` |
| 128 | `noncomputable def` | `budget` | `∑ i, δ i · exp(−(n i)/2)` |
| 133 | `def` | `Reaches` | every polymer with an effective change touches some region |
| 139 | theorem | `abs_touchFactor_sub_le_one` | `\|b − b′\| ≤ 1` under the profile bounds |
| 149 | theorem | `coverSum_nonneg` | the cover sum of a non-negative budget is `≥ 0` |
| 157 | theorem | `budget_nonneg'` | the cost of a non-negative budget is `≥ 0` |
| 164 | theorem | `admissible_one_of_reaches` | the unit budget is admissible under `hreach` |
| 183 | theorem | `reaches_of_admissible` | an admissible budget gives `hreach` (no profile bound) |
| 195 | theorem | `reaches_iff_exists_admissible` | the equivalence |
| 205 | `noncomputable def` | `clip` | `δ i ↦ min (δ i) 1` |
| 207, 210, 212 | theorem | `clip_nonneg`, `clip_le_one`, `clip_le` | elementary properties |
| 217 | theorem | `admissible_clip` | clipping preserves admissibility |
| 247 | theorem | `budget_clip_le` | clipping does not increase the cost |
| 254 | `def` | `feasibleBox` | `Icc 0 1 ∩ {cover}` |
| 258 | theorem | `isClosed_additiveCover` | the cover set is closed |
| 273 | theorem | `isCompact_feasibleBox` | compactness |
| 278 | theorem | `feasibleBox_nonempty` | non-empty under `hreach` |
| 285 | theorem | `continuous_budget` | continuity of the cost |
| 295 | theorem | `exists_optimal` | an admissible budget in `[0, 1]^m` of minimal cost among **all** admissible budgets |
| 312 | `noncomputable def` | `optimalBudget` | `Classical.choose` of `exists_optimal` |
| 320 | `noncomputable def` | `minCost` | `B*`, the cost of `optimalBudget` |
| 326 | theorem | `optimalBudget_admissible` | |
| 333 | theorem | `optimalBudget_le_one` | |
| 341 | theorem | `minCost_le_budget` | `B* ≤ B(δ)` for every admissible `δ` |
| 348 | theorem | `minCost_nonneg` | `0 ≤ B*` |
| 355 | theorem | `budget_eq_of_isMin` | two minimizers have the same cost |
| 364 | theorem | `minCost_eq_budget_of_isMin` | `B*` is the cost of any minimizer |
| 376 | theorem | `admissible_zero_of_touchFactor_eq` | the zero budget is admissible when the effective factors coincide |
| 383 | theorem | `budget_zero` | the cost of the zero budget is `0` |
| 390 | theorem | `minCost_eq_zero_iff` | `B* = 0 ↔ ∀ η, b(η) = b′(η)` |
| 423 | theorem | `touchFactor_eq_of_reaches_fin_zero` | `m = 0` under `hreach`: equal effective factors |
| 431 | theorem | `budget_fin_zero` | the cost over `Fin 0` is `0` |
| 435 | theorem | `reaches_empty_region` | `R = ∅`: `hreach` for arbitrary real profiles |
| 457 | theorem | `abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms` | the two-term estimate with `B*` |
| 478 | theorem | `abs_profileExpectation_sub_profileExpectation_le_optimal_cover` | the compact estimate with `B*` (capstone) |
| 498 | theorem | `optimal_two_terms_le_additive_two_terms` | the optimal two-term bound is at most the Stone 58 two-term bound of every admissible budget |
| 516 | theorem | `optimal_compact_le_additive_compact` | likewise for the compact bounds |
| 533 | theorem | `abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms_of_optimal` | the Stone 58 two-term estimate recovered from the optimal one |
| 556 | theorem | `abs_profileExpectation_sub_profileExpectation_le_additive_cover_of_optimal` | the Stone 58 compact estimate recovered |
| 580 | theorem | `profileExpectation_eq_of_minCost_eq_zero` | `B* = 0` gives `F_R(a) = F_R(a′)` exactly |
| 592 | theorem | `profileExpectation_eq_of_reaches_fin_zero` | `m = 0` under `hreach` gives `F_R(a) = F_R(a′)` exactly, for arbitrary real profiles |

The first 36 declarations are in the namespace
`LatticeGauge.ActivityProfileOptimalCover`; the last eight are public in
`LatticeGauge`. Imports: `Mathlib` and
`LatticeGauge.ActivityProfileDampingAdditiveCover` (Stone 58). Real
dependencies, in code: from Stone 58 the two published estimates (one use
each, in the two optimal estimates); from Stone 56
`profileExpectation_eq_of_touchFactor_eq` (two uses: `B* = 0` and `m = 0`);
from Stone 52-E `nonneg_of_abs_le_of_config` (two uses, the comparisons);
from Stone 55 `touchFactor_nonneg`, `touchFactor_le_one`; from the polymer
layer `not_blockTouchesSupport_empty`; from Mathlib `isCompact_Icc`,
`IsCompact.inter_right`, `isClosed_iInter`, `isClosed_le`,
`continuous_finset_sum`, `continuous_apply`, `IsCompact.exists_isMinOn`,
`isMinOn_iff`, `Finset.single_le_sum`, `Finset.sum_eq_zero_iff_of_nonneg`,
`Real.exp_pos`, `Real.exp_le_one_iff`, `Real.exp_lt_one_iff`. The Stone 57
capstones and the Stone 58 auxiliaries (`move`, `prefixCost`,
`additiveProfile`, the chain lemma) have no use in code. `Classical.choose`
occurs only in `optimalBudget` and its specifications. Hygiene: 0 `sorry`,
`admit`, `native_decide`, scientific `axiom`, `unsafe`, `implemented_by`,
`set_option`, `maxHeartbeats`; linters active; 0 warnings in the module.

Origin of the proposal: the scientific architecture of GPT Astra / Can (tape
59-AL, feasibility and construction in one tape, the passage from gate A to
gate L authorized in advance); the route was proposed on paper and compiled
in Lean by the constructing instance only. The feasibility file
`T59A_optimal_cover_tests.lean` (the chain and the tests T1–T7 in a
disposable file, plus the expected failure T8x; four elaboration attempts —
the first with eight errors in the chain, the second clean, the third with
eight errors in the tests, the fourth clean) was promoted to this module,
whose definitive count is 36 theorems and 8 definitions.

## 4. Interfaces, control cases and limits

| Case | Declaration or test | Content |
|---|---|---|
| feasibility | `reaches_iff_exists_admissible`; T2 (constructor), Q1a (auditor) | under the profile bounds, `hreach` holds iff some admissible budget exists; the unit budget is the witness in one direction; the other direction needs no profile bound |
| clipping | `admissible_clip`, `budget_clip_le`; T1, Q1b–d | `clip 7 = 1`, `clip 0 = 0`, `clip 1 = 1`, `clip (1/4) = 1/4`; admissibility preserved and cost not increased for arbitrary admissible budgets; `2 ≤ min 2 1` is false. The auditor's Q1e exhibits the **necessity of the profile bounds** for the clipping: with a profile value `2` on a polymer touching `R` and `r 0`, the budget `δ = 2` covers the change `2` while `clip δ = 1` does not |
| the attained minimum | `exists_optimal`; T2, Q2 | the existence is obtained from `hreach` alone, no minimizer being supplied; the auditor's Q2 re-proves the closedness of the cover set over all polymers, the compactness of the box, the existence on the box and the promotion to all admissible budgets by its own route, without `exists_optimal`, and shows the cost unbounded on the unrestricted admissible set (`m = 1`), so that no compactness of that set is used |
| a budget with a coordinate `7` | T6 (constructor), Q6b (auditor) | the Stone 58 recoveries applied with `δ ≡ 7`: `minCost_le_budget` has no hypothesis `δ ≤ 1`; the constructor's T6 applies `δ ≡ 7` to the compact recovery, the auditor's Q6b to both recoveries |
| the global witness of a strict cost improvement | T4 (constructor, theorems `w_*`), Q4 (auditor) | `a ≡ 1/4`, `a′ = 3/4` at `η₀` and `1/4` elsewhere (both in `[0, 1]`), scales `n = (0, 4)`, `η₀` touching `R`, `r 0` and `r 1` by hypothesis: the effective change at `η₀` is `1/2`; every admissible budget has `δ 0 + δ 1 ≥ 1/2` (constructor) and hence cost `δ 0 + δ 1·e^{−2} ≥ (1/2)·e^{−2}`; the budget `(0, 1/2)` is admissible for every polymer with that cost, so **`B* = (1/2)·e^{−2}`** (constructor by `le_antisymm` through `minCost_le_budget` and the lower bound; auditor through `minCost_eq_budget_of_isMin`); and **`B* < 1/4 + (1/4)·e^{−2}`**, the cost of the budget `(1/4, 1/4)` — a strict improvement of the **cost** against that particular budget. The complete compact bounds are strictly ordered when `Cf > 0` and both equal `0` when `Cf = 0` (recorded by an `example` in T4 and by Q4d/e). `B*` is a bound, not the actual deviation; no universal strict improvement is inferred |
| non-uniqueness of the minimizer | T5 (constructor, `w_two_minimizers`), Q5 (auditor) | equal scales `n ≡ 0` on the same witness: `(1/2, 0)` and `(0, 1/2)` are both admissible, distinct, both of cost `1/2 = B*` — the value is unique, the vector is not |
| zero cost, equal effective factors, non-unit common background | `minCost_eq_zero_iff`, `profileExpectation_eq_of_minCost_eq_zero`; T3, Q3b, Q3e | `B* = 0` iff the effective factors coincide; raw differences off `R` are ignored; the auditor's Q3e takes a common factor `1/2` on `R` with raw differences off `R`: `B* = 0` and `F_R(a) = F_R(a′)` |
| `m = 0` | `touchFactor_eq_of_reaches_fin_zero`, `budget_fin_zero`, `profileExpectation_eq_of_reaches_fin_zero`; T3, Q3c | the empty family under `hreach` forces equal effective factors and exact equality of the functionals for **arbitrary real** profiles (the auditor's Q3c uses `a′ = −7` off `R`); the typed `B*` is only defined under the profile bounds, and the algebraic identity does not extend its definition |
| `R = ∅` | `reaches_empty_region`; T3, Q3d | all effective factors are `1`, `hreach` holds for arbitrary real profiles; under the profile bounds `B* = 0` and `F_∅(a) = F_∅(a′)` (Q3d with raw values `1/3` and `2/3`) |
| recoveries and signatures | `…_of_optimal` (two), T6, Q6b/c | both Stone 58 statements recovered from the optimal ones; the types of the recoveries and of the published Stone 58 theorems are definitionally equal in both directions (`example`s by `rfl` between proof terms are proof irrelevance, not syntactic identity of proofs) |
| closure by hand | T7 (constructor), Q6a (auditor) | a minimizer taken from the `exists_optimal` interface, the Stone 58 estimate applied to it and the comparison with any admissible budget assembled by minimality and signs, without the two optimal capstones; the constructor's T7 uses the compact Stone 58 form directly and `mul_le_mul_of_nonneg_left`, not `optimal_two_terms_le_additive_two_terms` |
| expected failure | T8x (constructor), Q8x (auditor) | a change `1/2` on a polymer touching `R` but no region: `¬ ∃ admissible` and `¬ Reaches` are **proved** (`no_admissible`, `reach_false`), and the attempt to apply the optimal estimate fails with exactly one error at the obligation of reach (constructor: `unsolved goals … ⊢ False` at 47:58; auditor: the single open goal `typedTouchesSupport η₀ (r₁ 0)`, negated by its hypothesis) — an application failure by an impossible hypothesis, not a counterexample to the conclusion on `F_R`, not an import or timeout failure |

The geometric tests are parameterized by `typedTouchesSupport` hypotheses
(which polymer touches which region); no concrete lattice instance is
constructed, and the coordination executed none of these tests in Lean. The
result is of finite volume, in the declared regime, on periodic
four-dimensional lattices; it does not construct a thermodynamic or
continuum limit or a mass gap, does not prove the Clay problem, and claims
no bibliographic priority, monotonicity or differentiability of the
functional, new Gibbs measure or boundary condition, uniqueness of the
minimizing vector, optimization of the regions or scales, numerical
algorithm or linear-programming duality.

## 5. Kernel certificates and CI

- The module carries 44 in-file `#print axioms` commands (one per
  declaration: the 36 theorems and the 8 definitions); each reports
  `[propext, Classical.choice, Quot.sound]`. The library carries 361 in-file
  `#print axioms` commands at `dcd6e6b1…` and at `1dab07ab…` (317 + 44);
  these are certificate commands, not a count of theorems and not a global
  inventory of the axioms of every declaration.
- The CI runs emit **364 axiom outputs = 361 of the build + 3 of the workflow
  step** on the Version 49–51 capstones, for **362 distinct names**: two of
  the three workflow outputs repeat names already certified by the build
  (`abs_gibbsCovariance_le_local_exp_decay`,
  `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`,
  multiplicity 2 each), and the third,
  `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name to the list
  emitted by the build (the Version 49 capstone has no in-file `#print
  axioms`); it is not a new theorem added by the workflow. In runs 515 and
  516, 105 of the 364 lists are printed across more than one line (104 of
  the 361 in the auditor's clean build); the reading recomposes each list up
  to its closing bracket and accepts names with apostrophes
  (`activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`,
  `ActivityProfileOptimalCover.budget_nonneg'`). The number of line breaks is
  a property of the printing, observed and not imposed on future runs.
- Hygiene in the module: 114 inherited build warnings (unchanged since
  Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`
  (the Version 58 snapshot `52cc0915…`), delivered as a verifiable git
  bundle; the QA1 audit and the two adversarial readings before publication;
  push of the audited commit, a non-draft pull request, `build-phase3` green
  on the pull-request head, a normal merge with the expected head SHA locked
  (no squash, no rebase), and `build-phase3` green again on `main` at the
  merge commit.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `dcd6e6b18a909914dd789667d9830bff106bc762` | [#44](https://github.com/consensusframework/yang-mills-mass-gap/pull/44) | [515](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/39605343046) (id 39605343046, job 119239976474) | `1dab07ab9da3052c7b957f858ccaf084501ecf4d` | [516](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/39607407756) (id 39607407756, job 119247067798) |

Custody note: the pull-request run 515 is associated with the head
`dcd6e6b1…`, but its effective checkout was the provisional merge commit
`edcb4fdeefddeb6e6d2291538b9bf47a9057735f` ("Merge dcd6e6b1… into
52cc0915…"), as recorded in the job log read by the publishing instance
(`docs/audits/stone59/publication/RELATORIO_59-P.md`), whose parents are the
base and the candidate and whose root tree is the candidate's; run 516
compiled the definitive merge `1dab07ab…` itself. The run metadata alone do
not prove the effective checkout; the attribution is to the log reading.
Both runs (2026-10-21): `Build completed successfully`; the dependency
manifest `c376bbe9…1227` recorded and verified after the resolution and
after the build, the nine dependencies checked out at the recorded
revisions, no `lake update`; **120 `LatticeGauge` modules built, 120
distinct names, 0 replayed** — no replay of the project; the nine `Built`
targets outside `LatticeGauge` are the Mathlib cache tool (four Lean modules
`Cache.IO`, `Cache.Hashing`, `Cache.Requests`, `Cache.Main`, their four C
objects and the executable `cache`), not nine rebuilt packages; the nine
package revisions are verified against the manifest in a separate step, and
the remaining dependency artifacts come from the cache, so the log does not
show a rebuild of Mathlib and the dependencies from source; 0 errors; 114
warnings, all in `LatticeGauge/`, none in the new module, none from
dependencies, the full warning blocks identical as a multiset to the QA1
baseline of this stone (and to the QA1 baseline of Stone 58); 364 axiom
outputs, all standard, the 44 of the new module included; no `sorryAx`; the
certificate multisets of the two runs identical. The two logs are preserved
in `docs/audits/stone59/packages/STONE59P_evidence.zip` and can be re-read
with the coordination's script
`docs/audits/stone59/tools/verify_ci59.py` (see the audit index).

Toolchain at `1dab07ab…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 120
modules, 39,827 Lean source lines and 1,878 top-level declaration lines by
the textual count (1,834 at Version 58 plus the 44 of this module) — 1,878
is not a number of theorems.

## 6. Relation to Stone 58

Stone 58 bounds the difference of the functionals by `Cf·(E6 + E4)·B(δ)`
for **any** admissible budget `δ` of the additive cover, the user choosing
the budget. Stone 59 fixes the family and the scales, takes the admissible
budgets as a feasible set, shows that it is non-empty exactly under
`Reaches`, that the cost attains its minimum on it, and replaces `B(δ)` by
that minimum `B*`: the optimal estimate is at most the Stone 58 estimate of
every admissible budget, with the same constant, rate and regime, and both
Stone 58 statements are recovered from it. The Stone 58 estimates are
consumed (one use each); the recoveries are compatibility checks, not an
independent proof of Stone 58, and nothing of the chain 56–57–58 is
reopened.

## 7. Audits and review

Recorded, with hashes and provenance, in
[`docs/audits/stone59/`](../audits/stone59/README.md). Four kinds of evidence
with distinct scopes; none is specialized human mathematical review. No
complementary execution on a third platform was received for this stone.

- **59-QA1** — reproduction by execution of the candidate `dcd6e6b1…` by a
  separate instance of Claude Fable 5.1 (same model as the constructor; prior
  exposure to the earlier stones declared, not blind; the constructor's
  report read before the execution only to identify the target and the
  custody, the constructor's logs and tests opened only in a second pass
  after the auditor's own conclusions, recorded in
  `PRELIMINARY_CONCLUSIONS_first_pass.md`). Reconstruction of the commit
  from the bundle (the ref not recreated); dependencies reused from the
  auditor's Stone 57/58 bench (materialized then from the Mathlib community
  cache at the nine manifest revisions; 9/9 revisions checked before the
  build; no `lake update`; not recompiled — 0 built / 0 replayed of
  dependencies and no dependency diagnostics in that log); project
  artifacts removed before the build; single integral `lake build`
  2026-10-18, 13:31:47Z → 13:52:03Z, 1,216 s, exit 0, **120 modules built
  (120 distinct names), 0 replayed**, 0 errors, 361 certificates standard
  (104 multi-line), 0 `sorryAx`, manifest identical before and after; 114
  inherited warning blocks identical to the Stone 58 QA1 baseline, none in
  the new module; own certificates Q0 of **44/44** declarations; own tests
  Q1–Q6 pass, Q7 by `#check` and grep, Q8x fails on the single obligation of
  reach; 62 warnings in the auditor's own disposable tests (Q4 6, Q5 4, Q6
  52), separate from the 114 of the project. The constructor's tests T1–T8x
  were re-executed by the auditor in the second pass (the positive test has
  13 `#check` and no `#print axioms`); the re-execution does not transfer
  their authorship. Verdict `PASS NO ESCOPO` (custody, execution,
  mathematics, documentation PASS). No errata was issued by the auditor; its
  §6 records five observations on the **constructor's** report, matrices and
  scripts (not on the candidate), recorded in the audit index.
- **59-G-ADV with its errata C1** — adversarial review by **Gemini**
  (interface web, as the document identifies itself; no model version is
  inferred), a different model family, by reading and mathematical analysis
  of the module in full and of the Stone 58 module, with the manifests of
  the transport package compared textually, **without any Lean execution and
  without recomputing hashes**; prior exposure declared (the Version 58
  Zenodo record), not blind; no report of the constructor, the auditor or
  the other reviewer consulted. Verdict `PASS NO ESCOPO`. The review is
  preserved in three files: the first part as received, and the technical
  continuation and the errata C1 as transcriptions by the coordination of
  messages in the chat (no integral original file exists; the continuation
  repeats part of the item at which the first part was cut). C1 (prompted by
  the coordination's conference, not a finding of the first pass) corrects
  three points of the **report** and keeps the verdict: there is no
  definition `ActivityProfileMultiRegion.budget` (Stone 58 uses the theorem
  `budget_nonneg` with an expanded sum; `budget` is a new definition of
  Stone 59); the unrestricted admissible set fails to be compact only when
  non-empty and `m ≥ 1` (empty, or `m = 0`, it is compact; the box is
  compact unconditionally); `χ` is a bounded measurable real function, with
  no character hypothesis.
- **59-K-ADV with its errata C1** — adversarial review by **Kimi (Moonshot
  AI)**, as the documents identify the reviewer, a different model family,
  by reading and mathematical analysis of the module in full and of the
  interfaces consumed, with own custody checks (hashes of the transport
  package, the Git blobs of the 125 packaged files, the `Phase3/` and root
  trees recomputed and compared with the public base `52cc0915…`, the diff of
  exactly two paths, the counts) **without any Lean execution**; same
  conversation instance as the Stone 57 and 58 reviews, prior exposure
  declared, not blind. The commit object `dcd6e6b1…` was not yet on GitHub
  at the time, so its authorship, message and signature were not
  authenticated by the reviewer (a limitation of that moment, not a failure
  of the bundle, which the QA1 had verified; the commit was published later
  by PR #44). Verdict `PASS NO ESCOPO`: no mathematical defect, no interface
  problem, no documentary imprecision in the module. One errata (C1,
  2026-10-19, by the same instance, after the coordination's conference)
  corrects four points of the **report** and keeps the verdict: the cost of
  the budget `(1, 1)` with equal weights `w` is `2w`, not `w`; the
  non-compactness of the unrestricted set is qualified (non-empty and
  `m ≥ 1`); for an arbitrary witness of `exists_optimal` the identification
  of its cost with `B*` is by `minCost_eq_budget_of_isMin`, while the
  definitional unfolding applies to `optimalBudget` itself (the route the
  module uses); the 44 commands counted in the source are commands, not 44
  executions by the reviewer.
- **59-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit), with the operational package of the two
  CI logs; to be read with the coordination's precisions C59-P1 and C59-P2
  of the audit index.
- **GPT Astra / Can** — scientific architecture and review: the tape 59-AL
  (feasibility and construction), the integration tape 59-P, the documentary
  conference of 2026-10-21 (the two CI logs re-read through the GitHub tool,
  the certificates and the warnings re-counted, the portable script
  `verify_ci59.py` written) and this consolidation; no Lean build of its own.

## 8. Version records

| Step | Record |
|---|---|
| Version 58 (the current version) | commit `52cc0915547a13c0b738b0b506d572d00b011a12` (merge of PR #43, the documentary consolidation of Stone 58; Stone 58 itself integrated at `69706b9a…`, PR #42), tag `zenodo-v58` (simple tag), GitHub Release [`zenodo-v58`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v58) published on 2026-10-18 (`draft = false`, 2026-10-18T12:00:16Z, read through the GitHub API by the consolidating session) with four assets (`yang-mills-mass-gap-zenodo-v58.zip`, 1,891,210 bytes, SHA-256 `1828df6a…fc63`; `RELEASE_NOTES_PEDRA58.md`, 37,782 bytes, SHA-256 `6041916b…6a3c`; `MANIFEST_v58.txt`, 41,658 bytes, SHA-256 `b726f8af…b6e3`; `SHA256SUMS.txt`, 275 bytes, SHA-256 `5e073455…cc91`; sizes and digests as reported by the API, equal to those of the packaging delivery 58-RELEASE-L; not a new comparison of downloaded bytes); Zenodo record DOI [10.5281/zenodo.23439473](https://doi.org/10.5281/zenodo.23439473) (concept DOI 10.5281/zenodo.17397622), **published**, as confirmed by the coordinator — the exact Zenodo publication date was not established by the materials of this consolidation and is not inferred from the Release date; the consolidating session did not consult Zenodo. The deposit contains Stones 52–58 and the committed dependency manifest, and not Stone 59 |
| Stone 59 | integrated on `main` at `1dab07ab…` (2026-10-21, PR #44), audited (QA1 2026-10-18), reviewed (Gemini, 2026-10-18, with its errata C1 whose date the transcription does not record; Kimi, 2026-10-19, with its errata C1 of the same day) and CI-verified (runs 515 and 516); **no tag, no Release, no deposit and no reserved DOI of its own recorded here**. It is cited by its commit. The future Version 59, if deposited, will be packaged from the definitive documentary merge in a step of its own |
