# Stone 58 — finite-volume Lipschitz stability under additive multiregion cover

Integrated state of `main` at commit
[`69706b9a13a23b0f132418f2390d4030e1fcc78b`](https://github.com/consensusframework/yang-mills-mass-gap/commit/69706b9a13a23b0f132418f2390d4030e1fcc78b)
(merge of [PR #42](https://github.com/consensusframework/yang-mills-mass-gap/pull/42);
parents `18c6ff084020e52c8932ecfd20e4b19f47efdf02` and
`d942edd3986ac8cb13a8d5958bf1e11461434794`; root tree
`674507a44812160be7cc7bf319359f66f5dca4a2`, `Phase3/` tree
`58a60e8be11d00cfa94f36a9adbc81b5dbe3e32b`). Four states are to be kept
apart: the **candidate** `d942edd3…` (the audited commit, single parent
`18c6ff08…`, whose root tree is the merge's), the **scientific integration**
`69706b9a…` (the merge above), the **documentary consolidation** (this
document and the audit records, merged after it) and the **deposit**. At
consolidation time (2026-10-17) Stone 58 was integrated on `main`, audited,
reviewed and CI-verified, but not part of any release and without a deposit
of its own: the most recent version is **Version 57** (commit
`18c6ff084020e52c8932ecfd20e4b19f47efdf02`, tag `zenodo-v57`, GitHub Release
published on 2026-10-11, Zenodo record DOI
[10.5281/zenodo.23305142](https://doi.org/10.5281/zenodo.23305142), whose
publication is confirmed by the coordinator; see §8). Stone 58 is later than
the Version 57 snapshot and is not in that deposit; it is cited by its
commit. No DOI is reserved or recorded for a future Version 58 in this
document.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. The object is the normalized polymer functional of
> Stones 55–57 with the damping region kept everywhere: no new Gibbs measure,
> boundary condition, modified action, per-link profile or physical switch-off
> is constructed or claimed; nothing asserts monotonicity or differentiability
> of the functional in the profile (the scalar path of the construction is
> monotone towards its target, the functional is not claimed monotone), a
> spatial-mixing theorem, an optimal choice of budgets or of the order of the
> steps, a Euclidean distance or a restriction on the number or size of the
> regions; no optimality, sharpness or bibliographic priority is claimed for
> the constant, the hypothesis or the route. Stone 58 widens the **cover
> hypothesis** of Stone 57 and keeps its constant, rate and regime; the bound
> itself is not improved. The published Stone 56 two-term estimate is consumed
> at every step, and nothing of its cluster, erosion or budget chain is
> reopened.

## 1. The statement

Principal declarations (module
[`Phase3/LatticeGauge/ActivityProfileDampingAdditiveCover.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingAdditiveCover.lean),
blob `9d0274fd94ee2cb245e9cc80c9482c9a409d177e`):

```
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_additive_cover
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms_of_additive
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_multiregion_of_additive
LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_additive
LatticeGauge.profileExpectation_eq_of_additive_cover_empty_family
LatticeGauge.profileExpectation_eq_of_additive_cover_zero_budget
```

Objects of Stones 55–57, unchanged: the damping region `R` stays in the
definition of the functional, the weights, the activities and the exponents,

```
F_R(a) = profileExpectation μm β χ f s R a,
b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
D_s    = card (supportLinkFinset s).
```

A **finite family of change regions**, indexed by `i : Fin m` (`m = 0`
included), with its own separation scale and budget per region:

```
r : Fin m → Set (Link N),   n : Fin m → ℕ,   δ : Fin m → ℝ,
B = ∑ i : Fin m, δ i · exp(−(n i : ℝ) / 2).
```

The new hypothesis is the **additive cover** of the effective changes:

```
hadd : ∀ η, |b(η) − b′(η)|
  ≤ ∑ i : Fin m, if typedTouchesSupport η (r i) then δ i else 0.
```

For profiles `a, a′` with values in `[0, 1]`, under the hypotheses of the
table below:

```
|F_R(a) − F_R(a′)|
    ≤ Cf · [exp(6 · D_s / 113) + exp(4 · D_s / 113)] · B      (two-term form)
    ≤ (2 · Cf) · exp(6 · D_s / 113) · B.                      (capstone)
```

Exactly the constant, the rate `exp(−n/2)` per region and the regime of Stone
57. What changes is the cover: in Stone 57 every polymer whose effective
factor changes had to find **one** region that pays the whole change; here
the regions a polymer touches may **share** the cost, the change being paid by
the sum of their budgets. The Stone 57 cover implies the additive one under
`δ i ≥ 0` (`additive_of_cover`); the converse fails, as the parametric witness
of §4 shows (budgets `1/4, 1/4` and a change `1/2` on a polymer touching both
regions). The condition is on the **effective factors** of the polymers, not
on raw differences of profiles ignored outside `R`, and it is not a cover of a
union of sets of links. Nothing is divided by any budget, by the sum of the
budgets, by an accumulated capacity or by a difference of profiles (there are
divisions by the fixed non-zero constants `2`, `113` and `40000` in the
exponents and the regime, as in the earlier stones); no `δ i ≤ 1` is
required; no factor of `m`, of the volume, of `card R` or of `card (r i)`
enters outside the sum.

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
| `hδ0 : ∀ i, 0 ≤ δ i` | the budgets are non-negative; no upper bound on any `δ i` |
| `hsep : ∀ i, WalkBarrierSeparated s (r i) (n i)` | walk-barrier separation of the set `s` from each change region `r i` at its own scale `n i` |
| `h0 h1 h0' h1' : ∀ η, 0 ≤ a η ≤ 1, 0 ≤ a′ η ≤ 1` | the two profiles take values in `[0, 1]` (the absence of an upper bound on `δ i` does not remove this hypothesis) |
| `hadd : ∀ η, \|touchFactor R a η − touchFactor R a′ η\| ≤ ∑ i, if typedTouchesSupport η (r i) then δ i else 0` | **additive cover of the effective changes by polymers**: the change of the effective factor of each polymer is paid by the sum of the budgets of the regions that polymer touches; no single region has to pay it |

Not required by the public signatures: an `owner` or a decomposition of the
amplitudes supplied by the user (the intermediate profiles are built inside
the proof); `m > 0`; disjointness of the regions; `r i ⊆ R`; a separation of
`s` from `R`; a unit background outside the regions; `δ i ≤ 1`; a sign
condition on activities or exponents; `DependsOnlyOn f s` in the comparison of
the two functionals. `s` is the regional parameter of the functional (the set
whose touching cores index the polymer representation); it is asserted to be
a support of `f` only where `DependsOnlyOn f s` is present, which is not the
case here. `R` stays the damping region of both functionals and may carry a
common, non-unit background near `s`. The bound is uniform in the admissible
background; this does not mean that the functional is independent of the
background, and a non-unit common background is not identified with the
original Gibbs expectation.

### Algebraic auxiliaries versus analytic capstones

The auxiliaries of the namespace `LatticeGauge.ActivityProfileAdditiveCover`
(the scalar move, the costs and capacities, the intermediate profiles, the
step obligations and the endpoint identity) carry no regime, no separation
and no bound on `f`; the interval `[0, 1]` enters only through the transport
of the limits of the profiles (`move_mem_Icc`), and the analytic hypotheses
above belong to the capstones through the Stone 56 estimate consumed by the
composition. The `m = 0` and `δ ≡ 0` interfaces are algebraic (they omit the
four measure instances and accept arbitrary real profiles); the one-region
interface is analytic.

## 2. The route, as formalized

The chain promoted from the feasibility file (gate 58-A,
`T58A_additive_cover_tests.lean`) to the module (gate 58-L), with the Stone 56
two-term estimate as the only analytic input. No division by any quantity of
the data occurs anywhere in the construction.

- **The truncated scalar move.** `move x y t := if x ≤ y then min y (x + t)
  else max y (x − t)`: the value of `x` moved towards `y` by at most `t`. Both
  branches are proved for arbitrary reals: `move x y 0 = x` (`move_zero`);
  for `t ≥ 0` the value stays between `min x y` and `max x y` (`move_mem`,
  hence in `[0, 1]` when `x, y ∈ [0, 1]`: `move_mem_Icc`); `|x − y| ≤ t`
  gives `move x y t = y` (saturation, `move_eq_of_abs_le`); and the
  **increment bound** `|move x y (t + u) − move x y t| ≤ u` holds for `u ≥ 0`
  and **any real `t`** (`abs_move_add_sub_move_le`; no sign of `t` is needed,
  the feasibility having shown the hypothesis `t ≥ 0` of the proposal to be
  unnecessary). `move x x t = x` for `t ≥ 0` (`move_self`).
- **Region costs and prefix capacities.** `regionCost r δ i η := if
  typedTouchesSupport η (r i) then δ i else 0` and `prefixCost r δ k η :=
  ∑ i : Fin m, if i.val < k then regionCost r δ i η else 0`, with
  `prefixCost_zero` (`C_0 = 0`), `prefixCost_succ` (`C_(i+1) = C_i + c_i`, by
  splitting the indicator `i.val < k + 1` into `i.val < k` or `i = k` and
  `Finset.sum_ite_eq'`), `prefixCost_last` (`C_m` is the right-hand side of
  `hadd`), `prefixCost_nonneg` and `regionCost_nonneg`. A polymer touching
  several regions accumulates their budgets; outside `r i` the cost of step
  `i` is exactly zero even when the polymer touches other regions.
- **Intermediate profiles.** `additiveProfile R r δ a a′ k η := if
  typedTouchesSupport η R then move (a η) (a′ η) (prefixCost r δ k η) else
  a η`: the move on the polymers touching `R`, the raw value of `a` kept
  elsewhere (never read by the effective factor). `p_0 = a` as profiles
  (`additiveProfile_zero`); each `p_k` stays in `[0, 1]`
  (`additiveProfile_mem`); the effective factor of `p_k` is the move on the
  polymers touching `R` and `1` elsewhere (`touchFactor_additiveProfile`). A
  polymer may move at several steps; there is no single owner.
- **The Stone 56 hypotheses at every step.** At step `i`: outside `r i` the
  effective factors of `p_i` and `p_(i+1)` are **exactly** equal
  (`step_same`, the prefix not changing); on `r i` they differ by at most
  `δ i` (`step_bound`, the increment bound with `u = δ i`; off `R` both
  factors are `1`). Overlapping or repeated regions are admitted and charged
  at each of their steps.
- **The last profile.** Under `hadd`, `touchFactor R (p_m) η = touchFactor R
  a′ η` for every `η` (`touchFactor_additiveProfile_last`): the total capacity
  `C_m` is at least `|b(η) − b′(η)|` on the polymers touching `R`, so the move
  saturates at the target; off `R` both factors are `1`. An equality of
  **effective** factors, not of raw profiles — values never read outside `R`
  may still differ (`p_m η = a η` there). The functionals then agree exactly
  by the Stone 56 identity `profileExpectation_eq_of_touchFactor_eq`.
- **Composition.** `abs_profileExpectation_sub_le_of_chain`: for an arbitrary
  finite chain of profiles in `[0, 1]` starting at `a`, ending with the
  effective factors of `a′` and satisfying the Stone 56 hypotheses with
  `r i, δ i` at step `i`, the **published two-term estimate of Stone 56**
  (`abs_profileExpectation_sub_profileExpectation_le_two_terms_localized`) at
  every step, the Stone 56 identity at the last profile, the finite
  telescoping of Stone 57 (`ActivityProfileMultiRegion.abs_telescope`) and
  `Finset.sum_range`, `Finset.sum_le_sum`, `Finset.mul_sum` reorganize the
  sum into `Cf·(E6 + E4)·B`, the exponents rewritten `6·D_s/113`,
  `4·D_s/113`. The two-term capstone instantiates the chain with the
  additive profiles; `0 ≤ Cf` (derived), `B ≥ 0`
  (`ActivityProfileMultiRegion.budget_nonneg`) and `exp(4·D_s/113) ≤
  exp(6·D_s/113)` (`D_s ≥ 0`) give the compact capstone.
- **The Stone 57 cover implies the additive cover.** `additive_of_cover`: a
  zero difference lies below the non-negative sum; a non-zero difference is
  paid by its covering index, one term of the sum (`Finset.single_le_sum`).

The Stone 57 capstone is **not** used to prove the additive case: there is no
conversion of the general additive case into a single owner, and the public
Stone 57 theorems have no use in the code of this module (they are mentioned
in docstrings as the statements recovered). This is not an independent
re-derivation of the Stone 56 estimate: Stone 56 is the input of the general
construction.

## 3. The module and its declarations

One new module (660 Lean lines; 32 top-level declaration lines by the
textual count of the README — `grep -cE` of lines beginning with `theorem`,
`lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`,
`inductive` or `class` followed by a space — at the candidate `d942edd3…` and
at the merge `69706b9a…`: 28 `theorem` and 4 `noncomputable def`; 26 in-file
`#print axioms` certificates: the four definitions and 22 of the theorems —
the six auxiliaries `regionCost_nonneg`, `regionCost_of_not_touch`,
`regionCost_of_touch`, `prefixCost_zero`, `prefixCost_nonneg` and
`touchFactor_additiveProfile` carry no in-file command and were certified by
the auditor's test Q0), a leaf over Stone 57; no pre-existing module was
modified; the only change outside the new file is its glob in
`Phase3/lakefile.toml` (118 → 119 modules; blob
`9ad914d0e1a2ba4823aebeb341029211291a7f2e`, previously `11de6e17…`).

| Namespace | Declarations | Content |
|---|---|---|
| `LatticeGauge.ActivityProfileAdditiveCover` (auxiliaries) | `move`, `regionCost`, `prefixCost`, `additiveProfile` (noncomputable defs); `move_zero`, `move_self`, `move_mem`, `move_eq_of_abs_le`, `abs_move_add_sub_move_le`, `move_mem_Icc`, `regionCost_nonneg`, `regionCost_of_not_touch`, `regionCost_of_touch`, `prefixCost_zero`, `prefixCost_nonneg`, `prefixCost_succ`, `prefixCost_last`, `additiveProfile_zero`, `additiveProfile_mem`, `touchFactor_additiveProfile`, `step_same`, `step_bound`, `touchFactor_additiveProfile_last`, `abs_profileExpectation_sub_le_of_chain`, `additive_of_cover` | the truncated scalar move; costs and prefix capacities; the intermediate profiles; the Stone 56 hypotheses at every step; the endpoint by saturation; the composition along an arbitrary chain; the Stone 57 cover implies the additive cover |
| `LatticeGauge` (public) | `abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms`, `abs_profileExpectation_sub_profileExpectation_le_additive_cover`, `abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms_of_additive`, `abs_profileExpectation_sub_profileExpectation_le_multiregion_of_additive`, `abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_additive`, `profileExpectation_eq_of_additive_cover_empty_family`, `profileExpectation_eq_of_additive_cover_zero_budget` | the two estimates under `hadd`; the two Stone 57 estimates recovered; the Stone 56 bound recovered; the two exact interfaces |

Imports: `Mathlib` and `LatticeGauge.ActivityProfileDampingMultiRegion`
(Stone 57). Real dependencies, in code: from Stone 56 the two-term estimate
(one use, in the chain) and `profileExpectation_eq_of_touchFactor_eq` (three
uses: the last profile, `m = 0`, `δ ≡ 0`); from Stone 57 the auxiliaries
`abs_telescope` and `budget_nonneg` (one use each); from Stone 52-E
`nonneg_of_abs_le_of_config` (one use). The Stone 57 capstone and its two-term
form have no use in code; `coverOwner` and `stepProfile` are not used.
Hygiene: 0 `sorry`, `admit`, `native_decide`, scientific `axiom`,
`set_option`, `maxHeartbeats` (the word "admitted" occurs once, in a
docstring); linters active; 0 warnings in the module.

Origin of the proposal: the scientific architecture of GPT Astra / Can (tape
58-AL, feasibility and construction in one tape, the passage from gate A to
gate L authorized in advance); the route was proposed on paper and compiled
in Lean by the constructing instance only. The feasibility file
`T58A_additive_cover_tests.lean` (the chain and the tests T1–T7 in a
disposable file, plus the expected failure T8x; three elaboration attempts,
the third clean) was promoted to this module, whose definitive count is 28
theorems and 4 definitions.

## 4. Interfaces, control cases and limits

| Case | Declaration or test | Content |
|---|---|---|
| the Stone 57 cover | `additive_of_cover`, then `…_le_multiregion_two_terms_of_additive` and `…_le_multiregion_of_additive` | `hcover` (Stone 57) with `hδ0` gives `hadd`; the two Stone 57 estimates are recovered by specialization, their types being those of the published Stone 57 theorems (the auditor's Q6b/c compare the compact recovery with the published capstone by definitional equality in both directions; the two-term recovery is in the module and certified in Q0 — see the precision C58-Q6 in the audit index). A recovery, not an independent proof of the chain 56–57 |
| one region | `abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_additive` | the Stone 56 hypotheses (`hsame`, `hδ` for one region) give `hadd` with `m = 1` (outside `r` the difference is `0`, on `r` at most `δ`), and the capstone returns the Stone 56 bound, the sum over `Fin 1` on the **right-hand side** reducing to `δ·exp(−n/2)`; its type is the type of the Stone 57 one-region interface (Q6c′, T6). A compatibility test of the composition, not a proof of Stone 56 |
| no region | `profileExpectation_eq_of_additive_cover_empty_family` | `m = 0`: the empty sum is `0`, so `hadd` forces the equality of all effective factors, hence `F_R(a) = F_R(a′)` exactly, with no analytic hypothesis and for arbitrary real profiles (Q4e: profiles outside `[0, 1]` off `R`); the analytic capstone also accepts `m = 0`, with `B = 0` |
| zero budgets | `profileExpectation_eq_of_additive_cover_zero_budget`; T6, Q4f, Q6e | `δ ≡ 0`: the sum is `0` term by term, hence exact equality; the analytic capstone applied with `δ ≡ 0` returns `≤ 0` (an effective application, not a simplification of the right-hand side) |
| cost sharing (the strict extension) | T2 (constructor), Q2 (auditor) | one coordinate `1/4 → 3/4` with two regions touched and budgets `1/4, 1/4`: the effective factor passes through `1/4, 1/2, 3/4` (and `3/4, 1/2, 1/4` on the decreasing path); `hadd` holds at the witness while **no single index pays `1/2`** — the Stone 57 cover is false there. T2 proves the obligation at the witness coordinate; Q2 proves `hadd` for **every** polymer of its parametric profiles (`a ≡ 1/4`, `a′ = 3/4` at `η₀` and `1/4` elsewhere), the absence of a single payer at the witness and an application of the capstone to those profiles. The contacts of `η₀` with `R`, `r 0` and `r 1` are hypotheses; no concrete lattice is constructed |
| saturation and excess | T3, Q3c | capacities `1/8, 7, 0` on `1/4 → 3/4`: stages `1/4, 3/8, 3/4, 3/4`; the excess budget never passes the target (proved for all `x ≤ y` and `y < x`); the decreasing path symmetric |
| localization, overlap, repeated regions, background `1/2` | T4, Q3 | outside `r i` the step is exactly null even when the polymer touches other regions; `r 0 = r 1` is admitted and charged at both steps (`C_2 = δ₀ + δ₁`); a polymer touching `R` with value `1/2` and touching no region keeps `1/2` at every stage (`move_self`) — distinguished from "no factor changes", where every `p_k = a` as profiles |
| ignored raw values, endpoint by factors, `R = ∅` | T5, Q4c/d | raw values differing off `R` (e.g. `3/10` vs `9/10`) are not effective: both factors are `1`; at the endpoint `p_m η = a η` off `R` while its effective factor is that of `a′` (equality of effective factors without equality of raw profiles); `R = ∅` gives factors `1` and `F_∅(a) = F_∅(a′)` by the Stone 55 identity |
| closure by hand | T7 (constructor), Q5 (auditor, with its own telescoping) | the composition assembled along the additive profiles from the Stone 56 two-term estimate, the endpoint identity and finite telescoping, without the two capstones and without the chain lemma |
| expected failure | T8x (constructor), Q8x (auditor) | a change `1/2` with budgets `![1/4, 0]` (total capacity `1/4`): the obligation `hadd` at the witness reads `1/2 ≤ 1/4 + 0` and is **proved false** (`T8x_obligation_false`, `Q8x_obligation_false`); the application attempt fails with one error, `unsolved goals … ⊢ False`, exactly at that obligation — an application failure by an impossible hypothesis, not a counterexample to the conclusion on `F_R`, not an import or timeout failure |

The gain of Stone 58 is on the **hypothesis**: more pairs of profiles are
admissible (a change shared by several regions), with the same right-hand
side `B` as Stone 57. No universal numerical improvement, optimal sum or
optimal order of the steps is claimed; two equal regions still give two equal
terms, and a duplicated family costs twice. The geometric tests are
parameterized by `typedTouchesSupport` hypotheses; no concrete lattice
instance is constructed. The result is of finite volume, in the declared
regime, on periodic four-dimensional lattices; it does not construct a
thermodynamic or continuum limit or a mass gap, does not prove the Clay
problem, and claims no bibliographic priority, monotonicity or
differentiability of the functional, new Gibbs measure or boundary condition.

## 5. Kernel certificates and CI

- The module carries 26 in-file `#print axioms` commands (22 theorems and
  the 4 definitions); each reports `[propext, Classical.choice, Quot.sound]`.
  The library carries 317 in-file `#print axioms` commands at `d942edd3…`
  and at `69706b9a…` (291 + 26); these are certificate commands, not a count
  of theorems and not a global inventory of the axioms of every declaration.
  The six auxiliaries without an in-file command were certified by the
  auditor's Q0 (32/32 with the 26); those 32 are the auditor's checks, not
  commands of the module.
- The CI runs emit **320 axiom outputs = 317 of the build + 3 of the workflow
  step** on the Version 49–51 capstones, for **318 distinct names**: two of
  the three workflow outputs repeat names already certified by the build
  (`abs_gibbsCovariance_le_local_exp_decay`,
  `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`,
  multiplicity 2 each), and the third,
  `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name to the list
  emitted by the build (the Version 49 capstone has no in-file `#print
  axioms`); it is not a new theorem added by the workflow. In runs 511 and
  512, 87 of the 320 lists are printed across more than one line (86 of the
  317 in the auditor's clean build); the reading recomposes each list up to
  its closing bracket and accepts names with apostrophes
  (`activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`). The number of
  line breaks is a property of the printing, not of the certificates.
- Hygiene in the module: 114 inherited build warnings (unchanged since
  Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`
  (the Version 57 snapshot `18c6ff08…`), delivered as a verifiable git
  bundle; the QA1 audit before publication; push of the audited commit, a
  non-draft pull request, `build-phase3` green on the pull-request head, a
  normal merge with the expected head SHA locked (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit; then the
  adversarial review of the integrated state.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `d942edd3986ac8cb13a8d5958bf1e11461434794` | [#42](https://github.com/consensusframework/yang-mills-mass-gap/pull/42) | [511](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/38807381633) (id 38807381633, job 116671625661) | `69706b9a13a23b0f132418f2390d4030e1fcc78b` | [512](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/38808823637) (id 38808823637, job 116676549072) |

Custody note: the pull-request run 511 is associated with the head
`d942edd3…`, but its effective checkout was the provisional merge commit
`e8eb54d9b3ab397f6290ffa3f31d5000f963f9ab` ("Merge d942edd3… into
18c6ff08…"), as recorded in the job log read by the publishing instance
(`docs/audits/stone58/publication/RELATORIO_58-P.md`); run 512 compiled the
definitive merge `69706b9a…` itself. The run metadata alone do not prove the
effective checkout; the attribution is to the log reading. Both runs: `Build
completed successfully`; the dependency manifest `c376bbe9…1227` recorded and
verified after the resolution and after the build, the nine dependencies
checked out at the recorded revisions, no `lake update`; **119 `LatticeGauge`
modules built, 0 replayed** — no replay of the project; the nine `Built`
targets outside `LatticeGauge` are the Mathlib cache tool (four Lean modules
`Cache.IO`, `Cache.Hashing`, `Cache.Requests`, `Cache.Main`, their four C
objects and the executable `cache`), not nine rebuilt packages; the nine
package revisions are verified against the manifest in a separate step, and
the remaining dependency artifacts come from the cache, so the log does not
show a rebuild of Mathlib and the dependencies from source; 0 errors; 114
warnings, all in `LatticeGauge/`, none in the new module, none from
dependencies, the full warning blocks identical as a multiset to the QA1
baseline of this stone; 320 axiom outputs, all standard, the 26 of the new
module included; no `sorryAx`.

Toolchain at `69706b9a…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 119
modules, 39,181 Lean source lines and 1,834 top-level declaration lines by
the textual count (1,802 at Version 57 plus the 32 of this module) — 1,834
is not a number of theorems.

## 6. Relation to Stones 56 and 57

Stone 56 proved the localized stability with one change region, one
separation and one majorant, the damping region `R` kept in the functional.
Stone 57 composed it over a finite family of change regions under a cover in
which one region pays the whole change of each polymer. Stone 58 keeps the
composition and widens the cover: the regions a polymer touches share its
cost, the intermediate profiles moving each coordinate by the capacities
accumulated so far instead of switching it whole at the step of an owner.
The constant, the rate and the regime are unchanged and the cost is the same
finite sum `B`. The Stone 56 two-term estimate is consumed at every step; the
Stone 57 statements and the Stone 56 statement are recovered by the
interfaces as applications, which are compatibility checks of the
composition and not circularities, since Stone 56 is the input of the general
construction and the Stone 57 capstone is not used.

## 7. Audits and review

Recorded, with hashes and provenance, in
[`docs/audits/stone58/`](../audits/stone58/README.md). Three kinds of evidence
with distinct scopes; none is specialized human mathematical review. No
complementary execution on a third platform was received for this stone (the
Manus execution of Stone 57 is a record of that stone).

- **58-QA1** — reproduction by execution of the candidate `d942edd3…` by a
  separate instance of Claude Fable 5.1 (same model as the constructor; prior
  exposure to the earlier stones declared, not blind; the constructor's
  report read before the execution to identify the target, the constructor's
  logs and tests opened only in a second pass after the auditor's own
  conclusions, recorded in `PRELIMINARY_CONCLUSIONS_first_pass.md`; one
  execution although the tape was received twice). Dependencies reused from
  the auditor's Stone 57 bench (materialized then from the Mathlib community
  cache at the nine manifest revisions; 9/9 revisions checked before the
  build; no `lake update`; not recompiled — 0 built / 0 replayed of
  dependencies and no dependency diagnostics in that log, which says nothing
  about the warnings of a recompilation of the dependencies); project
  artifacts removed before the build; single integral `lake build`
  2026-10-15, 1,658 s, exit 0, **119 modules built (119 distinct names), 0
  replayed**, 0 errors, 317 certificates standard (86 multi-line), 0
  `sorryAx`, manifest identical before and after; 114 inherited warning
  blocks identical to the Stone 57 QA1 baseline, none in the new module; own
  certificates Q0 of **32/32** declarations (the 26 with an in-file command
  and the six auxiliaries without one); own tests Q1–Q6 pass, Q7 by reading
  and grep, Q8x fails on the impossible capacity `1/2 ≤ 1/4 + 0` with the
  goal `False` open; 61 warnings in the auditor's own disposable tests (Q1 2,
  Q2 3, Q3 2, Q6 54), separate from the 114 of the project. The
  constructor's tests T1–T8x were re-executed by the auditor in the second
  pass (the positive test has 15 `#check` and no `#print axioms`); the
  re-execution does not transfer their authorship. Verdict `PASS NO ESCOPO`
  (custody, execution, mathematics, documentation PASS). No errata was issued
  by the auditor; the precisions D1–D3 and the scope of T2/Q2 (recorded by
  the auditor on the constructor's report and tests, accepted by the
  coordination) and the coordination's precision C58-Q6 qualify descriptions
  of the constructor's and the auditor's materials, not the candidate, and
  are recorded in the audit index.
- **58-K-ADV with its errata C1** — adversarial review by **Kimi (Moonshot
  AI)**, as the documents identify the reviewer (the historical credits of
  the project say "Kimi 3" and, for Stone 57, "Kimi K3"; no build or version
  is inferred), a different model family, by reading and mathematical
  analysis of the module in full and of the interfaces consumed, with own
  custody checks (hashes of the transport package and of the two evidence
  packages, the Git objects of the merge, the candidate and the base, the
  diff, the counts) **without any Lean execution** (no build, no test); same
  conversation instance as the Stone 57 review, prior exposure declared, not
  blind; the second pass opened the constructor's and the auditor's
  materials. Verdict `PASS NO ESCOPO`: no mathematical defect, no hidden
  hypothesis, no owner reintroduced, no division by any quantity of the
  data; the precisions D1–D3, T2/Q2 and C58-Q6 confirmed as precisions of
  reporting. One errata (C1, 2026-10-16, by the same instance) corrects four
  points of the **report** and keeps the verdict: the transport package's
  manifest is 16/16 (not 6/6; the six originals were a subset, individually
  checked); the module has divisions only by the fixed non-zero constants 2,
  113 and 40000, none by budgets, accumulated capacities or differences of
  profiles (the original sentence "no division in the module" was too broad);
  in the branch `η ≠ η₀` of the auditor's Q2 the raw profiles are both `1/4`
  and the effective factors are both `1/4` on `R` and both `1` off `R`; the
  scalar numerical sampling in Python declared in the review has no preserved
  script, parameters or output, is not auditable from records and is not
  evidence — the verdict does not rest on it. Its declared limits: the CI
  logs of runs 511/512 were not downloaded (their numbers are attributed to
  the publication report and the coordination); the SSH signature of the
  candidate was not verified; Zenodo and the Release were not consulted.
- **58-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).
- **GPT Astra / Can** — scientific architecture and review: the tape 58-AL
  (feasibility and construction), the integration tape 58-P and this
  consolidation; reading of the module, the reports, the packages and the
  logs; no Lean build of its own.

## 8. Version records

| Step | Record |
|---|---|
| Version 57 (the current version) | commit `18c6ff084020e52c8932ecfd20e4b19f47efdf02` (merge of PR #41, the final documentary preparation of Stone 57; Stone 57 itself integrated at `b66c255c…`, PR #39, consolidated at `c09fa063…`, PR #40), tag `zenodo-v57` (simple tag), GitHub Release [`zenodo-v57`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v57) published on 2026-10-11 (`draft = false`, 2026-10-11T22:20:54Z, read through the GitHub API by the consolidating session) with four assets (`yang-mills-mass-gap-zenodo-v57.zip`, 1,758,764 bytes, SHA-256 `edf602a7…61a9`; `RELEASE_NOTES_PEDRA57.md`, 35,160 bytes, SHA-256 `92a26044…c365` — the notes updated by the coordinator with the DOI after the original packaging, with the checksum file updated accordingly, `SHA256SUMS.txt`, 275 bytes, SHA-256 `6cac346e…7626`; `MANIFEST_v57.txt`, 39,136 bytes, SHA-256 `aaa2eafd…46cc`; the ZIP and the manifest are the originals of the packaging; sizes and digests as reported by the API, not a new comparison of downloaded bytes); Zenodo record DOI [10.5281/zenodo.23305142](https://doi.org/10.5281/zenodo.23305142) (concept DOI 10.5281/zenodo.17397622), **published**, as confirmed by the coordinator — the exact Zenodo publication date was not established by the materials of this consolidation and is not inferred from the Release date; the consolidating session could not reach Zenodo. The deposit contains Stones 52–57 and the committed dependency manifest, and not Stone 58 |
| Stone 58 | integrated on `main` at `69706b9a…` (2026-10-15, PR #42), audited (QA1 2026-10-15), reviewed (Kimi, 2026-10-16, with its errata C1 of the same day) and CI-verified (runs 511 and 512); **no tag, no Release, no deposit and no reserved DOI of its own recorded here**. It is cited by its commit. The future Version 58, if deposited, will be packaged from the definitive documentary merge in a step of its own |
