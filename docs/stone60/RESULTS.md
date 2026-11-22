# Stone 60 — the optimal cost of Stone 59 as a pseudometric on each reach component, and the profile functional as a Lipschitz map

Integrated state of `main` at commit
[`58eb3d1bf3cc2b3393c7608581905530053d0e96`](https://github.com/consensusframework/yang-mills-mass-gap/commit/58eb3d1bf3cc2b3393c7608581905530053d0e96)
(merge of [PR #46](https://github.com/consensusframework/yang-mills-mass-gap/pull/46);
parents `2ef6500deeb5dd7ddd70c5f208f690e9e0470353` and
`778e2c7b27f0357110ba83e9b466984747577823`; root tree
`a7295ffe3dd1bec2496a1353f7a2fd8665490199`, `Phase3/` tree
`ffabe44339920053581a294929ab8a094d329b77`, `Phase3/LatticeGauge/` tree
`62c5fc4f73b3bf42dddb14304764a53afa28aedb`). Four states are to be kept
apart: the **candidate** `778e2c7b…` (the audited commit, single parent
`2ef6500d…`, whose root tree is the merge's), the **scientific integration**
`58eb3d1b…` (the merge above), the **documentary consolidation** (this
document and the audit records, merged after it) and the **deposit**. At
consolidation time (2026-11-22) Stone 60 was integrated on `main`, audited,
reviewed and CI-verified, but not part of any release and without a deposit
of its own: the most recent version is **Version 59** (commit
`2ef6500deeb5dd7ddd70c5f208f690e9e0470353`, tag `zenodo-v59`, GitHub Release
published on 2026-10-31, Zenodo record DOI
[10.5281/zenodo.23697327](https://doi.org/10.5281/zenodo.23697327), whose
publication is confirmed by the coordinator and stated in the Release body;
see §8 for the source of each status). Stone 60 is later than the Version 59
snapshot and is not in that deposit; it is cited by its commit. No DOI is
reserved or recorded for a future Version 60 in this document.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice; the analytic part is in the small-β
> (strong-coupling, Wilson convention) regime `0 ≤ β ≤ 1/40000`. "Distance"
> between regions is walk separation in the plaquette graph; "distance"
> between profiles, in this stone, is the Stone 59 optimal cost. The program
> is a formal, machine-checked study of finite-volume lattice gauge theory
> directed at the Yang–Mills existence and mass-gap problem: the
> finite-volume stability results are established; the thermodynamic and
> continuum limits and the mass gap remain open and are not claimed here.
> The object is the normalized polymer functional of Stones 55–59 with the
> damping region kept everywhere: no new Gibbs measure, boundary condition,
> modified action, per-link profile or physical switch-off is constructed or
> claimed. Stone 60 reads the Stone 59 optimal cost, for a **fixed** finite
> family of regions and **fixed** scales, as a **pseudometric** on each
> component of profiles that reach one another, and the functional as a
> **Lipschitz** map on that component with the two Stone 59 constants. It is
> a pseudometric, not a metric: distinct raw profiles can be at distance
> zero. No metric quotient, completeness, equivalence with a product
> topology or a uniform norm, extension to pairs without reach, infinite
> volume, linear-programming duality, algorithm, differentiability or
> monotonicity of the functional, new Gibbs measure, thermodynamic or
> continuum limit, mass gap or bibliographic priority is claimed. The
> constants are those of Stone 59; nothing is improved numerically. Nothing
> of the chain 56–57–58–59 is reopened.

## 1. The statement

Principal declarations (module
[`Phase3/LatticeGauge/ActivityProfileDampingOptimalGeometry.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingOptimalGeometry.lean),
blob `fbf6452ab07668d8b7965a3a35f9a11e3a194e9c`, SHA-256
`035a9cd5f18bd137bc989b18db0373fd9015272edcb589075a313b34d97948d9`,
36,088 bytes, 646 lines; all in the namespace
`LatticeGauge.ActivityProfileOptimalGeometry`):

```
instPseudoMetricSpace : PseudoMetricSpace (ProfileComponent R r n aref)
optimalDist_eq_zero_iff
minCost_triangle
lipschitzWith_functional_two_terms
lipschitzWith_functional
functional_eq_of_dist_eq_zero
recover_optimal_cover
recover_optimal_cover_two_terms
```

Objects of Stones 55–59, unchanged: the damping region `R` stays in the
definition of the functional, the weights, the activities and the exponents,

```
F_R(a) = profileExpectation μm β χ f s R a,
b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
D_s    = card (supportLinkFinset s),
```

the effective factor `b(η)` being the profile value `a η` when the polymer
`η` touches `R` and `1` otherwise; a **fixed** finite family of regions with
its own separation scale per region, `r : Fin m → Set (Link N)`,
`n : Fin m → ℕ` (`m = 0` included); the Stone 59 budgets, their cost
`B(δ) = ∑ i, δ i · exp(−(n i)/2)`, the admissibility `Admissible R r a a′ δ`
(non-negative coordinates and an additive cover of the effective changes),
the reach `Reaches R r a a′` (every polymer whose effective factor changes
touches some `r i`) and the optimal cost `B*(a, a′) = minCost …`, defined
for profiles in `[0, 1]` that reach each other.

**Why the optimal cost is a pseudometric.** With `R`, `r`, `n` fixed:

1. `Reaches R r a a′` is equivalent to "`b(η) = b′(η)` for every polymer `η`
   that touches no region of the family" (`reaches_iff_untouched_eq`), for
   arbitrary real profiles; it is reflexive, symmetric and transitive
   (`reaches_equivalence`). No cover of all polymers is assumed; polymers
   untouched by the family are simply required to keep their effective
   factor.
2. Admissible budgets transport along symmetry (`admissible_symm`) and add
   along a path: if `δab` covers `(a, b)` and `δbc` covers `(b, c)`, then
   `δab + δbc` covers `(a, c)` — polymer by polymer,
   `|b_a − b_c| ≤ |b_a − b_b| + |b_b − b_c|` — and the cost is additive,
   `B(δab + δbc) = B(δab) + B(δbc)` (`admissible_add`, `budget_add`). Index
   by index: repeated regions keep their multiplicity.
3. Hence the **value** `B*` is symmetric (`minCost_comm`), zero on the
   diagonal (`minCost_self`) and satisfies the **triangle inequality**
   `B*(a, c) ≤ B*(a, b) + B*(b, c)` (`minCost_triangle`): the sum of the two
   optimal budgets of `(a, b)` and `(b, c)` is **admissible** for `(a, c)`,
   even though some coordinate of the sum may exceed `1` — `Admissible`
   carries no upper bound, and `minCost_le_budget` compares `B*` with
   **every** admissible budget — and its cost is the sum of the two optimal
   costs. The summed budget is a witness for the upper bound; **it is not
   claimed to be optimal** (on the return path `a → b → a` it has a
   coordinate `2` while `B*(a, a) = 0`), and no uniqueness of any
   minimizing vector is used: only values are compared.
4. For a reference profile `aref` (an arbitrary real profile, with no bound
   and no requirement of membership), `ProfileComponent R r n aref` is the
   type of profiles with values in `[0, 1]` reached from `aref`. Any two
   members reach each other (`ProfileComponent.reaches`), so
   `optimalDist x y := B*(x.prof, y.prof)` is defined on **every** pair of
   the component, with no conventional value for pairs without reach. The
   scales `n` are carried in the type so that the geometry is inferable;
   membership itself does not depend on `n`. The component may be empty.
5. `optimalDist` is non-negative, zero on the diagonal, symmetric and
   subadditive (`optimalDist_nonneg`, `_self`, `_comm`, `_triangle`), and
   **`optimalDist x y = 0` iff `touchFactor R x.prof η = touchFactor R y.prof
   η` for every polymer `η`** (`optimalDist_eq_zero_iff`): zero distance is
   equality of the **effective** factors, not of the raw profiles — two
   members with raw values differing off `R` are at distance `0`. That is why
   the structure is a pseudometric and not a metric. Members of two
   components (two references, same `R`, `r`, `n`) with equal profiles have
   equal distances (`optimalDist_ref_indep`): the reference organizes the
   domain and does not enter the optimization of a pair.
6. `instPseudoMetricSpace : PseudoMetricSpace (ProfileComponent R r n aref)`
   is an instance of the Mathlib structure with `dist = optimalDist`,
   definitionally `minCost` (`dist_eq_optimalDist`, `dist_eq_minCost`, both
   `rfl`); uniformity and bornology are the Mathlib defaults of that
   distance.
7. Variation and chains: `|d(x, z) − d(y, z)| ≤ d(x, y)`
   (`abs_optimalDist_sub_le`), `|d(x, y) − d(x′, y′)| ≤ d(x, x′) + d(y, y′)`
   (`abs_optimalDist_sub_optimalDist_le`), and the polygonal inequality
   `d(x₀, x_k) ≤ ∑_{j<k} d(x_j, x_{j+1})` for every chain
   `x : Fin (k+1) → ProfileComponent …`, `k = 0` included
   (`optimalDist_chain_le`).

**The functional as a Lipschitz map.** Under **exactly** the analytic
hypotheses of the Stone 59 capstones — `0 ≤ β ≤ 1/40000`, `χ : G → ℝ`
measurable with `|χ| ≤ 1`, `f` measurable with `|f| ≤ Cf`,
`WalkBarrierSeparated s (r i) (n i)` for each `i` — the map
`functional μm β χ f s : ProfileComponent R r n aref → ℝ`,
`x ↦ F_R(x.prof)`, satisfies

```
|F_R(x) − F_R(y)| ≤ K₂ · dist x y,   K₂ = Cf · [exp(6·D_s/113) + exp(4·D_s/113)]   (two-term form)
|F_R(x) − F_R(y)| ≤ K  · dist x y,   K  = (2 · Cf) · exp(6·D_s/113)               (compact form)
```

(`abs_functional_sub_functional_le_two_terms`,
`abs_functional_sub_functional_le`), is `LipschitzWith K₂` and
`LipschitzWith K` for the two constants given as non-negative reals whose
coercions are **exactly** the expressions above (`twoTermConst`,
`compactConst`, `coe_twoTermConst`, `coe_compactConst` by `rfl`; `0 ≤ Cf` is
**derived** from the absolute majorant), hence `UniformContinuous` and
`Continuous` for the pseudometric constructed here and for no other
topology (`lipschitzWith_functional_two_terms`, `lipschitzWith_functional`,
`uniformContinuous_functional`, `continuous_functional`). Along a finite
chain, `|F_R(x₀) − F_R(x_k)| ≤ K₂ · ∑_j d(x_j, x_{j+1})` and likewise with
`K` (`abs_functional_chain_le_two_terms`, `abs_functional_chain_le`). These
are the two Stone 59 constants, with no numerical improvement claimed. Two
routes to equality are to be kept apart: **zero distance gives exact
equality of the functional by the algebraic route** — `d = 0` means equal
effective factors, and the Stone 56 identity
`profileExpectation_eq_of_touchFactor_eq` then gives `F_R(x) = F_R(y)` with
**no** regime, separation, measurability or majorant hypothesis
(`functional_eq_of_dist_eq_zero`) — whereas the Lipschitz **bounds** above
use the small-β regime and the Stone 59 hypotheses.

**Compatibility.** Two profiles in `[0, 1]` with reach are placed in the
component of the first (`ofReach`, `ofReach'`); their distance is the raw
`minCost` definitionally (`dist_ofReach`), and the two Stone 59 estimates
are recovered through the new interface with the types of the published
capstones (`recover_optimal_cover`, `recover_optimal_cover_two_terms`) —
compatibility checks that depend on Stone 59, not independent derivations.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]` throughout;
for the analytic part (G6–G7) also `{G : Type*} [Group G] [MeasurableSpace G]
[MeasurableMul₂ G] [MeasurableInv G]`, `(μm : Measure G) [SigmaFinite μm]
[IsProbabilityMeasure μm]`, declared after the geometric part so that the
latter cannot capture them.

| Hypothesis | Where | Meaning |
|---|---|---|
| `R : Set (Link N)`, `r : Fin m → Set (Link N)`, `n : Fin m → ℕ` | everywhere | the damping region and the fixed family with its scales; `m = 0` admitted; overlaps and repetitions allowed |
| `aref : Polymer N → ℝ` | the component | the reference; arbitrary real, not required to be in `[0, 1]`, not required to be a member |
| `prof`, `0 ≤ prof ≤ 1`, `Reaches R r aref prof` | the fields of `ProfileComponent` | a member: a profile in `[0, 1]` reached from the reference |
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | G6–G7 only | small-β regime of the Stone 59 capstones |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | G6–G7 only | `χ : G → ℝ` bounded measurable; no character hypothesis |
| `mf : Measurable f`, `hCf : ∀ U, \|f U\| ≤ Cf` | G6–G7 only | measurability and absolute majorant of the observable; `0 ≤ Cf` **derived** (`nonneg_of_abs_le_of_config`, 52-E) |
| `hsep : ∀ i, WalkBarrierSeparated s (r i) (n i)` | G6–G7 only | walk-barrier separation of `s` from each region at its own scale |

The geometric part (G0–G5) involves no measure, no `β`, no `χ`, no `f` and
no separation; the two definitions of constants and their coercions omit the
three measurable-structure instances (`omit [MeasurableSpace G]
[MeasurableMul₂ G] [MeasurableInv G] in`), and `functional_eq_of_dist_eq_zero`
omits `[MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm]
[IsProbabilityMeasure μm]`, keeping only what the type of
`profileExpectation` needs. These `omit`s are those of the source. Not
required anywhere: `m > 0`, a cover of all polymers, disjoint regions,
`r i ⊆ R`, a separation of `s` from `R`, a unit background, `DependsOnlyOn f
s`, `δ i ≤ 1` on the budgets compared, a unique minimizer, `Cf > 0`, a
non-empty component, a bound on the reference, a factor of `m` or of the
volume outside the sum.

## 2. The route, as formalized

The chain promoted from the feasibility file (gate 60-A,
`T60A_optimal_geometry_tests.lean`, two elaboration attempts, the first with
three errors in the tests and none in the chain, the second clean; plus the
expected failure `T60A_T9x_reach_EXPECT_FAIL.lean`) to the module (gate
60-L), with the two published Stone 59 capstones as the only analytic input
and the Stone 56 identity for the algebraic equality. No hypothesis was
added at any step; in particular no bound on the reference was needed.

- **G0 — reach as an equivalence.** `reaches_iff_untouched_eq` is the
  contrapositive reading of the Stone 59 definition; `reaches_refl`, `_symm`,
  `_trans` and `reaches_equivalence` follow from it, for arbitrary real
  profiles, with no cover of all polymers.
- **G1 — transport and addition of covers.** `additiveCover_symm`
  (`abs_sub_comm`), `admissible_symm`, `admissible_zero_self` (through the
  Stone 59 `admissible_zero_of_touchFactor_eq`), `coverSum_add` (sums
  distribute over the `if … then δ i else 0` terms, index by index),
  `admissible_add` (`abs_sub_le` polymer by polymer, `add_nonneg`
  coordinate by coordinate) and `budget_add` (`Finset.sum_add_distrib`). No
  `β`, no integration, no separation, no `Cf`, no profile bound.
- **G2 — the value of the optimal cost.** `minCost_proof_irrel` (`rfl`,
  proof irrelevance of the hypotheses — not a statement on the minimizing
  vector); `minCost_comm` by `le_antisymm` with `minCost_le_budget` applied
  to the transported minimizer in each direction; `minCost_self` through
  `minCost_eq_zero_iff`; `minCost_triangle` — the two optimal budgets are
  admissible (`optimalBudget_admissible`), their sum is admissible for the
  endpoints (`admissible_add`), `minCost_le_budget` bounds `B*(a, c)` by its
  cost, and `budget_add` rewrites that cost as `B*(a, b) + B*(b, c)`. Values
  are compared, never the chosen vectors.
- **G3 — the component.** `ProfileComponent` (four fields),
  `ProfileComponent.reaches` (symmetry and transitivity through the
  reference), `optimalDist` and its five properties projected from G2,
  `optimalDist_eq_zero_iff` from the Stone 59 `minCost_eq_zero_iff`,
  `optimalDist_ref_indep` by `cases`, `subst`, `rfl`.
- **G4 — the instance.** `instPseudoMetricSpace` with the four fields
  `dist`, `dist_self`, `dist_comm`, `dist_triangle`; `dist_eq_optimalDist`
  and `dist_eq_minCost` by `rfl`.
- **G5 — variation and chains.** `abs_dist_sub_le` and `dist_dist_dist_le`
  of Mathlib (the latter with `Real.dist_eq`); the polygonal inequality by
  induction on `k` with `Fin.sum_univ_castSucc`, `Fin.succ_castSucc`, the
  triangle inequality at the last step.
- **G6 — Lipschitz.** `functional`; `twoTermConst` and `compactConst` as
  `ℝ≥0` with the non-negativity from `nonneg_of_abs_le_of_config` and the
  positivity of the exponentials; the two capstones of Stone 59 applied to
  the members (whose bounds and reach are the fields), the right-hand side
  being `K · dist` definitionally; `LipschitzWith.of_dist_le_mul`;
  `LipschitzWith.uniformContinuous`, `.continuous`; the chains by
  `mul_le_mul_of_nonneg_left` over the polygonal inequality;
  `functional_eq_of_dist_eq_zero` through `optimalDist_eq_zero_iff` and the
  Stone 56 identity.
- **G7 — compatibility.** `ofReach`, `ofReach'`, `dist_ofReach` (`rfl`),
  `recover_optimal_cover` and `recover_optimal_cover_two_terms` by applying
  G6 to the placed profiles.

The dependency **59 → 60 → recovery of 59** is intentional: the two Stone 59
estimates are the input of the two Lipschitz bounds, and the recoveries are
compatibility checks of the interface, not an independent proof of Stone 59.

## 3. The module and its declarations

One new module (646 Lean lines; **50 declarations**: 42 `theorem`, 2 `def`,
4 `noncomputable def`, 1 `structure` and 1 `noncomputable instance`; 50
in-file `#print axioms` commands, one per declaration), a leaf over Stone
59; no pre-existing module was modified; the only change outside the new
file is its glob in `Phase3/lakefile.toml` (120 → 121 modules; blob
`f9f902f76e767b143384f4339fc92cb48f430d17`, previously `cd461108…`). The
diff from the base is exactly these two paths, +647/−1. The textual count of
the README (`grep -cE` of lines beginning with `theorem`, `lemma`, `def`,
`abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or
`class` followed by a space) gives **49** declaration lines for this module
and 1,927 for the library at the candidate and at the merge: the regex does
not match the line `noncomputable instance instPseudoMetricSpace …` (it
matches `instance` only at the start of a line). Both numbers — 50 by the
classification of the matrices, 49 by the published textual method — are
recorded by the constructor, the QA1 and this consolidation; the method is
not changed.

| Line | Kind | Declaration | Content |
|---|---|---|---|
| 130 | theorem | `reaches_iff_untouched_eq` | reach ⟺ equal effective factors on every polymer touching no region; arbitrary real profiles |
| 145, 149, 153 | theorem | `reaches_refl`, `reaches_symm`, `reaches_trans` | |
| 160 | theorem | `reaches_equivalence` | `Equivalence (Reaches R r)` |
| 167 | theorem | `additiveCover_symm` | the cover condition is symmetric in the two profiles |
| 174 | theorem | `admissible_symm` | |
| 180 | theorem | `admissible_zero_self` | the zero budget covers `(a, a)` |
| 186 | theorem | `coverSum_add` | the cover sum of a sum of budgets is the sum of the cover sums (index by index) |
| 198 | theorem | `admissible_add` | admissible budgets add along a path; no profile bound used |
| 210 | theorem | `budget_add` | `B(δ₁ + δ₂) = B(δ₁) + B(δ₂)` |
| 222 | theorem | `minCost_proof_irrel` | `B*` does not depend on the proof terms of its hypotheses (`rfl`) |
| 232 | theorem | `minCost_comm` | symmetry of the value |
| 244 | theorem | `minCost_self` | `B*(a, a) = 0` |
| 252 | theorem | `minCost_triangle` | `B*(a, c) ≤ B*(a, b) + B*(b, c)` through the summed (not claimed optimal) budget |
| 274 | `structure` | `ProfileComponent` | `prof`, `nonneg`, `le_one`, `reach : Reaches R r aref prof`; `n` in the type |
| 285 | theorem | `ProfileComponent.reaches` | any two members reach each other |
| 291 | `noncomputable def` | `optimalDist` | `minCost` of the two members |
| 294 | theorem | `optimalDist_eq_minCost` | `rfl` |
| 299, 302, 305, 309 | theorem | `optimalDist_nonneg`, `_self`, `_comm`, `_triangle` | the pseudometric axioms |
| 315 | theorem | `optimalDist_eq_zero_iff` | `d = 0 ↔ ∀ η, touchFactor R x.prof η = touchFactor R y.prof η` |
| 321 | theorem | `optimalDist_ref_indep` | equal profiles in two components have equal distances |
| 336 | `noncomputable instance` | `instPseudoMetricSpace` | `PseudoMetricSpace (ProfileComponent R r n aref)` with `dist = optimalDist` |
| 343, 345 | theorem | `dist_eq_optimalDist`, `dist_eq_minCost` | `rfl` |
| 351 | theorem | `abs_optimalDist_sub_le` | three-point variation |
| 357 | theorem | `abs_optimalDist_sub_optimalDist_le` | four-point variation |
| 363 | theorem | `optimalDist_chain_le` | polygonal inequality, `k = 0` included |
| 391 | `noncomputable def` | `functional` | `x ↦ profileExpectation μm β χ f s R x.prof` |
| 398 | `noncomputable def` | `twoTermConst` | `K₂ : ℝ≥0`, `0 ≤ Cf` derived |
| 406 | `noncomputable def` | `compactConst` | `K : ℝ≥0` |
| 412, 419 | theorem | `coe_twoTermConst`, `coe_compactConst` | the coercions are exactly the Stone 59 constants (`rfl`) |
| 426 | theorem | `abs_functional_sub_functional_le_two_terms` | `\|F(x) − F(y)\| ≤ K₂ · dist x y` |
| 440 | theorem | `abs_functional_sub_functional_le` | `\|F(x) − F(y)\| ≤ K · dist x y` |
| 452, 464 | theorem | `lipschitzWith_functional_two_terms`, `lipschitzWith_functional` | `LipschitzWith K₂`, `LipschitzWith K` |
| 476, 484 | theorem | `uniformContinuous_functional`, `continuous_functional` | for this pseudometric only |
| 493, 512 | theorem | `abs_functional_chain_le_two_terms`, `abs_functional_chain_le` | control along a finite chain |
| 530 | theorem | `functional_eq_of_dist_eq_zero` | `d = 0 ⇒ F(x) = F(y)`, algebraic, no regime |
| 538, 543 | `def` | `ofReach`, `ofReach'` | two profiles with reach placed in the component of the first |
| 549 | theorem | `dist_ofReach` | their distance is the raw `minCost` (`rfl`) |
| 557 | theorem | `recover_optimal_cover` | the Stone 59 compact estimate recovered (transport) |
| 574 | theorem | `recover_optimal_cover_two_terms` | the Stone 59 two-term estimate recovered (transport) |

Imports: `Mathlib` and `LatticeGauge.ActivityProfileDampingOptimalCover`
(Stone 59). Real dependencies, in code: from Stone 59 `Admissible`,
`AdditiveCover`, `budget`, `Reaches`, `minCost`, `optimalBudget`,
`optimalBudget_admissible`, `minCost_le_budget`, `minCost_nonneg`,
`minCost_eq_zero_iff`, `admissible_zero_of_touchFactor_eq` and the two
capstones (one use each, in the two Lipschitz bounds); from Stone 56
`profileExpectation_eq_of_touchFactor_eq` (one use, the algebraic
equality); from Stone 52-E `nonneg_of_abs_le_of_config` (two uses, the
constants); from Stone 55 `touchFactor`; from Mathlib `PseudoMetricSpace`,
`LipschitzWith.of_dist_le_mul`, `LipschitzWith.uniformContinuous`,
`LipschitzWith.continuous`, `abs_dist_sub_le`, `dist_dist_dist_le`,
`Real.dist_eq`, `Fin.sum_univ_castSucc`, `Fin.succ_castSucc`,
`Finset.sum_add_distrib`, `abs_sub_le`, `abs_sub_comm`. `Classical.choice`
enters only through the Stone 59 `optimalBudget`. Hygiene: 0 `sorry`,
`admit`, `native_decide`, scientific `axiom`, `unsafe`, `implemented_by`,
`set_option`, `maxHeartbeats`; linters active; 0 warnings in the module.

Origin of the proposal: the scientific architecture of GPT Astra / Can
(tape 60-A, feasibility; tape 60-L, construction); the route was proposed
on paper and compiled in Lean by the constructing instance only. The
feasibility file `T60A_optimal_geometry_tests.lean` (the chain G0–G7 and the
tests T1–T10 in a disposable file, plus the expected failure T9x against a
local copy of the wrapper; two elaboration attempts, the second clean) was
promoted to this module with the 50 declarations under the same names and
gates; the tests were kept outside the tree (`T60L_api_tests.lean`, 15 test
certificates, and `T60L_T9x_EXPECT_FAIL.lean`, this time against the real
`ProfileComponent`).

## 4. Interfaces, control cases and limits

| Case | Declaration or test | Content |
|---|---|---|
| reach as an equivalence | `reaches_iff_untouched_eq`, `reaches_equivalence`; T1 (constructor), Q1 (auditor) | the characterization and the three properties, re-proved by the auditor without the module's lemmas; no cover of all polymers |
| reference outside `[0, 1]`; empty component | `ProfileComponent`; T1-extra (constructor), Q1 (auditor), Kimi §5 with its errata C1 | with `R = ∅` a reference constant `2` admits the members `0` and `1` (distance `0`), the reference itself not being a member; with `m = 0`, a polymer touching `R` and a reference worth `2` there, the component is **empty** (Q1d; Kimi C1 gives an explicit witness polymer built from the definitions) — no member is presupposed anywhere, and the theorems hold vacuously on an empty component |
| summed budgets, coordinate `2` | `admissible_add`, `budget_add`; T2 (constructor), Q2c (auditor) | on `a → b → a` with a change `1` at a witness, the two unit budgets add to `2` on the single region, admissible for `(a, a)`, with cost `2w`; the optimal cost of the endpoints is `0`: the sum is admissible, not optimal |
| symmetry and triangle without the module | Q2a/b (auditor) | both re-derived from `optimalBudget_admissible` and `minCost_le_budget` alone |
| exact distance and the triangle on `dist` | T3 (constructor), Q4 (auditor) | one region, one witness `η₀` touching `R` and `r 0` by hypothesis: `d(p c, p c′) = \|c − c′\|·e^{−n₀/2}` by a global cover plus the lower bound at the witness; the three values `w/4`, `w/2`, `3w/4` with the triangle **with equality** and the **strict** return inequality — stated on `dist` itself in the auditor's Q4 (the constructor's `t3_triangle_eq_and_return_strict` is an arithmetic statement on the values) |
| zero distance, distinct raw profiles | `optimalDist_eq_zero_iff`, `functional_eq_of_dist_eq_zero`; T4, T10 (constructor), Q3c (auditor) | with `R = ∅`, the constant profiles `0` and `1` are members at distance `0` with distinct profiles; the raw identification `d = 0 → prof = prof` is **false** (proved positively); the functional is equal by the algebraic route |
| `m = 0` and `R = ∅` | `touchFactor_eq_of_reaches_fin_zero`, `reaches_empty_region` (Stone 59); T6 (constructor), Q4 deg (auditor) | both give `d = 0` on the whole component, for two different reasons (no index can witness a change; all effective factors are `1`), kept in separate theorems |
| change of reference | `optimalDist_ref_indep`; T5 (constructor, background `1/2`), Q3 (auditor) | members with equal profiles in the components of two references have equal distances |
| the inferred instance; three, four points; chains | `instPseudoMetricSpace`, G5; T7, T8 (constructor), Q5 (auditor) | the instance found by inference is the candidate's (`rfl`); the Mathlib bounds apply; chains with `k = 0, 1, 2` and the auditor's own induction |
| the two constants, `Cf = 0`, the recoveries | `coe_twoTermConst`, `coe_compactConst`, `recover_*`; T7 (constructor), Q6 (auditor) | the coercions are exactly the Stone 59 constants; with `Cf = 0` both are `0` and the functional is constant; the recoveries have the types of the Stone 59 capstones in both directions (`rfl` between proof terms is proof irrelevance: equality of types, not of derivations); the auditor re-obtains both Lipschitz bounds from the Stone 59 capstones with its own constants |
| expected failure | T9x (constructor), Q7x (auditor), both against the real `ProfileComponent` | an effective change on a polymer touching `R` and no region: `¬ Reaches`, no admissible budget and no member with the changed profile are **proved** (T9, Q7), and the attempt to build the member fails with exit 1 and exactly one error at the field `reach`, the open goal `⊢ ∃ i, typedTouchesSupport η (r i)` (constructor at `56:13`; auditor at `21:4`) — an application failure by an impossible hypothesis, not a counterexample to any statement on `F_R`, not an import or timeout failure |

The geometric tests are parameterized by `typedTouchesSupport` hypotheses
(which polymer touches which region); no concrete lattice instance is
constructed, and the coordination executed none of these tests in Lean. The
result is of finite volume, on periodic four-dimensional lattices; the
analytic part is in the declared regime; it does not construct a
thermodynamic or continuum limit or a mass gap, does not prove the Clay
problem, and claims no metric on raw profiles, quotient, completeness,
product or uniform topology, extension to pairs without reach,
linear-programming duality, algorithm, differentiability, monotonicity of
the functional, new Gibbs measure, boundary condition, new constant or
bibliographic priority.

## 5. Kernel certificates and CI

- The module carries 50 in-file `#print axioms` commands (one per
  declaration); each reports `[propext, Classical.choice, Quot.sound]`. The
  library carries 411 in-file `#print axioms` commands at `778e2c7b…` and at
  `58eb3d1b…` (361 + 50); these are certificate commands, not a count of
  theorems and not a global inventory of the axioms of every declaration.
- The CI runs emit **414 axiom outputs = 411 of the build + 3 of the workflow
  step** on the Version 49–51 capstones, for **412 distinct names**: two of
  the three workflow outputs repeat names already certified by the build
  (`abs_gibbsCovariance_le_local_exp_decay`,
  `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay`,
  multiplicity 2 each), and the third,
  `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name to the list
  emitted by the build (the Version 49 capstone has no in-file `#print
  axioms`); it is not a new theorem added by the workflow. In runs 519 and
  520, 138 of the 414 lists are printed across more than one line (137 of
  the 411 in the auditor's and in the constructor's clean builds); the
  reading recomposes each list up to its closing bracket and accepts names
  with apostrophes (`ofReach'` among them). The number of line breaks is a
  property of the printing, observed and not imposed on future runs.
- Hygiene in the module: 114 inherited build warnings (unchanged since
  Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`
  (the Version 59 snapshot `2ef6500d…`), delivered as a verifiable git
  bundle; the QA1 audit with its addendum and the adversarial reading with
  its two errata before publication; push of the audited commit, a
  non-draft pull request, `build-phase3` green on the pull-request head, a
  normal merge with the expected head SHA locked (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `778e2c7b27f0357110ba83e9b466984747577823` | [#46](https://github.com/consensusframework/yang-mills-mass-gap/pull/46) | [519](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/45066737956) (id 45066737956, job 137344481922) | `58eb3d1bf3cc2b3393c7608581905530053d0e96` | [520](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/45068310285) (id 45068310285, job 137349341525) |

Custody note: the pull-request run 519 is associated with the head
`778e2c7b…`, but its effective checkout was the provisional merge commit
`7e1d3e7…` ("Merge 778e2c7b… into 2ef6500d…"), as recorded in the job log
read by the publishing instance
(`docs/audits/stone60/publication/RELATORIO_60-P.md`), whose parents are
the base and the candidate and whose root tree is the candidate's; run 520
compiled the definitive merge `58eb3d1b…` itself. The run metadata alone do
not prove the effective checkout; the attribution is to the log reading.
Both runs (2026-11-22): `Build completed successfully`; the dependency
manifest `c376bbe9…1227` recorded and verified after the resolution and
after the build, the nine dependencies checked out at the recorded
revisions, no `lake update`; **121 `LatticeGauge` modules built, 121
distinct names, 0 replayed** — no replay of the project; the nine `Built`
targets outside `LatticeGauge` are the Mathlib cache tool (four Lean modules
`Cache.IO`, `Cache.Hashing`, `Cache.Requests`, `Cache.Main`, their four C
objects and the executable `cache`), not nine rebuilt packages; 0 errors
(the three lines containing `error:` are the echo of the workflow's own
script); 114 warnings, all in `LatticeGauge/`, none in the new module, none
from dependencies, the full warning blocks identical as a multiset to the
QA1 baseline of this stone (and to the QA1 baseline of Stone 59); 414 axiom
outputs, all standard, the 50 of the new module included; no `sorryAx` in
any list; the certificate multisets of the two runs identical. The two logs
are preserved in `docs/audits/stone60/packages/STONE60P_evidence.zip`.

Toolchain at `58eb3d1b…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 121
modules, 40,473 Lean source lines and 1,927 top-level declaration lines by
the textual count (1,878 at Version 59 plus the 49 lines of this module
that the regex matches; the module has 50 declarations) — 1,927 is not a
number of theorems.

## 6. Relation to Stone 59

Stone 59 defines, for a fixed family and fixed scales, the optimal cost `B*`
of a pair of profiles that reach each other, and bounds the difference of
the functionals by `(2·Cf)·e^{6D_s/113}·B*` (and by the two-term form). Stone
60 reads that cost as a distance: on each component of profiles that reach
one another, `B*` is a pseudometric (symmetric, zero on the diagonal,
subadditive, with kernel the equality of the effective factors), the
component carries the Mathlib `PseudoMetricSpace` structure with
`dist = B*` definitionally, and the two Stone 59 estimates become the two
Lipschitz constants of the functional, which is therefore uniformly
continuous and continuous for that distance. The Stone 59 estimates are
consumed (one use each); the recoveries are compatibility checks, not an
independent proof of Stone 59, and nothing of the chain 56–59 is reopened.
No constant is improved: the gain is structural (a geometry on the profiles
in which the functional is Lipschitz), not numerical.

## 7. Audits and review

Recorded, with hashes and provenance, in
[`docs/audits/stone60/`](../audits/stone60/README.md). Three kinds of
evidence with distinct scopes; none is specialized human mathematical
review. No complementary execution on a third platform was received for
this stone, and Gemini did not participate in this round.

- **60-QA1 with its addendum A1** — reproduction by execution of the
  candidate `778e2c7b…` by a separate instance of Claude (session model id
  `claude-fable-5-2` as the report declares; the QA1 reports of Stones 52–59
  were issued under `claude-fable-5-1`; same model family as the
  constructor; prior exposure declared, not blind; the constructor's report
  read before the execution; the constructor's logs, tests and matrices
  opened only in a second pass after the auditor's own conclusions, recorded
  in `PRELIMINARY_CONCLUSIONS_first_pass.md`). Reconstruction of the commit
  from the bundle on a **fresh** container (the previous bench lost; elan
  and the v4.15.0 toolchain installed; dependencies materialized from the
  Mathlib community cache at the nine manifest revisions; 9/9 revisions
  checked; no `lake update`; not recompiled); no project artifact before the
  build; single integral `lake build` 2026-11-22, 14:16:15Z → 14:30:02Z,
  827 s, exit 0, **121 modules built (121 distinct names), 0 replayed**, 0
  errors, 411 certificates standard (137 multi-line), 0 `sorryAx`, manifest
  identical before the dependencies, before and after the build; 114
  inherited warning blocks identical to the Stone 59 QA1 baseline, none in
  the new module; own certificates Q0 of **50/50** declarations; own tests
  Q1–Q7 pass (the seven items of the tape re-obtained by the auditor's own
  proofs, including the triangle **on `dist`** with equality and strict, and
  the empty component), Q7x fails on the single obligation of reach; 32
  warnings in the auditor's own disposable tests (Q6 29, Q5 2, Q3 1),
  separate from the 114 of the project. The constructor's tests T1–T10 and
  T9x were re-executed by the auditor in the second pass (same results);
  the re-execution does not transfer their authorship. Verdict `PASS NO
  ESCOPO` (execution, mathematics, documentation PASS; custody PASS with one
  non-blocking pendency — the constructor's report received as pasted text
  — closed by the **addendum A1** of the same day, which reconstructs the
  text byte for byte to 14,107 bytes and the SHA-256 `ced9b68d…8666` of the
  constructor's delivery; the verdict then stands without pendency). No
  errata was issued by the auditor; its §6 records one observation on the
  **constructor's** test file (the arithmetic nature of
  `t3_triangle_eq_and_return_strict`) and the environment difference of the
  two clean rebuilds, recorded in the audit index.
- **60-K-ADV with its errata C1 and C2** — adversarial review by **Kimi
  (K-ADV)**, as the documents identify the reviewer, a different model
  family, by reading and mathematical analysis of the module in full and of
  the Stone 59 and 56 interfaces consumed (read in the frozen v59 source),
  with own custody checks (hashes of the three files received, `git bundle
  verify`, the blob and the root tree recomputed, the diff regenerated and
  compared byte for byte, the public parent fetched from GitHub) **without
  any Lean execution**; prior exposure declared, not blind; the SSH
  signature not verified. Verdict `PASS NO ESCOPO`: all proof chains G0–G7
  re-derived by reading, no hidden hypothesis, no overclaim, no correction
  proposed to the candidate. **Two errata** by the same instance, both
  prompted by the coordination's conference and each prevailing on its
  point: **C1** (three documentary precisions of the report — the 20 paths of
  the Stone 59 consolidation including `README.md` and
  `VERIFICATION_STATUS.md`; the empty-component example restated with an
  explicit witness polymer; the review date `2026-11-23` being the
  reviewer's UTC+8 local date, 2026-11-22 in UTC); **C2** (the `Phase3/` tree
  of the candidate in §1.3 corrected from `6f408214…` to `ffabe443…`, the
  wrong value traced to a path-prefix defect of the reviewer's own Python
  recomputation and the corrected routine validated against `git rev-parse`
  for the candidate, the parent and `Phase3/LatticeGauge/`). Neither errata
  touches the candidate, the proofs, the interfaces or the two custody
  conclusions that weighed (exactly two paths changed; the parent's
  `Phase3/` equal to the frozen v59 base); the verdict is unchanged in both.
- **60-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit), with the operational package of the two
  CI logs; to be read with the coordination's precision C60-P1 of the audit
  index (the hashes of A1 and C1 had been communicated before the
  integration tape although not transcribed in its text).
- **GPT Astra / Can** — scientific architecture and review: the tapes 60-A
  (feasibility), 60-L (construction), 60-P (integration) and this
  consolidation; the documentary conference of the feasibility delivery and
  of the reports; no Lean build of its own.

## 8. Version records

For Version 59 the two publication statuses have different sources and are
kept apart: the **GitHub** state was read through the GitHub API by the
consolidating session; the **Zenodo** state is recorded as confirmed by the
coordinator and as stated in the body of the GitHub Release, the
consolidating session not having consulted Zenodo (the host is unreachable
from it).

| Step | Record |
|---|---|
| Version 59 (the current version) | commit `2ef6500deeb5dd7ddd70c5f208f690e9e0470353` (merge of PR #45, the documentary consolidation of Stone 59; Stone 59 itself integrated at `1dab07ab…`, PR #44), tag `zenodo-v59` (simple tag → `2ef6500d…`), **GitHub Release** [`zenodo-v59`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v59) published on 2026-10-31 (`draft = false`, `published_at` 2026-10-31T19:04:26Z; the Release object created 2026-10-22T21:22:08Z; read through the GitHub API by the consolidating session) with **one** asset, `V59_QUATRO_ARQUIVOS_PARA_UPLOAD.zip` (2,201,008 bytes, digest `sha256:a7ba421d…62e5` as reported by the API), a container of the four packaging files of the delivery 59-RELEASE-L (`yang-mills-mass-gap-zenodo-v59.zip`, `RELEASE_NOTES_PEDRA59.md`, `MANIFEST_v59.txt`, `SHA256SUMS.txt`), whose bytes were not compared again by this consolidation; its editorial regularization into four separate assets, if any, is the coordinator's and is not performed here; **Zenodo** record DOI [10.5281/zenodo.23697327](https://doi.org/10.5281/zenodo.23697327) (concept DOI 10.5281/zenodo.17397622), **published**, as confirmed by the coordinator and as stated in the Release body — the exact Zenodo publication date was not established by the materials of this consolidation and is not inferred from the Release date. The deposit contains Stones 52–59 and the committed dependency manifest, and not Stone 60 |
| Stone 60 | **integrated** on `main` at `58eb3d1b…` (2026-11-22, PR #46), audited (QA1 2026-11-22, with its addendum A1 of the same day), reviewed (Kimi, 2026-11-22 UTC, with its errata C1 and C2) and CI-verified (runs 519 and 520); **publication state: no tag, no Release, no deposit and no reserved DOI of its own recorded here** (no `zenodo-v60` tag or Release exists at consolidation time, as read through the GitHub API). It is cited by its commit. The future Version 60, if deposited, will be packaged from the definitive documentary merge in a step of its own |
