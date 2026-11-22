/-
# Stone 60 — The optimal cost of Stone 59 as a pseudometric on each reach
# component, and the profile functional as a Lipschitz map

Scientific architecture: GPT Astra / Can (tape 60-A, feasibility; tape 60-L,
construction). Construction: Claude Fable 5.1 (Claude Code), promoted from the
feasibility file `T60A_optimal_geometry_tests.lean` (gate 60-A), whose chain
G0–G7 elaborated unchanged. Base: commit 2ef6500deeb5dd7ddd70c5f208f690e9e0470353
(Version 59). The route was proposed by the coordination on paper and was
compiled in Lean by the constructing instance only.

## The question

Stone 59 defines, for a FIXED family of regions `r : Fin m → Set (Link N)` and
scales `n : Fin m → ℕ`, the minimal admissible cost `B*(a, b) = minCost` of the
additive cover between two profiles `a, b` with values in [0, 1] that reach each
other, and bounds `|F_R(a) − F_R(b)|` by `(2 Cf)·e^{6 D_s/113}·B*`. Does that
optimal cost give a coherent geometry for comparing several profiles at once?

## The statement

Objects of Stones 55–59 are kept (`F_R`, the effective factors `touchFactor`,
`D_s`, `budget`, `Admissible`, `Reaches`, `minCost`). `R`, `r`, `n` are fixed.

1. `Reaches R r a b ↔ ∀ η, (∀ i, ¬ typedTouchesSupport η (r i)) →
   touchFactor R a η = touchFactor R b η`, for arbitrary real profiles; reach is
   an equivalence relation (`reaches_equivalence`). No cover of all polymers is
   assumed.
2. Admissible budgets transport along symmetry and add along a path: if `δab`
   covers `(a, b)` and `δbc` covers `(b, c)`, then `δab + δbc` covers `(a, c)`,
   and `B(δab + δbc) = B(δab) + B(δbc)`. These lemmas carry no `β`, no
   integration, no separation, no `Cf` and no profile bound.
3. The minimal cost is symmetric, zero on the diagonal and satisfies the
   triangle inequality `B*(a, c) ≤ B*(a, b) + B*(b, c)`: the sum of two
   minimizers is admissible for the endpoints (its coordinates may exceed `1`;
   `minCost_le_budget` compares with ALL admissible budgets), and the cost is
   additive. Values are compared, never the chosen vectors.
4. For a reference profile `aref` (arbitrary real, no bound), the component
   `ProfileComponent R r n aref` is the type of profiles with values in [0, 1]
   reached from `aref`; `n` is carried in the type so that the geometry is
   inferable, although membership does not depend on `n`. Any two members reach
   each other, so `optimalDist x y := minCost` is defined on every pair of the
   component, with no conventional value for pairs without reach.
5. `optimalDist` is a pseudometric: `0 ≤ d`, `d(x, x) = 0`, symmetry, triangle,
   and `d(x, y) = 0 ↔ ∀ η, touchFactor R x.prof η = touchFactor R y.prof η`
   (equality of the EFFECTIVE factors — raw values ignored off `R` are not
   identified). Members of two components with equal profiles have equal
   distances: the reference organizes the domain, it does not enter the
   optimization of a pair. Proof terms of the hypotheses are irrelevant to the
   value (not a uniqueness of the minimizing vector).
6. `PseudoMetricSpace (ProfileComponent R r n aref)` is an instance of the
   Mathlib structure with `dist = optimalDist` (definitionally `minCost`);
   uniformity and bornology are the Mathlib defaults of that distance.
7. Variation: `|d(x, z) − d(y, z)| ≤ d(x, y)`, `|d(x, y) − d(x′, y′)| ≤ d(x, x′)
   + d(y, y′)` (Mathlib), and the polygonal inequality
   `d(x₀, x_k) ≤ ∑_{j<k} d(x_j, x_{j+1})` for `x : Fin (k+1) → C`, `k = 0`
   included.
8. The functional `a ↦ F_R(a)` on the component, under EXACTLY the analytic
   hypotheses of Stone 59 (`0 ≤ β ≤ 1/40000`, `χ` real measurable with `|χ| ≤ 1`,
   `f` measurable with `|f| ≤ Cf`, `WalkBarrierSeparated s (r i) (n i)`), is
   `LipschitzWith` for the two Stone 59 constants, given as non-negative reals
   whose coercions are exactly

     K₂ = Cf · [e^{6 D_s/113} + e^{4 D_s/113}],     K = (2 Cf) · e^{6 D_s/113},

   with `0 ≤ Cf` derived from the absolute majorant; hence `UniformContinuous`
   and `Continuous` for the pseudometric constructed here (no other topology is
   claimed). Along a finite chain, `|F_R(x₀) − F_R(x_k)| ≤ K₂ · ∑ d(x_j, x_{j+1})`
   and likewise with `K`. Zero distance gives exact equality of the functional
   by the Stone 56 identity, without the small-β regime.
9. Compatibility: two profiles in [0, 1] with reach are placed in the component
   of the first; their distance is the raw `minCost` definitionally, and the two
   Stone 59 estimates are recovered through the new interface, with the types of
   the published capstones.

## The route

The two Stone 59 capstones are the only analytic inputs (items 8–9 are a
TRANSPORT of Stone 59 to the new geometry, not an independent proof of it). The
new content is items 1–7: the equivalence of reach, the transport and addition of
covers (`abs_sub_le` polymer by polymer; sums index by index, multiplicities of
repeated regions preserved), the comparison of minimal costs through transported
and summed minimizers, the component, the instance, and the variation and chain
inequalities (the three- and four-point bounds are Mathlib's for any
pseudometric; the polygonal inequality is proved by induction on the chain).

## Interfaces and boundaries

The geometric part (items 1–7) involves no measure, no `β`, no `χ`, no `f` and
no separation. The wrapper requires its members in [0, 1] and reached from the
reference; the reference itself is unconstrained (the component may be empty,
and the reference need not be a member). Not required anywhere: `m > 0`, a cover
of all polymers, disjoint regions, `r i ⊆ R`, a separation of `s` from `R`, a
unit background, `DependsOnlyOn f s`, `δ i ≤ 1` on the budgets compared, a
unique minimizer, `Cf > 0`, a factor of `m` or of the volume outside the sum.
`m = 0` under reach gives distance `0` (equal effective factors); `R = ∅` gives
distance `0` for any profiles of the interval (all factors are `1`) — two
different reasons.

## Limits

A pseudometric on each reach component, not a metric on raw profiles: distinct
profiles with equal effective factors are at distance `0`. No metric quotient,
completeness, equivalence with a product topology or a uniform norm, extension
to pairs without reach, infinite volume, linear-programming duality, algorithm,
differentiability, monotonicity of the functional, new Gibbs measure,
thermodynamic or continuum limit, mass gap or bibliographic priority is claimed.
The constants are those of Stone 59; nothing is improved numerically. Finite
volume, finite family, small-β regime in the analytic part.
-/

import Mathlib
import LatticeGauge.ActivityProfileDampingOptimalCover

open MeasureTheory
open scoped Classical BigOperators NNReal

namespace LatticeGauge

namespace ActivityProfileOptimalGeometry

open ActivityProfileOptimalCover

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## G0 — reach as an equivalence relation (arbitrary real profiles) -/

/-- Reach, characterized: the effective factors agree on every polymer that touches no
    region of the family. No profile bound, no cover of all polymers. -/
theorem reaches_iff_untouched_eq {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a b : Polymer N → ℝ) :
    Reaches R r a b ↔
      ∀ η : Polymer N, (∀ i, ¬ typedTouchesSupport (N := N) η (r i)) →
        touchFactor R a η = touchFactor R b η := by
  constructor
  · intro h η hno
    by_contra hne
    obtain ⟨i, hi⟩ := h η hne
    exact hno i hi
  · intro h η hne
    by_contra hno
    push_neg at hno
    exact hne (h η hno)

theorem reaches_refl {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a : Polymer N → ℝ) : Reaches R r a a :=
  fun _ hne => absurd rfl hne

theorem reaches_symm {m : ℕ} {R : Set (Link N)} {r : Fin m → Set (Link N)}
    {a b : Polymer N → ℝ} (h : Reaches R r a b) : Reaches R r b a :=
  fun η hne => h η (Ne.symm hne)

theorem reaches_trans {m : ℕ} {R : Set (Link N)} {r : Fin m → Set (Link N)}
    {a b c : Polymer N → ℝ} (hab : Reaches R r a b) (hbc : Reaches R r b c) :
    Reaches R r a c := by
  rw [reaches_iff_untouched_eq] at hab hbc ⊢
  intro η hno
  exact (hab η hno).trans (hbc η hno)

theorem reaches_equivalence {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N)) :
    Equivalence (Reaches (N := N) R r) :=
  ⟨reaches_refl R r, reaches_symm, reaches_trans⟩

/-! ## G1 — transport of admissibility and addition of budgets -/

/-- The cover sum is symmetric in the two profiles (|x − y| = |y − x|). -/
theorem additiveCover_symm {m : ℕ} {R : Set (Link N)} {r : Fin m → Set (Link N)}
    {a b : Polymer N → ℝ} {δ : Fin m → ℝ} (h : AdditiveCover R r a b δ) :
    AdditiveCover R r b a δ := by
  intro η
  rw [abs_sub_comm]
  exact h η

theorem admissible_symm {m : ℕ} {R : Set (Link N)} {r : Fin m → Set (Link N)}
    {a b : Polymer N → ℝ} {δ : Fin m → ℝ} (h : Admissible R r a b δ) :
    Admissible R r b a δ :=
  ⟨h.1, additiveCover_symm h.2⟩

/-- The zero budget covers `(a, a)` for any real profile. -/
theorem admissible_zero_self {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a : Polymer N → ℝ) : Admissible R r a a (fun _ => 0) :=
  admissible_zero_of_touchFactor_eq R r (fun _ => rfl)

/-- The cover sum of a sum of budgets is the sum of the cover sums (index by index;
    repeated regions keep their multiplicity). -/
theorem coverSum_add {m : ℕ} (r : Fin m → Set (Link N)) (δ₁ δ₂ : Fin m → ℝ) (η : Polymer N) :
    (∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then (δ₁ + δ₂) i else 0)
      = (∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ₁ i else 0)
        + ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ₂ i else 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases ht : typedTouchesSupport (N := N) η (r i)
  · simp [ht, Pi.add_apply]
  · simp [ht]

/-- Admissible budgets add along a path: `δab + δbc` covers `(a, c)`
    (`|b_a − b_c| ≤ |b_a − b_b| + |b_b − b_c|`). No profile bound is used. -/
theorem admissible_add {m : ℕ} {R : Set (Link N)} {r : Fin m → Set (Link N)}
    {a b c : Polymer N → ℝ} {δab δbc : Fin m → ℝ}
    (hab : Admissible R r a b δab) (hbc : Admissible R r b c δbc) :
    Admissible R r a c (δab + δbc) := by
  refine ⟨fun i => add_nonneg (hab.1 i) (hbc.1 i), fun η => ?_⟩
  rw [coverSum_add]
  calc |touchFactor R a η - touchFactor R c η|
      ≤ |touchFactor R a η - touchFactor R b η| + |touchFactor R b η - touchFactor R c η| :=
        abs_sub_le _ _ _
    _ ≤ _ := add_le_add (hab.2 η) (hbc.2 η)

/-- The cost is additive: `B(δ₁ + δ₂) = B(δ₁) + B(δ₂)`. -/
theorem budget_add {m : ℕ} (n : Fin m → ℕ) (δ₁ δ₂ : Fin m → ℝ) :
    budget n (δ₁ + δ₂) = budget n δ₁ + budget n δ₂ := by
  unfold budget
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.add_apply]
  ring

/-! ## G2 — symmetry, diagonal and triangle inequality of `minCost` (raw profiles) -/

/-- The minimal cost does not depend on the proof terms of its hypotheses
    (proof irrelevance; not a statement about the minimizing vector). -/
theorem minCost_proof_irrel {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a b : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ b η) (h1' : ∀ η, b η ≤ 1)
    (hreach : Reaches R r a b)
    (g0 : ∀ η, 0 ≤ a η) (g1 : ∀ η, a η ≤ 1) (g0' : ∀ η, 0 ≤ b η) (g1' : ∀ η, b η ≤ 1)
    (greach : Reaches R r a b) :
    minCost R r n h0 h1 h0' h1' hreach = minCost R r n g0 g1 g0' g1' greach := rfl

/-- Symmetry of the VALUE: two comparisons of minima through transported minimizers.
    The vectors `optimalBudget a b` and `optimalBudget b a` are not claimed equal. -/
theorem minCost_comm {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a b : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ b η) (h1' : ∀ η, b η ≤ 1)
    (hreach : Reaches R r a b) :
    minCost R r n h0 h1 h0' h1' hreach = minCost R r n h0' h1' h0 h1 (reaches_symm hreach) := by
  apply le_antisymm
  · exact minCost_le_budget R r n h0 h1 h0' h1' hreach
      (admissible_symm (optimalBudget_admissible R r n h0' h1' h0 h1 (reaches_symm hreach)))
  · exact minCost_le_budget R r n h0' h1' h0 h1 (reaches_symm hreach)
      (admissible_symm (optimalBudget_admissible R r n h0 h1 h0' h1' hreach))

/-- Diagonal: `B*(a, a) = 0`. -/
theorem minCost_self {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (hreach : Reaches R r a a) :
    minCost R r n h0 h1 h0 h1 hreach = 0 :=
  (minCost_eq_zero_iff R r n h0 h1 h0 h1 hreach).mpr (fun _ => rfl)

/-- Triangle inequality of the minimal cost: the sum of two minimizers is admissible for
    the endpoints (its coordinates may exceed `1`; `minCost_le_budget` compares with ALL
    admissible budgets), and the cost is additive. The summed budget is not claimed optimal. -/
theorem minCost_triangle {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a b c : Polymer N → ℝ}
    (ha0 : ∀ η, 0 ≤ a η) (ha1 : ∀ η, a η ≤ 1) (hb0 : ∀ η, 0 ≤ b η) (hb1 : ∀ η, b η ≤ 1)
    (hc0 : ∀ η, 0 ≤ c η) (hc1 : ∀ η, c η ≤ 1)
    (hab : Reaches R r a b) (hbc : Reaches R r b c) (hac : Reaches R r a c) :
    minCost R r n ha0 ha1 hc0 hc1 hac
      ≤ minCost R r n ha0 ha1 hb0 hb1 hab + minCost R r n hb0 hb1 hc0 hc1 hbc := by
  have hadm : Admissible R r a c
      (optimalBudget R r n ha0 ha1 hb0 hb1 hab + optimalBudget R r n hb0 hb1 hc0 hc1 hbc) :=
    admissible_add (optimalBudget_admissible R r n ha0 ha1 hb0 hb1 hab)
      (optimalBudget_admissible R r n hb0 hb1 hc0 hc1 hbc)
  calc minCost R r n ha0 ha1 hc0 hc1 hac
      ≤ budget n (optimalBudget R r n ha0 ha1 hb0 hb1 hab + optimalBudget R r n hb0 hb1 hc0 hc1 hbc) :=
        minCost_le_budget R r n ha0 ha1 hc0 hc1 hac hadm
    _ = minCost R r n ha0 ha1 hb0 hb1 hab + minCost R r n hb0 hb1 hc0 hc1 hbc :=
        budget_add n _ _

/-! ## G3 — the component of a reference profile and the distance -/

/-- A profile with values in `[0,1]` reached from the reference `aref` by the fixed family
    `r`. The scales `n` are carried in the type so that the geometry below is inferable;
    membership itself does not depend on `n`. No bound on `aref` is required. -/
structure ProfileComponent (R : Set (Link N)) {m : ℕ} (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) (aref : Polymer N → ℝ) where
  prof : Polymer N → ℝ
  nonneg : ∀ η, 0 ≤ prof η
  le_one : ∀ η, prof η ≤ 1
  reach : Reaches R r aref prof

variable {R : Set (Link N)} {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ}
  {aref : Polymer N → ℝ}

/-- Any two members of a component reach each other (symmetry and transitivity). -/
theorem ProfileComponent.reaches (x y : ProfileComponent R r n aref) :
    Reaches R r x.prof y.prof :=
  reaches_trans (reaches_symm x.reach) y.reach

/-- The distance: the Stone 59 minimal cost itself, with the bounds of the members and the
    reach derived from the component. -/
noncomputable def optimalDist (x y : ProfileComponent R r n aref) : ℝ :=
  minCost R r n x.nonneg x.le_one y.nonneg y.le_one (x.reaches y)

theorem optimalDist_eq_minCost (x y : ProfileComponent R r n aref)
    (h0 : ∀ η, 0 ≤ x.prof η) (h1 : ∀ η, x.prof η ≤ 1)
    (h0' : ∀ η, 0 ≤ y.prof η) (h1' : ∀ η, y.prof η ≤ 1) (hreach : Reaches R r x.prof y.prof) :
    optimalDist x y = minCost R r n h0 h1 h0' h1' hreach := rfl

theorem optimalDist_nonneg (x y : ProfileComponent R r n aref) : 0 ≤ optimalDist x y :=
  minCost_nonneg R r n _ _ _ _ _

theorem optimalDist_self (x : ProfileComponent R r n aref) : optimalDist x x = 0 :=
  minCost_self R r n x.nonneg x.le_one _

theorem optimalDist_comm (x y : ProfileComponent R r n aref) :
    optimalDist x y = optimalDist y x :=
  minCost_comm R r n x.nonneg x.le_one y.nonneg y.le_one (x.reaches y)

theorem optimalDist_triangle (x y z : ProfileComponent R r n aref) :
    optimalDist x z ≤ optimalDist x y + optimalDist y z :=
  minCost_triangle R r n x.nonneg x.le_one y.nonneg y.le_one z.nonneg z.le_one
    (x.reaches y) (y.reaches z) (x.reaches z)

/-- `d(x, y) = 0` iff the effective factors coincide — not the raw profiles. -/
theorem optimalDist_eq_zero_iff (x y : ProfileComponent R r n aref) :
    optimalDist x y = 0 ↔ ∀ η, touchFactor R x.prof η = touchFactor R y.prof η :=
  minCost_eq_zero_iff R r n x.nonneg x.le_one y.nonneg y.le_one (x.reaches y)

/-- Two references, same `R`, `r`, `n`: members with equal profiles have equal distances.
    The reference organizes the domain; it does not enter the optimization of a pair. -/
theorem optimalDist_ref_indep {aref' : Polymer N → ℝ}
    (x y : ProfileComponent R r n aref) (x' y' : ProfileComponent R r n aref')
    (hx : x.prof = x'.prof) (hy : y.prof = y'.prof) :
    optimalDist x y = optimalDist x' y' := by
  cases x with | mk xp x0 x1 xr =>
  cases y with | mk yp y0 y1 yr =>
  cases x' with | mk xp' x0' x1' xr' =>
  cases y' with | mk yp' y0' y1' yr' =>
  simp only at hx hy
  subst hx
  subst hy
  rfl

/-! ## G4 — the Mathlib instance -/

noncomputable instance instPseudoMetricSpace : PseudoMetricSpace (ProfileComponent R r n aref) where
  dist := optimalDist
  dist_self := optimalDist_self
  dist_comm := optimalDist_comm
  dist_triangle := optimalDist_triangle

/-- The inferred `dist` is the Stone 59 minimal cost. -/
theorem dist_eq_optimalDist (x y : ProfileComponent R r n aref) : dist x y = optimalDist x y := rfl

theorem dist_eq_minCost (x y : ProfileComponent R r n aref) :
    dist x y = minCost R r n x.nonneg x.le_one y.nonneg y.le_one (x.reaches y) := rfl

/-! ## G5 — variation of the optimal cost and finite chains -/

/-- Three-point variation: `|d(x, z) − d(y, z)| ≤ d(x, y)` (Mathlib `abs_dist_sub_le`). -/
theorem abs_optimalDist_sub_le (x y z : ProfileComponent R r n aref) :
    |optimalDist x z - optimalDist y z| ≤ optimalDist x y :=
  abs_dist_sub_le x y z

/-- Four-point variation: `|d(x, y) − d(x', y')| ≤ d(x, x') + d(y, y')`
    (Mathlib `dist_dist_dist_le` with `Real.dist_eq`). The vectors are not claimed continuous. -/
theorem abs_optimalDist_sub_optimalDist_le (x y x' y' : ProfileComponent R r n aref) :
    |optimalDist x y - optimalDist x' y'| ≤ optimalDist x x' + optimalDist y y' := by
  have h := dist_dist_dist_le x y x' y'
  rwa [Real.dist_eq] at h

/-- Polygonal inequality along a finite chain `x : Fin (k+1) → C`, `k = 0` included. -/
theorem optimalDist_chain_le {k : ℕ} (x : Fin (k + 1) → ProfileComponent R r n aref) :
    optimalDist (x 0) (x (Fin.last k))
      ≤ ∑ j : Fin k, optimalDist (x j.castSucc) (x j.succ) := by
  induction k with
  | zero =>
    simp [optimalDist_self]
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    have hmid := ih (fun j => x j.castSucc)
    simp only [Fin.castSucc_zero] at hmid
    calc optimalDist (x 0) (x (Fin.last (k + 1)))
        ≤ optimalDist (x 0) (x (Fin.last k).castSucc)
            + optimalDist (x (Fin.last k).castSucc) (x (Fin.last (k + 1))) :=
          optimalDist_triangle _ _ _
      _ ≤ (∑ j : Fin k, optimalDist (x j.castSucc.castSucc) (x j.castSucc.succ))
            + optimalDist (x (Fin.last k).castSucc) (x (Fin.last k).succ) := by
          apply add_le_add _ le_rfl
          refine le_trans hmid (le_of_eq ?_)
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Fin.succ_castSucc]

/-! ## G6 — the functional as a Lipschitz map with the two Stone 59 constants -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- `a ↦ F_R(a)` on the component, with `μm`, `β`, `χ`, `f`, `s`, `R` fixed. -/
noncomputable def functional (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) (s : Set (Link N))
    (x : ProfileComponent R r n aref) : ℝ :=
  profileExpectation μm β χ f s R x.prof

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The two-term constant `K₂ = Cf·[e^{6D_s/113} + e^{4D_s/113}]` as a non-negative real;
    `0 ≤ Cf` is derived from the absolute majorant. -/
noncomputable def twoTermConst {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (s : Set (Link N)) : ℝ≥0 :=
  ⟨Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)),
    mul_nonneg (nonneg_of_abs_le_of_config hCf) (add_pos (Real.exp_pos _) (Real.exp_pos _)).le⟩

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- The compact constant `K = (2Cf)·e^{6D_s/113}` as a non-negative real. -/
noncomputable def compactConst {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (s : Set (Link N)) : ℝ≥0 :=
  ⟨(2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113),
    mul_nonneg (by linarith [nonneg_of_abs_le_of_config hCf]) (Real.exp_pos _).le⟩

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem coe_twoTermConst {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (s : Set (Link N)) :
    ((twoTermConst hCf s : ℝ≥0) : ℝ)
      = Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)) := rfl

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem coe_compactConst {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (s : Set (Link N)) :
    ((compactConst hCf s : ℝ≥0) : ℝ)
      = (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := rfl

/-- **Two-term Lipschitz bound on the component**: the Stone 59 two-term capstone, the
    right-hand side being `K₂ · dist x y`. -/
theorem abs_functional_sub_functional_le_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    (x y : ProfileComponent R r n aref) :
    |functional μm β χ f s x - functional μm β χ f s y|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * dist x y :=
  abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms μm hβ mχ hχabs hsmall
    R mf hCf hsep x.nonneg x.le_one y.nonneg y.le_one (x.reaches y)

/-- **Compact Lipschitz bound on the component**: the Stone 59 capstone with `K · dist x y`. -/
theorem abs_functional_sub_functional_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    (x y : ProfileComponent R r n aref) :
    |functional μm β χ f s x - functional μm β χ f s y|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) * dist x y :=
  abs_profileExpectation_sub_profileExpectation_le_optimal_cover μm hβ mχ hχabs hsmall
    R mf hCf hsep x.nonneg x.le_one y.nonneg y.le_one (x.reaches y)

/-- **`LipschitzWith` with the two-term constant** (`LipschitzWith.of_dist_le_mul`). -/
theorem lipschitzWith_functional_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i)) :
    LipschitzWith (twoTermConst hCf s)
      (functional μm β χ f s : ProfileComponent R r n aref → ℝ) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [Real.dist_eq, coe_twoTermConst]
  exact abs_functional_sub_functional_le_two_terms μm hβ mχ hχabs hsmall mf hCf hsep x y

/-- **`LipschitzWith` with the compact constant.** -/
theorem lipschitzWith_functional
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i)) :
    LipschitzWith (compactConst hCf s)
      (functional μm β χ f s : ProfileComponent R r n aref → ℝ) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [Real.dist_eq, coe_compactConst]
  exact abs_functional_sub_functional_le μm hβ mχ hχabs hsmall mf hCf hsep x y

/-- Uniform continuity for the pseudometric constructed here (no other topology claimed). -/
theorem uniformContinuous_functional
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i)) :
    UniformContinuous (functional μm β χ f s : ProfileComponent R r n aref → ℝ) :=
  (lipschitzWith_functional μm hβ mχ hχabs hsmall mf hCf hsep).uniformContinuous

theorem continuous_functional
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i)) :
    Continuous (functional μm β χ f s : ProfileComponent R r n aref → ℝ) :=
  (lipschitzWith_functional μm hβ mχ hχabs hsmall mf hCf hsep).continuous

/-- Control along a finite chain, two-term constant. -/
theorem abs_functional_chain_le_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {k : ℕ} (x : Fin (k + 1) → ProfileComponent R r n aref) :
    |functional μm β χ f s (x 0) - functional μm β χ f s (x (Fin.last k))|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ j : Fin k, dist (x j.castSucc) (x j.succ) := by
  calc |functional μm β χ f s (x 0) - functional μm β χ f s (x (Fin.last k))|
      ≤ _ * dist (x 0) (x (Fin.last k)) :=
        abs_functional_sub_functional_le_two_terms μm hβ mχ hχabs hsmall mf hCf hsep _ _
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (optimalDist_chain_le x)
        exact mul_nonneg (nonneg_of_abs_le_of_config hCf)
          (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

/-- Control along a finite chain, compact constant. -/
theorem abs_functional_chain_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {k : ℕ} (x : Fin (k + 1) → ProfileComponent R r n aref) :
    |functional μm β χ f s (x 0) - functional μm β χ f s (x (Fin.last k))|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * ∑ j : Fin k, dist (x j.castSucc) (x j.succ) := by
  calc |functional μm β χ f s (x 0) - functional μm β χ f s (x (Fin.last k))|
      ≤ _ * dist (x 0) (x (Fin.last k)) :=
        abs_functional_sub_functional_le μm hβ mχ hχabs hsmall mf hCf hsep _ _
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left (optimalDist_chain_le x)
        exact mul_nonneg (by linarith [nonneg_of_abs_le_of_config hCf]) (Real.exp_pos _).le

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- Zero distance gives exact equality of the functional (algebraic; no regime). -/
theorem functional_eq_of_dist_eq_zero (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) (s : Set (Link N))
    (x y : ProfileComponent R r n aref) (h : dist x y = 0) :
    functional μm β χ f s x = functional μm β χ f s y :=
  profileExpectation_eq_of_touchFactor_eq μm β χ f s R ((optimalDist_eq_zero_iff x y).mp h)

/-! ## G7 — compatibility with the raw Stone 59 interface -/

/-- Two profiles in `[0,1]` with reach, placed in the component of the first. -/
def ofReach (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    ProfileComponent R r n a :=
  ⟨a, h0, h1, reaches_refl R r a⟩

def ofReach' (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a b : Polymer N → ℝ} (h0' : ∀ η, 0 ≤ b η) (h1' : ∀ η, b η ≤ 1) (hreach : Reaches R r a b) :
    ProfileComponent R r n a :=
  ⟨b, h0', h1', hreach⟩

/-- The distance of the two placed profiles is the raw `minCost` (definitionally). -/
theorem dist_ofReach {a b : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ b η) (h1' : ∀ η, b η ≤ 1)
    (hreach : Reaches R r a b) :
    dist (ofReach R r n h0 h1) (ofReach' R r n h0' h1' hreach)
      = minCost R r n h0 h1 h0' h1' hreach := rfl

/-- **Stone 59 compact estimate recovered** through the component interface (G6); a
    compatibility check depending on Stone 59, not an independent derivation. -/
theorem recover_optimal_cover
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ}
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * minCost R r n h0 h1 h0' h1' hreach :=
  abs_functional_sub_functional_le μm hβ mχ hχabs hsmall mf hCf hsep
    (ofReach R r n h0 h1) (ofReach' R r n h0' h1' hreach)

/-- **Stone 59 two-term estimate recovered** through the component interface. -/
theorem recover_optimal_cover_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ}
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * minCost R r n h0 h1 h0' h1' hreach :=
  abs_functional_sub_functional_le_two_terms μm hβ mχ hχabs hsmall mf hCf hsep
    (ofReach R r n h0 h1) (ofReach' R r n h0' h1' hreach)

end ActivityProfileOptimalGeometry

/-! ## 60-L.8 — certificates (one per declaration of this module) -/

#print axioms ActivityProfileOptimalGeometry.reaches_iff_untouched_eq
#print axioms ActivityProfileOptimalGeometry.reaches_refl
#print axioms ActivityProfileOptimalGeometry.reaches_symm
#print axioms ActivityProfileOptimalGeometry.reaches_trans
#print axioms ActivityProfileOptimalGeometry.reaches_equivalence
#print axioms ActivityProfileOptimalGeometry.additiveCover_symm
#print axioms ActivityProfileOptimalGeometry.admissible_symm
#print axioms ActivityProfileOptimalGeometry.admissible_zero_self
#print axioms ActivityProfileOptimalGeometry.coverSum_add
#print axioms ActivityProfileOptimalGeometry.admissible_add
#print axioms ActivityProfileOptimalGeometry.budget_add
#print axioms ActivityProfileOptimalGeometry.minCost_proof_irrel
#print axioms ActivityProfileOptimalGeometry.minCost_comm
#print axioms ActivityProfileOptimalGeometry.minCost_self
#print axioms ActivityProfileOptimalGeometry.minCost_triangle
#print axioms ActivityProfileOptimalGeometry.ProfileComponent
#print axioms ActivityProfileOptimalGeometry.ProfileComponent.reaches
#print axioms ActivityProfileOptimalGeometry.optimalDist
#print axioms ActivityProfileOptimalGeometry.optimalDist_eq_minCost
#print axioms ActivityProfileOptimalGeometry.optimalDist_nonneg
#print axioms ActivityProfileOptimalGeometry.optimalDist_self
#print axioms ActivityProfileOptimalGeometry.optimalDist_comm
#print axioms ActivityProfileOptimalGeometry.optimalDist_triangle
#print axioms ActivityProfileOptimalGeometry.optimalDist_eq_zero_iff
#print axioms ActivityProfileOptimalGeometry.optimalDist_ref_indep
#print axioms ActivityProfileOptimalGeometry.instPseudoMetricSpace
#print axioms ActivityProfileOptimalGeometry.dist_eq_optimalDist
#print axioms ActivityProfileOptimalGeometry.dist_eq_minCost
#print axioms ActivityProfileOptimalGeometry.abs_optimalDist_sub_le
#print axioms ActivityProfileOptimalGeometry.abs_optimalDist_sub_optimalDist_le
#print axioms ActivityProfileOptimalGeometry.optimalDist_chain_le
#print axioms ActivityProfileOptimalGeometry.functional
#print axioms ActivityProfileOptimalGeometry.twoTermConst
#print axioms ActivityProfileOptimalGeometry.compactConst
#print axioms ActivityProfileOptimalGeometry.coe_twoTermConst
#print axioms ActivityProfileOptimalGeometry.coe_compactConst
#print axioms ActivityProfileOptimalGeometry.abs_functional_sub_functional_le_two_terms
#print axioms ActivityProfileOptimalGeometry.abs_functional_sub_functional_le
#print axioms ActivityProfileOptimalGeometry.lipschitzWith_functional_two_terms
#print axioms ActivityProfileOptimalGeometry.lipschitzWith_functional
#print axioms ActivityProfileOptimalGeometry.uniformContinuous_functional
#print axioms ActivityProfileOptimalGeometry.continuous_functional
#print axioms ActivityProfileOptimalGeometry.abs_functional_chain_le_two_terms
#print axioms ActivityProfileOptimalGeometry.abs_functional_chain_le
#print axioms ActivityProfileOptimalGeometry.functional_eq_of_dist_eq_zero
#print axioms ActivityProfileOptimalGeometry.ofReach
#print axioms ActivityProfileOptimalGeometry.ofReach'
#print axioms ActivityProfileOptimalGeometry.dist_ofReach
#print axioms ActivityProfileOptimalGeometry.recover_optimal_cover
#print axioms ActivityProfileOptimalGeometry.recover_optimal_cover_two_terms

end LatticeGauge
