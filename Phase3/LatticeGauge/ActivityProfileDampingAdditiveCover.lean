/-
# Stone 58 — Stability of the profile-damped functional under an ADDITIVE
# cover of the effective changes by several regions

Scientific architecture: GPT Astra / Can (tape 58-AL, feasibility and
construction). Construction: Claude Fable 5.1 (Claude Code), promoted from the
feasibility file `T58A_additive_cover_tests.lean` (gate 58-A), whose chain
elaborated unchanged. Base: commit 18c6ff084020e52c8932ecfd20e4b19f47efdf02
(Version 57). The route was proposed by the coordination on paper and was
compiled in Lean by the constructing instance only; nothing here is certified
before its elaboration.

## The statement

Objects of Stones 55–57 are kept:

  F_R(a) = profileExpectation μm β χ f s R a,
  b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
  D_s    = card (supportLinkFinset s).

A FINITE family of change regions, indexed by `i : Fin m` (`m = 0` included):

  r : Fin m → Set (Link N),   n : Fin m → ℕ,   δ : Fin m → ℝ,
  hδ0  : ∀ i, 0 ≤ δ i,
  hsep : ∀ i, WalkBarrierSeparated s (r i) (n i),
  hadd : ∀ η, |b(η) − b′(η)| ≤ ∑ i, if typedTouchesSupport η (r i) then δ i else 0.

`hadd` is an ADDITIVE cover of the effective changes by polymers: the change of
the effective factor of a polymer is paid by the sum of the budgets of the
regions that polymer touches. No single region has to pay the whole change
(Stone 57 required one owner per polymer). It is a condition on the effective
factors, not on raw differences of profiles ignored outside `R`; it is not a
cover of a union of sets of links (E3). With `B = ∑ i : Fin m, δ i · exp(−(n i)/2)`,
for profiles `a, a′` with values in [0, 1], in the regime `0 ≤ β ≤ 1/40000`:

  |F_R(a) − F_R(a′)| ≤ Cf · [e^{6 D_s/113} + e^{4 D_s/113}] · B      (two terms)
                     ≤ (2 Cf) · e^{6 D_s/113} · B.                     (capstone)

Exactly the constant, the rate and the regime of Stone 57. Not required: `m > 0`;
disjoint regions; `r i ⊆ R`; any separation of `s` from `R`; a unit background;
`δ i ≤ 1`; a sign condition on activities or exponents; `DependsOnlyOn f s`; an
owner or an amplitude decomposition supplied by the user; a factor of `m` or of
a volume outside the sum. Nothing is divided by `δ i`, by the sum of the budgets
or by the difference of the profiles (E5). `0 ≤ Cf` is derived.

## The route (no division)

1. A truncated scalar move `move x y t = if x ≤ y then min y (x+t) else max y (x−t)`:
   `move x y 0 = x`; for `t ≥ 0` the value stays between `min x y` and
   `max x y`; `|x−y| ≤ t` gives `move x y t = y` (saturation); for `t, u ≥ 0`,
   `|move x y (t+u) − move x y t| ≤ u` (increment bound). Both branches are
   proved for arbitrary reals; the interval [0,1] enters only when the limits of
   the profiles are transported.
2. Per polymer, the region costs `c_i(η) = if touches (r i) then δ i else 0` and
   the prefix capacities `C_k(η) = ∑_{i.val < k} c_i(η)`: `C_0 = 0`,
   `C_(i+1) = C_i + c_i`, `C_m = ∑ i, c_i`, all non-negative.
3. Intermediate profiles `p_k(η) = if touches R then move (a η) (a′ η) (C_k η) else a η`:
   `p_0 = a` as profiles; each `p_k` stays in [0,1]; at step `i` the effective
   factors of `p_i` and `p_(i+1)` agree outside `r i` (the step cost is exactly
   zero there, whatever other regions the polymer touches) and differ by at most
   `δ i` on `r i` (increment bound; both factors are `1` off `R`). A polymer may
   move at several steps (E1).
4. Under `hadd`, saturation gives `touchFactor R p_m η = b′(η)` for every `η`:
   equality of EFFECTIVE factors, not of raw profiles (outside `R` the raw values
   may still differ).
5. The Stone 56 two-term estimate at every step with `r i, n i, δ i` and the
   two intermediate profiles; finite telescoping (Stone 57 `abs_telescope`);
   the Stone 56 identity by equal effective factors at the last profile; the
   reorganization of the sum; then `0 ≤ Cf`, `B ≥ 0`, `e^{4 D_s/113} ≤ e^{6 D_s/113}`.

The composition is stated once for an arbitrary chain of profiles
(`abs_profileExpectation_sub_le_of_chain`) and instantiated with the additive
profiles. The Stone 57 capstone is NOT used to prove the additive case (there is
no conversion to a single owner); the Stone 57 statements are RECOVERED below.

## Interfaces and recoveries

`additive_of_cover`: the Stone 57 cover `hcover` with `hδ0` implies `hadd` (a
zero difference lies below the non-negative sum; a non-zero one is paid by its
covering index, one term of the sum). Hence the two Stone 57 estimates are
recovered by specialization (not an independent proof of the chain 56–57).
`m = 1`: the Stone 56 hypotheses `hsame`, `hδ` give `hadd` and the Stone 56 bound
returns. `m = 0`: `hadd` forces equal effective factors, hence `F_R(a) = F_R(a′)`
exactly, for arbitrary real profiles and with no analytic hypothesis; the same
for `δ ≡ 0`.

## Precisions (E1–E6)

E1. A polymer may change at several steps; each step respects its region and
its budget; there is no single owner in the general case.
E2. The gain is on the cover hypothesis. The bound keeps `B`; no universal
numerical improvement, optimal sum or optimal order of the steps is claimed.
E3. The additive cover controls the effective change of each polymer; covering
a union of sets of links is not a substitute.
E4. The common background may be non-unit; `R` stays in every definition; the
bound is uniform in the admissible background, not an identity of independence
from it; `s` is called the support of `f` only where that hypothesis is present.
E5. The route without division handles zero differences, zero budgets and
budgets larger than 1; no normalization dividing by a positive capacity.
E6. Finite volume, finite family, small-β regime. No thermodynamic or continuum
limit, no new Gibbs measure, no monotonicity of the functional (the scalar
path is monotone towards its target; `F_R` is not claimed monotone), no
differentiability, no mass gap, no solution of the Clay problem.
-/

import Mathlib
import LatticeGauge.ActivityProfileDampingMultiRegion

open MeasureTheory
open scoped Classical BigOperators

namespace LatticeGauge

namespace ActivityProfileAdditiveCover

/-! ## 58-L.1 — truncated scalar move towards a target -/

/-- Truncated move of `x` towards `y` by at most `t`. Both branches work for
    arbitrary reals; no `x ≤ y` is required globally. -/
noncomputable def move (x y t : ℝ) : ℝ :=
  if x ≤ y then min y (x + t) else max y (x - t)

theorem move_zero (x y : ℝ) : move x y 0 = x := by
  unfold move
  split_ifs with h
  · rw [add_zero]; exact min_eq_right h
  · rw [sub_zero]; exact max_eq_right (le_of_lt (not_le.mp h))

theorem move_self (x t : ℝ) (ht : 0 ≤ t) : move x x t = x := by
  unfold move
  rw [if_pos le_rfl]
  exact min_eq_left (by linarith)

/-- For `t ≥ 0` the result stays between `min x y` and `max x y`. -/
theorem move_mem (x y t : ℝ) (ht : 0 ≤ t) :
    min x y ≤ move x y t ∧ move x y t ≤ max x y := by
  unfold move
  split_ifs with h
  · constructor
    · exact le_min (by linarith [min_le_left x y, min_le_right x y])
        (by linarith [min_le_left x y])
    · exact le_trans (min_le_left _ _) (le_max_right _ _)
  · have h' : y < x := not_le.mp h
    constructor
    · exact le_trans (min_le_right _ _) (le_max_left _ _)
    · exact max_le (le_max_right _ _) (by linarith [le_max_left x y])

/-- Saturation: enough capacity reaches the target exactly. -/
theorem move_eq_of_abs_le {x y t : ℝ} (h : |x - y| ≤ t) : move x y t = y := by
  unfold move
  have h1 := (abs_le.mp h).1
  have h2 := (abs_le.mp h).2
  split_ifs with hxy
  · exact min_eq_left (by linarith)
  · exact max_eq_left (by linarith)

/-- The increment bound: adding capacity `u ≥ 0` moves by at most `u` (for any
    real `t`; no sign of `t` is needed). -/
theorem abs_move_add_sub_move_le (x y : ℝ) (t : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |move x y (t + u) - move x y t| ≤ u := by
  unfold move
  rw [abs_le]
  split_ifs with h
  · simp only [min_def]
    split_ifs <;> constructor <;> linarith
  · simp only [max_def]
    split_ifs <;> constructor <;> linarith

/-- Transport of the interval: values in `[0,1]` give a move in `[0,1]`. -/
theorem move_mem_Icc {x y t : ℝ} (ht : 0 ≤ t) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 0 ≤ move x y t ∧ move x y t ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := move_mem x y t ht
  exact ⟨le_trans (le_min hx0 hy0) hlo, le_trans hhi (max_le hx1 hy1)⟩

/-! ## 58-L.2 — region costs and prefix capacities -/

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-- `c_i(η)`: the budget of region `i` if the polymer touches it, else `0`. -/
noncomputable def regionCost {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (i : Fin m) (η : Polymer N) : ℝ :=
  if typedTouchesSupport (N := N) η (r i) then δ i else 0

/-- `C_k(η) = ∑_{i.val < k} c_i(η)`. -/
noncomputable def prefixCost {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (k : ℕ) (η : Polymer N) : ℝ :=
  ∑ i : Fin m, if i.val < k then regionCost r δ i η else 0

theorem regionCost_nonneg {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (i : Fin m) (η : Polymer N) : 0 ≤ regionCost r δ i η := by
  unfold regionCost
  split_ifs
  · exact hδ0 i
  · exact le_rfl

theorem regionCost_of_not_touch {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (i : Fin m) {η : Polymer N} (h : ¬ typedTouchesSupport (N := N) η (r i)) :
    regionCost r δ i η = 0 := by
  unfold regionCost
  exact if_neg h

theorem regionCost_of_touch {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (i : Fin m) {η : Polymer N} (h : typedTouchesSupport (N := N) η (r i)) :
    regionCost r δ i η = δ i := by
  unfold regionCost
  exact if_pos h

theorem prefixCost_zero {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (η : Polymer N) : prefixCost r δ 0 η = 0 := by
  unfold prefixCost
  exact Finset.sum_eq_zero (fun i _ => if_neg (Nat.not_lt_zero _))

theorem prefixCost_nonneg {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) (k : ℕ) (η : Polymer N) : 0 ≤ prefixCost r δ k η := by
  unfold prefixCost
  refine Finset.sum_nonneg (fun i _ => ?_)
  split_ifs
  · exact regionCost_nonneg r δ hδ0 i η
  · exact le_rfl

/-- `C_(i+1) = C_i + c_i`: the prefix grows by exactly the cost of the step. -/
theorem prefixCost_succ {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (i : Fin m) (η : Polymer N) :
    prefixCost r δ (i.val + 1) η = prefixCost r δ i.val η + regionCost r δ i η := by
  unfold prefixCost
  have hsplit : ∀ j : Fin m,
      (if j.val < i.val + 1 then regionCost r δ j η else 0)
        = (if j.val < i.val then regionCost r δ j η else 0)
          + (if j = i then regionCost r δ j η else 0) := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [if_pos (Nat.lt_succ_self _), if_neg (lt_irrefl _), if_pos rfl, zero_add]
    · have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      rw [if_neg hji, add_zero]
      by_cases hlt : j.val < i.val
      · rw [if_pos (Nat.lt_succ_of_lt hlt), if_pos hlt]
      · have : ¬ j.val < i.val + 1 := by omega
        rw [if_neg this, if_neg hlt]
  rw [Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' Finset.univ i]
  rw [if_pos (Finset.mem_univ i)]

/-- `C_m = ∑ i, c_i`: the full capacity of the additive cover. -/
theorem prefixCost_last {m : ℕ} (r : Fin m → Set (Link N)) (δ : Fin m → ℝ)
    (η : Polymer N) : prefixCost r δ m η
      = ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0 := by
  unfold prefixCost regionCost
  exact Finset.sum_congr rfl (fun i _ => if_pos i.isLt)

/-! ## 58-L.3 — the intermediate profiles -/

/-- `p_k`: on the polymers touching `R`, the truncated move of `a` towards `a′`
    with capacity `C_k`; elsewhere `a` (never read by the effective factor). -/
noncomputable def additiveProfile {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ) (k : ℕ) (η : Polymer N) : ℝ :=
  if typedTouchesSupport (N := N) η R then move (a η) (a' η) (prefixCost r δ k η) else a η

/-- `p_0 = a` as profiles. -/
theorem additiveProfile_zero {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ) : additiveProfile R r δ a a' 0 = a := by
  funext η
  unfold additiveProfile
  by_cases hR : typedTouchesSupport (N := N) η R
  · rw [if_pos hR, prefixCost_zero, move_zero]
  · rw [if_neg hR]

/-- Each `p_k` stays in `[0,1]`. -/
theorem additiveProfile_mem {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (k : ℕ) (η : Polymer N) :
    0 ≤ additiveProfile R r δ a a' k η ∧ additiveProfile R r δ a a' k η ≤ 1 := by
  unfold additiveProfile
  split_ifs
  · exact move_mem_Icc (prefixCost_nonneg r δ hδ0 k η) (h0 η) (h1 η) (h0' η) (h1' η)
  · exact ⟨h0 η, h1 η⟩

/-- The effective factor of `p_k`: the move on polymers touching `R`, `1` elsewhere. -/
theorem touchFactor_additiveProfile {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ) (k : ℕ) (η : Polymer N) :
    touchFactor R (additiveProfile R r δ a a' k) η
      = if typedTouchesSupport (N := N) η R
          then move (a η) (a' η) (prefixCost r δ k η) else 1 := by
  unfold touchFactor additiveProfile
  split_ifs <;> rfl

/-- **Step `i`, `hsame`**: outside `r i` the effective factors of `p_i` and
    `p_(i+1)` agree (the step cost is exactly zero there, whatever other
    regions the polymer touches). -/
theorem step_same {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ) (i : Fin m) :
    ∀ η, ¬ typedTouchesSupport (N := N) η (r i) →
      touchFactor R (additiveProfile R r δ a a' i.val) η
        = touchFactor R (additiveProfile R r δ a a' (i.val + 1)) η := by
  intro η hη
  rw [touchFactor_additiveProfile, touchFactor_additiveProfile,
    prefixCost_succ, regionCost_of_not_touch r δ i hη, add_zero]

/-- **Step `i`, `hδ`**: on `r i` the effective factors differ by at most `δ i`
    (increment bound of the move; both factors are `1` off `R`). -/
theorem step_bound {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (a a' : Polymer N → ℝ) (i : Fin m) :
    ∀ η, typedTouchesSupport (N := N) η (r i) →
      |touchFactor R (additiveProfile R r δ a a' i.val) η
        - touchFactor R (additiveProfile R r δ a a' (i.val + 1)) η| ≤ δ i := by
  intro η hη
  rw [touchFactor_additiveProfile, touchFactor_additiveProfile, prefixCost_succ,
    regionCost_of_touch r δ i hη]
  split_ifs with hR
  · rw [abs_sub_comm]
    exact abs_move_add_sub_move_le (a η) (a' η) _ (hδ0 i)
  · rw [sub_self, abs_zero]; exact hδ0 i

/-- **The last profile**: under the additive cover, `p_m` has the effective
    factors of `a′` (saturation of the move). Equality of EFFECTIVE factors only. -/
theorem touchFactor_additiveProfile_last {m : ℕ} (R : Set (Link N))
    (r : Fin m → Set (Link N)) (δ : Fin m → ℝ) (a a' : Polymer N → ℝ)
    (hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0)
    (η : Polymer N) :
    touchFactor R (additiveProfile R r δ a a' m) η = touchFactor R a' η := by
  rw [touchFactor_additiveProfile, prefixCost_last]
  have h := hadd η
  unfold touchFactor at h ⊢
  by_cases hR : typedTouchesSupport (N := N) η R
  · rw [if_pos hR, if_pos hR] at h
    rw [if_pos hR, if_pos hR]
    exact move_eq_of_abs_le h
  · rw [if_neg hR, if_neg hR]

/-! ## 58-L.4 — composition along an arbitrary chain of profiles -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **Chain estimate**: a finite sequence of profiles in `[0,1]`, starting at
    `a` (as profiles), ending with the effective factors of `a′`, whose step `i`
    satisfies the Stone 56 hypotheses with the region `r i` and the budget
    `δ i`. The Stone 56 two-term estimate at every step, the Stone 56 identity by
    equal effective factors at the last profile, finite telescoping (Stone 57
    `abs_telescope`), reorganization of the sum. The conclusion is written with
    `6 D_s/113` and `4 D_s/113`. `R` is kept in every profile and functional. -/
theorem abs_profileExpectation_sub_le_of_chain
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ} (p : ℕ → Polymer N → ℝ)
    (hp0 : ∀ k η, 0 ≤ p k η) (hp1 : ∀ k η, p k η ≤ 1)
    (hstart : p 0 = a)
    (hlast : ∀ η, touchFactor R (p m) η = touchFactor R a' η)
    (hsame : ∀ i : Fin m, ∀ η, ¬ typedTouchesSupport (N := N) η (r i) →
      touchFactor R (p i.val) η = touchFactor R (p (i.val + 1)) η)
    (hδ : ∀ i : Fin m, ∀ η, typedTouchesSupport (N := N) η (r i) →
      |touchFactor R (p i.val) η - touchFactor R (p (i.val + 1)) η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  set g : ℕ → ℝ := fun k => profileExpectation μm β χ f s R (p k) with hg
  have hg0 : g 0 = profileExpectation μm β χ f s R a := by
    simp only [hg, hstart]
  have hgm : g m = profileExpectation μm β χ f s R a' :=
    profileExpectation_eq_of_touchFactor_eq μm β χ f s R hlast
  have hstep : ∀ i : Fin m,
      |g i.val - g (i.val + 1)|
        ≤ δ i * Cf * Real.exp (-((n i : ℕ) : ℝ) / 2)
            * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
                + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
    intro i
    exact abs_profileExpectation_sub_profileExpectation_le_two_terms_localized
      μm hβ mχ hχabs hsmall R mf hCf (hsep i) (hδ0 i)
      (hp0 i.val) (hp1 i.val) (hp0 (i.val + 1)) (hp1 (i.val + 1)) (hsame i) (hδ i)
  have e1 : Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      = Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    congr 1; ring
  have e2 : Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      = Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    congr 1; ring
  calc |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      = |g 0 - g m| := by rw [hg0, hgm]
    _ ≤ ∑ j ∈ Finset.range m, |g j - g (j + 1)| :=
        ActivityProfileMultiRegion.abs_telescope g m
    _ = ∑ i : Fin m, |g i.val - g (i.val + 1)| :=
        Finset.sum_range (fun j => |g j - g (j + 1)|)
    _ ≤ ∑ i : Fin m, δ i * Cf * Real.exp (-((n i : ℕ) : ℝ) / 2)
            * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
                + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = _ := by
        rw [e1, e2, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## 58-L.5 — the Stone 57 cover implies the additive cover -/

/-- `hcover` (Stone 57) with `hδ0` gives `hadd`: a zero difference is below the
    non-negative sum; a non-zero difference is paid by the covering index, one
    term of the sum. -/
theorem additive_of_cover {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (hδ0 : ∀ i, 0 ≤ δ i) (a a' : Polymer N → ℝ)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0 := by
  intro η
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      0 ≤ (if typedTouchesSupport (N := N) η (r i) then δ i else 0) := by
    intro i _
    split_ifs
    · exact hδ0 i
    · exact le_rfl
  by_cases hne : touchFactor R a η = touchFactor R a' η
  · rw [hne, sub_self, abs_zero]
    exact Finset.sum_nonneg hnn
  · obtain ⟨i, hti, hbi⟩ := hcover η hne
    calc |touchFactor R a η - touchFactor R a' η| ≤ δ i := hbi
      _ = (if typedTouchesSupport (N := N) η (r i) then δ i else 0) := (if_pos hti).symm
      _ ≤ ∑ j : Fin m, if typedTouchesSupport (N := N) η (r j) then δ j else 0 :=
          Finset.single_le_sum hnn (Finset.mem_univ i)

end ActivityProfileAdditiveCover

/-! ## 58-L.6 — the public statements -/

open ActivityProfileAdditiveCover

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **TWO-TERM ESTIMATE, ADDITIVE COVER**: under `hadd`,
      |F_R(a) − F_R(a′)| ≤ Cf·[e^{6 D_s/113} + e^{4 D_s/113}]·∑ i, δ i·e^{−n i/2}.
    The intermediate profiles are the truncated moves with the prefix capacities;
    a polymer may move at several steps (E1). `m = 0` is admitted; the regions
    may overlap or repeat; `R` is arbitrary; no separation of `s` from `R`, no
    `r i ⊆ R`, no unit background, no `δ i ≤ 1`, no `DependsOnlyOn f s`; nothing
    divided by any budget, capacity or difference (E5); no factor of `m` outside
    the sum. The exponents are the Stone 56 ones, rewritten `6 D_s/113`, `4 D_s/113`. -/
theorem abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) :=
  abs_profileExpectation_sub_le_of_chain μm hβ mχ hχabs hsmall R mf hCf hδ0 hsep
    (additiveProfile R r δ a a')
    (fun k η => (additiveProfile_mem R r δ hδ0 h0 h1 h0' h1' k η).1)
    (fun k η => (additiveProfile_mem R r δ hδ0 h0 h1 h0' h1' k η).2)
    (additiveProfile_zero R r δ a a')
    (touchFactor_additiveProfile_last R r δ a a' hadd)
    (fun i => step_same R r δ a a' i)
    (fun i => step_bound R r δ hδ0 a a' i)

/-- **CAPSTONE 58 — STABILITY OF THE PROFILE-DAMPED FUNCTIONAL UNDER AN
    ADDITIVE COVER OF THE EFFECTIVE CHANGES BY SEVERAL REGIONS**: under `hadd`,
      |F_R(a) − F_R(a′)| ≤ (2 Cf)·e^{6 D_s/113}·∑ i, δ i·e^{−n i/2},
    exactly the constant, the rate and the regime of Stone 57, with the cover
    hypothesis widened from "one region pays each polymer" to "the regions a
    polymer touches share its cost". From the two-term estimate, `0 ≤ Cf`
    (derived), `B ≥ 0` and `e^{4 D_s/113} ≤ e^{6 D_s/113}` (`D_s ≥ 0`). The bound
    keeps `B`: no universal numerical improvement, optimal sum or optimal order
    of the steps is claimed (E2). -/
theorem abs_profileExpectation_sub_profileExpectation_le_additive_cover
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hB := ActivityProfileMultiRegion.budget_nonneg n δ hδ0
  have h2 := abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms
    μm hβ mχ hχabs hsmall R mf hCf hδ0 hsep h0 h1 h0' h1' hadd
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) := Nat.cast_nonneg _
  have hmono : Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      ≤ Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine le_trans h2 ?_
  calc Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2)
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_left _ hCf0
        exact add_le_add_left hmono _
    _ = _ := by ring

/-! ## 58-L.7 — recoveries -/

/-- **Stone 57 two terms recovered**: the Stone 57 cover gives the additive cover
    (`additive_of_cover`) and the additive estimate returns the Stone 57 statement.
    A recovery by specialization, not an independent proof of the chain 56–57. -/
theorem abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms_of_additive
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) :=
  abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms
    μm hβ mχ hχabs hsmall R mf hCf hδ0 hsep h0 h1 h0' h1'
    (additive_of_cover R r δ hδ0 a a' hcover)

/-- **Stone 57 capstone recovered** by the same specialization: the statement of
    `abs_profileExpectation_sub_profileExpectation_le_multiregion`, proved through
    the additive route (the published Stone 57 capstone is not used). -/
theorem abs_profileExpectation_sub_profileExpectation_le_multiregion_of_additive
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) :=
  abs_profileExpectation_sub_profileExpectation_le_additive_cover
    μm hβ mχ hχabs hsmall R mf hCf hδ0 hsep h0 h1 h0' h1'
    (additive_of_cover R r δ hδ0 a a' hcover)

/-- **One region recovers Stone 56**: the Stone 56 hypotheses `hsame`, `hδ` for
    one region `r` give the additive cover with `m = 1` (outside `r` the
    difference is `0`, on `r` it is at most `δ`), and the additive capstone
    returns the Stone 56 bound, the sum over `Fin 1` reducing to `δ·e^{−n/2}`.
    A compatibility test of the composition, not an independent proof of Stone 56. -/
theorem abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_additive
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin 1, if typedTouchesSupport (N := N) η ((fun _ => r) i)
          then (fun _ => δ) i else 0 := by
    intro η
    rw [Fin.sum_univ_one]
    by_cases ht : typedTouchesSupport (N := N) η r
    · rw [if_pos ht]; exact hδ η ht
    · rw [if_neg ht, hsame η ht, sub_self, abs_zero]
  have h := abs_profileExpectation_sub_profileExpectation_le_additive_cover μm hβ mχ hχabs hsmall
    R mf hCf (m := 1) (r := fun _ => r) (n := fun _ => n) (δ := fun _ => δ)
    (fun _ => hδ0) (fun _ => hsep) h0 h1 h0' h1' hadd
  rw [Fin.sum_univ_one] at h
  calc _ ≤ _ := h
    _ = _ := by ring

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **No region**: `m = 0` under the additive cover forces the equality of all
    effective factors (the empty sum is `0`), hence `F_R(a) = F_R(a′)` EXACTLY,
    for arbitrary real profiles and with no analytic hypothesis. -/
theorem profileExpectation_eq_of_additive_cover_empty_family
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {r : Fin 0 → Set (Link N)} {δ : Fin 0 → ℝ}
    {a a' : Polymer N → ℝ}
    (hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin 0, if typedTouchesSupport (N := N) η (r i) then δ i else 0) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' := by
  apply profileExpectation_eq_of_touchFactor_eq μm β χ f s R
  intro η
  have h := hadd η
  rw [Finset.univ_eq_empty, Finset.sum_empty] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Zero budgets**: `δ ≡ 0` under the additive cover forces equal effective
    factors, hence exact equality (the analytic bound would give `≤ 0`). -/
theorem profileExpectation_eq_of_additive_cover_zero_budget
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {m : ℕ} {r : Fin m → Set (Link N)}
    {a a' : Polymer N → ℝ}
    (hadd : ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
      ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then (0 : ℝ) else 0) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' := by
  apply profileExpectation_eq_of_touchFactor_eq μm β χ f s R
  intro η
  have h := hadd η
  rw [Finset.sum_eq_zero (fun i _ => by split_ifs <;> rfl)] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

/-! ## 58-L.8 — certificates -/

#print axioms ActivityProfileAdditiveCover.move
#print axioms ActivityProfileAdditiveCover.move_zero
#print axioms ActivityProfileAdditiveCover.move_self
#print axioms ActivityProfileAdditiveCover.move_mem
#print axioms ActivityProfileAdditiveCover.move_eq_of_abs_le
#print axioms ActivityProfileAdditiveCover.abs_move_add_sub_move_le
#print axioms ActivityProfileAdditiveCover.move_mem_Icc
#print axioms ActivityProfileAdditiveCover.regionCost
#print axioms ActivityProfileAdditiveCover.prefixCost
#print axioms ActivityProfileAdditiveCover.prefixCost_succ
#print axioms ActivityProfileAdditiveCover.prefixCost_last
#print axioms ActivityProfileAdditiveCover.additiveProfile
#print axioms ActivityProfileAdditiveCover.additiveProfile_zero
#print axioms ActivityProfileAdditiveCover.additiveProfile_mem
#print axioms ActivityProfileAdditiveCover.step_same
#print axioms ActivityProfileAdditiveCover.step_bound
#print axioms ActivityProfileAdditiveCover.touchFactor_additiveProfile_last
#print axioms ActivityProfileAdditiveCover.abs_profileExpectation_sub_le_of_chain
#print axioms ActivityProfileAdditiveCover.additive_of_cover
#print axioms abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms
#print axioms abs_profileExpectation_sub_profileExpectation_le_additive_cover
#print axioms abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms_of_additive
#print axioms abs_profileExpectation_sub_profileExpectation_le_multiregion_of_additive
#print axioms abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_additive
#print axioms profileExpectation_eq_of_additive_cover_empty_family
#print axioms profileExpectation_eq_of_additive_cover_zero_budget

end LatticeGauge
