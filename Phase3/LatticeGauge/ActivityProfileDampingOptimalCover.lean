/-
# Stone 59 — Optimal budget for a FIXED family of change regions: the minimal
# admissible cost of the additive cover, and the stability estimate at that cost

Scientific architecture: GPT Astra / Can (tape 59-AL, feasibility and
construction). Construction: Claude Fable 5.1 (Claude Code), promoted from the
feasibility file `T59A_optimal_cover_tests.lean` (gate 59-A), whose chain
elaborated unchanged. Base: commit 52cc0915547a13c0b738b0b506d572d00b011a12
(Version 58). The route was proposed by the coordination on paper and was
compiled in Lean by the constructing instance only.

## The question

Stone 58 accepts ANY non-negative budget vector `δ : Fin m → ℝ` that covers the
effective changes additively,

  hadd : ∀ η, |b(η) − b′(η)| ≤ ∑ i, if typedTouchesSupport η (r i) then δ i else 0,

and bounds `|F_R(a) − F_R(a′)|` by `(2 Cf)·e^{6 D_s/113}·B(δ)` with
`B(δ) = ∑ i, δ i · exp(−n i/2)`. For a FIXED family of regions `r` and scales `n`,
this module proves that an admissible budget of MINIMAL cost exists, defines
that minimal cost `B*`, and applies the Stone 58 estimate to it.

## The statement

Objects of Stones 55–58 are kept (`F_R`, `b`, `b′`, `D_s`). With

  Admissible δ := (∀ i, 0 ≤ δ i) ∧ hadd(δ),
  Reaches      := ∀ η, b(η) ≠ b′(η) → ∃ i, typedTouchesSupport η (r i),

for profiles `a, a′` with values in [0, 1]:

1. `Reaches ↔ ∃ δ, Admissible δ` (feasibility): the unit budget is admissible
   under reach, since every effective change is at most `1`; conversely an
   effective change without any contact has cover sum `0`.
2. `clip δ = min δ 1` keeps admissibility and does not increase the cost.
3. There is `δ*` with `Admissible δ*`, `∀ i, δ* i ≤ 1` and
   `∀ δ, Admissible δ → B(δ*) ≤ B(δ)` — the minimum is ATTAINED, and it is a
   minimum over ALL admissible budgets (no upper bound on those; `δ* ≤ 1` is a
   property of the chosen minimizer, not a hypothesis on the budgets of Stone 58).
4. `B* := B(δ*)` (the cost of an optimal budget, chosen classically; its type
   carries the feasibility conditions: reach and the interval). Under the
   analytic hypotheses of Stone 58 and reach,

     |F_R(a) − F_R(a′)| ≤ Cf · [e^{6 D_s/113} + e^{4 D_s/113}] · B*
                        ≤ (2 Cf) · e^{6 D_s/113} · B*.

5. `B* ≤ B(δ)` for every admissible `δ`, so both optimized bounds are ≤ the
   corresponding Stone 58 bounds, and both Stone 58 estimates are recovered.

Exactly the constant, the rate and the regime of Stones 57–58. Not required:
`m > 0`, disjoint regions, `r i ⊆ R`, a separation of `s` from `R`, a unit
background, a sign condition, `DependsOnlyOn f s`, a minimizer or a positive
capacity supplied by the user. `0 ≤ Cf` is derived. The optimization phase
(§§1–3) depends on the effective factors, the contacts and the weights only; it
carries no integration hypothesis and no `β`.

## The route (compactness, no algorithm)

- Interval: `0 ≤ b, b′ ≤ 1` and `|b − b′| ≤ 1` from the profiles; off `R` both
  factors are `1` even when the raw profiles differ.
- Truncation: for a fixed polymer, if some touched region has budget `≥ 1`, its
  truncated term is `1` and alone covers the change (`≤ 1`); otherwise every
  touched term is unchanged. Untouched budgets do not enter the sum.
- Compactness: `K = [0,1]^m ∩ {additive cover}`; the box is compact (also for
  `m = 0`), each cover constraint is closed (`|b(η) − b′(η)|` is constant in `δ`,
  the right-hand side a finite sum of continuous functions of the coordinates),
  so `K` is compact; `K` is non-empty under reach (the unit budget); the cost is
  continuous and attains its minimum on `K`; truncation promotes that minimum
  to a minimum over all admissible budgets. The unrestricted set of
  non-negative budgets is not claimed compact.
- Application: the published Stone 58 two-term estimate and capstone at the
  optimal budget; comparison with any admissible budget by `0 ≤ Cf` and the
  positivity of the exponentials.

## Interfaces and boundaries

`B* ≥ 0`; `B*` is the cost of ANY minimizer (the value is unique, the vector
need not be: two distinct minimizers of equal cost are exhibited in the tests);
`B* = 0 ↔ ∀ η, b(η) = b′(η)` (positive weights, a finite sum of non-negative
terms, the admissibility of the minimizer); effectively equal profiles have the
zero budget admissible, `B* = 0` and `F_R(a) = F_R(a′)`; `m = 0`: reach forces
equal effective factors, the cost of the empty family is `0` and the
functionals agree exactly, for arbitrary real profiles; `R = ∅`: all effective
factors are `1`, reach holds for any profiles and `B* = 0`.

## Limits

The optimization is over the budgets of a FIXED family and FIXED scales only:
regions, scales, the order of the steps, the universal constant, the volume
and the physics are not optimized. The existence is classical and provides no
algorithm or numerical solver; the minimizer is not claimed unique; the minimal
cost is a bound, not the actual deviation of the functional; the optimized
bound is not claimed strictly smaller than the Stone 58 bound for every budget
(it is ≤; a strict improvement against one particular budget is exhibited in
the tests). No linear-programming duality, metric between profiles, infinite
family, thermodynamic or continuum limit, new Gibbs measure, monotonicity of
the functional or mass gap is claimed; no bibliographic priority. Finite
volume, finite family, small-β regime.
-/

import Mathlib
import LatticeGauge.ActivityProfileDampingAdditiveCover

open MeasureTheory
open scoped Classical BigOperators

namespace LatticeGauge

namespace ActivityProfileOptimalCover

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 59-L.1 — budgets, admissibility, cost, reach -/

/-- The additive cover of Stone 58, as a predicate on the budget vector. -/
def AdditiveCover {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) (δ : Fin m → ℝ) : Prop :=
  ∀ η : Polymer N, |touchFactor R a η - touchFactor R a' η|
    ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0

/-- Admissible budgets: non-negative and covering additively. -/
def Admissible {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) (δ : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ δ i) ∧ AdditiveCover R r a a' δ

/-- The cost `B(δ) = ∑ i, δ i · exp(−n i/2)` of Stones 57–58. -/
noncomputable def budget {m : ℕ} (n : Fin m → ℕ) (δ : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2)

/-- Reach: every polymer whose effective factor changes touches some region.
    A cover of the effectively changed coordinates by contacts; no budget. -/
def Reaches {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) : Prop :=
  ∀ η : Polymer N, touchFactor R a η ≠ touchFactor R a' η →
    ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)

/-- Effective factors of profiles in `[0,1]` differ by at most `1`. -/
theorem abs_touchFactor_sub_le_one (R : Set (Link N)) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (η : Polymer N) : |touchFactor R a η - touchFactor R a' η| ≤ 1 := by
  have hb0 := touchFactor_nonneg R h0 η
  have hb1 := touchFactor_le_one R h1 η
  have hb0' := touchFactor_nonneg R h0' η
  have hb1' := touchFactor_le_one R h1' η
  rw [abs_le]
  constructor <;> linarith

theorem coverSum_nonneg {m : ℕ} (r : Fin m → Set (Link N)) {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i) (η : Polymer N) :
    0 ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0 := by
  refine Finset.sum_nonneg (fun i _ => ?_)
  split_ifs
  · exact hδ0 i
  · exact le_rfl

theorem budget_nonneg' {m : ℕ} (n : Fin m → ℕ) {δ : Fin m → ℝ} (hδ0 : ∀ i, 0 ≤ δ i) :
    0 ≤ budget n δ :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hδ0 i) (Real.exp_pos _).le)

/-! ## 59-L.2 — feasibility: reach ↔ an admissible budget exists -/

/-- Under reach, the unit budget is admissible (every effective change is ≤ 1). -/
theorem admissible_one_of_reaches {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') : Admissible R r a a' (fun _ => 1) := by
  refine ⟨fun _ => zero_le_one, fun η => ?_⟩
  by_cases hne : touchFactor R a η = touchFactor R a' η
  · rw [hne, sub_self, abs_zero]
    exact coverSum_nonneg r (fun _ => zero_le_one) η
  · obtain ⟨i, hi⟩ := hreach η hne
    calc |touchFactor R a η - touchFactor R a' η|
        ≤ 1 := abs_touchFactor_sub_le_one R h0 h1 h0' h1' η
      _ = (if typedTouchesSupport (N := N) η (r i) then (fun _ : Fin m => (1:ℝ)) i else 0) :=
          (if_pos hi).symm
      _ ≤ ∑ j : Fin m, if typedTouchesSupport (N := N) η (r j) then (fun _ : Fin m => (1:ℝ)) j else 0 :=
          Finset.single_le_sum
            (f := fun j : Fin m => if typedTouchesSupport (N := N) η (r j) then (fun _ : Fin m => (1:ℝ)) j else 0)
            (fun j _ => by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ i)

/-- Any admissible budget forces reach: a change without contact has sum `0`. -/
theorem reaches_of_admissible {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ} {δ : Fin m → ℝ} (h : Admissible R r a a' δ) :
    Reaches R r a a' := by
  intro η hne
  by_contra hno
  push_neg at hno
  have hsum : (∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0) = 0 :=
    Finset.sum_eq_zero (fun i _ => if_neg (hno i))
  have hc := h.2 η
  rw [hsum] at hc
  exact hne (sub_eq_zero.mp (abs_nonpos_iff.mp hc))

theorem reaches_iff_exists_admissible {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1) :
    Reaches R r a a' ↔ ∃ δ : Fin m → ℝ, Admissible R r a a' δ :=
  ⟨fun hreach => ⟨fun _ => 1, admissible_one_of_reaches R r h0 h1 h0' h1' hreach⟩,
   fun ⟨_, hδ⟩ => reaches_of_admissible R r hδ⟩

/-! ## 59-L.3 — truncation at 1 -/

/-- `clip δ i = min (δ i) 1`. -/
noncomputable def clip {m : ℕ} (δ : Fin m → ℝ) : Fin m → ℝ := fun i => min (δ i) 1

theorem clip_nonneg {m : ℕ} {δ : Fin m → ℝ} (hδ0 : ∀ i, 0 ≤ δ i) (i : Fin m) : 0 ≤ clip δ i :=
  le_min (hδ0 i) zero_le_one

theorem clip_le_one {m : ℕ} (δ : Fin m → ℝ) (i : Fin m) : clip δ i ≤ 1 := min_le_right _ _

theorem clip_le {m : ℕ} (δ : Fin m → ℝ) (i : Fin m) : clip δ i ≤ δ i := min_le_left _ _

/-- Truncation keeps admissibility: if a touched region has budget `≥ 1`, its
    truncated term `1` alone covers the change (`≤ 1`); otherwise every touched
    term is unchanged. Budgets of untouched regions do not enter the sum. -/
theorem admissible_clip {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    {δ : Fin m → ℝ} (h : Admissible R r a a' δ) : Admissible R r a a' (clip δ) := by
  refine ⟨clip_nonneg h.1, fun η => ?_⟩
  by_cases hex : ∃ i, typedTouchesSupport (N := N) η (r i) ∧ 1 ≤ δ i
  · obtain ⟨i, hi, hδi⟩ := hex
    calc |touchFactor R a η - touchFactor R a' η|
        ≤ 1 := abs_touchFactor_sub_le_one R h0 h1 h0' h1' η
      _ = (if typedTouchesSupport (N := N) η (r i) then clip δ i else 0) := by
          rw [if_pos hi]; unfold clip; rw [min_eq_right hδi]
      _ ≤ ∑ j : Fin m, if typedTouchesSupport (N := N) η (r j) then clip δ j else 0 :=
          Finset.single_le_sum
            (f := fun j : Fin m => if typedTouchesSupport (N := N) η (r j) then clip δ j else 0)
            (fun j _ => by
              dsimp only
              split_ifs
              · exact clip_nonneg h.1 j
              · exact le_rfl) (Finset.mem_univ i)
  · push_neg at hex
    have heq : (∑ j : Fin m, if typedTouchesSupport (N := N) η (r j) then clip δ j else 0)
        = ∑ j : Fin m, if typedTouchesSupport (N := N) η (r j) then δ j else 0 := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases ht : typedTouchesSupport (N := N) η (r j)
      · rw [if_pos ht, if_pos ht]; unfold clip; exact min_eq_left (le_of_lt (hex j ht))
      · rw [if_neg ht, if_neg ht]
    rw [heq]
    exact h.2 η

/-- Truncation does not increase the cost (positive weights). -/
theorem budget_clip_le {m : ℕ} (n : Fin m → ℕ) (δ : Fin m → ℝ) :
    budget n (clip δ) ≤ budget n δ :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (clip_le δ i) (Real.exp_pos _).le)

/-! ## 59-L.4 — compactness and continuity -/

/-- `K = [0,1]^m ∩ {additive cover}`. -/
def feasibleBox {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) : Set (Fin m → ℝ) :=
  Set.Icc (0 : Fin m → ℝ) 1 ∩ {δ | AdditiveCover R r a a' δ}

theorem isClosed_additiveCover {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) : _root_.IsClosed {δ : Fin m → ℝ | AdditiveCover R r a a' δ} := by
  have hset : {δ : Fin m → ℝ | AdditiveCover R r a a' δ}
      = ⋂ η : Polymer N, {δ : Fin m → ℝ | |touchFactor R a η - touchFactor R a' η|
          ≤ ∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δ i else 0} := by
    ext δ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, AdditiveCover]
  rw [hset]
  refine isClosed_iInter (fun η => ?_)
  refine isClosed_le continuous_const ?_
  refine continuous_finset_sum _ (fun i _ => ?_)
  by_cases ht : typedTouchesSupport (N := N) η (r i)
  · simp only [if_pos ht]; exact continuous_apply i
  · simp only [if_neg ht]; exact continuous_const

theorem isCompact_feasibleBox {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (a a' : Polymer N → ℝ) : IsCompact (feasibleBox R r a a') :=
  (isCompact_Icc : IsCompact (Set.Icc (0 : Fin m → ℝ) 1)).inter_right
    (isClosed_additiveCover R r a a')

theorem feasibleBox_nonempty {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') : (feasibleBox R r a a').Nonempty :=
  ⟨fun _ => 1, ⟨Set.mem_Icc.mpr ⟨fun i => by simp, fun i => le_rfl⟩,
    (admissible_one_of_reaches R r h0 h1 h0' h1' hreach).2⟩⟩

theorem continuous_budget {m : ℕ} (n : Fin m → ℕ) : Continuous (budget n) :=
  continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)

/-! ## 59-L.5 — the minimum is attained, over ALL admissible budgets -/

/-- **Existence of an optimal budget**: under reach and profiles in `[0,1]`, an
    admissible budget with every coordinate `≤ 1` whose cost is minimal among
    ALL admissible budgets (no upper bound on those). Compactness of
    `[0,1]^m ∩ {cover}`, continuity of the cost, and truncation to promote the
    minimum on the box to a global one. -/
theorem exists_optimal {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') :
    ∃ δs : Fin m → ℝ, Admissible R r a a' δs ∧ (∀ i, δs i ≤ 1)
      ∧ ∀ δ : Fin m → ℝ, Admissible R r a a' δ → budget n δs ≤ budget n δ := by
  obtain ⟨δs, hδs, hmin⟩ := (isCompact_feasibleBox R r a a').exists_isMinOn
    (feasibleBox_nonempty R r h0 h1 h0' h1' hreach) (continuous_budget n).continuousOn
  have hbox := Set.mem_Icc.mp hδs.1
  refine ⟨δs, ⟨fun i => by simpa using hbox.1 i, hδs.2⟩, fun i => hbox.2 i, fun δ hδ => ?_⟩
  have hclip : clip δ ∈ feasibleBox R r a a' :=
    ⟨Set.mem_Icc.mpr ⟨fun i => by simpa using clip_nonneg hδ.1 i, fun i => clip_le_one δ i⟩,
      (admissible_clip R r h0 h1 h0' h1' hδ).2⟩
  exact le_trans (isMinOn_iff.mp hmin _ hclip) (budget_clip_le n δ)

/-- An optimal budget, chosen classically from `exists_optimal`. Its type carries
    the conditions that guarantee feasibility (reach and the interval). -/
noncomputable def optimalBudget {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') : Fin m → ℝ :=
  Classical.choose (exists_optimal R r n h0 h1 h0' h1' hreach)

/-- **The minimal cost `B*`**: the cost of an optimal budget. No algorithm is
    provided; the minimizer need not be unique, the value is. -/
noncomputable def minCost {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') : ℝ :=
  budget n (optimalBudget R r n h0 h1 h0' h1' hreach)

theorem optimalBudget_admissible {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') :
    Admissible R r a a' (optimalBudget R r n h0 h1 h0' h1' hreach) :=
  (Classical.choose_spec (exists_optimal R r n h0 h1 h0' h1' hreach)).1

theorem optimalBudget_le_one {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') (i : Fin m) :
    optimalBudget R r n h0 h1 h0' h1' hreach i ≤ 1 :=
  (Classical.choose_spec (exists_optimal R r n h0 h1 h0' h1' hreach)).2.1 i

/-- `B* ≤ B(δ)` for EVERY admissible budget `δ`. -/
theorem minCost_le_budget {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') {δ : Fin m → ℝ} (hδ : Admissible R r a a' δ) :
    minCost R r n h0 h1 h0' h1' hreach ≤ budget n δ :=
  (Classical.choose_spec (exists_optimal R r n h0 h1 h0' h1' hreach)).2.2 δ hδ

theorem minCost_nonneg {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') : 0 ≤ minCost R r n h0 h1 h0' h1' hreach :=
  budget_nonneg' n (optimalBudget_admissible R r n h0 h1 h0' h1' hreach).1

/-- Two minimizers have the same cost (the VALUE is unique, the vector need not be). -/
theorem budget_eq_of_isMin {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ} {δ₁ δ₂ : Fin m → ℝ}
    (h₁ : Admissible R r a a' δ₁) (h₂ : Admissible R r a a' δ₂)
    (hmin₁ : ∀ δ, Admissible R r a a' δ → budget n δ₁ ≤ budget n δ)
    (hmin₂ : ∀ δ, Admissible R r a a' δ → budget n δ₂ ≤ budget n δ) :
    budget n δ₁ = budget n δ₂ :=
  le_antisymm (hmin₁ δ₂ h₂) (hmin₂ δ₁ h₁)

/-- `B*` is the cost of ANY minimizer: independent of the classical choice. -/
theorem minCost_eq_budget_of_isMin {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') {δ : Fin m → ℝ} (hδ : Admissible R r a a' δ)
    (hmin : ∀ δ', Admissible R r a a' δ' → budget n δ ≤ budget n δ') :
    minCost R r n h0 h1 h0' h1' hreach = budget n δ :=
  budget_eq_of_isMin R r n (optimalBudget_admissible R r n h0 h1 h0' h1' hreach) hδ
    (fun _ hδ' => minCost_le_budget R r n h0 h1 h0' h1' hreach hδ') hmin

/-! ## 59-L.6 — the zero cost and the degenerate families -/

/-- Equal effective factors make the zero budget admissible. -/
theorem admissible_zero_of_touchFactor_eq {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    {a a' : Polymer N → ℝ} (hb : ∀ η, touchFactor R a η = touchFactor R a' η) :
    Admissible R r a a' (fun _ => 0) := by
  refine ⟨fun _ => le_rfl, fun η => ?_⟩
  rw [hb η, sub_self, abs_zero]
  exact coverSum_nonneg r (fun _ => le_rfl) η

theorem budget_zero {m : ℕ} (n : Fin m → ℕ) : budget n (fun _ => 0) = 0 := by
  unfold budget; simp

/-- **`B* = 0` iff all effective factors coincide** (under the feasibility
    conditions carried by `minCost`). The weights `exp(−n i/2)` are positive, so a
    zero cost forces every optimal budget to vanish and the cover then forces
    equality; conversely the zero budget is admissible with cost `0`. -/
theorem minCost_eq_zero_iff {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (n : Fin m → ℕ) {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') :
    minCost R r n h0 h1 h0' h1' hreach = 0 ↔ ∀ η, touchFactor R a η = touchFactor R a' η := by
  constructor
  · intro hz η
    set δs := optimalBudget R r n h0 h1 h0' h1' hreach with hδs
    have hadm := optimalBudget_admissible R r n h0 h1 h0' h1' hreach
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ δs i * Real.exp (-((n i : ℕ) : ℝ) / 2) :=
      fun i _ => mul_nonneg (hadm.1 i) (Real.exp_pos _).le
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hz
    have hzero : ∀ i, δs i = 0 := by
      intro i
      have := hall i (Finset.mem_univ i)
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    have hc := hadm.2 η
    have hsum : (∑ i : Fin m, if typedTouchesSupport (N := N) η (r i) then δs i else 0) = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hzero i]; split_ifs <;> rfl)
    rw [hsum] at hc
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hc)
  · intro hb
    apply le_antisymm
    · calc minCost R r n h0 h1 h0' h1' hreach
          ≤ budget n (fun _ => 0) :=
            minCost_le_budget R r n h0 h1 h0' h1' hreach (admissible_zero_of_touchFactor_eq R r hb)
        _ = 0 := budget_zero n
    · exact minCost_nonneg R r n h0 h1 h0' h1' hreach

/-- `m = 0`: reach forces equal effective factors (there is no region). -/
theorem touchFactor_eq_of_reaches_fin_zero (R : Set (Link N)) {r : Fin 0 → Set (Link N)}
    {a a' : Polymer N → ℝ} (hreach : Reaches R r a a') :
    ∀ η, touchFactor R a η = touchFactor R a' η := by
  intro η
  by_contra hne
  obtain ⟨i, _⟩ := hreach η hne
  exact i.elim0

theorem budget_fin_zero (n : Fin 0 → ℕ) (δ : Fin 0 → ℝ) : budget n δ = 0 := by
  unfold budget; simp

/-- `R = ∅`: every effective factor is `1`, so reach holds for any profiles. -/
theorem reaches_empty_region {m : ℕ} (r : Fin m → Set (Link N)) (a a' : Polymer N → ℝ) :
    Reaches (∅ : Set (Link N)) r a a' := by
  intro η hne
  exfalso
  apply hne
  have hn : ¬ typedTouchesSupport (N := N) η (∅ : Set (Link N)) := not_blockTouchesSupport_empty η.val
  unfold touchFactor
  rw [if_neg hn, if_neg hn]

end ActivityProfileOptimalCover

/-! ## 59-L.7 — the public statements -/

open ActivityProfileOptimalCover

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **TWO-TERM ESTIMATE WITH THE OPTIMAL BUDGET**: under reach, the Stone 58
    two-term estimate applied to an optimal budget. -/
theorem abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms
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
  abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms μm hβ mχ hχabs hsmall
    R mf hCf (optimalBudget_admissible R r n h0 h1 h0' h1' hreach).1 hsep h0 h1 h0' h1'
    (optimalBudget_admissible R r n h0 h1 h0' h1' hreach).2

/-- **CAPSTONE 59 — STABILITY WITH THE MINIMAL ADMISSIBLE COST**: under reach,
      |F_R(a) − F_R(a′)| ≤ (2 Cf)·e^{6 D_s/113}·B*,
    `B*` the minimal cost over all admissible budgets of the fixed family. -/
theorem abs_profileExpectation_sub_profileExpectation_le_optimal_cover
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
  abs_profileExpectation_sub_profileExpectation_le_additive_cover μm hβ mχ hχabs hsmall
    R mf hCf (optimalBudget_admissible R r n h0 h1 h0' h1' hreach).1 hsep h0 h1 h0' h1'
    (optimalBudget_admissible R r n h0 h1 h0' h1' hreach).2

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
/-- **The optimized two-term bound is ≤ the Stone 58 two-term bound** for every
    admissible budget (`0 ≤ Cf` derived, positive exponentials, `B* ≤ B(δ)`). -/
theorem optimal_two_terms_le_additive_two_terms
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') {δ : Fin m → ℝ} (hδ : Admissible R r a a' δ) :
    Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * minCost R r n h0 h1 h0' h1' hreach
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * budget n δ := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  apply mul_le_mul_of_nonneg_left (minCost_le_budget R r n h0 h1 h0' h1' hreach hδ)
  exact mul_nonneg hCf0 (add_pos (Real.exp_pos _) (Real.exp_pos _)).le

omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] in
theorem optimal_compact_le_additive_compact
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} (r : Fin m → Set (Link N)) (n : Fin m → ℕ)
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') {δ : Fin m → ℝ} (hδ : Admissible R r a a' δ) :
    (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * minCost R r n h0 h1 h0' h1' hreach
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * budget n δ := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  apply mul_le_mul_of_nonneg_left (minCost_le_budget R r n h0 h1 h0' h1' hreach hδ)
  exact mul_nonneg (by linarith) (Real.exp_pos _).le

/-- **Stone 58 two terms recovered** for any admissible budget (reach follows
    from admissibility; `B* ≤ B(δ)`). -/
theorem abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms_of_optimal
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
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  have hδ : Admissible R r a a' δ := ⟨hδ0, hadd⟩
  have hreach := reaches_of_admissible R r hδ
  calc _ ≤ _ := abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms μm hβ mχ
        hχabs hsmall R mf hCf hsep h0 h1 h0' h1' hreach
    _ ≤ _ := optimal_two_terms_le_additive_two_terms R hCf r n h0 h1 h0' h1' hreach hδ

/-- **Stone 58 capstone recovered** for any admissible budget. -/
theorem abs_profileExpectation_sub_profileExpectation_le_additive_cover_of_optimal
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
  have hδ : Admissible R r a a' δ := ⟨hδ0, hadd⟩
  have hreach := reaches_of_admissible R r hδ
  calc _ ≤ _ := abs_profileExpectation_sub_profileExpectation_le_optimal_cover μm hβ mχ
        hχabs hsmall R mf hCf hsep h0 h1 h0' h1' hreach
    _ ≤ _ := optimal_compact_le_additive_compact R hCf r n h0 h1 h0' h1' hreach hδ

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Zero minimal cost gives exact equality** of the functionals (no analytic
    hypothesis beyond those carried by `minCost`). -/
theorem profileExpectation_eq_of_minCost_eq_zero (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {m : ℕ} {r : Fin m → Set (Link N)} (n : Fin m → ℕ)
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hreach : Reaches R r a a') (hz : minCost R r n h0 h1 h0' h1' hreach = 0) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' :=
  profileExpectation_eq_of_touchFactor_eq μm β χ f s R
    ((minCost_eq_zero_iff R r n h0 h1 h0' h1' hreach).mp hz)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **No region**: `m = 0` under reach forces equal effective factors, hence exact
    equality, for arbitrary real profiles; the cost of the empty family is `0`. -/
theorem profileExpectation_eq_of_reaches_fin_zero (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {r : Fin 0 → Set (Link N)} {a a' : Polymer N → ℝ}
    (hreach : Reaches R r a a') :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' :=
  profileExpectation_eq_of_touchFactor_eq μm β χ f s R
    (touchFactor_eq_of_reaches_fin_zero R hreach)

/-! ## 59-L.8 — certificates -/

#print axioms ActivityProfileOptimalCover.AdditiveCover
#print axioms ActivityProfileOptimalCover.Admissible
#print axioms ActivityProfileOptimalCover.budget
#print axioms ActivityProfileOptimalCover.Reaches
#print axioms ActivityProfileOptimalCover.clip
#print axioms ActivityProfileOptimalCover.feasibleBox
#print axioms ActivityProfileOptimalCover.optimalBudget
#print axioms ActivityProfileOptimalCover.minCost
#print axioms ActivityProfileOptimalCover.abs_touchFactor_sub_le_one
#print axioms ActivityProfileOptimalCover.coverSum_nonneg
#print axioms ActivityProfileOptimalCover.budget_nonneg'
#print axioms ActivityProfileOptimalCover.admissible_one_of_reaches
#print axioms ActivityProfileOptimalCover.reaches_of_admissible
#print axioms ActivityProfileOptimalCover.reaches_iff_exists_admissible
#print axioms ActivityProfileOptimalCover.clip_nonneg
#print axioms ActivityProfileOptimalCover.clip_le_one
#print axioms ActivityProfileOptimalCover.clip_le
#print axioms ActivityProfileOptimalCover.admissible_clip
#print axioms ActivityProfileOptimalCover.budget_clip_le
#print axioms ActivityProfileOptimalCover.isClosed_additiveCover
#print axioms ActivityProfileOptimalCover.isCompact_feasibleBox
#print axioms ActivityProfileOptimalCover.feasibleBox_nonempty
#print axioms ActivityProfileOptimalCover.continuous_budget
#print axioms ActivityProfileOptimalCover.exists_optimal
#print axioms ActivityProfileOptimalCover.optimalBudget_admissible
#print axioms ActivityProfileOptimalCover.optimalBudget_le_one
#print axioms ActivityProfileOptimalCover.minCost_le_budget
#print axioms ActivityProfileOptimalCover.minCost_nonneg
#print axioms ActivityProfileOptimalCover.budget_eq_of_isMin
#print axioms ActivityProfileOptimalCover.minCost_eq_budget_of_isMin
#print axioms ActivityProfileOptimalCover.admissible_zero_of_touchFactor_eq
#print axioms ActivityProfileOptimalCover.budget_zero
#print axioms ActivityProfileOptimalCover.minCost_eq_zero_iff
#print axioms ActivityProfileOptimalCover.touchFactor_eq_of_reaches_fin_zero
#print axioms ActivityProfileOptimalCover.budget_fin_zero
#print axioms ActivityProfileOptimalCover.reaches_empty_region
#print axioms abs_profileExpectation_sub_profileExpectation_le_optimal_cover_two_terms
#print axioms abs_profileExpectation_sub_profileExpectation_le_optimal_cover
#print axioms optimal_two_terms_le_additive_two_terms
#print axioms optimal_compact_le_additive_compact
#print axioms abs_profileExpectation_sub_profileExpectation_le_additive_cover_two_terms_of_optimal
#print axioms abs_profileExpectation_sub_profileExpectation_le_additive_cover_of_optimal
#print axioms profileExpectation_eq_of_minCost_eq_zero
#print axioms profileExpectation_eq_of_reaches_fin_zero

end LatticeGauge
