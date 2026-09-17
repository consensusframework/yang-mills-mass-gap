/-
LatticeGauge/ActivityProfileDamping.lean — PEDRA 55,
Gate 55-A: REMOTE ACTIVITY DAMPING WITH A PROFILE OF FACTORS PER POLYMER —
OBJECTS, WEIGHTS, REPRESENTATION AND THE TWO-PROFILE LEDGER
(architecture and review: GPT Astra; feasibility and execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): Stones 52–54 damp the
activity of every polymer touching a remote region r by ONE scalar
θ ∈ [0, 1]. Stone 55 replaces the scalar by a PROFILE a : Polymer N → ℝ,
one factor per polymer:
    z_a(γ) = a(γ)·z(γ)   if γ touches r,      z_a(γ) = z(γ)   otherwise
(`profileDampedActivity`; the values of a outside r are never read — the
remote character is built into the definition, no side hypothesis).
Everything below is a finite-volume polymer gas or a NORMALIZED POLYMER
FUNCTIONAL of the profile-damped activity, exactly as in Stone 52: no
Gibbs measure, boundary condition, modified action, per-link profile or
physical switch-off is constructed or claimed.

Where Stone 52 has the count weight θ^{touchCount r Γ}, Stone 55 has the
PRODUCT weight A_Γ = ∏_{γ ∈ Γ} touchFactor r a γ (= ∏ over the members
touching r of a(γ); tuples: positions counted, repetitions included).
The scalar case is the constant profile: `profileDampedActivity z r
(fun _ => θ) = dampedActivity z r θ` holds by `rfl`, and the weights
reduce to the powers by `Finset.prod_ite`. This gate builds:
  * the profile-damped activity, the family and tuple weights, and the
    constant-profile specializations (definitional identities);
  * domination |z_a| ≤ |z| for 0 ≤ a ≤ 1 and the KP transport
    (`abstractKP_mono`, Stone 46/50 not redone);
  * the literal weight identities ∏ z_a = A_Γ·∏ z (families and tuples),
    0 ≤ A_Γ ≤ 1, A_Γ = 1 on families avoiding r;
  * THE TELESCOPING PRODUCT LEMMA in [0,1]: |∏ x_i − ∏ y_i| ≤ Σ |x_i − y_i|,
    hence |A_Γ − A′_Γ| ≤ touchCount r Γ·δ and, for tuples,
    |A_δ − A′_δ| ≤ tupleTouchCount r δ·δ ≤ k·δ whenever
    |a(γ) − a′(γ)| ≤ δ on the polymers touching r — the profile analogue
    of |θ^j − θ′^j| ≤ j·|θ − θ′|, which is recovered as a corollary;
  * the profile gases, the normalized functional and the profile core
    exponent E_T(a); gas = exp(cluster sum) > 0 (KP as OUTPUT), the ratio
    identity, and |E_T(a)| ≤ b_T·(2/113) (the κ = 1 cost, route 53-A);
  * the fibering of the marked gas over touching cores (the 52-A.F proof
    with the product split in place of the count split), the exponential
    form F(a) = Σ_T A_T·W_T·e^{E_T(a)}, and THE EXACT TWO-PROFILE LEDGER
      F(a) − F(a′) = Σ_{T touching} A′_T·W_T·(e^{E_T(a)} − e^{E_T(a′)})
                   + Σ_{T bridge}   (A_T − A′_T)·W_T·e^{E_T(a)},
    an identity with no hypothesis on f;
  * the exact endpoints: constant profiles give the Stone 52 objects, the
    unit profile the original activity (and Gibbs under `DependsOnlyOn`),
    the zero profile the Stone 51 restricted activity and functional,
    r = ∅ makes every profile trivial (F(a) = F(a′) for all real profiles).

HARD HOLD (not here): the profile connector, its erosion, the
exponential control, the column bounds, the capstone and the endpoints
with bounds (55-B); any Disjoint s r, size restriction on r or volume
factor; per-link profiles; monotonicity or differentiability in the
profile; Gibbs-measure, boundary-condition or modified-action
interpretations; thermodynamic limit, continuum, mass gap. No
project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityDampingLipschitzRefined

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 55-A.1 — the profile-damped activity and the profile weights -/

/-- The pointwise factor of a profile: a γ on the polymers touching r,
    1 elsewhere (the values of a outside r are never read). -/
noncomputable def touchFactor (r : Set (Link N)) (a : Polymer N → ℝ)
    (η : Polymer N) : ℝ :=
  if typedTouchesSupport (N := N) η r then a η else 1

/-- **Remote activity damping by a profile**: the activity of a polymer
    touching r is multiplied by its own factor a η; the activity of a
    polymer avoiding r is kept. TOTAL in a; the semantic interval
    0 ≤ a ≤ 1 enters only the quantitative theorems. -/
noncomputable def profileDampedActivity (z : Polymer N → ℝ) (r : Set (Link N))
    (a : Polymer N → ℝ) : Polymer N → ℝ :=
  fun η => if typedTouchesSupport (N := N) η r then a η * z η else z η

/-- The family weight A_Γ = ∏_{η ∈ Γ} touchFactor r a η. -/
noncomputable def profileWeight (r : Set (Link N)) (a : Polymer N → ℝ)
    (Γ : Finset (Polymer N)) : ℝ :=
  ∏ η ∈ Γ, touchFactor r a η

/-- The tuple weight (positions counted, repetitions included). -/
noncomputable def tupleProfileWeight (r : Set (Link N)) (a : Polymer N → ℝ)
    {k : ℕ} (δ : Fin k → Polymer N) : ℝ :=
  ∏ i : Fin k, touchFactor r a (δ i)

/-! ## 55-A.2 — the constant profile IS the Stone 52 damping (definitional) -/

/-- **Constant profile = scalar damping**, an identity of definitions. -/
theorem profileDampedActivity_const (z : Polymer N → ℝ) (r : Set (Link N)) (θ : ℝ) :
    profileDampedActivity z r (fun _ => θ) = dampedActivity z r θ := rfl

/-- The family weight of the constant profile is the count power. -/
theorem profileWeight_const (r : Set (Link N)) (θ : ℝ) (Γ : Finset (Polymer N)) :
    profileWeight r (fun _ => θ) Γ = θ ^ touchCount r Γ := by
  unfold profileWeight touchFactor touchCount
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- The tuple weight of the constant profile is the position-count power. -/
theorem tupleProfileWeight_const (r : Set (Link N)) (θ : ℝ) {k : ℕ}
    (δ : Fin k → Polymer N) :
    tupleProfileWeight r (fun _ => θ) δ = θ ^ tupleTouchCount r δ := by
  unfold tupleProfileWeight touchFactor tupleTouchCount
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

/-- **Unit profile**: the original activity (through `dampedActivity_one`). -/
theorem profileDampedActivity_one (z : Polymer N → ℝ) (r : Set (Link N)) :
    profileDampedActivity z r (fun _ => 1) = z :=
  dampedActivity_one z r

/-- **Zero profile**: the Stone 51 restricted activity (through
    `dampedActivity_zero`). -/
theorem profileDampedActivity_zero (z : Polymer N → ℝ) (r : Set (Link N)) :
    profileDampedActivity z r (fun _ => 0)
      = restrictedActivity z (regionAllowed (N := N) r) :=
  dampedActivity_zero z r

/-- **Empty remote region**: no polymer touches ∅, every profile is trivial. -/
theorem profileDampedActivity_empty_region (z : Polymer N → ℝ) (a : Polymer N → ℝ) :
    profileDampedActivity (N := N) z (∅ : Set (Link N)) a = z := by
  funext η
  unfold profileDampedActivity
  exact if_neg (not_blockTouchesSupport_empty η.val)

/-! ## 55-A.3 — domination and KP transport -/

/-- **Domination**: for 0 ≤ a ≤ 1, |z_a| ≤ |z| pointwise. -/
theorem abs_profileDampedActivity_le (z : Polymer N → ℝ) (r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (η : Polymer N) :
    |profileDampedActivity z r a η| ≤ |z η| := by
  unfold profileDampedActivity
  split_ifs with h
  · rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    rw [abs_of_nonneg (h0 η)]
    exact h1 η
  · exact le_rfl

/-- **KP transport**: for 0 ≤ a ≤ 1 the profile-damped activity inherits
    the abstract KP hypothesis by monotonicity (Stone 46/50 not redone). -/
theorem abstractKP_profileDampedActivity {z c : Polymer N → ℝ} (r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) c) :
    AbstractKPHypothesis (N := N) (fun η => |profileDampedActivity z r a η|) c :=
  abstractKP_mono (fun η => abs_profileDampedActivity_le z r h0 h1 η)
    (fun _ => abs_nonneg _) hKP

/-! ## 55-A.4 — the literal weight identities -/

/-- **THE LITERAL WEIGHT IDENTITY (families)**: ∏ z_a = A_Γ · ∏ z. -/
theorem prod_profileDampedActivity (z : Polymer N → ℝ) (r : Set (Link N))
    (a : Polymer N → ℝ) (Γ : Finset (Polymer N)) :
    (∏ η ∈ Γ, profileDampedActivity z r a η)
      = profileWeight r a Γ * ∏ η ∈ Γ, z η := by
  unfold profileWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun η _ => ?_)
  unfold profileDampedActivity touchFactor
  split_ifs <;> simp

/-- **THE LITERAL WEIGHT IDENTITY (tuples, multiplicities kept)**. -/
theorem prod_profileDampedActivity_tuple (z : Polymer N → ℝ) (r : Set (Link N))
    (a : Polymer N → ℝ) {k : ℕ} (δ : Fin k → Polymer N) :
    (∏ i : Fin k, profileDampedActivity z r a (δ i))
      = tupleProfileWeight r a δ * ∏ i : Fin k, z (δ i) := by
  unfold tupleProfileWeight
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold profileDampedActivity touchFactor
  split_ifs <;> simp

theorem touchFactor_nonneg (r : Set (Link N)) {a : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (η : Polymer N) : 0 ≤ touchFactor r a η := by
  unfold touchFactor
  split_ifs with h
  · exact h0 η
  · exact zero_le_one

theorem touchFactor_le_one (r : Set (Link N)) {a : Polymer N → ℝ}
    (h1 : ∀ η, a η ≤ 1) (η : Polymer N) : touchFactor r a η ≤ 1 := by
  unfold touchFactor
  split_ifs with h
  · exact h1 η
  · exact le_rfl

theorem profileWeight_nonneg (r : Set (Link N)) {a : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (Γ : Finset (Polymer N)) : 0 ≤ profileWeight r a Γ :=
  Finset.prod_nonneg (fun η _ => touchFactor_nonneg r h0 η)

theorem profileWeight_le_one (r : Set (Link N)) {a : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (Γ : Finset (Polymer N)) :
    profileWeight r a Γ ≤ 1 :=
  Finset.prod_le_one (fun η _ => touchFactor_nonneg r h0 η)
    (fun η _ => touchFactor_le_one r h1 η)

/-- Weight 1 on families avoiding r (whatever the profile). -/
theorem profileWeight_eq_one_of_touchCount_zero (r : Set (Link N)) (a : Polymer N → ℝ)
    {Γ : Finset (Polymer N)} (h : touchCount r Γ = 0) : profileWeight r a Γ = 1 := by
  have hall := (touchCount_eq_zero_iff r Γ).mp h
  unfold profileWeight
  refine Finset.prod_eq_one (fun η hη => ?_)
  unfold touchFactor
  exact if_neg (regionAllowed_iff.mp (hall η hη))

/-- Weight 1 on region-allowed cores. -/
theorem profileWeight_eq_one_of_mem_activityAllowedCores {s r : Set (Link N)}
    (a : Polymer N → ℝ) {T : Finset (Polymer N)}
    (hT : T ∈ activityAllowedCores (N := N) s r) : profileWeight r a T = 1 :=
  profileWeight_eq_one_of_touchCount_zero r a
    ((touchCount_eq_zero_iff r T).mpr (mem_activityAllowedCores.mp hT).2)

/-- Tuple weight 1 on tuples avoiding r. -/
theorem tupleProfileWeight_eq_one_of_tupleTouchCount_zero (r : Set (Link N))
    (a : Polymer N → ℝ) {k : ℕ} {δ : Fin k → Polymer N} (h : tupleTouchCount r δ = 0) :
    tupleProfileWeight r a δ = 1 := by
  have hall := (tupleTouchCount_eq_zero_iff r δ).mp h
  unfold tupleProfileWeight
  refine Finset.prod_eq_one (fun i _ => ?_)
  unfold touchFactor
  exact if_neg (regionAllowed_iff.mp (hall i))

/-- **Empty remote region**: every family weight is 1. -/
theorem profileWeight_empty_region (a : Polymer N → ℝ) (Γ : Finset (Polymer N)) :
    profileWeight (N := N) (∅ : Set (Link N)) a Γ = 1 :=
  profileWeight_eq_one_of_touchCount_zero (∅ : Set (Link N)) a (touchCount_empty_region Γ)

/-! ## 55-A.5 — the telescoping product lemma in [0,1] and the count bounds -/

/-- **TELESCOPING DIFFERENCE OF PRODUCTS**: for factors in [0,1],
    |∏ x_i − ∏ y_i| ≤ Σ |x_i − y_i| (induction on the index set;
    |x·P − y·Q| ≤ |x|·|P − Q| + |x − y|·|Q| with |x|, |Q| ≤ 1). -/
theorem abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} (S : Finset ι) (x y : ι → ℝ)
    (hx0 : ∀ i ∈ S, 0 ≤ x i) (hx1 : ∀ i ∈ S, x i ≤ 1)
    (hy0 : ∀ i ∈ S, 0 ≤ y i) (hy1 : ∀ i ∈ S, y i ≤ 1) :
    |(∏ i ∈ S, x i) - ∏ i ∈ S, y i| ≤ ∑ i ∈ S, |x i - y i| := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hx0' : ∀ j ∈ S, 0 ≤ x j := fun j hj => hx0 j (Finset.mem_insert_of_mem hj)
    have hx1' : ∀ j ∈ S, x j ≤ 1 := fun j hj => hx1 j (Finset.mem_insert_of_mem hj)
    have hy0' : ∀ j ∈ S, 0 ≤ y j := fun j hj => hy0 j (Finset.mem_insert_of_mem hj)
    have hy1' : ∀ j ∈ S, y j ≤ 1 := fun j hj => hy1 j (Finset.mem_insert_of_mem hj)
    have hxi0 : 0 ≤ x i := hx0 i (Finset.mem_insert_self i S)
    have hxi1 : x i ≤ 1 := hx1 i (Finset.mem_insert_self i S)
    have hQ0 : 0 ≤ ∏ j ∈ S, y j := Finset.prod_nonneg hy0'
    have hQ1 : ∏ j ∈ S, y j ≤ 1 := Finset.prod_le_one hy0' hy1'
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have key : x i * ∏ j ∈ S, x j - y i * ∏ j ∈ S, y j
        = x i * (∏ j ∈ S, x j - ∏ j ∈ S, y j) + (x i - y i) * ∏ j ∈ S, y j := by ring
    rw [key]
    have hA : |x i| * |(∏ j ∈ S, x j) - ∏ j ∈ S, y j|
        ≤ 1 * |(∏ j ∈ S, x j) - ∏ j ∈ S, y j| :=
      mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hxi0]; exact hxi1) (abs_nonneg _)
    have hB : |x i - y i| * |∏ j ∈ S, y j| ≤ |x i - y i| * 1 :=
      mul_le_mul_of_nonneg_left (by rw [abs_of_nonneg hQ0]; exact hQ1) (abs_nonneg _)
    calc |x i * ((∏ j ∈ S, x j) - ∏ j ∈ S, y j) + (x i - y i) * ∏ j ∈ S, y j|
        ≤ |x i * ((∏ j ∈ S, x j) - ∏ j ∈ S, y j)| + |(x i - y i) * ∏ j ∈ S, y j| :=
          abs_add _ _
      _ = |x i| * |(∏ j ∈ S, x j) - ∏ j ∈ S, y j| + |x i - y i| * |∏ j ∈ S, y j| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * |(∏ j ∈ S, x j) - ∏ j ∈ S, y j| + |x i - y i| * 1 := add_le_add hA hB
      _ = |(∏ j ∈ S, x j) - ∏ j ∈ S, y j| + |x i - y i| := by ring
      _ ≤ (∑ j ∈ S, |x j - y j|) + |x i - y i| :=
          add_le_add_right (ih hx0' hx1' hy0' hy1') _
      _ = |x i - y i| + ∑ j ∈ S, |x j - y j| := add_comm _ _

/-- The Stone 53 power lemma is the constant-profile case (a control). -/
theorem abs_pow_sub_pow_le_of_prod {θ θ' : ℝ}
    (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (h0' : 0 ≤ θ') (h1' : θ' ≤ 1) (j : ℕ) :
    |θ ^ j - θ' ^ j| ≤ (j : ℝ) * |θ - θ'| := by
  have := abs_prod_sub_prod_le_sum_abs_sub (Finset.univ : Finset (Fin j))
    (fun _ => θ) (fun _ => θ') (fun _ _ => h0) (fun _ _ => h1) (fun _ _ => h0') (fun _ _ => h1')
  simpa [Finset.prod_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using this

/-- **FAMILY WEIGHT DIFFERENCE**: |A_Γ − A′_Γ| ≤ touchCount r Γ · δ when
    |a − a′| ≤ δ on the polymers touching r (outside r the factors agree). -/
theorem abs_profileWeight_sub_le (r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ)
    (Γ : Finset (Polymer N)) :
    |profileWeight r a Γ - profileWeight r a' Γ| ≤ (touchCount r Γ : ℝ) * δ := by
  unfold profileWeight
  refine le_trans (abs_prod_sub_prod_le_sum_abs_sub Γ _ _
    (fun η _ => touchFactor_nonneg r h0 η) (fun η _ => touchFactor_le_one r h1 η)
    (fun η _ => touchFactor_nonneg r h0' η) (fun η _ => touchFactor_le_one r h1' η)) ?_
  unfold touchCount
  rw [← Finset.sum_filter_add_sum_filter_not Γ (fun η => typedTouchesSupport (N := N) η r)]
  have h2 : (∑ η ∈ Γ.filter (fun η => ¬ typedTouchesSupport (N := N) η r),
      |touchFactor r a η - touchFactor r a' η|) = 0 := by
    refine Finset.sum_eq_zero (fun η hη => ?_)
    have hn := (Finset.mem_filter.mp hη).2
    unfold touchFactor
    rw [if_neg hn, if_neg hn, sub_self, abs_zero]
  rw [h2, add_zero]
  calc (∑ η ∈ Γ.filter (fun η => typedTouchesSupport (N := N) η r),
        |touchFactor r a η - touchFactor r a' η|)
      = ∑ η ∈ Γ.filter (fun η => typedTouchesSupport (N := N) η r), |a η - a' η| := by
        refine Finset.sum_congr rfl (fun η hη => ?_)
        have ht := (Finset.mem_filter.mp hη).2
        unfold touchFactor
        rw [if_pos ht, if_pos ht]
    _ ≤ ∑ η ∈ Γ.filter (fun η => typedTouchesSupport (N := N) η r), δ :=
        Finset.sum_le_sum (fun η hη => hδ η (Finset.mem_filter.mp hη).2)
    _ = ((Γ.filter (fun η => typedTouchesSupport (N := N) η r)).card : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **TUPLE WEIGHT DIFFERENCE** (positions counted, repetitions included):
    |A_δ − A′_δ| ≤ tupleTouchCount r δ · δ. -/
theorem abs_tupleProfileWeight_sub_le (r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ)
    {k : ℕ} (δt : Fin k → Polymer N) :
    |tupleProfileWeight r a δt - tupleProfileWeight r a' δt|
      ≤ (tupleTouchCount r δt : ℝ) * δ := by
  unfold tupleProfileWeight
  refine le_trans (abs_prod_sub_prod_le_sum_abs_sub Finset.univ _ _
    (fun i _ => touchFactor_nonneg r h0 (δt i)) (fun i _ => touchFactor_le_one r h1 (δt i))
    (fun i _ => touchFactor_nonneg r h0' (δt i))
    (fun i _ => touchFactor_le_one r h1' (δt i))) ?_
  unfold tupleTouchCount
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r)]
  have h2 : (∑ i ∈ Finset.univ.filter
      (fun i : Fin k => ¬ typedTouchesSupport (N := N) (δt i) r),
      |touchFactor r a (δt i) - touchFactor r a' (δt i)|) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    have hn := (Finset.mem_filter.mp hi).2
    unfold touchFactor
    rw [if_neg hn, if_neg hn, sub_self, abs_zero]
  rw [h2, add_zero]
  calc (∑ i ∈ Finset.univ.filter (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r),
        |touchFactor r a (δt i) - touchFactor r a' (δt i)|)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r),
          |a (δt i) - a' (δt i)| := by
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have ht := (Finset.mem_filter.mp hi).2
        unfold touchFactor
        rw [if_pos ht, if_pos ht]
    _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r), δ :=
        Finset.sum_le_sum (fun i hi => hδ (δt i) (Finset.mem_filter.mp hi).2)
    _ = ((Finset.univ.filter
          (fun i : Fin k => typedTouchesSupport (N := N) (δt i) r)).card : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- tupleTouchCount ≤ k transports the tuple bound to k·δ (0 ≤ δ). -/
theorem abs_tupleProfileWeight_sub_le_k (r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ)
    {k : ℕ} (δt : Fin k → Polymer N) :
    |tupleProfileWeight r a δt - tupleProfileWeight r a' δt| ≤ (k : ℝ) * δ :=
  le_trans (abs_tupleProfileWeight_sub_le r h0 h1 h0' h1' hδ δt)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (tupleTouchCount_le r δt)) hδ0)

/-- The family weight difference against the count ≤ card: |A_T − A′_T| ≤ card T·δ. -/
theorem abs_profileWeight_sub_le_card (r : Set (Link N)) {a a' : Polymer N → ℝ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |a η - a' η| ≤ δ)
    (T : Finset (Polymer N)) :
    |profileWeight r a T - profileWeight r a' T| ≤ (T.card : ℝ) * δ :=
  le_trans (abs_profileWeight_sub_le r h0 h1 h0' h1' hδ T)
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (touchCount_le_card r T)) hδ0)

/-! ## 55-A.6 — the profile gases, the functional and the core exponent -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- The typed polymer gas of the profile-damped activity (a purely
    polymeric object). -/
noncomputable def profilePolymerGas (β : ℝ) (χ : G → ℝ) (r : Set (Link N))
    (a : Polymer N → ℝ) : ℝ :=
  typedPolymerGas (N := N)
    (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)

/-- The profile-damped marked numerator: every compatible family
    contributes its Stone 50 marked weight times A_Γ — core and remote
    members alike. -/
noncomputable def profileMarkedGas (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (a : Polymer N → ℝ) : ℝ :=
  ∑ Γ ∈ typedCompatiblePolymerFamilies N,
    profileWeight r a Γ * markedRawFamilyWeight μm β χ f s (rawFamily Γ)

/-- **The profile-damped expectation**: a NORMALIZED POLYMER FUNCTIONAL
    (finite volume), quotient of the profile-damped marked gas by the
    profile-damped gas. No identification with a Gibbs measure, a
    boundary condition, a per-link profile or a modified action. -/
noncomputable def profileExpectation (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (a : Polymer N → ℝ) : ℝ :=
  profileMarkedGas μm β χ f s r a / profilePolymerGas μm β χ r a

/-- The profile core exponent E_T(a): cluster sum of the profile-damped
    activity restricted to the remote-allowed polymers of T, minus the
    cluster sum of the profile-damped activity. -/
noncomputable def profileCoreExponent (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) (a : Polymer N → ℝ) : ℝ :=
  (∑' n, kpSignedUnrootedCoeff n
      (restrictedActivity
        (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)
        (remoteAllowed T s)))
    - ∑' n, kpSignedUnrootedCoeff n
        (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Constant profile (denominator)**: the Stone 52 damped gas (definitional). -/
theorem profilePolymerGas_const (β : ℝ) (χ : G → ℝ) (r : Set (Link N)) (θ : ℝ) :
    profilePolymerGas μm β χ r (fun _ => θ) = activityDampedPolymerGas μm β χ r θ := rfl

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Constant profile (exponent)**: the Stone 52 damped core exponent (definitional). -/
theorem profileCoreExponent_const (β : ℝ) (χ : G → ℝ) (T : Finset (Polymer N))
    (s r : Set (Link N)) (θ : ℝ) :
    profileCoreExponent μm β χ T s r (fun _ => θ)
      = dampedActivityCoreExponent μm β χ T s r θ := rfl

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Constant profile (numerator)**: the Stone 52 damped marked gas
    (the weights reduce to the count powers). -/
theorem profileMarkedGas_const (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (θ : ℝ) :
    profileMarkedGas μm β χ f s r (fun _ => θ) = activityDampedMarkedGas μm β χ f s r θ := by
  unfold profileMarkedGas activityDampedMarkedGas
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [profileWeight_const]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Constant profile (functional)**: the Stone 52 damped functional. -/
theorem profileExpectation_const (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (θ : ℝ) :
    profileExpectation μm β χ f s r (fun _ => θ) = activityDampedExpectation μm β χ f s r θ := by
  unfold profileExpectation
  rw [profileMarkedGas_const, profilePolymerGas_const]
  rfl

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Zero profile (functional)**: the Stone 51 activity-restricted
    functional — through the constant-profile identity and the Stone 52
    endpoint; no hypothesis at all. -/
theorem profileExpectation_zero (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) :
    profileExpectation μm β χ f s r (fun _ => 0)
      = activityRestrictedExpectation μm β χ f s r := by
  rw [profileExpectation_const]
  exact activityDampedExpectation_zero μm β χ f s r

/-- **Unit profile (functional)**: the Gibbs expectation, under EXACTLY
    the hypotheses of the published representation (0 ≤ β, measurable
    bounded χ, `DependsOnlyOn f s`, f measurable and bounded); no
    smallness of β. An application of the Stone 52 endpoint, not an
    identity of definitions. -/
theorem profileExpectation_one
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) (r : Set (Link N)) :
    profileExpectation μm β χ f s r (fun _ => 1) = gibbsExpectation (N := N) μm β χ f := by
  rw [profileExpectation_const]
  exact activityDampedExpectation_one μm hβ mχ hχabs hf mf hCf r

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region (denominator)**: the original typed gas. -/
theorem profilePolymerGas_empty_region (β : ℝ) (χ : G → ℝ) (a : Polymer N → ℝ) :
    profilePolymerGas μm β χ (∅ : Set (Link N)) a
      = typedPolymerGas (N := N) (fun η => polymerWeight (N := N) μm β χ η.val) := by
  unfold profilePolymerGas
  rw [profileDampedActivity_empty_region]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region (numerator)**: every weight is 1. -/
theorem profileMarkedGas_empty_region (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (a : Polymer N → ℝ) :
    profileMarkedGas μm β χ f s (∅ : Set (Link N)) a = typedMarkedPolymerGas μm β χ f s := by
  unfold profileMarkedGas typedMarkedPolymerGas
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [profileWeight_empty_region, one_mul]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **r = ∅**: the profiles are trivial and F(a) = F(a′) exactly, for ALL
    real profiles (no hypotheses: both sides are the undamped ratio). -/
theorem profileExpectation_sub_profileExpectation_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) (a a' : Polymer N → ℝ) :
    profileExpectation μm β χ f s (∅ : Set (Link N)) a
        - profileExpectation μm β χ f s (∅ : Set (Link N)) a' = 0 := by
  unfold profileExpectation
  rw [profileMarkedGas_empty_region μm β χ f s a, profileMarkedGas_empty_region μm β χ f s a',
    profilePolymerGas_empty_region μm β χ a, profilePolymerGas_empty_region μm β χ a', sub_self]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Equal profiles**: the difference is 0 (no hypotheses). -/
theorem profileExpectation_sub_self (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (a : Polymer N → ℝ) :
    profileExpectation μm β χ f s r a - profileExpectation μm β χ f s r a = 0 :=
  sub_self _

/-! ## 55-A.7 — representation: KP transported, positivity, ratio, barrier bound -/

/-- The profile gas as an exponential of its cluster sum (KP transported
    for 0 ≤ a ≤ 1). -/
theorem profilePolymerGas_eq_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    profilePolymerGas μm β χ r a
      = Real.exp (∑' n, kpSignedUnrootedCoeff n
          (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)) := by
  unfold profilePolymerGas
  exact typedPolymerGas_eq_exp_tsum_of_KP (fun γ => Nat.cast_nonneg _)
    (abstractKP_profileDampedActivity r h0 h1
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall))

/-- **Positivity of the denominator** (KP as OUTPUT, never a premise). -/
theorem profilePolymerGas_pos
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    0 < profilePolymerGas μm β χ r a := by
  rw [profilePolymerGas_eq_exp μm hβ mχ hχabs hsmall r h0 h1]
  exact Real.exp_pos _

/-- **Profile gas ratio**: KP is inherited for 0 ≤ a ≤ 1 and the published
    ratio identity applies. No denominator is cancelled. -/
theorem profileGas_ratio_eq_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    typedPolymerGas (N := N)
        (restrictedActivity
          (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)
          (remoteAllowed T s))
      / profilePolymerGas μm β χ r a
      = Real.exp (profileCoreExponent μm β χ T s r a) := by
  unfold profilePolymerGas profileCoreExponent
  exact typedPolymerGas_ratio_eq_exp_sub (fun γ => Nat.cast_nonneg _)
    (abstractKP_profileDampedActivity r h0 h1
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall))
    (remoteAllowed T s)

/-- **THE PROFILE EXPONENT PAYS ONLY THE LOCAL BARRIER (κ = 1)**: for
    0 ≤ a ≤ 1, |E_T(a)| ≤ card(barrierLinkFinset T s)·(2/113). Route 53-A.3,
    generic in the activity, with the profile domination. -/
theorem abs_profileCoreExponent_le_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    |profileCoreExponent μm β χ T s r a|
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  have hKP := abstractKP_of_beta_le_one_div_40000 (N := N) μm hβ mχ hχabs hsmall
  have hKPa := abstractKP_profileDampedActivity r h0 h1 hKP
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) := fun γ => Nat.cast_nonneg _
  unfold profileCoreExponent
  rw [tsum_restricted_sub_full ha hKPa (remoteAllowed (N := N) T s), abs_neg]
  have hsum := summable_abs_kpForbiddenUnrootedCoeff ha hKPa (remoteAllowed (N := N) T s)
  have h1' : ‖∑' k : ℕ, kpForbiddenUnrootedCoeff (N := N) k
      (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)
      (remoteAllowed (N := N) T s)‖
      ≤ ∑' k : ℕ, ‖kpForbiddenUnrootedCoeff (N := N) k
          (profileDampedActivity (fun η => polymerWeight (N := N) μm β χ η.val) r a)
          (remoteAllowed (N := N) T s)‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsum
  simp only [Real.norm_eq_abs] at h1'
  refine h1'.trans ?_
  refine (tsum_abs_kpForbiddenUnrootedCoeff_le ha hKPa (remoteAllowed (N := N) T s)).trans ?_
  refine (kpForbiddenRootEnvelope_mono
    (fun η => abs_profileDampedActivity_le _ r h0 h1 η) _).trans ?_
  have henv : kpForbiddenRootEnvelope
      (fun η => |polymerWeight (N := N) μm β χ η.val|)
      (fun η => ((η.val.card : ℕ) : ℝ))
      (remoteAllowed (N := N) T s)
      = ∑ γ₀ : Polymer N,
          if remoteAllowed (N := N) T s γ₀ then 0
          else |polymerWeight (N := N) μm β χ γ₀.val|
            * Real.exp ((γ₀.val.card : ℕ) : ℝ) := rfl
  rw [henv]
  exact kpForbiddenRootEnvelope_le_barrierLinkCount μm hβ mχ hχabs hsmall T s

/-- e^{E_T(a)} ≤ e^{b_T·(2/113)} for 0 ≤ a ≤ 1. -/
theorem exp_profileCoreExponent_le_exp_barrier
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    Real.exp (profileCoreExponent μm β χ T s r a)
      ≤ Real.exp (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) :=
  Real.exp_le_exp.mpr (le_trans (le_abs_self _)
    (abs_profileCoreExponent_le_barrier μm hβ mχ hχabs hsmall T s r h0 h1))

/-! ## 55-A.8 — the profile-weighted fibering and the exponential form -/

/-- **THE PROFILE-WEIGHTED FINITE REGROUPING**: the profile-damped marked
    gas fibers over its touching cores; each fiber contributes A_T ×
    (core weight) × (gas of the profile-damped activity restricted to the
    remote-allowed polymers of T). The weight of a family splits EXACTLY as
    A_T·A_R between core and remote part — the product over the disjoint
    split, multiplicity preserved, nothing approximated, nothing cancelled.
    (The 52-A.F proof with the product split in place of the count split.) -/
theorem profileMarkedGas_eq_sum_core_mul_profile
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (a : Polymer N → ℝ) :
    profileMarkedGas μm β χ f s r a
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight r a T
            * typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (profileDampedActivity
                    (fun η => polymerWeight (N := N) μm β χ η.val) r a)
                  (remoteAllowed T s)) := by
  classical
  unfold profileMarkedGas
  rw [Finset.sum_congr rfl
    (fun Γ _ => by rw [markedRawFamilyWeight_rawFamily μm β χ f s Γ])]
  have hmaps : ∀ Γ ∈ typedCompatiblePolymerFamilies N,
      Γ.filter (fun η => typedTouchesSupport (N := N) η s)
        ∈ typedTouchingFamilies (N := N) s := by
    intro Γ hΓ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_typedCompatiblePolymerFamilies.mpr
        (typedCompatible_mono (Finset.filter_subset _ _)
          (mem_typedCompatiblePolymerFamilies.mp hΓ))
    · intro η hη
      exact (Finset.mem_filter.mp hη).2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Γ : Finset (Polymer N) =>
      profileWeight r a Γ *
      ((∫ U : Config N G,
        f U * ∏ η ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s),
          blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val))]
  refine Finset.sum_congr rfl (fun T hT => ?_)
  obtain ⟨hTtyped, hTtouch⟩ := Finset.mem_filter.mp hT
  -- inside the fiber the core is constant and the weight splits
  have hfib : ∀ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.filter
        (fun η => typedTouchesSupport (N := N) η s) = T),
      (profileWeight r a Γ *
      ((∫ U : Config N G,
        f U * ∏ η ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s),
          blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val))
      = profileWeight r a T * typedMarkedCoreWeight μm β χ f T
          * (profileWeight r a (Γ.filter
                (fun η => ¬ typedTouchesSupport (N := N) η s))
              * ∏ η ∈ Γ.filter
                  (fun η => ¬ typedTouchesSupport (N := N) η s),
                  polymerWeight (N := N) μm β χ η.val) := by
    intro Γ hΓ
    have hΓfib := (Finset.mem_filter.mp hΓ).2
    have hsplit : profileWeight r a Γ
        = profileWeight r a T * profileWeight r a (Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s)) := by
      rw [← hΓfib]
      unfold profileWeight
      exact (Finset.prod_filter_mul_prod_filter_not Γ
        (fun η => typedTouchesSupport (N := N) η s) (touchFactor r a)).symm
    rw [hsplit, hΓfib]
    unfold typedMarkedCoreWeight
    ring
  rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
  congr 1
  -- the fiber ↔ allowed remote families bijection, weight riding along
  rw [typedPolymerGas_restricted_eq_sum_allowed]
  refine Finset.sum_bij
    (fun Γ _ => Γ.filter
      (fun η => ¬ typedTouchesSupport (N := N) η s))
    ?_ ?_ ?_ ?_
  · intro Γ hΓ
    obtain ⟨hΓtyped, hΓfib⟩ := Finset.mem_filter.mp hΓ
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact mem_typedCompatiblePolymerFamilies.mpr
        (typedCompatible_mono (Finset.filter_subset _ _)
          (mem_typedCompatiblePolymerFamilies.mp hΓtyped))
    · intro η hη
      obtain ⟨hηΓ, hηnot⟩ := Finset.mem_filter.mp hη
      refine ⟨hηnot, ?_⟩
      intro t ht
      have htfil : t ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s) :=
        hΓfib.symm ▸ ht
      have htΓ : t ∈ Γ := (Finset.mem_filter.mp htfil).1
      have hne : η ≠ t := by
        rintro rfl
        exact hηnot (Finset.mem_filter.mp htfil).2
      exact mem_typedCompatiblePolymerFamilies.mp hΓtyped
        η hηΓ t htΓ hne
  · intro Γ₁ h₁ Γ₂ h₂ heq
    have heq' : Γ₁.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s)
      = Γ₂.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) := heq
    have hf₁ := (Finset.mem_filter.mp h₁).2
    have hf₂ := (Finset.mem_filter.mp h₂).2
    calc Γ₁ = Γ₁.filter
          (fun η => typedTouchesSupport (N := N) η s)
        ∪ Γ₁.filter
          (fun η => ¬ typedTouchesSupport (N := N) η s) :=
          (Finset.filter_union_filter_neg_eq _ _).symm
      _ = T ∪ Γ₂.filter
          (fun η => ¬ typedTouchesSupport (N := N) η s) := by
          rw [hf₁, heq']
      _ = Γ₂.filter
          (fun η => typedTouchesSupport (N := N) η s)
        ∪ Γ₂.filter
          (fun η => ¬ typedTouchesSupport (N := N) η s) := by
          rw [hf₂]
      _ = Γ₂ := Finset.filter_union_filter_neg_eq _ _
  · intro R hR
    obtain ⟨hRtyped, hRallowed⟩ := Finset.mem_filter.mp hR
    have hTfilter : T.filter
        (fun η => typedTouchesSupport (N := N) η s) = T :=
      Finset.filter_true_of_mem hTtouch
    have hRfilter : R.filter
        (fun η => typedTouchesSupport (N := N) η s) = ∅ :=
      Finset.filter_false_of_mem
        (fun η hη => (hRallowed η hη).1)
    have hTnot : T.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) = ∅ :=
      Finset.filter_false_of_mem
        (fun η hη h => h (hTtouch η hη))
    have hRnot : R.filter
        (fun η => ¬ typedTouchesSupport (N := N) η s) = R :=
      Finset.filter_true_of_mem
        (fun η hη => (hRallowed η hη).1)
    refine ⟨T ∪ R, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ' hθ hne
      rcases Finset.mem_union.mp hη with hηT | hηR
      · rcases Finset.mem_union.mp hθ with hθT | hθR
        · exact mem_typedCompatiblePolymerFamilies.mp hTtyped
            η hηT θ' hθT hne
        · exact plaquetteCompatible_symm
            ((hRallowed θ' hθR).2 η hηT)
      · rcases Finset.mem_union.mp hθ with hθT | hθR
        · exact (hRallowed η hηR).2 θ' hθT
        · exact mem_typedCompatiblePolymerFamilies.mp hRtyped
            η hηR θ' hθR hne
    · show (T ∪ R).filter
          (fun η => typedTouchesSupport (N := N) η s) = T
      rw [Finset.filter_union, hTfilter, hRfilter,
        Finset.union_empty]
    · show (T ∪ R).filter
          (fun η => ¬ typedTouchesSupport (N := N) η s) = R
      rw [Finset.filter_union, hTnot, hRnot,
        Finset.empty_union]
  · intro Γ _
    exact (prod_profileDampedActivity _ r a _).symm

/-- **Exponential form of the profile functional**: the fibering divided
    termwise by the profile gas, each ratio an exponential of the profile
    core exponent, the weight A_T exhibited. No `DependsOnlyOn`,
    measurability or bound on f is needed on this side. -/
theorem profileExpectation_eq_sum_core_mul_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N))
    {a : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) :
    profileExpectation μm β χ f s r a
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight r a T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a) := by
  unfold profileExpectation
  rw [profileMarkedGas_eq_sum_core_mul_profile μm β χ f s r a,
    Finset.sum_div]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [mul_div_assoc]
  congr 1
  exact profileGas_ratio_eq_exp μm hβ mχ hχabs hsmall T s r h0 h1

/-! ## 55-A.9 — CAPSTONE 55-A: the exact two-profile ledger -/

/-- **THE EXACT TWO-PROFILE LEDGER**: for profiles a, a′ in [0,1],
      F(a) − F(a′)
        = Σ_{T touching} A′_T · W_T · (e^{E_T(a)} − e^{E_T(a′)})
        + Σ_{T bridge}   (A_T − A′_T) · W_T · e^{E_T(a)}.
    Finite algebra on the exponential form of both sides; on the allowed
    column both weights are 1, so the bridge column is supported on bridge
    cores only. The connector column carries the weight of the SECOND
    profile and the exponent difference; the bridge column carries the
    weight difference and the exponent of the FIRST profile (the 53-B.1
    convention). No `DependsOnlyOn`, no measurability or bound on f. -/
theorem profileExpectation_sub_eq_two_column_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (f : Config N G → ℝ) (s r : Set (Link N))
    {a a' : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1) :
    profileExpectation μm β χ f s r a
        - profileExpectation μm β χ f s r a'
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight r a' T
            * typedMarkedCoreWeight μm β χ f T
            * (Real.exp (profileCoreExponent μm β χ T s r a)
                - Real.exp (profileCoreExponent μm β χ T s r a')))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (profileWeight r a T - profileWeight r a' T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a) := by
  rw [profileExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0 h1,
    profileExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs hsmall
      f s r h0' h1']
  -- the a-weighted sum with the a-exponent, rewritten with the a′-weight
  -- plus the bridge correction (weights agree on allowed cores)
  have hsplit : (∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight r a T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a))
      = (∑ T ∈ typedTouchingFamilies (N := N) s,
          profileWeight r a' T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          (profileWeight r a T - profileWeight r a' T)
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a) := by
    rw [sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => profileWeight r a T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a)),
      sum_touchingFamilies_eq_activityAllowed_add_bridge s r
        (fun T => profileWeight r a' T
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a))]
    have hallowed : (∑ T ∈ activityAllowedCores (N := N) s r,
          profileWeight r a T
            * typedMarkedCoreWeight μm β χ f T
            * Real.exp (profileCoreExponent μm β χ T s r a))
        = ∑ T ∈ activityAllowedCores (N := N) s r,
            profileWeight r a' T
              * typedMarkedCoreWeight μm β χ f T
              * Real.exp (profileCoreExponent μm β χ T s r a) := by
      refine Finset.sum_congr rfl (fun T hT => ?_)
      rw [profileWeight_eq_one_of_mem_activityAllowedCores a hT,
        profileWeight_eq_one_of_mem_activityAllowedCores a' hT]
    rw [hallowed, add_assoc, ← Finset.sum_add_distrib, add_right_inj]
    refine Finset.sum_congr rfl (fun T _ => ?_)
    ring
  rw [hsplit, add_sub_right_comm, ← Finset.sum_sub_distrib, add_left_inj]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  ring

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Equal profiles, column by column**: both ledger columns vanish termwise. -/
theorem two_column_profile_ledger_self (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) (a : Polymer N → ℝ) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        profileWeight r a T
          * typedMarkedCoreWeight μm β χ f T
          * (Real.exp (profileCoreExponent μm β χ T s r a)
              - Real.exp (profileCoreExponent μm β χ T s r a)))
      + ∑ T ∈ activityBridgeCores (N := N) s r,
        (profileWeight r a T - profileWeight r a T)
          * typedMarkedCoreWeight μm β χ f T
          * Real.exp (profileCoreExponent μm β χ T s r a) = 0 := by
  simp

#print axioms profileDampedActivity_const
#print axioms profileWeight_const
#print axioms tupleProfileWeight_const
#print axioms profileDampedActivity_one
#print axioms profileDampedActivity_zero
#print axioms profileDampedActivity_empty_region
#print axioms abs_profileDampedActivity_le
#print axioms abstractKP_profileDampedActivity
#print axioms prod_profileDampedActivity
#print axioms prod_profileDampedActivity_tuple
#print axioms touchFactor_nonneg
#print axioms touchFactor_le_one
#print axioms profileWeight_nonneg
#print axioms profileWeight_le_one
#print axioms profileWeight_eq_one_of_touchCount_zero
#print axioms profileWeight_eq_one_of_mem_activityAllowedCores
#print axioms tupleProfileWeight_eq_one_of_tupleTouchCount_zero
#print axioms profileWeight_empty_region
#print axioms abs_prod_sub_prod_le_sum_abs_sub
#print axioms abs_pow_sub_pow_le_of_prod
#print axioms abs_profileWeight_sub_le
#print axioms abs_tupleProfileWeight_sub_le
#print axioms abs_tupleProfileWeight_sub_le_k
#print axioms abs_profileWeight_sub_le_card
#print axioms profilePolymerGas_const
#print axioms profileCoreExponent_const
#print axioms profileMarkedGas_const
#print axioms profileExpectation_const
#print axioms profileExpectation_zero
#print axioms profileExpectation_one
#print axioms profilePolymerGas_empty_region
#print axioms profileMarkedGas_empty_region
#print axioms profileExpectation_sub_profileExpectation_empty_region
#print axioms profileExpectation_sub_self
#print axioms profilePolymerGas_eq_exp
#print axioms profilePolymerGas_pos
#print axioms profileGas_ratio_eq_exp
#print axioms abs_profileCoreExponent_le_barrier
#print axioms exp_profileCoreExponent_le_exp_barrier
#print axioms profileMarkedGas_eq_sum_core_mul_profile
#print axioms profileExpectation_eq_sum_core_mul_exp
#print axioms profileExpectation_sub_eq_two_column_ledger
#print axioms two_column_profile_ledger_self

end LatticeGauge
