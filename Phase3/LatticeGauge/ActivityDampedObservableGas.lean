/-
LatticeGauge/ActivityDampedObservableGas.lean — PEDRA 52,
Gate 52-A: THE REMOTE ACTIVITY DAMPING FUNCTIONAL
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): Stone 51 zeroed
the activity of every polymer touching a remote region r (activity
restriction). Stone 52 replaces the hard zero by a CONTINUOUS
damping parameter θ: the activity of a polymer touching r is
multiplied by θ, the activity of a polymer avoiding r is kept.
The two endpoints are the existing objects — θ = 0 is the Stone 51
restriction, θ = 1 is the original activity — and nothing in
between is a new physical theory: all objects below are
finite-volume polymer gases and NORMALIZED POLYMER FUNCTIONALS of
the damped activity. This gate builds:

  * dampedActivity z r θ — the pointwise remote activity damping,
    total in θ (the semantic interval 0 ≤ θ ≤ 1 enters only the
    quantitative theorems: |z_θ| ≤ |z| and the KP transport);
  * touchCount r Γ / tupleTouchCount r δ — the number of members
    (positions, for tuples: repetitions count) touching r, with
    the exact relation between the two counts and the counting-to-
    mass compatibility with Stone 52-A0;
  * the LITERAL product identity  ∏ z_θ = θ^{touchCount} · ∏ z
    (the exponent is a count, never a boolean indicator), and its
    consequence at the coefficient level: the damped signed and
    connector cluster coefficients are the original tuple sums with
    the position weight θ^{tupleTouchCount} inserted (bridges for the
    future ledger; no difference and no bound are taken here);
  * activityDampedPolymerGas / activityDampedMarkedGas /
    activityDampedExpectation — denominator, numerator and their
    quotient in the Stone 51 conventions, with the family weight
    θ^{touchCount r Γ} exhibited, true normalization at f = 1,
    s = ∅, positivity of the denominator (KP as OUTPUT), and the
    two endpoint identities with the EXISTING objects;
  * CAPSTONE: the θ-weighted finite regrouping by touching cores —
    the A3a fibering redone with the damping weight split exactly
    as θ^{touchCount T} · θ^{touchCount R} between core and remote
    part (touch counts are additive over the disjoint split).

HARD HOLD (not here): the damped-versus-full ledger, the damped
cluster difference, connector or bridge columns, any exponential
bound, the Stone 52 capstone; Gibbs-measure, boundary-condition,
modified-action or switch-off interpretations; thermodynamic
limit, continuum, mass gap. No project-local scientific axioms;
0 sorry.
-/
import Mathlib
import LatticeGauge.ActivityRestrictedObservableGas
import LatticeGauge.ActivityRestrictionLedger
import LatticeGauge.ActivityDampingBudgets

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 52-A.A — the damped activity -/

/-- **Remote activity damping**: the activity of a polymer touching
    the remote region r is multiplied by θ; the activity of a
    polymer avoiding r is kept. The definition is TOTAL in θ; the
    semantic interval 0 ≤ θ ≤ 1 is a hypothesis of the
    quantitative theorems, not part of the object. -/
noncomputable def dampedActivity (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) : Polymer N → ℝ :=
  fun η => if typedTouchesSupport (N := N) η r then θ * z η else z η

theorem dampedActivity_of_regionAllowed (z : Polymer N → ℝ)
    {r : Set (Link N)} (θ : ℝ) {η : Polymer N}
    (h : regionAllowed (N := N) r η) :
    dampedActivity z r θ η = z η := by
  unfold dampedActivity
  exact if_neg (regionAllowed_iff.mp h)

theorem dampedActivity_of_touches (z : Polymer N → ℝ)
    {r : Set (Link N)} (θ : ℝ) {η : Polymer N}
    (h : typedTouchesSupport (N := N) η r) :
    dampedActivity z r θ η = θ * z η := by
  unfold dampedActivity
  exact if_pos h

/-- **Endpoint θ = 0**: the damped activity IS the Stone 51
    restricted activity (pointwise, hence as functions). -/
theorem dampedActivity_zero (z : Polymer N → ℝ) (r : Set (Link N)) :
    dampedActivity z r 0
      = restrictedActivity z (regionAllowed (N := N) r) := by
  funext η
  unfold dampedActivity restrictedActivity regionAllowed
  by_cases h : typedTouchesSupport (N := N) η r
  · rw [if_pos h, if_neg (not_not.mpr h), zero_mul]
  · rw [if_neg h, if_pos h]

/-- **Endpoint θ = 1**: the damped activity IS the original one. -/
theorem dampedActivity_one (z : Polymer N → ℝ) (r : Set (Link N)) :
    dampedActivity z r 1 = z := by
  funext η
  unfold dampedActivity
  split_ifs <;> simp

/-- **Domination**: for 0 ≤ θ ≤ 1, |z_θ| ≤ |z| pointwise. -/
theorem abs_dampedActivity_le (z : Polymer N → ℝ) (r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (η : Polymer N) :
    |dampedActivity z r θ η| ≤ |z η| := by
  unfold dampedActivity
  split_ifs
  · rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_of_le_one_left (abs_nonneg _) h1
  · exact le_rfl

/-- The damped activity vanishes wherever the original one does. -/
theorem dampedActivity_eq_zero_of_eq_zero (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) {η : Polymer N} (h : z η = 0) :
    dampedActivity z r θ η = 0 := by
  unfold dampedActivity
  split_ifs <;> simp [h]

/-- **KP transport**: for 0 ≤ θ ≤ 1 the damped activity inherits
    the abstract KP hypothesis by monotonicity (Stone 46/50 not
    redone). -/
theorem abstractKP_dampedActivity {z a : Polymer N → ℝ}
    (r : Set (Link N)) {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    AbstractKPHypothesis (N := N)
      (fun η => |dampedActivity z r θ η|) a :=
  abstractKP_mono (fun η => abs_dampedActivity_le z r h0 h1 η)
    (fun _ => abs_nonneg _) hKP

/-- **Damping commutes with restriction** (both are pointwise
    scalings; the zero of the restriction absorbs θ). -/
theorem restrictedActivity_dampedActivity (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) (P : Polymer N → Prop) :
    restrictedActivity (dampedActivity z r θ) P
      = dampedActivity (restrictedActivity z P) r θ := by
  funext η
  unfold restrictedActivity dampedActivity
  by_cases hP : P η
  · simp [hP]
  · simp [hP]

/-- **Empty remote region**: damping by ∅ is the identity (no
    polymer touches ∅), whatever θ. -/
theorem dampedActivity_empty_region (z : Polymer N → ℝ) (θ : ℝ) :
    dampedActivity (N := N) z (∅ : Set (Link N)) θ = z := by
  funext η
  unfold dampedActivity
  exact if_neg (not_blockTouchesSupport_empty η.val)

/-! ## 52-A.B — touch counts (families and tuples) -/

/-- The number of members of a family touching the remote region r. -/
noncomputable def touchCount (r : Set (Link N))
    (Γ : Finset (Polymer N)) : ℕ :=
  (Γ.filter (fun η => typedTouchesSupport (N := N) η r)).card

/-- The number of POSITIONS of a tuple touching r: a polymer
    occurring twice is counted twice. -/
noncomputable def tupleTouchCount (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) : ℕ :=
  (Finset.univ.filter
    (fun i : Fin k => typedTouchesSupport (N := N) (δ i) r)).card

theorem touchCount_empty (r : Set (Link N)) :
    touchCount (N := N) r ∅ = 0 := by
  simp [touchCount]

theorem touchCount_insert_of_touches (r : Set (Link N))
    {η : Polymer N} {Γ : Finset (Polymer N)} (hη : η ∉ Γ)
    (ht : typedTouchesSupport (N := N) η r) :
    touchCount r (insert η Γ) = touchCount r Γ + 1 := by
  unfold touchCount
  rw [Finset.filter_insert, if_pos ht, Finset.card_insert_of_not_mem]
  intro h
  exact hη (Finset.mem_filter.mp h).1

theorem touchCount_insert_of_regionAllowed (r : Set (Link N))
    {η : Polymer N} (Γ : Finset (Polymer N))
    (ha : regionAllowed (N := N) r η) :
    touchCount r (insert η Γ) = touchCount r Γ := by
  unfold touchCount
  rw [Finset.filter_insert, if_neg (regionAllowed_iff.mp ha)]

/-- **Additivity** over a disjoint union. -/
theorem touchCount_union_of_disjoint (r : Set (Link N))
    {T R : Finset (Polymer N)} (h : Disjoint T R) :
    touchCount r (T ∪ R) = touchCount r T + touchCount r R := by
  unfold touchCount
  rw [Finset.filter_union]
  exact Finset.card_union_of_disjoint
    (Finset.disjoint_filter_filter h)

/-- **Additivity over any filter split**: the touch count of Γ is
    the touch count of the p-part plus that of the ¬p-part. -/
theorem touchCount_filter_add_filter_not (r : Set (Link N))
    (Γ : Finset (Polymer N)) (p : Polymer N → Prop) :
    touchCount r (Γ.filter p) + touchCount r (Γ.filter (fun η => ¬ p η))
      = touchCount r Γ := by
  unfold touchCount
  rw [Finset.filter_comm, Finset.filter_comm (fun η => ¬ p η)]
  exact Finset.filter_card_add_filter_neg_card_eq_card p

theorem touchCount_eq_zero_iff (r : Set (Link N))
    (Γ : Finset (Polymer N)) :
    touchCount r Γ = 0 ↔ ∀ η ∈ Γ, regionAllowed (N := N) r η := by
  unfold touchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h η hη => regionAllowed_iff.mpr (h hη),
    fun h η hη => regionAllowed_iff.mp (h η hη)⟩

theorem touchCount_pos_iff (r : Set (Link N))
    (Γ : Finset (Polymer N)) :
    0 < touchCount r Γ ↔ ∃ η ∈ Γ, typedTouchesSupport (N := N) η r := by
  unfold touchCount
  rw [Finset.card_pos, Finset.filter_nonempty_iff]

theorem touchCount_le_card (r : Set (Link N)) (Γ : Finset (Polymer N)) :
    touchCount r Γ ≤ Γ.card :=
  Finset.card_filter_le _ _

/-- Compatibility with Stone 52-A0: count ≤ family mass. -/
theorem touchCount_le_familyTotalCard (r : Set (Link N))
    (Γ : Finset (Polymer N)) :
    touchCount r Γ ≤ familyTotalCard Γ :=
  le_trans (touchCount_le_card r Γ) (familyCard_le_familyTotalCard Γ)

theorem tupleTouchCount_zero (r : Set (Link N)) (δ : Fin 0 → Polymer N) :
    tupleTouchCount r δ = 0 := by
  simp [tupleTouchCount]

/-- Touch count as a sum of position indicators. -/
theorem tupleTouchCount_eq_sum (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) :
    tupleTouchCount r δ
      = ∑ i : Fin k,
          if typedTouchesSupport (N := N) (δ i) r then 1 else 0 := by
  unfold tupleTouchCount
  exact Finset.card_filter _ _

/-- **Count under `Fin.cons`**: the head contributes its indicator. -/
theorem tupleTouchCount_cons (r : Set (Link N)) {k : ℕ}
    (η : Polymer N) (δ : Fin k → Polymer N) :
    tupleTouchCount r (Fin.cons η δ : Fin (k + 1) → Polymer N)
      = (if typedTouchesSupport (N := N) η r then 1 else 0)
        + tupleTouchCount r δ := by
  rw [tupleTouchCount_eq_sum, tupleTouchCount_eq_sum, Fin.sum_univ_succ]
  simp

/-- **Permutation invariance** of the position count. -/
theorem tupleTouchCount_comp_perm (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) (σ : Equiv.Perm (Fin k)) :
    tupleTouchCount r (δ ∘ σ) = tupleTouchCount r δ := by
  rw [tupleTouchCount_eq_sum, tupleTouchCount_eq_sum]
  exact Equiv.sum_comp σ
    (fun i => if typedTouchesSupport (N := N) (δ i) r then 1 else 0)

theorem tupleTouchCount_le (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) :
    tupleTouchCount r δ ≤ k := by
  unfold tupleTouchCount
  exact le_trans (Finset.card_filter_le _ _) (by simp)

/-- Compatibility with Stone 52-A0: count ≤ tuple mass. -/
theorem tupleTouchCount_le_tupleTotalCard (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) :
    tupleTouchCount r δ ≤ tupleTotalCard δ :=
  le_trans (tupleTouchCount_le r δ) (nat_le_tupleTotalCard δ)

/-- **The exact relation between the two counts**: for an injective
    tuple the position count is the touch count of its image family
    (with repetitions the position count is the larger one — that
    is the whole point of counting positions). -/
theorem tupleTouchCount_eq_touchCount_image (r : Set (Link N)) {k : ℕ}
    {δ : Fin k → Polymer N} (hδ : Function.Injective δ) :
    tupleTouchCount r δ = touchCount r (Finset.univ.image δ) := by
  unfold tupleTouchCount touchCount
  rw [Finset.filter_image, Finset.card_image_of_injective _ hδ]

theorem tupleTouchCount_eq_zero_iff (r : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) :
    tupleTouchCount r δ = 0 ↔ ∀ i, regionAllowed (N := N) r (δ i) := by
  unfold tupleTouchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact ⟨fun h i => regionAllowed_iff.mpr (h (Finset.mem_univ i)),
    fun h i _ => regionAllowed_iff.mp (h i)⟩

/-- **Count under concatenation** (`Fin.append`): positions add. -/
theorem tupleTouchCount_append (r : Set (Link N)) {m n : ℕ}
    (δ : Fin m → Polymer N) (δ' : Fin n → Polymer N) :
    tupleTouchCount r (Fin.append δ δ')
      = tupleTouchCount r δ + tupleTouchCount r δ' := by
  rw [tupleTouchCount_eq_sum, tupleTouchCount_eq_sum, tupleTouchCount_eq_sum,
    Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- **Empty remote region**: nothing touches ∅, so the count is 0. -/
theorem touchCount_empty_region (Γ : Finset (Polymer N)) :
    touchCount (N := N) (∅ : Set (Link N)) Γ = 0 := by
  unfold touchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro η _ h
  exact not_blockTouchesSupport_empty η.val h

theorem tupleTouchCount_empty_region {k : ℕ} (δ : Fin k → Polymer N) :
    tupleTouchCount (N := N) (∅ : Set (Link N)) δ = 0 := by
  unfold tupleTouchCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _ h
  exact not_blockTouchesSupport_empty (δ i).val h

/-! ## 52-A.C — the damped product identity -/

/-- **THE LITERAL WEIGHT IDENTITY (families)**:
    ∏_{η ∈ Γ} z_θ(η) = θ^{touchCount r Γ} · ∏_{η ∈ Γ} z(η). -/
theorem prod_dampedActivity (z : Polymer N → ℝ) (r : Set (Link N))
    (θ : ℝ) (Γ : Finset (Polymer N)) :
    (∏ η ∈ Γ, dampedActivity z r θ η)
      = θ ^ touchCount r Γ * ∏ η ∈ Γ, z η := by
  unfold touchCount
  rw [← Finset.prod_filter_mul_prod_filter_not Γ
      (fun η => typedTouchesSupport (N := N) η r)
      (dampedActivity z r θ),
    ← Finset.prod_filter_mul_prod_filter_not Γ
      (fun η => typedTouchesSupport (N := N) η r) z]
  have h1 : (∏ η ∈ Γ.filter
        (fun η => typedTouchesSupport (N := N) η r),
        dampedActivity z r θ η)
      = θ ^ (Γ.filter
          (fun η => typedTouchesSupport (N := N) η r)).card
        * ∏ η ∈ Γ.filter
            (fun η => typedTouchesSupport (N := N) η r), z η := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun η hη => ?_)
    exact dampedActivity_of_touches z θ (Finset.mem_filter.mp hη).2
  have h2 : (∏ η ∈ Γ.filter
        (fun η => ¬ typedTouchesSupport (N := N) η r),
        dampedActivity z r θ η)
      = ∏ η ∈ Γ.filter
          (fun η => ¬ typedTouchesSupport (N := N) η r), z η := by
    refine Finset.prod_congr rfl (fun η hη => ?_)
    exact dampedActivity_of_regionAllowed z θ
      (regionAllowed_iff.mpr (Finset.mem_filter.mp hη).2)
  rw [h1, h2, mul_assoc]

/-- **THE LITERAL WEIGHT IDENTITY (tuples, multiplicities kept)**. -/
theorem prod_dampedActivity_tuple (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) {k : ℕ} (δ : Fin k → Polymer N) :
    (∏ i : Fin k, dampedActivity z r θ (δ i))
      = θ ^ tupleTouchCount r δ * ∏ i : Fin k, z (δ i) := by
  unfold tupleTouchCount
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => typedTouchesSupport (N := N) (δ i) r)
      (fun i => dampedActivity z r θ (δ i)),
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => typedTouchesSupport (N := N) (δ i) r)
      (fun i => z (δ i))]
  have h1 : (∏ i ∈ Finset.univ.filter
        (fun i => typedTouchesSupport (N := N) (δ i) r),
        dampedActivity z r θ (δ i))
      = θ ^ (Finset.univ.filter
          (fun i => typedTouchesSupport (N := N) (δ i) r)).card
        * ∏ i ∈ Finset.univ.filter
            (fun i => typedTouchesSupport (N := N) (δ i) r), z (δ i) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i hi => ?_)
    exact dampedActivity_of_touches z θ (Finset.mem_filter.mp hi).2
  have h2 : (∏ i ∈ Finset.univ.filter
        (fun i => ¬ typedTouchesSupport (N := N) (δ i) r),
        dampedActivity z r θ (δ i))
      = ∏ i ∈ Finset.univ.filter
          (fun i => ¬ typedTouchesSupport (N := N) (δ i) r), z (δ i) := by
    refine Finset.prod_congr rfl (fun i hi => ?_)
    exact dampedActivity_of_regionAllowed z θ
      (regionAllowed_iff.mpr (Finset.mem_filter.mp hi).2)
  rw [h1, h2, mul_assoc]

theorem prod_dampedActivity_empty (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) :
    (∏ η ∈ (∅ : Finset (Polymer N)), dampedActivity z r θ η) = 1 := by
  simp

/-- Weight 1 on families avoiding r (whatever θ — 0⁰ = 1 included). -/
theorem prod_dampedActivity_of_touchCount_zero (z : Polymer N → ℝ)
    (r : Set (Link N)) (θ : ℝ) {Γ : Finset (Polymer N)}
    (h : touchCount r Γ = 0) :
    (∏ η ∈ Γ, dampedActivity z r θ η) = ∏ η ∈ Γ, z η := by
  rw [prod_dampedActivity, h, pow_zero, one_mul]

/-- θ = 0: families avoiding r keep their weight, the others vanish. -/
theorem prod_dampedActivity_zero (z : Polymer N → ℝ)
    (r : Set (Link N)) (Γ : Finset (Polymer N)) :
    (∏ η ∈ Γ, dampedActivity z r 0 η)
      = if touchCount r Γ = 0 then ∏ η ∈ Γ, z η else 0 := by
  rw [prod_dampedActivity]
  by_cases h : touchCount r Γ = 0
  · rw [if_pos h, h, pow_zero, one_mul]
  · rw [if_neg h, zero_pow h, zero_mul]

theorem prod_dampedActivity_one (z : Polymer N → ℝ)
    (r : Set (Link N)) (Γ : Finset (Polymer N)) :
    (∏ η ∈ Γ, dampedActivity z r 1 η) = ∏ η ∈ Γ, z η := by
  rw [prod_dampedActivity, one_pow, one_mul]

/-- The weight factors over a disjoint split of the family. -/
theorem pow_touchCount_union_of_disjoint (r : Set (Link N)) (θ : ℝ)
    {T R : Finset (Polymer N)} (h : Disjoint T R) :
    θ ^ touchCount r (T ∪ R) = θ ^ touchCount r T * θ ^ touchCount r R := by
  rw [touchCount_union_of_disjoint r h, pow_add]

/-! ## 52-A.C′ — the damped cluster coefficients (bridges for the
    future ledger; no difference, no bound taken here) -/

/-- **Damped signed unrooted coefficient**: the Stone 49 coefficient
    of the damped activity is the SAME tuple sum with the position
    weight θ^{tupleTouchCount r δ} inserted in front of each summand —
    Ursell factor, product, and 1/k! exactly as defined (k = 0
    included: the sum over `Fin 0 → Polymer N` is untouched). -/
theorem kpSignedUnrootedCoeff_dampedActivity (k : ℕ)
    (z : Polymer N → ℝ) (r : Set (Link N)) (θ : ℝ) :
    kpSignedUnrootedCoeff (N := N) k (dampedActivity z r θ)
      = (∑ δ : Fin k → Polymer N,
          θ ^ tupleTouchCount r δ
            * (((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
                * ∏ i : Fin k, z (δ i)))
        / ((Nat.factorial k : ℕ) : ℝ) := by
  unfold kpSignedUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_dampedActivity_tuple]
  ring

/-- **Damped connector coefficient** (the Stone 50/51 connector
    coefficient `kpConnectorUnrootedCoeff` with its literal
    `TupleHitsBothForbidden` filter): the same identity, the filter
    untouched, the weight θ^{tupleTouchCount r δ} in front of each
    surviving summand. -/
theorem kpConnectorUnrootedCoeff_dampedActivity (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop)
    (r : Set (Link N)) (θ : ℝ) :
    kpConnectorUnrootedCoeff (N := N) k (dampedActivity z r θ) P Q
      = (∑ δ : Fin k → Polymer N,
          if TupleHitsBothForbidden P Q δ then
            θ ^ tupleTouchCount r δ
              * (((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
                  * ∏ i : Fin k, z (δ i))
          else 0)
        / ((Nat.factorial k : ℕ) : ℝ) := by
  unfold kpConnectorUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  split_ifs
  · rw [prod_dampedActivity_tuple]
    ring
  · rfl

/-- Endpoint θ = 1 of the damped coefficient (the weight is 1). -/
theorem kpSignedUnrootedCoeff_dampedActivity_one (k : ℕ)
    (z : Polymer N → ℝ) (r : Set (Link N)) :
    kpSignedUnrootedCoeff (N := N) k (dampedActivity z r 1)
      = kpSignedUnrootedCoeff (N := N) k z := by
  rw [dampedActivity_one]

/-- Endpoint θ = 0 of the damped coefficient: the coefficient of the
    Stone 51 restricted activity. -/
theorem kpSignedUnrootedCoeff_dampedActivity_zero (k : ℕ)
    (z : Polymer N → ℝ) (r : Set (Link N)) :
    kpSignedUnrootedCoeff (N := N) k (dampedActivity z r 0)
      = kpSignedUnrootedCoeff (N := N) k
          (restrictedActivity z (regionAllowed (N := N) r)) := by
  rw [dampedActivity_zero]

/-! ## 52-A.D — the damped gases -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- The typed polymer gas of the damped activity — a purely polymeric
    object (NOT the partition function of a new physical theory). -/
noncomputable def activityDampedPolymerGas
    (β : ℝ) (χ : G → ℝ) (r : Set (Link N)) (θ : ℝ) : ℝ :=
  typedPolymerGas (N := N)
    (dampedActivity
      (fun η => polymerWeight (N := N) μm β χ η.val) r θ)

/-- The damped marked numerator: every compatible family
    contributes its Stone 50 marked weight times the damping
    weight θ^{touchCount r Γ} — core and remote members alike. -/
noncomputable def activityDampedMarkedGas
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) (θ : ℝ) : ℝ :=
  ∑ Γ ∈ typedCompatiblePolymerFamilies N,
    θ ^ touchCount r Γ * markedRawFamilyWeight μm β χ f s (rawFamily Γ)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- The damped gas with the family weight exhibited. -/
theorem activityDampedPolymerGas_eq_sum_pow (β : ℝ) (χ : G → ℝ)
    (r : Set (Link N)) (θ : ℝ) :
    activityDampedPolymerGas μm β χ r θ
      = ∑ Γ ∈ typedCompatiblePolymerFamilies N,
          θ ^ touchCount r Γ
            * ∏ η ∈ Γ, polymerWeight (N := N) μm β χ η.val := by
  unfold activityDampedPolymerGas typedPolymerGas
  exact Finset.sum_congr rfl (fun Γ _ => prod_dampedActivity _ r θ Γ)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 0 (denominator)**: the Stone 51 restricted gas. -/
theorem activityDampedPolymerGas_zero (β : ℝ) (χ : G → ℝ)
    (r : Set (Link N)) :
    activityDampedPolymerGas μm β χ r 0
      = activityRestrictedPolymerGas μm β χ r := by
  unfold activityDampedPolymerGas activityRestrictedPolymerGas
  rw [dampedActivity_zero]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 1 (denominator)**: the original typed gas. -/
theorem activityDampedPolymerGas_one (β : ℝ) (χ : G → ℝ)
    (r : Set (Link N)) :
    activityDampedPolymerGas μm β χ r 1
      = typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  unfold activityDampedPolymerGas
  rw [dampedActivity_one]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 0 (numerator)**: the Stone 51 restricted marked gas. -/
theorem activityDampedMarkedGas_zero (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    activityDampedMarkedGas μm β χ f s r 0
      = activityRestrictedMarkedGas μm β χ f s r := by
  unfold activityDampedMarkedGas activityRestrictedMarkedGas
    regionAllowedFamilies
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  by_cases h : ∀ η ∈ Γ, regionAllowed (N := N) r η
  · rw [if_pos h, (touchCount_eq_zero_iff r Γ).mpr h, pow_zero, one_mul]
  · rw [if_neg h, zero_pow (fun h0 => h ((touchCount_eq_zero_iff r Γ).mp h0)),
      zero_mul]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 1 (numerator)**: the Stone 50 typed marked gas. -/
theorem activityDampedMarkedGas_one (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    activityDampedMarkedGas μm β χ f s r 1
      = typedMarkedPolymerGas μm β χ f s := by
  unfold activityDampedMarkedGas typedMarkedPolymerGas
  simp

/-- **Normalization of the numerator** at f = 1, s = ∅: the damped
    marked gas IS the damped gas — BOTH carry the same damping
    weight (no damping "only in the denominator"). -/
theorem activityDampedMarkedGas_one_empty (β : ℝ) (χ : G → ℝ)
    (r : Set (Link N)) (θ : ℝ) :
    activityDampedMarkedGas μm β χ (fun _ => 1) (∅ : Set (Link N)) r θ
      = activityDampedPolymerGas μm β χ r θ := by
  rw [activityDampedPolymerGas_eq_sum_pow]
  unfold activityDampedMarkedGas
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  congr 1
  rw [markedRawFamilyWeight_one_empty]
  unfold rawFamily
  exact Finset.prod_image (fun a _ b _ h => Subtype.val_injective h)

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region (denominator)**: no damping at all. -/
theorem activityDampedPolymerGas_empty_region (β : ℝ) (χ : G → ℝ) (θ : ℝ) :
    activityDampedPolymerGas μm β χ (∅ : Set (Link N)) θ
      = typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  unfold activityDampedPolymerGas
  rw [dampedActivity_empty_region]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Empty remote region (numerator)**: every weight is θ^0 = 1. -/
theorem activityDampedMarkedGas_empty_region (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) (θ : ℝ) :
    activityDampedMarkedGas μm β χ f s (∅ : Set (Link N)) θ
      = typedMarkedPolymerGas μm β χ f s := by
  unfold activityDampedMarkedGas typedMarkedPolymerGas
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [touchCount_empty_region, pow_zero, one_mul]

/-- The damped gas as an exponential of its cluster sum (KP
    transported for 0 ≤ θ ≤ 1). -/
theorem activityDampedPolymerGas_eq_exp
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    activityDampedPolymerGas μm β χ r θ
      = Real.exp (∑' n, kpSignedUnrootedCoeff n
          (dampedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val) r θ)) := by
  unfold activityDampedPolymerGas
  exact typedPolymerGas_eq_exp_tsum_of_KP
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_dampedActivity r h0 h1
      (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall))

/-- **Positivity of the denominator** (KP as OUTPUT, never a premise). -/
theorem activityDampedPolymerGas_pos
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    0 < activityDampedPolymerGas μm β χ r θ := by
  rw [activityDampedPolymerGas_eq_exp μm hβ mχ hχabs hsmall r h0 h1]
  exact Real.exp_pos _

/-! ## 52-A.E — the normalized polymer functional -/

/-- **The activity-damped expectation**: a NORMALIZED POLYMER
    FUNCTIONAL of the damped activity (finite volume), quotient of
    the damped marked gas by the damped gas. No identification with
    a Gibbs measure, a boundary condition, a modified action or a
    physical switch-off is claimed. -/
noncomputable def activityDampedExpectation
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s : Set (Link N)) (r : Set (Link N)) (θ : ℝ) : ℝ :=
  activityDampedMarkedGas μm β χ f s r θ
    / activityDampedPolymerGas μm β χ r θ

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
theorem activityDampedExpectation_eq_div (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) (θ : ℝ) :
    activityDampedExpectation μm β χ f s r θ
      = activityDampedMarkedGas μm β χ f s r θ
        / activityDampedPolymerGas μm β χ r θ := rfl

/-- **TRUE NORMALIZATION**: at f = 1, s = ∅ the functional equals 1
    — numerator = denominator AND the denominator is positive. -/
theorem activityDampedExpectation_one_empty
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (r : Set (Link N))
    {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    activityDampedExpectation μm β χ (fun _ => 1)
        (∅ : Set (Link N)) r θ = 1 := by
  unfold activityDampedExpectation
  rw [activityDampedMarkedGas_one_empty]
  exact div_self (ne_of_gt
    (activityDampedPolymerGas_pos μm hβ mχ hχabs hsmall r h0 h1))

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Endpoint θ = 0 (functional)**: the Stone 51 activity-restricted
    functional — an identity of definitions, no hypothesis at all. -/
theorem activityDampedExpectation_zero (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s r : Set (Link N)) :
    activityDampedExpectation μm β χ f s r 0
      = activityRestrictedExpectation μm β χ f s r := by
  unfold activityDampedExpectation activityRestrictedExpectation
  rw [activityDampedMarkedGas_zero, activityDampedPolymerGas_zero]

/-- **Endpoint θ = 1 (functional)**: the original Gibbs expectation.
    The hypotheses are EXACTLY those of the published representation
    `gibbsExpectation_eq_markedGas_div_gas` (0 ≤ β, measurable
    bounded χ, f depending only on s, measurable and bounded); NO
    smallness of β is needed. -/
theorem activityDampedExpectation_one
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    (r : Set (Link N)) :
    activityDampedExpectation μm β χ f s r 1
      = gibbsExpectation (N := N) μm β χ f := by
  unfold activityDampedExpectation
  rw [activityDampedMarkedGas_one, activityDampedPolymerGas_one,
    gibbsExpectation_eq_markedGas_div_gas μm hβ mχ hχabs hf mf hCf]

/-! ## 52-A.F — the θ-weighted finite regrouping by touching cores -/

/-- Weight 1 on region-allowed cores. -/
theorem pow_touchCount_eq_one_of_allowed (r : Set (Link N)) (θ : ℝ)
    {T : Finset (Polymer N)}
    (h : ∀ η ∈ T, regionAllowed (N := N) r η) :
    θ ^ touchCount r T = 1 := by
  rw [(touchCount_eq_zero_iff r T).mpr h, pow_zero]

theorem pow_touchCount_eq_one_of_mem_activityAllowedCores
    {s r : Set (Link N)} (θ : ℝ) {T : Finset (Polymer N)}
    (h : T ∈ activityAllowedCores (N := N) s r) :
    θ ^ touchCount r T = 1 :=
  pow_touchCount_eq_one_of_allowed r θ (mem_activityAllowedCores.mp h).2

/-- On bridge cores the count is positive — the weight is a genuine
    power θ^{touchCount}, at least θ¹ (and θ^j for j occurrences). -/
theorem touchCount_pos_of_mem_activityBridgeCores
    {s r : Set (Link N)} {T : Finset (Polymer N)}
    (h : T ∈ activityBridgeCores (N := N) s r) :
    0 < touchCount r T :=
  (touchCount_pos_iff r T).mpr
    (mem_activityBridgeCores_iff_exists_touches.mp h).2

/-- **CAPSTONE 52-A — THE θ-WEIGHTED FINITE REGROUPING**: the damped
    marked gas fibers over its touching cores; each fiber contributes
    θ^{touchCount r T} × (core weight) × (gas of the damped activity
    restricted to the remote-allowed polymers of T). The damping
    weight of a family splits EXACTLY as θ^{touchCount T} ·
    θ^{touchCount R} between core and remote part — additivity of the
    touch count over the disjoint split, multiplicity preserved,
    nothing approximated, nothing cancelled. -/
theorem activityDampedMarkedGas_eq_sum_core_mul_damped
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (θ : ℝ) :
    activityDampedMarkedGas μm β χ f s r θ
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (dampedActivity
                    (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
                  (remoteAllowed T s)) := by
  classical
  unfold activityDampedMarkedGas
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
      θ ^ touchCount r Γ *
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
      (θ ^ touchCount r Γ *
      ((∫ U : Config N G,
        f U * ∏ η ∈ Γ.filter
          (fun η => typedTouchesSupport (N := N) η s),
          blockActivity β χ η.val U ∂(configMeasure μm N))
        * ∏ η ∈ Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s),
            polymerWeight (N := N) μm β χ η.val))
      = θ ^ touchCount r T * typedMarkedCoreWeight μm β χ f T
          * (θ ^ touchCount r (Γ.filter
                (fun η => ¬ typedTouchesSupport (N := N) η s))
              * ∏ η ∈ Γ.filter
                  (fun η => ¬ typedTouchesSupport (N := N) η s),
                  polymerWeight (N := N) μm β χ η.val) := by
    intro Γ hΓ
    have hΓfib := (Finset.mem_filter.mp hΓ).2
    have hsplit : touchCount r Γ
        = touchCount r T + touchCount r (Γ.filter
            (fun η => ¬ typedTouchesSupport (N := N) η s)) := by
      rw [← hΓfib]
      exact (touchCount_filter_add_filter_not r Γ
        (fun η => typedTouchesSupport (N := N) η s)).symm
    rw [hsplit, pow_add, hΓfib]
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
    exact (prod_dampedActivity _ r θ _).symm

/-- The fiber gas in the equivalent "damp after restricting" form
    (interface for the future ledger; pure commutation). -/
theorem activityDampedMarkedGas_eq_sum_core_mul_damped'
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (θ : ℝ) :
    activityDampedMarkedGas μm β χ f s r θ
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (dampedActivity
                  (restrictedActivity
                    (fun η => polymerWeight (N := N) μm β χ η.val)
                    (remoteAllowed T s)) r θ) := by
  rw [activityDampedMarkedGas_eq_sum_core_mul_damped]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  rw [restrictedActivity_dampedActivity]

/-- **Allowed + bridge split of the θ-weighted regrouping**: on the
    allowed column the weight is 1; on the bridge column it is a
    positive power of θ (the count is ≥ 1). No inequality yet. -/
theorem activityDampedMarkedGas_eq_allowed_add_bridge
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s r : Set (Link N)) (θ : ℝ) :
    activityDampedMarkedGas μm β χ f s r θ
      = (∑ T ∈ activityAllowedCores (N := N) s r,
          typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (dampedActivity
                    (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
                  (remoteAllowed T s)))
        + ∑ T ∈ activityBridgeCores (N := N) s r,
          θ ^ touchCount r T
            * typedMarkedCoreWeight μm β χ f T
            * typedPolymerGas (N := N)
                (restrictedActivity
                  (dampedActivity
                    (fun η => polymerWeight (N := N) μm β χ η.val) r θ)
                  (remoteAllowed T s)) := by
  rw [activityDampedMarkedGas_eq_sum_core_mul_damped,
    sum_touchingFamilies_eq_activityAllowed_add_bridge s r]
  congr 1
  refine Finset.sum_congr rfl (fun T hT => ?_)
  rw [pow_touchCount_eq_one_of_mem_activityAllowedCores θ hT, one_mul]

#print axioms dampedActivity_zero
#print axioms dampedActivity_one
#print axioms abs_dampedActivity_le
#print axioms abstractKP_dampedActivity
#print axioms touchCount_filter_add_filter_not
#print axioms tupleTouchCount_eq_touchCount_image
#print axioms prod_dampedActivity
#print axioms prod_dampedActivity_tuple
#print axioms tupleTouchCount_append
#print axioms dampedActivity_empty_region
#print axioms kpSignedUnrootedCoeff_dampedActivity
#print axioms kpConnectorUnrootedCoeff_dampedActivity
#print axioms activityDampedMarkedGas_one_empty
#print axioms activityDampedPolymerGas_pos
#print axioms activityDampedExpectation_one_empty
#print axioms activityDampedExpectation_zero
#print axioms activityDampedExpectation_one
#print axioms activityDampedMarkedGas_eq_sum_core_mul_damped
#print axioms activityDampedMarkedGas_eq_allowed_add_bridge

end LatticeGauge
