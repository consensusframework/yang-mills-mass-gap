/-
LatticeGauge/ActivityDampingBudgets.lean — PEDRA 52,
Gate 52-A0: THE QUANTITATIVE INFRASTRUCTURE OF CONTINUOUS
REMOTE ACTIVITY DAMPING (architecture: Sol/GPT-5.6; adversarial
review: Astra; execution: Fable).

CONCEPTUAL RECORD. The planned Stone 52 compares the Gibbs
expectation with a normalized polymer functional in which every
polymer touching a remote region r carries its activity damped by
a factor θ ∈ [0, 1] — a normalized polymer functional, NOT a
modified action, a boundary condition, a second Gibbs measure or a
physical switch-off. The planned linear factor (1 − θ) arises
tuple by tuple from 1 − θ^j ≤ j (1 − θ), and the counting factor j
must be paid by MASS. This gate builds only the reusable
quantitative infrastructure that pays that factor, without
touching the constant planned for the capstone:

  * A. damped powers: 0 ≤ θ^j ≤ 1 and 1 − θ^j ≤ j (1 − θ);
  * B. mass absorption: x ≤ (8/(3e))·e^{3x/8} ≤ e^{3x/8}, with
    8/(3e) ≤ 1 from e ≥ 8/3 (partial sum of the series), and the
    counting-to-mass inequalities k ≤ tupleTotalCard δ and
    card T ≤ familyTotalCard T (every typed polymer is nonempty);
  * C. the tilted KP hypothesis at λ = 7/8 with the complementary
    penalty card/8: 64q/(1 − r) ≤ 8/113 ≤ 1/8;
  * D. recombination: tilt × exp(penalty) = |w| e^{card}, hence the
    forbidden-root envelope at any tilt λ with the complementary
    penalty (1 − λ)·card is the SAME λ-free sum, localized by the
    existing 2/113 per barrier link;
  * E. the two first moments — connectors with the factor k and
    bridge cores with the factor card T — each absorbed by the
    additional tilt 3/8 on top of the geometric tilt 1/2;
  * F. the core budget instance (λ, κ) = (7/8, 1); the instance
    (1/2, 3) is the existing `sum_halfTilt_three_le`.

HARD HOLD (not here): dampedActivity, the damped marked gas and
functional, endpoints, the damped ledger, the damped connector
coefficient, any Stone 52 capstone, any optimality statement about
Stone 51's constant, thermodynamic limit, infinite volume,
continuum, spatial mixing, mass gap, Clay. No project-local
scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPConnectorTiltSpecialization
import LatticeGauge.KPConnectorEnvelopeLocalization
import LatticeGauge.CovarianceBridgeCoreTilt
import LatticeGauge.CovarianceCoreLocalBudget
import LatticeGauge.CovarianceNormalizedColumns
import LatticeGauge.ActivityRestrictionConnectorGeometry

open MeasureTheory
open scoped Classical

namespace LatticeGauge

/-! ## 52-A0.A — damped powers (pure real arithmetic) -/

theorem dampedPow_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (j : ℕ) :
    0 ≤ θ ^ j :=
  pow_nonneg h0 j

theorem dampedPow_le_one {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (j : ℕ) : θ ^ j ≤ 1 :=
  pow_le_one₀ h0 h1

theorem one_sub_dampedPow_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ 1)
    (j : ℕ) : 0 ≤ 1 - θ ^ j :=
  sub_nonneg.mpr (dampedPow_le_one h0 h1 j)

/-- **The linear factor**: 1 − θ^j ≤ j·(1 − θ) for 0 ≤ θ ≤ 1. The
    cast of j to ℝ is explicit. Induction:
    1 − θ^{j+1} = θ(1 − θ^j) + (1 − θ) ≤ (1 − θ^j) + (1 − θ). -/
theorem one_sub_dampedPow_le_nat_mul_one_sub {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ ≤ 1) (j : ℕ) :
    1 - θ ^ j ≤ (j : ℝ) * (1 - θ) := by
  induction j with
  | zero => simp
  | succ m ih =>
    have hm : 0 ≤ 1 - θ ^ m := one_sub_dampedPow_nonneg h0 h1 m
    have hθ1 : 0 ≤ 1 - θ := sub_nonneg.mpr h1
    have key : 1 - θ ^ (m + 1) = θ * (1 - θ ^ m) + (1 - θ) := by
      rw [pow_succ]; ring
    rw [key, Nat.cast_succ]
    have hle : θ * (1 - θ ^ m) ≤ 1 - θ ^ m := by
      have := mul_le_mul_of_nonneg_right h1 hm
      simpa using this
    nlinarith

theorem one_sub_dampedPow_zero_exp (θ : ℝ) : 1 - θ ^ (0 : ℕ) = 0 := by
  simp

theorem one_sub_dampedPow_of_theta_zero {j : ℕ} (hj : 0 < j) :
    1 - (0 : ℝ) ^ j = 1 := by
  rw [zero_pow (Nat.pos_iff_ne_zero.mp hj)]; ring

theorem one_sub_dampedPow_of_theta_one (j : ℕ) :
    1 - (1 : ℝ) ^ j = 0 := by
  simp

/-! ## 52-A0.B — mass absorption -/

/-- e ≥ 8/3 from the first four terms of the exponential series
    (`Real.sum_le_exp_of_nonneg` at x = 1, n = 4): 1 + 1 + 1/2 + 1/6. -/
theorem eight_div_three_le_exp_one : (8 : ℝ) / 3 ≤ Real.exp 1 := by
  have h := Real.sum_le_exp_of_nonneg (x := (1 : ℝ)) (by norm_num) 4
  have hsum : (∑ i ∈ Finset.range 4, (1 : ℝ) ^ i / (i.factorial : ℝ))
      = 8 / 3 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  rw [hsum] at h
  exact h

theorem eight_div_three_exp_one_le_one :
    (8 : ℝ) / (3 * Real.exp 1) ≤ 1 := by
  have he := eight_div_three_le_exp_one
  have hpos : 0 < 3 * Real.exp 1 := by positivity
  rw [div_le_iff₀ hpos]
  linarith

/-- **Absorption by a tilt**: for δ₀ > 0, x ≤ (1/(e δ₀))·e^{δ₀ x}
    (from y + 1 ≤ e^y at y = δ₀x − 1). Valid for every real x. -/
theorem le_inv_mul_exp_mul {δ₀ : ℝ} (hδ : 0 < δ₀) (x : ℝ) :
    x ≤ (1 / (Real.exp 1 * δ₀)) * Real.exp (δ₀ * x) := by
  have h := Real.add_one_le_exp (δ₀ * x - 1)
  have hsplit : Real.exp (δ₀ * x - 1) = Real.exp (δ₀ * x) / Real.exp 1 := by
    rw [Real.exp_sub]
  rw [hsplit] at h
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h' : δ₀ * x * Real.exp 1 ≤ Real.exp (δ₀ * x) := by
    have := (le_div_iff₀ he).mp (by linarith : δ₀ * x ≤ Real.exp (δ₀ * x) / Real.exp 1)
    exact this
  have hpos : 0 < Real.exp 1 * δ₀ := mul_pos he hδ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hpos]
  linarith [h']

/-- The 3/8 specialization: x ≤ (8/(3e))·e^{3x/8}. -/
theorem le_eight_div_three_exp_mul_exp_three_eighths (x : ℝ) :
    x ≤ (8 / (3 * Real.exp 1)) * Real.exp ((3 / 8 : ℝ) * x) := by
  have h := le_inv_mul_exp_mul (δ₀ := (3 / 8 : ℝ)) (by norm_num) x
  have hc : (1 : ℝ) / (Real.exp 1 * (3 / 8)) = 8 / (3 * Real.exp 1) := by
    field_simp
    ring
  rw [hc] at h
  exact h

/-- **Natural masses**: the two-step chain x ≤ (8/(3e))·e^{3x/8} ≤ e^{3x/8}. -/
theorem nat_le_exp_three_eighths (x : ℕ) :
    (x : ℝ) ≤ Real.exp ((3 / 8 : ℝ) * (x : ℝ)) :=
  le_trans (le_eight_div_three_exp_mul_exp_three_eighths (x : ℝ))
    (mul_le_of_le_one_left (Real.exp_pos _).le eight_div_three_exp_one_le_one)

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-- Every typed polymer is nonempty: `Polymer N` is the subtype of
    `allPlaquettePolymers N`, whose filter `IsPlaquettePolymer`
    carries `Nonempty` as its first conjunct. -/
theorem polymer_card_pos (η : Polymer N) : 0 < (η.val).card := by
  have hmem := η.property
  unfold allPlaquettePolymers at hmem
  rw [Finset.mem_filter] at hmem
  exact Finset.card_pos.mpr hmem.2.1

theorem one_le_polymer_card (η : Polymer N) : 1 ≤ (η.val).card :=
  polymer_card_pos η

/-- **Count ≤ tuple mass**: k = Σᵢ 1 ≤ Σᵢ card(δ i). Repetitions in
    the tuple are counted on both sides (sums over positions). -/
theorem nat_le_tupleTotalCard {k : ℕ} (δ : Fin k → Polymer N) :
    k ≤ tupleTotalCard δ := by
  unfold tupleTotalCard
  calc k = ∑ _i : Fin k, 1 := by simp
    _ ≤ ∑ i : Fin k, ((δ i).val).card :=
        Finset.sum_le_sum (fun i _ => one_le_polymer_card (δ i))

/-- **Family cardinality ≤ family mass** (a family is a Finset of
    distinct polymers; each contributes at least one plaquette).
    Distinct from the existing `card_le_familyTotalCard`
    (CovarianceBadPairMass), which bounds ONE member's card. -/
theorem familyCard_le_familyTotalCard (T : Finset (Polymer N)) :
    T.card ≤ familyTotalCard T := by
  unfold familyTotalCard
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum (fun η _ => one_le_polymer_card η)

/-! ## 52-A0.C — the tilted KP hypothesis at λ = 7/8 -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **The eighth budget**: 64q/(1 − r) ≤ 8/113, from q ≤ 1/5000 and
    1 − r ≥ 113/625 (exact rational arithmetic, no decimals). -/
theorem kpScalar_le_eight_div_113 {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    64 * kpQ β 1 / (1 - kpR β 1) ≤ 8 / 113 := by
  have hq := kpQ_le_one_div_5000 hβ hsmall
  have hq0 := kpQ_nonneg hβ 1
  have hrle := kpR_le_512_div_625 hβ hsmall
  have hpos : 0 < 1 - kpR β 1 := by linarith
  rw [div_le_iff₀ hpos]
  unfold kpR
  nlinarith

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
theorem kpScalar_le_one_div_eight {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    64 * kpQ β 1 / (1 - kpR β 1) ≤ 1 / 8 :=
  le_trans (kpScalar_le_eight_div_113 hβ hsmall) (by norm_num)

/-- The complementary penalty of the tilt 7/8: card/8. -/
noncomputable def kpEighthCardPenalty (η : Polymer N) : ℝ :=
  (1/8 : ℝ) * ((η.val.card : ℕ) : ℝ)

theorem kpEighthCardPenalty_nonneg (η : Polymer N) :
    0 ≤ kpEighthCardPenalty η :=
  mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-- The finite KP sum with ONE EIGHTH of the right-hand side
    (Stone 46's geometric bound consumed through the general
    theorem, exactly as `kp_sum_le_half_card`). -/
theorem kp_sum_le_eighth_card
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp ((D.card : ℝ)))
      ≤ (1/8 : ℝ) * C.card := by
  have hr := kpR_lt_one_of_small_beta hβ hsmall
  have h := incompatible_kp_sum_geometric_bound
    μm hβ mχ hχabs hr C
  unfold kpActivityWeight at h
  simp only [one_mul] at h
  refine h.trans ?_
  calc (C.card : ℝ) * (64 * kpQ β 1 / (1 - kpR β 1))
      ≤ (C.card : ℝ) * (1/8 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (kpScalar_le_one_div_eight hβ hsmall) (Nat.cast_nonneg _)
    _ = (1/8 : ℝ) * C.card := mul_comm _ _

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **Recombination at 7/8**: tilt (7/8) × exp(card/8) = |w|·e^{card}. -/
theorem massTilt_sevenEighths_mul_exp_penalty {β : ℝ} (χ : G → ℝ)
    (η : Polymer N) :
    massTiltActivity (7/8)
        (fun η => |polymerWeight (N := N) μm β χ η.val|) η
      * Real.exp (kpEighthCardPenalty η)
      = |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((η.val.card : ℕ) : ℝ) := by
  simp only [massTiltActivity, kpEighthCardPenalty]
  rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **THE TILTED KP HYPOTHESIS AT λ = 7/8** with penalty card/8. -/
theorem abstractKP_massTilt_sevenEighths_polymerWeight
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    AbstractKPHypothesis (N := N)
      (massTiltActivity (7/8)
        (fun η => |polymerWeight (N := N) μm β χ η.val|))
      kpEighthCardPenalty := by
  intro γ₀
  show (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * massTiltActivity (7/8)
            (fun η => |polymerWeight (N := N) μm β χ η.val|) η
        * Real.exp (kpEighthCardPenalty η))
    ≤ kpEighthCardPenalty γ₀
  calc (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * massTiltActivity (7/8)
            (fun η => |polymerWeight (N := N) μm β χ η.val|) η
        * Real.exp (kpEighthCardPenalty η))
      = ∑ η : Polymer N,
          ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
            * (|polymerWeight (N := N) μm β χ η.val|
              * Real.exp ((η.val.card : ℕ) : ℝ)) :=
        Finset.sum_congr rfl (fun η _ => by
          rw [mul_assoc, massTilt_sevenEighths_mul_exp_penalty])
    _ = ∑ D ∈ incompatiblePolymers γ₀.val,
          |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)) :=
        sum_indicator_eq_sum_incompatible γ₀
          (fun D => |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)))
    _ ≤ (1/8 : ℝ) * γ₀.val.card :=
        kp_sum_le_eighth_card μm hβ mχ hχabs hsmall γ₀.val
    _ = kpEighthCardPenalty γ₀ := rfl

/-! ## 52-A0.D — recombination of the envelope, λ-free -/

/-- Tilts compose additively. -/
theorem massTiltActivity_comp (lam₁ lam₂ : ℝ) (ρ : Polymer N → ℝ) :
    massTiltActivity lam₁ (massTiltActivity lam₂ ρ)
      = massTiltActivity (lam₁ + lam₂) ρ := by
  funext η
  simp only [massTiltActivity]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **λ-independence as a formal consequence**: for ANY tilt λ with
    the complementary penalty (1 − λ)·card, the forbidden-root
    envelope is the λ-free sum Σ_{¬P} ρ·e^{card}. -/
theorem kpForbiddenRootEnvelope_massTilt_complement (lam : ℝ)
    (ρ : Polymer N → ℝ) (P : Polymer N → Prop) :
    kpForbiddenRootEnvelope (massTiltActivity lam ρ)
        (fun η => (1 - lam) * ((η.val.card : ℕ) : ℝ)) P
      = ∑ γ₀ : Polymer N,
          if P γ₀ then 0
          else ρ γ₀ * Real.exp ((γ₀.val.card : ℕ) : ℝ) := by
  unfold kpForbiddenRootEnvelope
  refine Finset.sum_congr rfl (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    simp only [massTiltActivity]
    rw [mul_comm (Real.exp _) _, mul_assoc, ← Real.exp_add]
    congr 2
    ring

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- The 7/8 instance, with the penalty in its named form. -/
theorem kpForbiddenRootEnvelope_massTilt_sevenEighths {β : ℝ}
    (χ : G → ℝ) (P : Polymer N → Prop) :
    kpForbiddenRootEnvelope
        (massTiltActivity (7/8)
          (fun η => |polymerWeight (N := N) μm β χ η.val|))
        kpEighthCardPenalty P
      = ∑ γ₀ : Polymer N,
          if P γ₀ then 0
          else |polymerWeight (N := N) μm β χ γ₀.val|
            * Real.exp ((γ₀.val.card : ℕ) : ℝ) := by
  have h := kpForbiddenRootEnvelope_massTilt_complement (N := N) (7/8)
    (fun η => |polymerWeight (N := N) μm β χ η.val|) P
  have hpen : (fun η : Polymer N => (1 - (7/8 : ℝ)) * ((η.val.card : ℕ) : ℝ))
      = kpEighthCardPenalty := by
    funext η
    unfold kpEighthCardPenalty
    norm_num
  rw [hpen] at h
  exact h

/-- **The 7/8 envelope is localized by the SAME 2/113 per barrier
    link** (existing localization consumed; nothing recounted). -/
theorem kpForbiddenRootEnvelope_sevenEighths_le_barrierLinkCount
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    kpForbiddenRootEnvelope
        (massTiltActivity (7/8)
          (fun η => |polymerWeight (N := N) μm β χ η.val|))
        kpEighthCardPenalty (remoteAllowed (N := N) T s)
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) := by
  rw [kpForbiddenRootEnvelope_massTilt_sevenEighths]
  exact kpForbiddenRootEnvelope_le_barrierLinkCount μm hβ mχ hχabs hsmall T s

/-! ## 52-A0.E — the two first moments -/

/-- **Tuple-wise absorption of the count**: k·(summand of ρ) ≤
    (8/(3e))·(summand of the 3/8-tilted ρ). -/
theorem nat_mul_kpAbsSummand_le_tilt_three_eighths
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    {k : ℕ} (δ : Fin k → Polymer N) :
    (k : ℝ) * kpAbsSummand ρ δ
      ≤ (8 / (3 * Real.exp 1))
          * kpAbsSummand (massTiltActivity (3/8) ρ) δ := by
  rw [kpAbsSummand_massTilt]
  have hk : (k : ℝ) ≤ (tupleTotalCard δ : ℝ) :=
    Nat.cast_le.mpr (nat_le_tupleTotalCard δ)
  have habs := le_eight_div_three_exp_mul_exp_three_eighths
    ((tupleTotalCard δ : ℕ) : ℝ)
  have hs := kpAbsSummand_nonneg hρ δ
  calc (k : ℝ) * kpAbsSummand ρ δ
      ≤ ((8 / (3 * Real.exp 1))
          * Real.exp ((3 / 8 : ℝ) * ((tupleTotalCard δ : ℕ) : ℝ)))
          * kpAbsSummand ρ δ :=
        mul_le_mul_of_nonneg_right (le_trans hk habs) hs
    _ = (8 / (3 * Real.exp 1))
          * (Real.exp ((3 / 8 : ℝ) * ((tupleTotalCard δ : ℕ) : ℝ))
            * kpAbsSummand ρ δ) := by ring

/-- Lifted to the coefficient. -/
theorem nat_mul_kpAbsConnector_le_tilt_three_eighths
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (k : ℕ) (P Q : Polymer N → Prop) :
    (k : ℝ) * kpAbsConnectorUnrootedCoeff k ρ P Q
      ≤ (8 / (3 * Real.exp 1))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity (3/8) ρ) P Q := by
  rw [kpAbsConnectorUnrootedCoeff_eq, kpAbsConnectorUnrootedCoeff_eq,
    ← mul_div_assoc, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum (fun δ _ => ?_)
  by_cases hhit : TupleHitsBothForbidden P Q δ
  · rw [if_pos hhit, if_pos hhit]
    exact nat_mul_kpAbsSummand_le_tilt_three_eighths hρ δ
  · rw [if_neg hhit, if_neg hhit, mul_zero, mul_zero]

/-- **Composite per-coefficient bound**: k·A_k(ρ) ≤ (8/(3e))·e^{−q/2}·
    A_k(ρ tilted by 7/8), across barriers walk-separated by q. -/
theorem nat_mul_kpAbsConnector_le_exp_neg_half_tilt_sevenEighths
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η) (k : ℕ)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') q) :
    (k : ℝ) * kpAbsConnectorUnrootedCoeff k ρ
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')
      ≤ (8 / (3 * Real.exp 1)) * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity (7/8) ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := by
  have h1 := nat_mul_kpAbsConnector_le_tilt_three_eighths hρ k
    (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s')
  have hρ' : ∀ η, 0 ≤ massTiltActivity (3/8) ρ η :=
    massTiltActivity_nonneg hρ
  have h2 := kpAbsConnector_le_exp_neg_mul_tilt
    (by norm_num : (0 : ℝ) ≤ 1/2) hρ' (k := k) hwsep
  rw [massTiltActivity_comp] at h2
  have h78 : ((1/2 : ℝ) + 3/8) = 7/8 := by norm_num
  rw [h78] at h2
  have hc : (0 : ℝ) ≤ 8 / (3 * Real.exp 1) := by positivity
  calc (k : ℝ) * kpAbsConnectorUnrootedCoeff k ρ
        (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s')
      ≤ (8 / (3 * Real.exp 1))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity (3/8) ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := h1
    _ ≤ (8 / (3 * Real.exp 1))
          * (Real.exp (-(1/2 : ℝ) * (q : ℝ))
            * kpAbsConnectorUnrootedCoeff k (massTiltActivity (7/8) ρ)
                (remoteAllowed (N := N) T s)
                (remoteAllowed (N := N) T' s')) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = (8 / (3 * Real.exp 1)) * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * kpAbsConnectorUnrootedCoeff k (massTiltActivity (7/8) ρ)
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := by ring

/-- **FIRST MOMENT OF THE CONNECTOR (P side)**: the count k is paid
    by the tilt 3/8, the separation by the tilt 1/2, the total tilt
    7/8 is covered by the eighth KP budget, and the envelope is the
    same 2/113 per barrier link. Summability included. -/
theorem summable_nat_mul_kpAbsConnector_polymerWeight
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') q) :
    Summable (fun k : ℕ => (k : ℝ)
      * kpAbsConnectorUnrootedCoeff k
          (fun η => |polymerWeight (N := N) μm β χ η.val|)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s')) := by
  have hρ : ∀ η : Polymer N, 0 ≤ |polymerWeight (N := N) μm β χ η.val| :=
    fun η => abs_nonneg _
  have hKP := abstractKP_massTilt_sevenEighths_polymerWeight
    (N := N) μm hβ mχ hχabs hsmall
  have hsum := summable_kpAbsConnectorUnrootedCoeff
    (massTiltActivity_nonneg hρ) kpEighthCardPenalty_nonneg hKP
    (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s')
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (Nat.cast_nonneg _)
      (kpAbsConnectorUnrootedCoeff_nonneg k hρ _ _))
    (fun k => nat_mul_kpAbsConnector_le_exp_neg_half_tilt_sevenEighths
      hρ k hwsep)
    (Summable.mul_left _ hsum)

theorem tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {q : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') q) :
    (∑' k : ℕ, (k : ℝ)
      * kpAbsConnectorUnrootedCoeff k
          (fun η => |polymerWeight (N := N) μm β χ η.val|)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s'))
      ≤ Real.exp (-(q : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
  have hρ : ∀ η : Polymer N, 0 ≤ |polymerWeight (N := N) μm β χ η.val| :=
    fun η => abs_nonneg _
  have hKP := abstractKP_massTilt_sevenEighths_polymerWeight
    (N := N) μm hβ mχ hχabs hsmall
  have hsum := summable_kpAbsConnectorUnrootedCoeff
    (massTiltActivity_nonneg hρ) kpEighthCardPenalty_nonneg hKP
    (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s')
  have htail := tsum_kpAbsConnector_le
    (massTiltActivity_nonneg hρ) kpEighthCardPenalty_nonneg hKP
    (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s')
  have henv := kpForbiddenRootEnvelope_sevenEighths_le_barrierLinkCount
    μm hβ mχ hχabs hsmall T s
  have hc1 := eight_div_three_exp_one_le_one
  have hc0 : (0 : ℝ) ≤ 8 / (3 * Real.exp 1) := by positivity
  have hE : (0 : ℝ) ≤ Real.exp (-(1/2 : ℝ) * (q : ℝ)) := (Real.exp_pos _).le
  have hS : (0 : ℝ) ≤ ∑' k : ℕ, kpAbsConnectorUnrootedCoeff k
      (massTiltActivity (7/8)
        (fun η => |polymerWeight (N := N) μm β χ η.val|))
      (remoteAllowed (N := N) T s) (remoteAllowed (N := N) T' s') :=
    tsum_nonneg (fun k => kpAbsConnectorUnrootedCoeff_nonneg k
      (massTiltActivity_nonneg hρ) _ _)
  calc (∑' k : ℕ, (k : ℝ)
      * kpAbsConnectorUnrootedCoeff k
          (fun η => |polymerWeight (N := N) μm β χ η.val|)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s'))
      ≤ ∑' k : ℕ, (8 / (3 * Real.exp 1)) * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * kpAbsConnectorUnrootedCoeff k
              (massTiltActivity (7/8)
                (fun η => |polymerWeight (N := N) μm β χ η.val|))
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') :=
        tsum_le_tsum
          (fun k => nat_mul_kpAbsConnector_le_exp_neg_half_tilt_sevenEighths
            hρ k hwsep)
          (summable_nat_mul_kpAbsConnector_polymerWeight
            μm hβ mχ hχabs hsmall hwsep)
          (Summable.mul_left _ hsum)
    _ = (8 / (3 * Real.exp 1)) * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * ∑' k : ℕ, kpAbsConnectorUnrootedCoeff k
              (massTiltActivity (7/8)
                (fun η => |polymerWeight (N := N) μm β χ η.val|))
              (remoteAllowed (N := N) T s)
              (remoteAllowed (N := N) T' s') := tsum_mul_left
    _ ≤ (8 / (3 * Real.exp 1)) * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) :=
        mul_le_mul_of_nonneg_left (le_trans htail henv)
          (mul_nonneg hc0 hE)
    _ ≤ 1 * Real.exp (-(1/2 : ℝ) * (q : ℝ))
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
        have hb : (0 : ℝ) ≤ ((barrierLinkFinset T s).card : ℝ) * (2 / 113) :=
          mul_nonneg (Nat.cast_nonneg _) (by norm_num)
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hc1 hE) hb
        exact this
    _ = Real.exp (-(q : ℝ) / 2)
          * (((barrierLinkFinset T s).card : ℝ) * (2 / 113)) := by
        rw [one_mul, show (-(1/2 : ℝ) * (q : ℝ)) = -(q : ℝ) / 2 from by ring]

/-- **FIRST MOMENT OF A BRIDGE CORE**: card T·|N_f(s,T)| ≤
    Cf·e^{−n/2}·e^{b_T}·Π massTilt(7/8) majorant. The chain is
    explicit: card T ≤ m_T ≤ (8/(3e))·e^{3 m_T/8} ≤ e^{3 m_T/8}, and
    n ≤ m_T pays e^{−n/2}·e^{m_T/2}; the normalized ratio costs
    e^{b_T} (existing transport). -/
theorem nat_card_mul_abs_normalizedMarkedCoreTerm_le_bridge
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    (T.card : ℝ) * |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
  -- the mass toll of the bridge core
  have hn : n ≤ familyTotalCard T :=
    activityBridgeCore_familyTotalCard_ge hT hsep
  have hnR : (n : ℝ) ≤ (familyTotalCard T : ℝ) := Nat.cast_le.mpr hn
  -- the count-to-mass step and its absorption
  have hcard : (T.card : ℝ) ≤ (familyTotalCard T : ℝ) :=
    Nat.cast_le.mpr (familyCard_le_familyTotalCard T)
  have habs := nat_le_exp_three_eighths (familyTotalCard T)
  -- the core weight against the Mayer majorant
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have hM : (0 : ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  -- the normalized transport: |N| ≤ L·e^{b_T} with L = card·(Cf Π majorant)… done
  -- termwise below to keep the count outside the transport.
  have hN := abs_normalizedMarkedCoreTerm_le_of_abs_le
    μm hβ mχ hχabs hsmall (s := s) (T := T) (f := f) hW
  have hb0 : (0 : ℝ) ≤ Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
    (Real.exp_pos _).le
  -- e^{−n/2}·e^{m/2} ≥ 1 and e^{3m/8}·e^{m/2} = e^{7m/8}
  have hpay : (1 : ℝ) ≤ Real.exp (-(n : ℝ) / 2)
      * Real.exp ((familyTotalCard T : ℝ) / 2) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hprod := prod_family_massTiltActivity (N := N) (7/8)
    (mayerCoreMajorant β) T
  calc (T.card : ℝ) * |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ (T.card : ℝ) * ((Cf * ∏ η ∈ T, mayerCoreMajorant β η)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_left hN (Nat.cast_nonneg _)
    _ ≤ Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
          * ((Cf * ∏ η ∈ T, mayerCoreMajorant β η)
            * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))) :=
        mul_le_mul_of_nonneg_right (le_trans hcard habs)
          (mul_nonneg (mul_nonneg hCf0 hM) hb0)
    _ ≤ (Real.exp (-(n : ℝ) / 2) * Real.exp ((familyTotalCard T : ℝ) / 2))
          * (Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
            * ((Cf * ∏ η ∈ T, mayerCoreMajorant β η)
              * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)))) := by
        refine le_mul_of_one_le_left ?_ hpay
        exact mul_nonneg (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hCf0 hM) hb0)
    _ = Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * (Real.exp ((7/8 : ℝ) * (familyTotalCard T : ℝ))
            * ∏ η ∈ T, mayerCoreMajorant β η) := by
        have h78 : Real.exp ((familyTotalCard T : ℝ) / 2)
            * Real.exp ((3/8 : ℝ) * (familyTotalCard T : ℝ))
            = Real.exp ((7/8 : ℝ) * (familyTotalCard T : ℝ)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← h78]; ring
    _ = Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := by
        rw [hprod]

/-! ## 52-A0.F — the core budget instance (7/8, 1) -/

/-- **(λ, κ) = (7/8, 1)**: 7/8 + 8/113 = 855/904 ≤ 1; the sum of
    e^{b_T}·Π massTilt(7/8) majorant over the touching cores is at
    most exp(2·D_s·(2/113)). The instance (1/2, 3) used by the
    connector column is the existing `sum_halfTilt_three_le`; the
    combination (7/8, 3) is NOT available (983/904 > 1) and is not
    needed. -/
theorem sum_sevenEighthsTilt_one_le
    {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)
      ≤ Real.exp
          (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
  have h := coreLocalBudget (N := N) (lam := 7/8) (κ := 1)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η)
      ≤ Real.exp (((1:ℝ) + 1)
          * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := h
    _ = Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)) := by
        rw [show ((1:ℝ) + 1) = 2 from by norm_num]

/-- The bridge first moment in the budget's summand form (κ = 1),
    ready for `sum_sevenEighthsTilt_one_le`. -/
theorem nat_card_mul_abs_normalizedMarkedCoreTerm_le_budgetTerm
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    {T : Finset (Polymer N)} {s r : Set (Link N)} {n : ℕ}
    (hT : T ∈ activityBridgeCores (N := N) s r)
    (hsep : WalkBarrierSeparated (N := N) s r n) :
    (T.card : ℝ) * |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
  have h := nat_card_mul_abs_normalizedMarkedCoreTerm_le_bridge
    μm hβ mχ hχabs hsmall mf hCf0 hCf hT hsep
  calc (T.card : ℝ) * |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ Cf * Real.exp (-(n : ℝ) / 2)
          * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η := h
    _ = Real.exp (-(n : ℝ) / 2) * Cf
          * (Real.exp (1 * ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, massTiltActivity (7/8) (mayerCoreMajorant β) η) := by
        rw [one_mul]; ring

#print axioms one_sub_dampedPow_le_nat_mul_one_sub
#print axioms eight_div_three_exp_one_le_one
#print axioms nat_le_exp_three_eighths
#print axioms nat_le_tupleTotalCard
#print axioms familyCard_le_familyTotalCard
#print axioms abstractKP_massTilt_sevenEighths_polymerWeight
#print axioms kpForbiddenRootEnvelope_massTilt_complement
#print axioms kpForbiddenRootEnvelope_sevenEighths_le_barrierLinkCount
#print axioms tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P
#print axioms nat_card_mul_abs_normalizedMarkedCoreTerm_le_bridge
#print axioms sum_sevenEighthsTilt_one_le

end LatticeGauge
