/-
LatticeGauge/KPConnectorTiltSpecialization.lean — PEDRA 50, Gate
50-A11: THE CONCRETE TILTED KP — HALF BUDGET, HALF MASS
(architecture: Sol; execution: Fable).

The abstract mass-tilted connector tail of A10 is specialized to
the concrete polymerWeight under the PUBLISHED threshold
0 ≤ β ≤ 1/40000, with the mandatory split
  λ = 1/2,   a(η) = card(η)/2,
so that tilt and penalty recompose EXACTLY the old weight:
  e^{card/2}·|w_β|·e^{card/2} = |w_β|·e^{card},
and the α = 1 capital of Stone 46 remains the combinatorial
majorant consumed — never recounted. The strong scalar budget:
  q = kpQ β 1 ≤ 1/5000,  r = kpR β 1 ≤ 512/625 < 1,
  64q/(1−r) ≤ 1/2   (no optimality of 1/2 claimed),
delivers the finite KP sum with HALF the RHS, hence the concrete
tilted KP hypothesis, hence the capstones:
  Σ'ₖ |connectorₖ(w_β)| ≤ e^{-n/2} · (concrete forbidden-root
  envelope Σ_{γ₀ not allowed} |w_β(γ₀)|·e^{card γ₀}),
for walk-separated barriers at distance n. This is an abstract
tail with an explicit rate — NOT covariance decay, NOT clustering.

NOT here (hard hold): no λ = 1, no change to 1/40000, no
optimality claim, no redoing Stone 45/46 (no walk counting, no
geometric series, no 64^d), no polymer recount, no
SimpleGraph.dist, no covariance, no Z[fg]·Z − Z[f]·Z[g] wiring,
no envelope localization, no correlation decay, no clustering, no
thermodynamic limit, no continuum, no mass gap, no Clay claim.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPSpecialization
import LatticeGauge.KPConnectorMassTilt

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A11.1 — the half-cardinality penalty -/

noncomputable def kpHalfCardPenalty (η : Polymer N) : ℝ :=
  (1/2 : ℝ) * ((η.val.card : ℕ) : ℝ)

theorem kpHalfCardPenalty_nonneg (η : Polymer N) :
    0 ≤ kpHalfCardPenalty η :=
  mul_nonneg (by norm_num) (Nat.cast_nonneg _)

/-! ## A11.2 — the strong scalar budget (visible arithmetic;
    Stone 46's kpQ/kpR consumed, KPSmallness never rebuilt) -/

theorem kpQ_le_one_div_5000 {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    kpQ β 1 ≤ 1 / 5000 := by
  unfold kpQ
  have h1 : β * Real.exp 1 ≤ (1 / 40000) * Real.exp 1 :=
    mul_le_mul_of_nonneg_right hsmall (Real.exp_pos 1).le
  have h4 := exp_one_lt_four
  nlinarith

theorem kpR_le_512_div_625 {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    kpR β 1 ≤ 512 / 625 := by
  unfold kpR
  have := kpQ_le_one_div_5000 hβ hsmall
  linarith

theorem kpR_lt_one_of_small_beta {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    kpR β 1 < 1 :=
  lt_of_le_of_lt (kpR_le_512_div_625 hβ hsmall) (by norm_num)

/-- **The half budget** (no optimality of 1/2 claimed): the
    denominator stays positive (1 − r ≥ 113/625) and
    64q ≤ 64/5000, so the scalar is at most 2112/5000·… ≤ 1/2. -/
theorem kpScalar_le_half {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    64 * kpQ β 1 / (1 - kpR β 1) ≤ 1 / 2 := by
  have hq := kpQ_le_one_div_5000 hβ hsmall
  have hq0 := kpQ_nonneg hβ 1
  have hrle := kpR_le_512_div_625 hβ hsmall
  have hpos : 0 < 1 - kpR β 1 := by linarith
  rw [div_le_iff₀ hpos]
  unfold kpR
  linarith

/-! ## A11.3 — the finite KP sum with HALF the right-hand side
    (Stone 46's geometric bound consumed through the general
    theorem; no geometry, no doubled walks, no series redone) -/

theorem kp_sum_le_half_card
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp ((D.card : ℝ)))
      ≤ (1/2 : ℝ) * C.card := by
  have hr := kpR_lt_one_of_small_beta hβ hsmall
  have h := incompatible_kp_sum_geometric_bound
    μm hβ mχ hχabs hr C
  unfold kpActivityWeight at h
  simp only [one_mul] at h
  refine h.trans ?_
  calc (C.card : ℝ) * (64 * kpQ β 1 / (1 - kpR β 1))
      ≤ (C.card : ℝ) * (1/2 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (kpScalar_le_half hβ hsmall) (Nat.cast_nonneg _)
    _ = (1/2 : ℝ) * C.card := mul_comm _ _

/-! ## A11.4 — the split-budget identity: tilt × penalty
    recomposes the α = 1 weight exactly -/

theorem massTilt_half_mul_exp_penalty {β : ℝ} (χ : G → ℝ)
    (η : Polymer N) :
    massTiltActivity (1/2)
        (fun η => |polymerWeight (N := N) μm β χ η.val|) η
      * Real.exp (kpHalfCardPenalty η)
      = |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((η.val.card : ℕ) : ℝ) := by
  simp only [massTiltActivity, kpHalfCardPenalty]
  calc Real.exp ((1/2 : ℝ) * ((η.val.card : ℕ) : ℝ))
        * |polymerWeight (N := N) μm β χ η.val|
        * Real.exp ((1/2 : ℝ) * ((η.val.card : ℕ) : ℝ))
      = |polymerWeight (N := N) μm β χ η.val|
          * (Real.exp ((1/2 : ℝ) * ((η.val.card : ℕ) : ℝ))
            * Real.exp ((1/2 : ℝ) * ((η.val.card : ℕ) : ℝ))) := by
        ring
    _ = |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((1/2 : ℝ) * ((η.val.card : ℕ) : ℝ)
              + (1/2 : ℝ) * ((η.val.card : ℕ) : ℝ)) := by
        rw [← Real.exp_add]
    _ = |polymerWeight (N := N) μm β χ η.val|
          * Real.exp ((η.val.card : ℕ) : ℝ) := by
        rw [show (1/2 : ℝ) * ((η.val.card : ℕ) : ℝ)
            + (1/2 : ℝ) * ((η.val.card : ℕ) : ℝ)
            = ((η.val.card : ℕ) : ℝ) from by ring]

/-! ## A11.5 — THE CONCRETE TILTED KP HYPOTHESIS (analytic
    capstone; the 47c-C1 glue route, half budget consumed) -/

theorem abstractKP_massTilt_half_polymerWeight
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) :
    AbstractKPHypothesis (N := N)
      (massTiltActivity (1/2)
        (fun η => |polymerWeight (N := N) μm β χ η.val|))
      kpHalfCardPenalty := by
  intro γ₀
  show (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * massTiltActivity (1/2)
            (fun η => |polymerWeight (N := N) μm β χ η.val|) η
        * Real.exp (kpHalfCardPenalty η))
    ≤ kpHalfCardPenalty γ₀
  calc (∑ η : Polymer N,
      ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
        * massTiltActivity (1/2)
            (fun η => |polymerWeight (N := N) μm β χ η.val|) η
        * Real.exp (kpHalfCardPenalty η))
      = ∑ η : Polymer N,
          ((incompatibilityIndicator γ₀ η : ℕ) : ℝ)
            * (|polymerWeight (N := N) μm β χ η.val|
              * Real.exp ((η.val.card : ℕ) : ℝ)) :=
        Finset.sum_congr rfl (fun η _ => by
          rw [mul_assoc, massTilt_half_mul_exp_penalty])
    _ = ∑ D ∈ incompatiblePolymers γ₀.val,
          |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)) :=
        sum_indicator_eq_sum_incompatible γ₀
          (fun D => |polymerWeight (N := N) μm β χ D|
            * Real.exp ((D.card : ℝ)))
    _ ≤ (1/2 : ℝ) * γ₀.val.card :=
        kp_sum_le_half_card μm hβ mχ hχabs hsmall γ₀.val
    _ = kpHalfCardPenalty γ₀ := rfl

/-! ## A11.6 — normalization of the concrete tilted envelope -/

theorem kpForbiddenRootEnvelope_massTilt_half {β : ℝ}
    (χ : G → ℝ) (P : Polymer N → Prop) :
    kpForbiddenRootEnvelope
        (massTiltActivity (1/2)
          (fun η => |polymerWeight (N := N) μm β χ η.val|))
        kpHalfCardPenalty P
      = ∑ γ₀ : Polymer N,
          if P γ₀ then 0
          else |polymerWeight (N := N) μm β χ γ₀.val|
            * Real.exp ((γ₀.val.card : ℕ) : ℝ) := by
  unfold kpForbiddenRootEnvelope
  refine Finset.sum_congr rfl (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]
    exact massTilt_half_mul_exp_penalty μm χ γ₀

/-! ## A11.7 — THE CONCRETE CAPSTONES: rate e^{-n/2} in the
    statement (A10 consumed; still NOT covariance decay) -/

/-- **CAPSTONE 50-A11 (P side)**. -/
theorem tsum_abs_kpConnector_polymerWeight_le_exp_neg_half
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-(n : ℝ)/2)
          * ∑ γ₀ : Polymer N,
              if remoteAllowed (N := N) T s γ₀ then 0
              else |polymerWeight (N := N) μm β χ γ₀.val|
                * Real.exp ((γ₀.val.card : ℕ) : ℝ) := by
  have hKP := abstractKP_massTilt_half_polymerWeight
    (N := N) μm hβ mχ hχabs hsmall
  have h := tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope
    (by norm_num : (0 : ℝ) ≤ 1/2)
    kpHalfCardPenalty_nonneg hKP hwsep
  rw [kpForbiddenRootEnvelope_massTilt_half (N := N) μm
    (β := β) χ (remoteAllowed (N := N) T s)] at h
  rw [show (-(1/2 : ℝ) * (n : ℝ)) = (-(n : ℝ)/2) from by ring]
    at h
  exact h

/-- **CAPSTONE 50-A11 (Q side)**. -/
theorem tsum_abs_kpConnector_polymerWeight_le_exp_neg_half_Q
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k
        (fun η => polymerWeight (N := N) μm β χ η.val)
        (remoteAllowed (N := N) T s)
        (remoteAllowed (N := N) T' s')|)
      ≤ Real.exp (-(n : ℝ)/2)
          * ∑ γ₀ : Polymer N,
              if remoteAllowed (N := N) T' s' γ₀ then 0
              else |polymerWeight (N := N) μm β χ γ₀.val|
                * Real.exp ((γ₀.val.card : ℕ) : ℝ) := by
  have hKP := abstractKP_massTilt_half_polymerWeight
    (N := N) μm hβ mχ hχabs hsmall
  have h := tsum_abs_kpConnector_le_exp_neg_mul_tiltedEnvelope_Q
    (by norm_num : (0 : ℝ) ≤ 1/2)
    kpHalfCardPenalty_nonneg hKP hwsep
  rw [kpForbiddenRootEnvelope_massTilt_half (N := N) μm
    (β := β) χ (remoteAllowed (N := N) T' s')] at h
  rw [show (-(1/2 : ℝ) * (n : ℝ)) = (-(n : ℝ)/2) from by ring]
    at h
  exact h

#print axioms abstractKP_massTilt_half_polymerWeight
#print axioms tsum_abs_kpConnector_polymerWeight_le_exp_neg_half
#print axioms tsum_abs_kpConnector_polymerWeight_le_exp_neg_half_Q

end LatticeGauge
