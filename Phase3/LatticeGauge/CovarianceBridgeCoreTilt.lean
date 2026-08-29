/-
LatticeGauge/CovarianceBridgeCoreTilt.lean — PEDRA 50, Gate
50-A15: THE BRIDGE-CORE TOLL (architecture: Sol; execution:
Fable).

RULING honoured: the raw twoMarkedFamilyIntegral is NOT
estimated (summing raw families before the remote polymers leave
could introduce volume dependence); the correct object is
typedMarkedCoreWeight, the one that appears AFTER the A3
regrouping. The chain of this gate:
  |coreWeight(F, Γ)| ≤ C · Π mayerCoreMajorant     (pointwise
    Mayer bound + probability measure; the integral is NOT
    factorized — core blocks may touch the observable and stay
    joint),
and if the family has a bridge (A14: n ≤ familyTotalCard):
  |coreWeight(F, Γ)| ≤ e^{-λn} · C · Π (half-tilted majorant),
capstone at λ = 1/2 for F = f·g. The toll's origin stays
visible: n ≤ familyTotalCard ⟹ λn ≤ λ·mass ⟹ exp mono; the
e^{-λn} is born from exp(-λn)·exp(λn) = 1.

mayerCoreMajorant (2β)^card is a POINTWISE MAJORANT of
blockActivity — it is NOT a physical activity and NOT
polymerWeight (the A11 tilt lives on polymerWeight; this gate
builds the analogous toll for the joint marked integral).

NOT here (hard hold): no raw twoMarkedFamilyIntegral estimate,
no |polymerWeight| in place of the majorant, no sum over Γ, no
rootedLink counting, no card(s ∪ s') prefactor, no restricted
gas ratio, no T/T' regrouping, no ConnectorClusters, no A12, no
covariance numerator, no covariance decay/clustering, no
SimpleGraph.dist, no thermodynamic limit, no continuum, no mass
gap, no Clay claim. A14 stays frozen.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceBridgeMass
import LatticeGauge.PolymerActivityBound

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A15.1 — the Mayer majorant of the core -/

noncomputable def mayerCoreMajorant (β : ℝ) (η : Polymer N) : ℝ :=
  (2 * β) ^ (η.val).card

theorem mayerCoreMajorant_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (η : Polymer N) :
    0 ≤ mayerCoreMajorant β η :=
  twoBeta_pow_nonneg hβ _

/-! ## A15.2 — the block product (pointwise; compatibility
    deliberately NOT used) -/

theorem abs_prod_blockActivity_le {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (hχabs : ∀ g : G, |χ g| ≤ 1)
    (Γ : Finset (Polymer N)) (U : Config N G) :
    |∏ η ∈ Γ, blockActivity β χ η.val U|
      ≤ ∏ η ∈ Γ, mayerCoreMajorant β η := by
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun η _ => abs_nonneg _)
    (fun η _ => abs_blockActivity_le hβ hχabs η.val U)

/-! ## A15.3 — the generic core-weight majorant (the integral is
    NOT factorized; the 44-stone route with F in front) -/

theorem abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {F : Config N G → ℝ} (mF : Measurable F)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ U, |F U| ≤ C)
    (Γ : Finset (Polymer N)) :
    |typedMarkedCoreWeight μm β χ F Γ|
      ≤ C * ∏ η ∈ Γ, mayerCoreMajorant β η := by
  unfold typedMarkedCoreWeight
  have hmeas : Measurable (fun U : Config N G =>
      F U * ∏ η ∈ Γ, blockActivity β χ η.val U) :=
    mF.mul (Finset.measurable_prod _
      (fun η _ => measurable_blockActivity β mχ η.val))
  have hbound : ∀ U : Config N G,
      |F U * ∏ η ∈ Γ, blockActivity β χ η.val U|
        ≤ C * ∏ η ∈ Γ, mayerCoreMajorant β η := by
    intro U
    rw [abs_mul]
    exact mul_le_mul (hCF U)
      (abs_prod_blockActivity_le hβ hχabs Γ U)
      (abs_nonneg _) hC0
  have hint : Integrable (fun U : Config N G =>
      F U * ∏ η ∈ Γ, blockActivity β χ η.val U)
      (configMeasure μm N) :=
    Integrable.mono'
      (integrable_const (C * ∏ η ∈ Γ, mayerCoreMajorant β η))
      hmeas.aestronglyMeasurable
      (ae_of_all _ (fun U => by
        rw [Real.norm_eq_abs]
        exact hbound U))
  have h1 : ‖∫ U : Config N G,
        F U * ∏ η ∈ Γ, blockActivity β χ η.val U
        ∂(configMeasure μm N)‖
      ≤ ∫ U : Config N G,
          ‖F U * ∏ η ∈ Γ, blockActivity β χ η.val U‖
          ∂(configMeasure μm N) :=
    norm_integral_le_integral_norm _
  simp only [Real.norm_eq_abs] at h1
  calc |∫ U : Config N G,
        F U * ∏ η ∈ Γ, blockActivity β χ η.val U
        ∂(configMeasure μm N)|
      ≤ ∫ U : Config N G,
          |F U * ∏ η ∈ Γ, blockActivity β χ η.val U|
          ∂(configMeasure μm N) := h1
    _ ≤ ∫ _U : Config N G,
          C * ∏ η ∈ Γ, mayerCoreMajorant β η
          ∂(configMeasure μm N) :=
        integral_mono hint.abs (integrable_const _) hbound
    _ = C * ∏ η ∈ Γ, mayerCoreMajorant β η := by
        rw [integral_const, measure_univ, ENNReal.one_toReal,
          one_smul]

/-! ## A15.4 — the exact tilt over a Finset (A10's definition
    consumed; its Ursell-tuple identity NOT converted — this is
    the Finset analogue, the visible chain repeated) -/

theorem prod_family_massTiltActivity (lam : ℝ)
    (ρ : Polymer N → ℝ) (Γ : Finset (Polymer N)) :
    (∏ η ∈ Γ, massTiltActivity lam ρ η)
      = Real.exp (lam * (familyTotalCard Γ : ℝ))
        * ∏ η ∈ Γ, ρ η := by
  unfold massTiltActivity
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Real.exp_sum]
  congr 1
  unfold familyTotalCard
  rw [Nat.cast_sum, Finset.mul_sum]

/-! ## A15.5 — the A14 mass enters -/

/-- The explicit composition: n ≤ Σ_bridge card ≤ family mass. -/
theorem bridge_n_le_familyTotalCard {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    n ≤ familyTotalCard Γ :=
  le_trans (bridgeCore_sum_card_ge hne hwsep)
    (bridgeCore_sum_le_familyTotalCard Γ s s')

/-- **exp(λn)·|coreWeight| ≤ C·Π tilted majorant** — the toll's
    origin visible: n ≤ mass ⟹ λn ≤ λ·mass ⟹ exp mono. -/
theorem exp_mass_mul_abs_coreWeight_le_tilt {lam : ℝ}
    (hlam : 0 ≤ lam) {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {F : Config N G → ℝ} (mF : Measurable F)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ U, |F U| ≤ C)
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    Real.exp (lam * (n : ℝ))
        * |typedMarkedCoreWeight μm β χ F Γ|
      ≤ C * ∏ η ∈ Γ,
          massTiltActivity lam (mayerCoreMajorant β) η := by
  rw [prod_family_massTiltActivity]
  have hmaj : (0 : ℝ)
      ≤ C * ∏ η ∈ Γ, mayerCoreMajorant β η :=
    mul_nonneg hC0
      (Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η))
  calc Real.exp (lam * (n : ℝ))
      * |typedMarkedCoreWeight μm β χ F Γ|
      ≤ Real.exp (lam * (n : ℝ))
          * (C * ∏ η ∈ Γ, mayerCoreMajorant β η) :=
        mul_le_mul_of_nonneg_left
          (abs_typedMarkedCoreWeight_le_mayerCoreMajorant
            μm hβ mχ hχabs mF hC0 hCF Γ)
          (Real.exp_pos _).le
    _ ≤ Real.exp (lam * (familyTotalCard Γ : ℝ))
          * (C * ∏ η ∈ Γ, mayerCoreMajorant β η) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left
              (Nat.cast_le.mpr
                (bridge_n_le_familyTotalCard hne hwsep)) hlam))
          hmaj
    _ = C * (Real.exp (lam * (familyTotalCard Γ : ℝ))
          * ∏ η ∈ Γ, mayerCoreMajorant β η) := by ring

/-! ## A15.6 — the e^{-λn} form -/

theorem abs_coreWeight_le_exp_neg_tilt {lam : ℝ}
    (hlam : 0 ≤ lam) {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {F : Config N G → ℝ} (mF : Measurable F)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ U, |F U| ≤ C)
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    |typedMarkedCoreWeight μm β χ F Γ|
      ≤ Real.exp (-lam * (n : ℝ))
          * (C * ∏ η ∈ Γ,
              massTiltActivity lam (mayerCoreMajorant β) η) := by
  have h1 : Real.exp (-lam * (n : ℝ))
      * Real.exp (lam * (n : ℝ)) = 1 := by
    have h0 : -lam * (n : ℝ) + lam * (n : ℝ) = 0 := by ring
    rw [← Real.exp_add, h0, Real.exp_zero]
  calc (|typedMarkedCoreWeight μm β χ F Γ|)
      = (Real.exp (-lam * (n : ℝ)) * Real.exp (lam * (n : ℝ)))
          * |typedMarkedCoreWeight μm β χ F Γ| := by
        rw [h1, one_mul]
    _ = Real.exp (-lam * (n : ℝ))
          * (Real.exp (lam * (n : ℝ))
            * |typedMarkedCoreWeight μm β χ F Γ|) :=
        mul_assoc _ _ _
    _ ≤ Real.exp (-lam * (n : ℝ))
          * (C * ∏ η ∈ Γ,
              massTiltActivity lam (mayerCoreMajorant β) η) :=
        mul_le_mul_of_nonneg_left
          (exp_mass_mul_abs_coreWeight_le_tilt
            μm hlam hβ mχ hχabs mF hC0 hCF hne hwsep)
          (Real.exp_pos _).le

/-! ## A15.7 — the concrete f·g capstone at λ = 1/2 -/

/-- **CAPSTONE 50-A15**: a bridge core weight of f·g pays
    e^{-n/2} against the half-tilted Mayer majorant. -/
theorem abs_bridgeCoreWeight_mul_le_exp_neg_half
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    |typedMarkedCoreWeight μm β χ (fun U => f U * g U) Γ|
      ≤ Real.exp (-(n : ℝ) / 2)
          * ((Cf * Cg) * ∏ η ∈ Γ,
              massTiltActivity (1/2) (mayerCoreMajorant β) η) := by
  have hfg : ∀ U : Config N G, |f U * g U| ≤ Cf * Cg := by
    intro U
    rw [abs_mul]
    exact mul_le_mul (hCf U) (hCg U) (abs_nonneg _) hCf0
  have h := abs_coreWeight_le_exp_neg_tilt μm
    (lam := 1/2) (by norm_num) hβ mχ hχabs (mf.mul mg)
    (mul_nonneg hCf0 hCg0) hfg hne hwsep
  rw [show (-(1/2 : ℝ) * (n : ℝ)) = (-(n : ℝ) / 2) from by ring]
    at h
  exact h

#print axioms abs_typedMarkedCoreWeight_le_mayerCoreMajorant
#print axioms abs_coreWeight_le_exp_neg_tilt
#print axioms abs_bridgeCoreWeight_mul_le_exp_neg_half

end LatticeGauge
