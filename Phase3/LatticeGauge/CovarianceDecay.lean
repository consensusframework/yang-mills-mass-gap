/-
LatticeGauge/CovarianceDecay.lean — PEDRA 50, Gate 50-A19c:
THE COVARIANCE DECAY (architecture: Sol; execution: Fable).

The final scientific gate of Stone 50. The three normalized
columns of A19b are summed against the published budgets (A17
generic at κ = 1, A19a connector budget at κ = 2), the exact
covariance socket is wired through A13's numerator identity and
the A2/49C marked-gas bridges, and the capstone closes:
  |Cov_β(f,g)| ≤ 3·C_fC_g·e^{6D/113}·e^{-n/2},
where D = |supportLinkFinset s| + |supportLinkFinset s'| is
LOCAL (no volume, no univ.card anywhere) and n is the walk
separation of the supports. CLAIMED: finite-volume exponential
clustering of two local observables in the small-β regime
0 ≤ β ≤ 1/40000. NOT claimed: thermodynamic limit,
volume-uniform clustering beyond the stated local D, continuum
limit, mass gap, Clay.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceNormalizedColumns

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A19c.1 — the union support is locally additive -/

theorem supportLinkFinset_union_card_le (s s' : Set (Link N)) :
    (supportLinkFinset (N := N) (s ∪ s')).card
      ≤ (supportLinkFinset (N := N) s).card
        + (supportLinkFinset (N := N) s').card := by
  have hsub : supportLinkFinset (N := N) (s ∪ s')
      ⊆ supportLinkFinset (N := N) s
        ∪ supportLinkFinset (N := N) s' := by
    intro ℓ hℓ
    rw [Finset.mem_union]
    rcases mem_supportLinkFinset.mp hℓ with h | h
    · exact Or.inl (mem_supportLinkFinset.mpr h)
    · exact Or.inr (mem_supportLinkFinset.mpr h)
  exact le_trans (Finset.card_le_card hsub)
    (Finset.card_union_le _ _)

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## The κ = 1 budget in the 2-exponent dress (A17 generic
    consumed; (1+1) = 2 is the only arithmetic) -/

theorem sum_halfTilt_one_le {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        halfTiltCoreBudgetTerm β 1 s T)
      ≤ Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := by
  have h := coreLocalBudget (lam := 1/2) (κ := 1)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  calc (∑ T ∈ typedTouchingFamilies (N := N) s,
      halfTiltCoreBudgetTerm β 1 s T)
      ≤ Real.exp (((1:ℝ) + 1)
          * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := h
    _ = Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) := by
        rw [show ((1:ℝ) + 1) = 2 from by norm_num]

theorem sum_halfTilt_two_le {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        halfTiltCoreBudgetTerm β 2 s T)
      ≤ Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ)
          * (2/113)) :=
  coreLocalBudget_connector hβ hsmall s

theorem sum_halfTilt_nonneg {β : ℝ} (hβ : 0 ≤ β) (κ : ℝ)
    (s : Set (Link N)) (F : Finset (Finset (Polymer N))) :
    (0:ℝ) ≤ ∑ T ∈ F, halfTiltCoreBudgetTerm β κ s T :=
  Finset.sum_nonneg
    (fun T _ => halfTiltCoreBudgetTerm_nonneg hβ κ s T)

/-! ## A19c.2 — the GOOD column sum -/

theorem abs_goodColumn_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {s s' : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |∑ p ∈ goodCorePairs (N := N) s s',
        normalizedMarkedCoreTerm μm β χ f s p.1
          * normalizedMarkedCoreTerm μm β χ g s' p.2
          * (Real.exp
              (coreConnectorSum μm β χ p.1 p.2 s s') - 1)|
      ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (3 * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) := by
  have hterm0 : ∀ p : Finset (Polymer N) × Finset (Polymer N),
      (0:ℝ) ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * (halfTiltCoreBudgetTerm β 2 s p.1
          * halfTiltCoreBudgetTerm β 2 s' p.2) :=
    fun p => mul_nonneg
      (mul_nonneg (Real.exp_pos _).le (mul_nonneg hCf0 hCg0))
      (mul_nonneg (halfTiltCoreBudgetTerm_nonneg hβ 2 s p.1)
        (halfTiltCoreBudgetTerm_nonneg hβ 2 s' p.2))
  calc |∑ p ∈ goodCorePairs (N := N) s s',
      normalizedMarkedCoreTerm μm β χ f s p.1
        * normalizedMarkedCoreTerm μm β χ g s' p.2
        * (Real.exp
            (coreConnectorSum μm β χ p.1 p.2 s s') - 1)|
      ≤ ∑ p ∈ goodCorePairs (N := N) s s',
          |normalizedMarkedCoreTerm μm β χ f s p.1
            * normalizedMarkedCoreTerm μm β χ g s' p.2
            * (Real.exp
                (coreConnectorSum μm β χ p.1 p.2 s s') - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ goodCorePairs (N := N) s s',
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * (halfTiltCoreBudgetTerm β 2 s p.1
              * halfTiltCoreBudgetTerm β 2 s' p.2) := by
        refine Finset.sum_le_sum (fun p hp => ?_)
        obtain ⟨⟨h1, h2⟩, -⟩ := mem_goodCorePairs.mp hp
        exact abs_normalizedCorePair_connector_le μm hβ mχ
          hχabs hsmall mf mg hCf0 hCg0 hCf hCg h1 h2 hsep
    _ ≤ ∑ p ∈ typedTouchingFamilyPairs (N := N) s s',
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * (halfTiltCoreBudgetTerm β 2 s p.1
              * halfTiltCoreBudgetTerm β 2 s' p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun p _ _ => hterm0 p)
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * ∑ p ∈ typedTouchingFamilyPairs (N := N) s s',
            halfTiltCoreBudgetTerm β 2 s p.1
              * halfTiltCoreBudgetTerm β 2 s' p.2 := by
        rw [Finset.mul_sum]
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * ((∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 2 s T)
          * ∑ T' ∈ typedTouchingFamilies (N := N) s',
              halfTiltCoreBudgetTerm β 2 s' T') := by
        rw [show typedTouchingFamilyPairs (N := N) s s'
            = typedTouchingFamilies (N := N) s
              ×ˢ typedTouchingFamilies (N := N) s' from rfl,
          Finset.sum_mul_sum]
        exact Finset.sum_product
    _ ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * (Real.exp (3
              * ((supportLinkFinset (N := N) s).card : ℝ)
              * (2/113))
          * Real.exp (3
              * ((supportLinkFinset (N := N) s').card : ℝ)
              * (2/113))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (sum_halfTilt_two_le hβ hsmall s)
            (sum_halfTilt_two_le hβ hsmall s')
            (sum_halfTilt_nonneg hβ 2 s' _)
            (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg hCf0 hCg0))
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (3
            * (((supportLinkFinset (N := N) s).card : ℝ)
              + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-! ## A19c.3 — the BRIDGE column sum -/

theorem abs_bridgeColumn_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {s s' : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
        normalizedMarkedCoreTerm μm β χ (fun U => f U * g U)
          (s ∪ s') Γ|
      ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (2 * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) := by
  have hD : (2:ℝ)
      * ((supportLinkFinset (N := N) (s ∪ s')).card : ℝ)
      * (2/113)
      ≤ 2 * (((supportLinkFinset (N := N) s).card : ℝ)
          + ((supportLinkFinset (N := N) s').card : ℝ))
        * (2/113) := by
    have h : ((supportLinkFinset (N := N) (s ∪ s')).card : ℝ)
        ≤ ((supportLinkFinset (N := N) s).card : ℝ)
          + ((supportLinkFinset (N := N) s').card : ℝ) := by
      exact_mod_cast supportLinkFinset_union_card_le s s'
    linarith
  calc |∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
      normalizedMarkedCoreTerm μm β χ (fun U => f U * g U)
        (s ∪ s') Γ|
      ≤ ∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
          |normalizedMarkedCoreTerm μm β χ (fun U => f U * g U)
            (s ∪ s') Γ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * halfTiltCoreBudgetTerm β 1 (s ∪ s') Γ :=
        Finset.sum_le_sum (fun Γ hΓ =>
          abs_normalizedBridgeCore_le μm hβ mχ hχabs hsmall
            mf mg hCf0 hCg0 hCf hCg hΓ hsep)
    _ ≤ ∑ Γ ∈ typedTouchingFamilies (N := N) (s ∪ s'),
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * halfTiltCoreBudgetTerm β 1 (s ∪ s') Γ :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun Γ _ _ => mul_nonneg
            (mul_nonneg (Real.exp_pos _).le
              (mul_nonneg hCf0 hCg0))
            (halfTiltCoreBudgetTerm_nonneg hβ 1 (s ∪ s') Γ))
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * ∑ Γ ∈ typedTouchingFamilies (N := N) (s ∪ s'),
            halfTiltCoreBudgetTerm β 1 (s ∪ s') Γ := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (2
            * ((supportLinkFinset (N := N) (s ∪ s')).card : ℝ)
            * (2/113)) :=
        mul_le_mul_of_nonneg_left
          (sum_halfTilt_one_le hβ hsmall (s ∪ s'))
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg hCf0 hCg0))
    _ ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (2
            * (((supportLinkFinset (N := N) s).card : ℝ)
              + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hD)
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg hCf0 hCg0))

/-! ## A19c.4 — the BAD column sum -/

theorem abs_badColumn_sum_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {s s' : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |∑ p ∈ badCorePairs (N := N) s s',
        normalizedMarkedCoreTerm μm β χ f s p.1
          * normalizedMarkedCoreTerm μm β χ g s' p.2|
      ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (2 * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) := by
  calc |∑ p ∈ badCorePairs (N := N) s s',
      normalizedMarkedCoreTerm μm β χ f s p.1
        * normalizedMarkedCoreTerm μm β χ g s' p.2|
      ≤ ∑ p ∈ badCorePairs (N := N) s s',
          |normalizedMarkedCoreTerm μm β χ f s p.1
            * normalizedMarkedCoreTerm μm β χ g s' p.2| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ badCorePairs (N := N) s s',
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * (halfTiltCoreBudgetTerm β 1 s p.1
              * halfTiltCoreBudgetTerm β 1 s' p.2) :=
        Finset.sum_le_sum (fun p hp =>
          abs_normalizedBadCorePair_le μm hβ mχ hχabs hsmall
            mf mg hCf0 hCg0 hCf hCg hp hsep)
    _ ≤ ∑ p ∈ typedTouchingFamilyPairs (N := N) s s',
          Real.exp (-(n : ℝ)/2) * (Cf * Cg)
            * (halfTiltCoreBudgetTerm β 1 s p.1
              * halfTiltCoreBudgetTerm β 1 s' p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun p _ _ => mul_nonneg
            (mul_nonneg (Real.exp_pos _).le
              (mul_nonneg hCf0 hCg0))
            (mul_nonneg
              (halfTiltCoreBudgetTerm_nonneg hβ 1 s p.1)
              (halfTiltCoreBudgetTerm_nonneg hβ 1 s' p.2)))
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * ∑ p ∈ typedTouchingFamilyPairs (N := N) s s',
            halfTiltCoreBudgetTerm β 1 s p.1
              * halfTiltCoreBudgetTerm β 1 s' p.2 := by
        rw [Finset.mul_sum]
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * ((∑ T ∈ typedTouchingFamilies (N := N) s,
              halfTiltCoreBudgetTerm β 1 s T)
          * ∑ T' ∈ typedTouchingFamilies (N := N) s',
              halfTiltCoreBudgetTerm β 1 s' T') := by
        rw [show typedTouchingFamilyPairs (N := N) s s'
            = typedTouchingFamilies (N := N) s
              ×ˢ typedTouchingFamilies (N := N) s' from rfl,
          Finset.sum_mul_sum]
        exact Finset.sum_product
    _ ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * (Real.exp (2
              * ((supportLinkFinset (N := N) s).card : ℝ)
              * (2/113))
          * Real.exp (2
              * ((supportLinkFinset (N := N) s').card : ℝ)
              * (2/113))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (sum_halfTilt_one_le hβ hsmall s)
            (sum_halfTilt_one_le hβ hsmall s')
            (sum_halfTilt_nonneg hβ 1 s' _)
            (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le
            (mul_nonneg hCf0 hCg0))
    _ = Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (2
            * (((supportLinkFinset (N := N) s).card : ℝ)
              + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-! ## A19c.5 — the exact covariance socket -/

theorem gibbsCovariance_eq_normalized_connector_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g)
    {Cf Cg : ℝ} (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg) :
    gibbsCovariance (N := N) μm β χ f g
      = (∑ p ∈ goodCorePairs (N := N) s s',
          normalizedMarkedCoreTerm μm β χ f s p.1
            * normalizedMarkedCoreTerm μm β χ g s' p.2
            * (Real.exp
                (coreConnectorSum μm β χ p.1 p.2 s s') - 1))
        + (∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
            normalizedMarkedCoreTerm μm β χ
              (fun U => f U * g U) (s ∪ s') Γ)
        - ∑ p ∈ badCorePairs (N := N) s s',
            normalizedMarkedCoreTerm μm β χ f s p.1
              * normalizedMarkedCoreTerm μm β χ g s' p.2 := by
  have hfg : DependsOnlyOn (fun U : Config N G => f U * g U)
      (s ∪ s') := dependsOnlyOn_mul_union hf hg
  have hCfg : ∀ U : Config N G, |f U * g U| ≤ Cf * Cg := by
    intro U
    rw [abs_mul]
    exact mul_le_mul (hCf U) (hCg U) (abs_nonneg _) hCf0
  rw [gibbsCovariance_eq_observableNumerator_cross
      μm hβ mχ hχabs hsmall f g,
    observableNumerator_eq_typedMarkedGas
      μm hβ mχ hχabs hfg (mf.mul mg) hCfg,
    observableNumerator_eq_typedMarkedGas
      μm hβ mχ hχabs hf mf hCf,
    observableNumerator_eq_typedMarkedGas
      μm hβ mχ hχabs hg mg hCg,
    realZ_eq_typed_polymer_gas μm hβ mχ hχabs]
  exact covariance_normalized_connector_ledger
    μm hβ mχ hχabs hsmall hss' hf mf hg mg

/-! ## A19c.6 — CAPSTONE: finite-volume exponential clustering
    in the small-β regime -/

/-- **CAPSTONE 50-A19c — THE COVARIANCE DECAY**: for local
    observables with disjoint supports separated by n in the
    walk metric, under 0 ≤ β ≤ 1/40000,
      |Cov_β(f,g)| ≤ 3·C_fC_g·e^{6D/113}·e^{-n/2},
    with D the LOCAL total support size. Finite volume; the
    rate 1/2 and the prefactor are explicit and volume-free. -/
theorem abs_gibbsCovariance_le_local_exp_decay
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |gibbsCovariance (N := N) μm β χ f g|
      ≤ 3 * (Cf * Cg)
        * Real.exp (6 * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ)) / 113)
        * Real.exp (-(n : ℝ)/2) := by
  have hG := abs_goodColumn_sum_le μm hβ mχ hχabs hsmall
    mf mg hCf0 hCg0 hCf hCg (s := s) (s' := s') hsep
  have hB := abs_bridgeColumn_sum_le μm hβ mχ hχabs hsmall
    mf mg hCf0 hCg0 hCf hCg hsep
  have hR := abs_badColumn_sum_le μm hβ mχ hχabs hsmall
    mf mg hCf0 hCg0 hCf hCg hsep
  have hK0 : (0:ℝ) ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg) :=
    mul_nonneg (Real.exp_pos _).le (mul_nonneg hCf0 hCg0)
  have hD0 : (0:ℝ)
      ≤ ((supportLinkFinset (N := N) s).card : ℝ)
        + ((supportLinkFinset (N := N) s').card : ℝ) :=
    add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmono : Real.exp (2
        * (((supportLinkFinset (N := N) s).card : ℝ)
          + ((supportLinkFinset (N := N) s').card : ℝ))
        * (2/113))
      ≤ Real.exp (3
          * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
          * (2/113)) := by
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hscale : Real.exp (-(n : ℝ)/2) * (Cf * Cg)
      * Real.exp (2
          * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
          * (2/113))
      ≤ Real.exp (-(n : ℝ)/2) * (Cf * Cg)
        * Real.exp (3
            * (((supportLinkFinset (N := N) s).card : ℝ)
              + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113)) :=
    mul_le_mul_of_nonneg_left hmono hK0
  rw [gibbsCovariance_eq_normalized_connector_ledger
    μm hβ mχ hχabs hsmall hss' hf mf hg mg hCf hCg hCf0 hCg0]
  have htri : |(∑ p ∈ goodCorePairs (N := N) s s',
      normalizedMarkedCoreTerm μm β χ f s p.1
        * normalizedMarkedCoreTerm μm β χ g s' p.2
        * (Real.exp
            (coreConnectorSum μm β χ p.1 p.2 s s') - 1))
      + (∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
          normalizedMarkedCoreTerm μm β χ
            (fun U => f U * g U) (s ∪ s') Γ)
      - ∑ p ∈ badCorePairs (N := N) s s',
          normalizedMarkedCoreTerm μm β χ f s p.1
            * normalizedMarkedCoreTerm μm β χ g s' p.2|
      ≤ |∑ p ∈ goodCorePairs (N := N) s s',
          normalizedMarkedCoreTerm μm β χ f s p.1
            * normalizedMarkedCoreTerm μm β χ g s' p.2
            * (Real.exp
                (coreConnectorSum μm β χ p.1 p.2 s s') - 1)|
        + |∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
            normalizedMarkedCoreTerm μm β χ
              (fun U => f U * g U) (s ∪ s') Γ|
        + |∑ p ∈ badCorePairs (N := N) s s',
            normalizedMarkedCoreTerm μm β χ f s p.1
              * normalizedMarkedCoreTerm μm β χ g s' p.2| := by
    rw [sub_eq_add_neg]
    refine le_trans (abs_add _ _) ?_
    rw [abs_neg]
    exact add_le_add_right (abs_add _ _) _
  refine le_trans htri ?_
  have hfinal : 3 * (Cf * Cg)
      * Real.exp (6 * (((supportLinkFinset (N := N) s).card : ℝ)
          + ((supportLinkFinset (N := N) s').card : ℝ)) / 113)
      * Real.exp (-(n : ℝ)/2)
      = 3 * (Real.exp (-(n : ℝ)/2) * (Cf * Cg)
          * Real.exp (3
              * (((supportLinkFinset (N := N) s).card : ℝ)
                + ((supportLinkFinset (N := N) s').card : ℝ))
              * (2/113))) := by
    rw [show 6 * (((supportLinkFinset (N := N) s).card : ℝ)
        + ((supportLinkFinset (N := N) s').card : ℝ)) / 113
        = 3 * (((supportLinkFinset (N := N) s).card : ℝ)
            + ((supportLinkFinset (N := N) s').card : ℝ))
            * (2/113) from by ring]
    ring
  rw [hfinal]
  linarith [hG, hB, hR, hscale]

#print axioms abs_goodColumn_sum_le
#print axioms abs_bridgeColumn_sum_le
#print axioms abs_badColumn_sum_le
#print axioms gibbsCovariance_eq_normalized_connector_ledger
#print axioms abs_gibbsCovariance_le_local_exp_decay

end LatticeGauge
