/-
LatticeGauge/CovarianceNormalizedColumns.lean — PEDRA 50, Gate
50-A19b: THE NORMALIZED COLUMNS (architecture: Sol; execution:
Fable).

The Z²-normalization of the connector ledger and the
term-by-term control of the three columns. The A16 quotients
finally leave the reserve: each restricted/full ratio is
POSITIVE and ≤ e^{b_T} (barrier budget), so the normalized
marked term N_f(s,T) = markedCoreGasTerm/Z obeys
  |N_f(s,T)| ≤ C_f·e^{b_T}·Π mayerCoreMajorant.
Then, with A_κ(s,T) = e^{κ·b_T}·Π massTilt_{1/2}(Mayer):
  good:   |N_f·N_g·(e^C − 1)| ≤ E_n·C_fC_g·A₂(s,T)·A₂(s',T')
          (two quotients + the A19a eroded connector; the per-
          core account e^{b}·e^{m/2+b}·ΠM = A₂ closes exactly);
  bridge: |N_fg| ≤ E_n·C_fC_g·A₁(s∪s',Γ) (ONE quotient only —
          the original term is mcgt·Z, so /Z² leaves mcgt/Z; no
          second barrier charged);
  bad:    |N_f·N_g| ≤ E_n·C_fC_g·A₁(s,p.1)·A₁(s',p.2) via the
          JOINT mass of A18b (1 ≤ E_n·e^{(m₁+m₂)/2} through the
          zero-residual case of the ℕ erosion lemma — the bridge
          lemma is NOT applied per core: a bad pair may arise
          from crossed incompatibility alone);
and the EXACT normalized ledger
  (M_fg·Z − M_f·M_g)/Z² = Σ N_fN_g(e^C−1) + Σ N_fg − Σ N_fN_g,
with Z > 0 an OUTPUT of concrete KP. field_simp only on small
scalar goals with the nonvanishing already proved.

NOT here (hard hold): no |C| ≤ 1, no isolated 1/Z or 1/Z²
estimate (only R/Z is controlled), no external nonvanishing, no
new combinatorics/geometry/counting/integral, no column-sum
estimates (A17/A19a budgets are A19c's), no gibbsCovariance, no
final constant claimed, no frozen file touched.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceConnectorControl

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A19b.1b — the budget term (measure-free section: no
    group, no measure, no observables) -/

noncomputable def halfTiltCoreBudgetTerm (β κ : ℝ)
    (s : Set (Link N)) (T : Finset (Polymer N)) : ℝ :=
  Real.exp (κ * ((barrierLinkFinset T s).card : ℝ) * (2/113))
    * ∏ η ∈ T, massTiltActivity (1/2) (mayerCoreMajorant β) η

theorem halfTiltCoreBudgetTerm_nonneg {β : ℝ} (hβ : 0 ≤ β)
    (κ : ℝ) (s : Set (Link N)) (T : Finset (Polymer N)) :
    0 ≤ halfTiltCoreBudgetTerm β κ s T :=
  mul_nonneg (Real.exp_pos _).le
    (Finset.prod_nonneg (fun η _ =>
      massTiltActivity_nonneg (mayerCoreMajorant_nonneg hβ) η))

/-- The half-tilt unfolded (prod_family_massTiltActivity
    consumed; no product rebuilt). -/
theorem halfTiltCoreBudgetTerm_eq (β κ : ℝ)
    (s : Set (Link N)) (T : Finset (Polymer N)) :
    halfTiltCoreBudgetTerm β κ s T
      = Real.exp ((familyTotalCard T : ℝ)/2
          + κ * ((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, mayerCoreMajorant β η := by
  unfold halfTiltCoreBudgetTerm
  rw [prod_family_massTiltActivity, ← mul_assoc, ← Real.exp_add,
    show κ * ((barrierLinkFinset T s).card : ℝ) * (2/113)
        + 1/2 * (familyTotalCard T : ℝ)
      = (familyTotalCard T : ℝ)/2
        + κ * ((barrierLinkFinset T s).card : ℝ) * (2/113)
      from by ring]

/-- Opaque scalar helper for the Z²-division (field_simp runs on
    free variables only — never on gas terms). -/
theorem div_sq_split (a b c Z : ℝ) (hZ : Z ≠ 0) :
    a * b * c / Z ^ 2 = a / Z * (b / Z) * c := by
  field_simp
  ring

theorem mul_div_sq_cancel (a Z : ℝ) (hZ : Z ≠ 0) :
    a * Z / Z ^ 2 = a / Z := by
  field_simp
  ring

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A19b.1a — the normalized marked term -/

noncomputable def normalizedMarkedCoreTerm (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N))
    (T : Finset (Polymer N)) : ℝ :=
  markedCoreGasTerm μm β χ f s T
    / typedPolymerGas (N := N)
        (fun η => polymerWeight (N := N) μm β χ η.val)

/-- The definitional bridge N_f(s,T) = W_f(T)·(R_T(s)/Z). -/
theorem normalizedMarkedCoreTerm_eq (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N))
    (T : Finset (Polymer N)) :
    normalizedMarkedCoreTerm μm β χ f s T
      = typedMarkedCoreWeight μm β χ f T
        * (coreRestrictedGas μm β χ T s
          / typedPolymerGas (N := N)
              (fun η => polymerWeight (N := N) μm β χ η.val)) := by
  unfold normalizedMarkedCoreTerm markedCoreGasTerm
  rw [mul_div_assoc]

/-! ## A19b.2 — the A16 quotients enter -/

/-- Generic transport: any bound on the core weight passes to
    the normalized term at the price of one barrier exponential
    (A16's positivity + ratio bound; 0 ≤ L is derived). -/
theorem abs_normalizedMarkedCoreTerm_le_of_abs_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} {s : Set (Link N)}
    {T : Finset (Polymer N)} {L : ℝ}
    (hW : |typedMarkedCoreWeight μm β χ f T| ≤ L) :
    |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ L * Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
  have hL0 : (0:ℝ) ≤ L := le_trans (abs_nonneg _) hW
  have hpos : 0 < coreRestrictedGas μm β χ T s
      / typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) :=
    restrictedGas_div_fullGas_pos μm hβ mχ hχabs hsmall T s
  have hle : coreRestrictedGas μm β χ T s
      / typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val)
      ≤ Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
    restrictedGas_div_fullGas_le_exp_barrier
      μm hβ mχ hχabs hsmall T s
  rw [normalizedMarkedCoreTerm_eq, abs_mul]
  calc |typedMarkedCoreWeight μm β χ f T|
      * |coreRestrictedGas μm β χ T s
          / typedPolymerGas (N := N)
              (fun η => polymerWeight (N := N) μm β χ η.val)|
      ≤ L * |coreRestrictedGas μm β χ T s
          / typedPolymerGas (N := N)
              (fun η => polymerWeight (N := N) μm β χ η.val)| :=
        mul_le_mul_of_nonneg_right hW (abs_nonneg _)
    _ = L * (coreRestrictedGas μm β χ T s
          / typedPolymerGas (N := N)
              (fun η => polymerWeight (N := N) μm β χ η.val)) := by
        rw [abs_of_pos hpos]
    _ ≤ L * Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2/113)) :=
        mul_le_mul_of_nonneg_left hle hL0

/-- The concrete normalized majorant (A15's marked Mayer bound
    through the quotient). -/
theorem abs_normalizedMarkedCoreTerm_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf0 : 0 ≤ Cf) (hCf : ∀ U, |f U| ≤ Cf)
    (s : Set (Link N)) (T : Finset (Polymer N)) :
    |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ Cf * Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, mayerCoreMajorant β η := by
  have hW := abs_typedMarkedCoreWeight_le_mayerCoreMajorant
    μm hβ mχ hχabs mf hCf0 hCf T
  have h := abs_normalizedMarkedCoreTerm_le_of_abs_le
    μm hβ mχ hχabs hsmall (s := s) hW
  calc |normalizedMarkedCoreTerm μm β χ f s T|
      ≤ (Cf * ∏ η ∈ T, mayerCoreMajorant β η)
        * Real.exp
            (((barrierLinkFinset T s).card : ℝ) * (2/113)) := h
    _ = Cf * Real.exp
          (((barrierLinkFinset T s).card : ℝ) * (2/113))
        * ∏ η ∈ T, mayerCoreMajorant β η := by ring

/-! ## A19b.3 — the GOOD column: two quotients, κ = 2 -/

theorem abs_normalizedCorePair_connector_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hT' : T' ∈ typedTouchingFamilies (N := N) s')
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |normalizedMarkedCoreTerm μm β χ f s T
      * normalizedMarkedCoreTerm μm β χ g s' T'
      * (Real.exp (coreConnectorSum μm β χ T T' s s') - 1)|
      ≤ Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * (halfTiltCoreBudgetTerm β 2 s T
          * halfTiltCoreBudgetTerm β 2 s' T') := by
  have h1 := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf s T
  have h2 := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mg hCg0 hCg s' T'
  have h3 := abs_exp_coreConnectorSum_sub_one_le_eroded
    μm hβ mχ hχabs hsmall hT hT' hsep
  have hM1 : (0:ℝ) ≤ ∏ η ∈ T, mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hM2 : (0:ℝ) ≤ ∏ η ∈ T', mayerCoreMajorant β η :=
    Finset.prod_nonneg (fun η _ => mayerCoreMajorant_nonneg hβ η)
  have hb1 : (0:ℝ) ≤ Cf * Real.exp
      (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 (Real.exp_pos _).le) hM1
  have hb2 : (0:ℝ) ≤ (Cf * Real.exp
      (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * ∏ η ∈ T, mayerCoreMajorant β η)
      * (Cg * Real.exp
        (((barrierLinkFinset T' s').card : ℝ) * (2/113))
        * ∏ η ∈ T', mayerCoreMajorant β η) :=
    mul_nonneg hb1
      (mul_nonneg (mul_nonneg hCg0 (Real.exp_pos _).le) hM2)
  have hm1 : Real.exp
      (((barrierLinkFinset T s).card : ℝ) * (2/113))
      * Real.exp ((familyTotalCard T : ℝ)/2
        + ((barrierLinkFinset T s).card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard T : ℝ)/2
        + 2 * ((barrierLinkFinset T s).card : ℝ) * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm2 : Real.exp
      (((barrierLinkFinset T' s').card : ℝ) * (2/113))
      * Real.exp ((familyTotalCard T' : ℝ)/2
        + ((barrierLinkFinset T' s').card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard T' : ℝ)/2
        + 2 * ((barrierLinkFinset T' s').card : ℝ) * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_mul, abs_mul]
  calc |normalizedMarkedCoreTerm μm β χ f s T|
      * |normalizedMarkedCoreTerm μm β χ g s' T'|
      * |Real.exp (coreConnectorSum μm β χ T T' s s') - 1|
      ≤ ((Cf * Real.exp
            (((barrierLinkFinset T s).card : ℝ) * (2/113))
          * ∏ η ∈ T, mayerCoreMajorant β η)
        * (Cg * Real.exp
            (((barrierLinkFinset T' s').card : ℝ) * (2/113))
          * ∏ η ∈ T', mayerCoreMajorant β η))
        * (Real.exp (-(n : ℝ) / 2)
          * (Real.exp ((familyTotalCard T : ℝ)/2
              + ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * Real.exp ((familyTotalCard T' : ℝ)/2
              + ((barrierLinkFinset T' s').card : ℝ)
                  * (2/113)))) :=
        mul_le_mul
          (mul_le_mul h1 h2 (abs_nonneg _) hb1)
          h3 (abs_nonneg _) hb2
    _ = Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * ((Real.exp
              (((barrierLinkFinset T s).card : ℝ) * (2/113))
            * Real.exp ((familyTotalCard T : ℝ)/2
              + ((barrierLinkFinset T s).card : ℝ) * (2/113))
            * ∏ η ∈ T, mayerCoreMajorant β η)
          * (Real.exp
              (((barrierLinkFinset T' s').card : ℝ) * (2/113))
            * Real.exp ((familyTotalCard T' : ℝ)/2
              + ((barrierLinkFinset T' s').card : ℝ) * (2/113))
            * ∏ η ∈ T', mayerCoreMajorant β η)) := by
        ring
    _ = Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * (halfTiltCoreBudgetTerm β 2 s T
          * halfTiltCoreBudgetTerm β 2 s' T') := by
        rw [hm1, hm2, halfTiltCoreBudgetTerm_eq,
          halfTiltCoreBudgetTerm_eq]

/-! ## A19b.4 — the BRIDGE column: one quotient, κ = 1 -/

theorem abs_normalizedBridgeCore_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hΓ : Γ ∈ bridgeTouchingFamilies (N := N) s s')
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |normalizedMarkedCoreTerm μm β χ (fun U => f U * g U)
        (s ∪ s') Γ|
      ≤ Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * halfTiltCoreBudgetTerm β 1 (s ∪ s') Γ := by
  have hne : (bridgeCore Γ s s').Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr
      (mem_bridgeTouchingFamilies.mp hΓ).2
  have hW := abs_bridgeCoreWeight_mul_le_exp_neg_half
    μm hβ mχ hχabs mf mg hCf0 hCg0 hCf hCg hne hsep
  have h := abs_normalizedMarkedCoreTerm_le_of_abs_le
    μm hβ mχ hχabs hsmall (s := s ∪ s') hW
  calc abs (normalizedMarkedCoreTerm μm β χ
        (fun U => f U * g U) (s ∪ s') Γ)
      ≤ (Real.exp (-(n : ℝ) / 2)
          * ((Cf * Cg) * ∏ η ∈ Γ,
              massTiltActivity (1/2) (mayerCoreMajorant β) η))
        * Real.exp
            (((barrierLinkFinset Γ (s ∪ s')).card : ℝ)
              * (2/113)) := h
    _ = Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * halfTiltCoreBudgetTerm β 1 (s ∪ s') Γ := by
        unfold halfTiltCoreBudgetTerm
        rw [one_mul]
        ring

/-! ## A19b.5 — the BAD column: joint mass, κ = 1 per side
    (the bridge lemma is NOT applied per core) -/

theorem abs_normalizedBadCorePair_le
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    {Cf Cg : ℝ} (hCf0 : 0 ≤ Cf) (hCg0 : 0 ≤ Cg)
    (hCf : ∀ U, |f U| ≤ Cf) (hCg : ∀ U, |g U| ≤ Cg)
    {p : Finset (Polymer N) × Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hp : p ∈ badCorePairs s s')
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |normalizedMarkedCoreTerm μm β χ f s p.1
      * normalizedMarkedCoreTerm μm β χ g s' p.2|
      ≤ Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * (halfTiltCoreBudgetTerm β 1 s p.1
          * halfTiltCoreBudgetTerm β 1 s' p.2) := by
  have h1 := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mf hCf0 hCf s p.1
  have h2 := abs_normalizedMarkedCoreTerm_le
    μm hβ mχ hχabs hsmall mg hCg0 hCg s' p.2
  have hb1 : (0:ℝ) ≤ Cf * Real.exp
      (((barrierLinkFinset p.1 s).card : ℝ) * (2/113))
      * ∏ η ∈ p.1, mayerCoreMajorant β η :=
    mul_nonneg (mul_nonneg hCf0 (Real.exp_pos _).le)
      (Finset.prod_nonneg
        (fun η _ => mayerCoreMajorant_nonneg hβ η))
  have hb2 : (0:ℝ) ≤ (Cf * Real.exp
      (((barrierLinkFinset p.1 s).card : ℝ) * (2/113))
      * ∏ η ∈ p.1, mayerCoreMajorant β η)
      * (Cg * Real.exp
        (((barrierLinkFinset p.2 s').card : ℝ) * (2/113))
        * ∏ η ∈ p.2, mayerCoreMajorant β η) :=
    mul_nonneg hb1
      (mul_nonneg (mul_nonneg hCg0 (Real.exp_pos _).le)
        (Finset.prod_nonneg
          (fun η _ => mayerCoreMajorant_nonneg hβ η)))
  have hmass := badCorePair_familyTotalCard_ge hp hsep
  have hone : (1:ℝ) ≤ Real.exp (-(n : ℝ)/2)
      * Real.exp (((familyTotalCard p.1
          + familyTotalCard p.2 : ℕ) : ℝ)/2) := by
    have h := exp_neg_nat_sub_half_le n
      (familyTotalCard p.1 + familyTotalCard p.2)
    rw [show n - (familyTotalCard p.1 + familyTotalCard p.2) = 0
      from by omega] at h
    simpa using h
  have hsplit : Real.exp (((familyTotalCard p.1
      + familyTotalCard p.2 : ℕ) : ℝ)/2)
      = Real.exp ((familyTotalCard p.1 : ℝ)/2)
        * Real.exp ((familyTotalCard p.2 : ℝ)/2) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hm1 : Real.exp ((familyTotalCard p.1 : ℝ)/2)
      * Real.exp
          (((barrierLinkFinset p.1 s).card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard p.1 : ℝ)/2
        + 1 * ((barrierLinkFinset p.1 s).card : ℝ)
            * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm2 : Real.exp ((familyTotalCard p.2 : ℝ)/2)
      * Real.exp
          (((barrierLinkFinset p.2 s').card : ℝ) * (2/113))
      = Real.exp ((familyTotalCard p.2 : ℝ)/2
        + 1 * ((barrierLinkFinset p.2 s').card : ℝ)
            * (2/113)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [abs_mul]
  calc |normalizedMarkedCoreTerm μm β χ f s p.1|
      * |normalizedMarkedCoreTerm μm β χ g s' p.2|
      ≤ (Cf * Real.exp
            (((barrierLinkFinset p.1 s).card : ℝ) * (2/113))
          * ∏ η ∈ p.1, mayerCoreMajorant β η)
        * (Cg * Real.exp
            (((barrierLinkFinset p.2 s').card : ℝ) * (2/113))
          * ∏ η ∈ p.2, mayerCoreMajorant β η) :=
        mul_le_mul h1 h2 (abs_nonneg _) hb1
    _ ≤ (Real.exp (-(n : ℝ)/2)
          * Real.exp (((familyTotalCard p.1
              + familyTotalCard p.2 : ℕ) : ℝ)/2))
        * ((Cf * Real.exp
              (((barrierLinkFinset p.1 s).card : ℝ) * (2/113))
            * ∏ η ∈ p.1, mayerCoreMajorant β η)
          * (Cg * Real.exp
              (((barrierLinkFinset p.2 s').card : ℝ) * (2/113))
            * ∏ η ∈ p.2, mayerCoreMajorant β η)) := by
        nlinarith [hb2, hone]
    _ = Real.exp (-(n : ℝ) / 2) * (Cf * Cg)
        * (halfTiltCoreBudgetTerm β 1 s p.1
          * halfTiltCoreBudgetTerm β 1 s' p.2) := by
        rw [halfTiltCoreBudgetTerm_eq, halfTiltCoreBudgetTerm_eq,
          hsplit, ← hm1, ← hm2]
        ring

/-! ## A19b.6 — the exact ledger divided by Z² -/

/-- **CAPSTONE 50-A19b (exact part)**: the connector ledger
    normalized by Z², with Z > 0 an output of concrete KP. -/
theorem covariance_normalized_connector_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g) :
    (typedMarkedPolymerGas μm β χ (fun U => f U * g U) (s ∪ s')
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val)
      - typedMarkedPolymerGas μm β χ f s
        * typedMarkedPolymerGas μm β χ g s')
      / (typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val)) ^ 2
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
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have hZ : 0 < typedPolymerGas (N := N)
      (fun η => polymerWeight (N := N) μm β χ η.val) :=
    typedPolymerGas_pos_of_KP
      (fun γ => Nat.cast_nonneg _) hKP
  have hZne : typedPolymerGas (N := N)
      (fun η => polymerWeight (N := N) μm β χ η.val) ≠ 0 :=
    ne_of_gt hZ
  rw [covariance_numerator_connector_ledger
      μm hβ mχ hχabs hsmall hss' hf mf hg mg,
    sub_div, add_div, Finset.sum_div, Finset.sum_div,
    Finset.sum_div]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      unfold normalizedMarkedCoreTerm
      exact div_sq_split _ _ _ _ hZne
    · refine Finset.sum_congr rfl (fun Γ _ => ?_)
      unfold normalizedMarkedCoreTerm
      exact mul_div_sq_cancel _ _ hZne
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    unfold normalizedMarkedCoreTerm
    exact div_sq_split _ _ _ _ hZne

#print axioms abs_normalizedCorePair_connector_le
#print axioms abs_normalizedBridgeCore_le
#print axioms abs_normalizedBadCorePair_le
#print axioms covariance_normalized_connector_ledger

end LatticeGauge
