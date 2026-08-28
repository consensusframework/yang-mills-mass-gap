/-
LatticeGauge/CovarianceConnectorControl.lean — PEDRA 50, Gate
50-A19a: THE ERODED CONNECTOR WITHOUT ARTIFICIAL SMALLNESS
(architecture: Sol; execution: Fable).

The analytic control of the good column's connector factor. The
GLOBAL inequality |e^x − 1| ≤ |x|·e^{|x|} (no |x| ≤ 1 anywhere)
splits the eroded bound |C| ≤ d·q (d = e^{-r/2} ≤ 1 the decay
tail, q = a·min(barriers) the size) as: the tail d·q goes to the
LINEAR factor, the non-increasing |C| ≤ q goes inside exp —
never the eroded bound inside another exponential. Then
q·e^q ≤ e^{2q} ≤ e^{b_T + b_{T'}} absorbs everything into the
two barrier budgets, and e^{-r/2} ≤ e^{-n/2}·e^{M/2} (valid in ℕ
truncated subtraction WITHOUT m ≤ n) repurchases e^{-n/2} at the
half-mass cost — which the κ = 2 budget of A17 pays:
1/2 + 2·(8/113) = 145/226 < 1. CAPSTONE, factorized per core:
  |e^C − 1| ≤ e^{-n/2}·(e^{m_T/2 + b_T}·e^{m_{T'}/2 + b_{T'}}).
No GoodCorePair, no Disjoint s s' — not needed for this control.

NOT here (hard hold): no observables, no quotients, no Z², no
good/bridge/bad sums, no gibbsCovariance, no artificial
connector-smallness hypothesis, no new combinatorial/geometric/
counting argument, no frozen file touched.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceConnectorLedger
import LatticeGauge.CovarianceBarrierErosion

open MeasureTheory
open scoped Classical

namespace LatticeGauge

/-! ## A19a.1–A19a.3 — scalar lemmas (own section: no geometry,
    no measure, no instances dragged in) -/

section ScalarLemmas

/-- **The global exponential inequality** — no |x| ≤ 1
    hypothesis: |e^x − 1| ≤ |x|·e^{|x|}, from add_one_le_exp on
    both sides (1 − x ≤ e^{-x} is add_one_le_exp at −x). -/
theorem abs_exp_sub_one_le_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  have hex := Real.exp_pos x
  have hgex : Real.exp x ≤ Real.exp |x| :=
    Real.exp_le_exp.mpr (le_abs_self x)
  have hone : (1 : ℝ) ≤ Real.exp |x| := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (abs_nonneg x)
  rw [abs_le]
  constructor
  · -- lower side: e^x − 1 ≥ x ≥ −|x| ≥ −|x|·e^{|x|}
    have h1 := Real.add_one_le_exp x
    have h2 : |x| * 1 ≤ |x| * Real.exp |x| :=
      mul_le_mul_of_nonneg_left hone (abs_nonneg x)
    rw [mul_one] at h2
    have h3 : -|x| ≤ x := neg_abs_le x
    linarith
  · -- upper side: (1 − x)·e^x ≤ 1 ⟹ e^x − 1 ≤ x·e^x ≤ |x|·e^{|x|}
    have h1 := Real.add_one_le_exp (-x)
    have h2 : (-x + 1) * Real.exp x ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right h1 hex.le
      rw [← Real.exp_add, show -x + x = 0 from by ring,
        Real.exp_zero] at h
      exact h
    have h3 : Real.exp x - 1 ≤ x * Real.exp x := by nlinarith
    have h4 : x * Real.exp x ≤ |x| * Real.exp |x| :=
      calc x * Real.exp x
          ≤ |x| * Real.exp x :=
            mul_le_mul_of_nonneg_right (le_abs_self x) hex.le
        _ ≤ |x| * Real.exp |x| :=
            mul_le_mul_of_nonneg_left hgex (abs_nonneg x)
    linarith

/-- **Tail–budget absorption**: the decay d stays LINEAR, the
    size q goes into the budget B ≥ 2q. -/
theorem abs_exp_sub_one_le_decay_exp {x d q B : ℝ}
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hq0 : 0 ≤ q)
    (hx : |x| ≤ d * q) (hB : 2 * q ≤ B) :
    |Real.exp x - 1| ≤ d * Real.exp B := by
  have h1 := abs_exp_sub_one_le_abs_mul_exp_abs x
  have hdq0 : (0 : ℝ) ≤ d * q := mul_nonneg hd0 hq0
  have hxq : |x| ≤ q := le_trans hx (by nlinarith)
  have h2 : Real.exp |x| ≤ Real.exp q := Real.exp_le_exp.mpr hxq
  have h3 : q ≤ Real.exp q := by
    have := Real.add_one_le_exp q
    linarith
  calc |Real.exp x - 1|
      ≤ |x| * Real.exp |x| := h1
    _ ≤ (d * q) * Real.exp q :=
        mul_le_mul hx h2 (Real.exp_pos _).le hdq0
    _ ≤ (d * Real.exp q) * Real.exp q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 hd0)
          (Real.exp_pos q).le
    _ = d * Real.exp (2 * q) := by
        rw [show (2 : ℝ) * q = q + q from by ring,
          Real.exp_add]
        ring
    _ ≤ d * Real.exp B :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hB) hd0

/-- **Truncated-subtraction erosion in ℕ, no m ≤ n hypothesis**:
    the case m > n (zero residual distance) is covered. -/
theorem exp_neg_nat_sub_half_le (n m : ℕ) :
    Real.exp (-((n - m : ℕ) : ℝ) / 2)
      ≤ Real.exp (-(n : ℝ) / 2) * Real.exp ((m : ℝ) / 2) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hnat : n ≤ (n - m) + m := by omega
  have h : (n : ℝ) ≤ ((n - m : ℕ) : ℝ) + (m : ℝ) := by
    exact_mod_cast hnat
  linarith

end ScalarLemmas

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A19a.4 — the signed connector obeys the A12 tail -/

theorem abs_coreConnectorSum_le_local_min
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {r : ℕ}
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') r) :
    |coreConnectorSum μm β χ T T' s s'|
      ≤ Real.exp (-(r : ℝ)/2)
        * ((min (barrierLinkFinset T s).card
            (barrierLinkFinset T' s').card : ℕ) : ℝ)
        * (2 / 113) := by
  unfold coreConnectorSum connectorClusterSum
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  have hsum := summable_abs_kpConnectorUnrootedCoeff
    ha hKP (remoteAllowed (N := N) T s)
    (remoteAllowed (N := N) T' s')
  have h1 : ‖∑' k : ℕ, kpConnectorUnrootedCoeff (N := N) k
      (fun η => polymerWeight (N := N) μm β χ η.val)
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s')‖
      ≤ ∑' k : ℕ, ‖kpConnectorUnrootedCoeff (N := N) k
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s)
          (remoteAllowed (N := N) T' s')‖ := by
    refine norm_tsum_le_tsum_norm ?_
    simpa [Real.norm_eq_abs] using hsum
  simp only [Real.norm_eq_abs] at h1
  exact h1.trans (tsum_abs_kpConnector_le_local_min
    μm hβ mχ hχabs hsmall hwsep)

/-! ## A19a.5 — CAPSTONE: the eroded connector control,
    factorized per core -/

/-- **CAPSTONE 50-A19a**: without any smallness hypothesis,
    |e^C − 1| ≤ e^{-n/2}·(e^{m_T/2 + b_T}·e^{m_T'/2 + b_T'}) —
    the tail stays linear, the sizes go into the per-core
    budgets, the erosion cost is repurchased at half mass. No
    GoodCorePair, no Disjoint s s'. -/
theorem abs_exp_coreConnectorSum_sub_one_le_eroded
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hT' : T' ∈ typedTouchingFamilies (N := N) s')
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    |Real.exp (coreConnectorSum μm β χ T T' s s') - 1|
      ≤ Real.exp (-(n : ℝ) / 2)
        * (Real.exp ((familyTotalCard T : ℝ) / 2
              + ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * Real.exp ((familyTotalCard T' : ℝ) / 2
              + ((barrierLinkFinset T' s').card : ℝ)
                  * (2/113))) := by
  have hero := walkBarrierSeparated_barrierRegions_sub_familyMass
    hT hT' hsep
  have hC := abs_coreConnectorSum_le_local_min
    μm hβ mχ hχabs hsmall hero
  have hd0 : (0:ℝ) ≤ Real.exp
      (-(((n - (familyTotalCard T + familyTotalCard T') : ℕ))
        : ℝ)/2) :=
    (Real.exp_pos _).le
  have hd1 : Real.exp
      (-(((n - (familyTotalCard T + familyTotalCard T') : ℕ))
        : ℝ)/2) ≤ 1 := by
    rw [← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    have h0 : (0:ℝ) ≤ (((n - (familyTotalCard T
        + familyTotalCard T') : ℕ)) : ℝ) := Nat.cast_nonneg _
    linarith
  have hq0 : (0:ℝ) ≤ ((min (barrierLinkFinset T s).card
      (barrierLinkFinset T' s').card : ℕ) : ℝ) * (2/113) :=
    mul_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hx : |coreConnectorSum μm β χ T T' s s'|
      ≤ Real.exp
          (-(((n - (familyTotalCard T + familyTotalCard T') : ℕ))
            : ℝ)/2)
        * (((min (barrierLinkFinset T s).card
            (barrierLinkFinset T' s').card : ℕ) : ℝ)
          * (2/113)) := by
    calc |coreConnectorSum μm β χ T T' s s'|
        ≤ Real.exp
            (-(((n - (familyTotalCard T
              + familyTotalCard T') : ℕ)) : ℝ)/2)
          * ((min (barrierLinkFinset T s).card
              (barrierLinkFinset T' s').card : ℕ) : ℝ)
          * (2/113) := hC
      _ = _ := mul_assoc _ _ _
  have hB : 2 * (((min (barrierLinkFinset T s).card
      (barrierLinkFinset T' s').card : ℕ) : ℝ) * (2/113))
      ≤ ((barrierLinkFinset T s).card : ℝ) * (2/113)
        + ((barrierLinkFinset T' s').card : ℝ) * (2/113) := by
    have h1 : ((min (barrierLinkFinset T s).card
        (barrierLinkFinset T' s').card : ℕ) : ℝ)
        ≤ ((barrierLinkFinset T s).card : ℝ) :=
      Nat.cast_le.mpr (min_le_left _ _)
    have h2 : ((min (barrierLinkFinset T s).card
        (barrierLinkFinset T' s').card : ℕ) : ℝ)
        ≤ ((barrierLinkFinset T' s').card : ℝ) :=
      Nat.cast_le.mpr (min_le_right _ _)
    linarith
  have hmain := abs_exp_sub_one_le_decay_exp
    hd0 hd1 hq0 hx hB
  have herode := exp_neg_nat_sub_half_le n
    (familyTotalCard T + familyTotalCard T')
  have hcomb : |Real.exp (coreConnectorSum μm β χ T T' s s') - 1|
      ≤ (Real.exp (-(n : ℝ)/2)
          * Real.exp (((familyTotalCard T
              + familyTotalCard T' : ℕ) : ℝ)/2))
        * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)
            + ((barrierLinkFinset T' s').card : ℝ) * (2/113)) :=
    le_trans hmain
      (mul_le_mul_of_nonneg_right herode (Real.exp_pos _).le)
  have hfinal : (Real.exp (-(n : ℝ)/2)
        * Real.exp (((familyTotalCard T
            + familyTotalCard T' : ℕ) : ℝ)/2))
      * Real.exp (((barrierLinkFinset T s).card : ℝ) * (2/113)
          + ((barrierLinkFinset T' s').card : ℝ) * (2/113))
      = Real.exp (-(n : ℝ) / 2)
        * (Real.exp ((familyTotalCard T : ℝ) / 2
              + ((barrierLinkFinset T s).card : ℝ) * (2/113))
          * Real.exp ((familyTotalCard T' : ℝ) / 2
              + ((barrierLinkFinset T' s').card : ℝ)
                  * (2/113))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hfinal] at hcomb
  exact hcomb

/-! ## A19a.6 — the good-column budget, ready (A17 at κ = 2:
    1/2 + 2·(8/113) = 145/226 < 1 by norm_num; no recount, no
    coverage, no powerset reopened) -/

theorem coreLocalBudget_connector {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ (1 : ℝ) / 40000) (s : Set (Link N)) :
    (∑ T ∈ typedTouchingFamilies (N := N) s,
        Real.exp (2 * ((barrierLinkFinset T s).card : ℝ)
            * (2/113))
          * ∏ η ∈ T,
              massTiltActivity (1/2) (mayerCoreMajorant β) η)
      ≤ Real.exp (3 * ((supportLinkFinset s).card : ℝ)
          * (2/113)) := by
  have h := coreLocalBudget (lam := 1/2) (κ := 2)
    (by norm_num) (by norm_num) (by norm_num) hβ hsmall s
  simpa [show (2:ℝ) + 1 = 3 from by norm_num] using h

#print axioms abs_exp_coreConnectorSum_sub_one_le_eroded
#print axioms coreLocalBudget_connector

end LatticeGauge
