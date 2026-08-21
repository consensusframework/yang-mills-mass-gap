/-
LatticeGauge/ExpRecurrenceEngine.lean — stone 49C-IV, Gate IV-1:
THE ANALYTIC HALF OF THE ABSTRACT EXP ENGINE (architecture:
Sol/GPT-5.6; execution: Fable).

ABSTRACT BY DESIGN: a small standalone result about real
sequences and their power series. This file does not know that
polymers exist. Zero Polymer, zero Ursell, zero kpGasCoeff, zero
KP, zero β, zero realZ, zero Real.log, zero FormalPowerSeries —
and Real.exp is not needed yet (it enters only at IV-3).

Content: the series Gser b t = Σ' bₙtⁿ; its SHIFTED derivative
Gderiv b t = Σ' (n+1)·b_{n+1}·tⁿ (no future user of these lemmas
carries n·t^(n−1)); the EXPLICIT summable-derivative-majorant
lemma — the architect's bolt, route (a): |bₙ| ≤ Σ'|b| by le_tsum,
then comparison against ((n+1)rⁿ)·Σ'|b|; continuity on Icc 0 1 by
the Weierstrass M-test; HasDerivAt on 0 ≤ t < 1 via
hasDerivAt_tsum_of_isPreconnected on the ball Ioo (−r) r with
r := (1+t)/2 < 1; endpoints Gser b 0 = 0 (0^0 = 1 handled through
the exact API tsum_eq_zero_add', not a fragile simp) and
Gser b 1 = Σ' bₙ. NO axioms.

Censused (Mathlib v4.15.0, source:line):
hasDerivAt_tsum_of_isPreconnected SmoothSeries:87;
continuousOn_tsum FunctionSeries:101; hasDerivAt_pow Deriv/Pow:39;
summable_geometric_of_lt_one SpecificLimits/Basic:291;
summable_pow_mul_geometric_of_norm_lt_one Normed:436;
le_tsum (to_additive of le_tprod) InfiniteSum/Order:109;
tsum_eq_zero_add' (to_additive of tprod_eq_zero_mul')
InfiniteSum/NatInt:187; summable_nat_add_iff (shift pattern as in
PSeries:425); pow_le_one₀ / pow_le_pow_left₀ (the ₀ names — the
bare names are deprecated aliases in the pin).
-/
import Mathlib

namespace LatticeGauge

/-! ## IV-1.1 — the series and its shifted derivative -/

/-- The power series of the sequence b at the point t. -/
noncomputable def Gser (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n, b n * t ^ n

/-- The SHIFTED derivative series: coefficients (n+1)·b_{n+1},
    exponent n. Users never see n·t^(n−1). -/
noncomputable def Gderiv (b : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, ((n : ℝ) + 1) * b (n + 1) * t ^ n

/-! ## IV-1.2 — the explicit derivative-majorant lemma (route (a):
    the single-term bound |bₙ| ≤ Σ'|b| via le_tsum, then
    comparison against ((n+1)rⁿ)·Σ'|b|) -/

theorem summable_deriv_majorant (b : ℕ → ℝ)
    (habs : Summable (fun n => |b n|)) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * |b (n + 1)| * r ^ n) := by
  have hC : ∀ n, |b n| ≤ ∑' m, |b m| :=
    fun n => le_tsum habs n (fun j _ => abs_nonneg _)
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    have h := summable_pow_mul_geometric_of_norm_lt_one 1
      (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    simpa using h
  have h2 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hr0 hr1
  have hgeo : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    refine (h1.add h2).congr (fun n => ?_)
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hgeo.mul_right (∑' m, |b m|))
  · positivity
  · calc ((n : ℝ) + 1) * |b (n + 1)| * r ^ n
        = ((n : ℝ) + 1) * r ^ n * |b (n + 1)| := by ring
      _ ≤ ((n : ℝ) + 1) * r ^ n * ∑' m, |b m| := by
          refine mul_le_mul_of_nonneg_left (hC (n + 1)) ?_
          positivity

/-! ## IV-1.3 — continuity on the closed interval (M-test) -/

theorem continuousOn_Gser (b : ℕ → ℝ)
    (habs : Summable (fun n => |b n|)) :
    ContinuousOn (Gser b) (Set.Icc (0 : ℝ) 1) := by
  unfold Gser
  refine continuousOn_tsum
    (fun i => (continuous_const.mul (continuous_pow i)).continuousOn)
    habs ?_
  intro n x hx
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hx.1]
  calc |b n| * x ^ n
      ≤ |b n| * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact pow_le_one₀ hx.1 hx.2
    _ = |b n| := mul_one _

/-! ## IV-1.4 — the derivative on 0 ≤ t < 1 (ball of radius
    r := (1+t)/2, bounds only on the open set — SmoothSeries:87) -/

set_option maxHeartbeats 800000 in
theorem hasDerivAt_Gser (b : ℕ → ℝ)
    (habs : Summable (fun n => |b n|)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (Gser b) (Gderiv b t) t := by
  set r : ℝ := (1 + t) / 2 with hrdef
  have hr0 : 0 < r := by rw [hrdef]; linarith
  have hr1 : r < 1 := by rw [hrdef]; linarith
  have htr : t < r := by rw [hrdef]; linarith
  have hmaj := summable_deriv_majorant b habs hr0.le hr1
  have hu : Summable
      (fun n : ℕ => (n : ℝ) * |b n| * r ^ (n - 1)) := by
    rw [← summable_nat_add_iff 1]
    refine hmaj.congr (fun n => ?_)
    push_cast [Nat.add_sub_cancel]
    ring
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Set.Ioo (-r) r →
      ‖b n * ((n : ℝ) * y ^ (n - 1))‖
        ≤ (n : ℝ) * |b n| * r ^ (n - 1) := by
    intro n y hy
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, Nat.abs_cast]
    have hyr : |y| ≤ r := (abs_lt.mpr ⟨hy.1, hy.2⟩).le
    calc |b n| * ((n : ℝ) * |y| ^ (n - 1))
        = (n : ℝ) * |b n| * |y| ^ (n - 1) := by ring
      _ ≤ (n : ℝ) * |b n| * r ^ (n - 1) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact pow_le_pow_left₀ (abs_nonneg y) hyr (n - 1)
  have hg0 : Summable (fun n : ℕ => b n * (0 : ℝ) ^ n) := by
    refine Summable.of_norm_bounded _ habs (fun n => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_zero]
    calc |b n| * (0 : ℝ) ^ n
        ≤ |b n| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          exact pow_le_one₀ le_rfl zero_le_one
      _ = |b n| := mul_one _
  have hkey : HasDerivAt (fun z : ℝ => ∑' n : ℕ, b n * z ^ n)
      (∑' n : ℕ, b n * ((n : ℝ) * t ^ (n - 1))) t :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => (n : ℝ) * |b n| * r ^ (n - 1))
      (g := fun (n : ℕ) (y : ℝ) => b n * y ^ n)
      (g' := fun (n : ℕ) (y : ℝ) => b n * ((n : ℝ) * y ^ (n - 1)))
      hu isOpen_Ioo (convex_Ioo (-r) r).isPreconnected
      (fun n y _ => (hasDerivAt_pow n y).const_mul (b n))
      hbound
      (Set.mem_Ioo.mpr ⟨by linarith, hr0⟩)
      hg0
      (Set.mem_Ioo.mpr ⟨by linarith, htr⟩)
  have hsum_deriv : Summable
      (fun n : ℕ => b n * ((n : ℝ) * t ^ (n - 1))) :=
    Summable.of_norm_bounded _ hu
      (fun n => hbound n t (Set.mem_Ioo.mpr ⟨by linarith, htr⟩))
  have hshift : (∑' n, b n * ((n : ℝ) * t ^ (n - 1)))
      = Gderiv b t := by
    rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hsum_deriv)]
    simp only [Nat.cast_zero, zero_mul, mul_zero, zero_add]
    unfold Gderiv
    refine tsum_congr (fun n => ?_)
    push_cast [Nat.add_sub_cancel]
    ring
  unfold Gser
  rw [← hshift]
  exact hkey

/-! ## IV-1.5 — endpoints (0^0 = 1 handled by exact API) -/

theorem Gser_zero (b : ℕ → ℝ) (hb0 : b 0 = 0) :
    Gser b 0 = 0 := by
  unfold Gser
  have hz : ∀ n : ℕ, b (n + 1) * (0 : ℝ) ^ (n + 1) = 0 :=
    fun n => by rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
  have hs : Summable (fun n : ℕ => b (n + 1) * (0 : ℝ) ^ (n + 1)) := by
    refine summable_zero.congr (fun n => ?_)
    rw [hz n]
  rw [tsum_eq_zero_add' hs, pow_zero, mul_one, hb0, zero_add]
  rw [tsum_congr hz, tsum_zero]

theorem Gser_one (b : ℕ → ℝ) : Gser b 1 = ∑' n, b n := by
  unfold Gser
  exact tsum_congr (fun n => by rw [one_pow, mul_one])

end LatticeGauge
