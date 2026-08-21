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
    rw [tsum_eq_zero_add'
      (f := fun n : ℕ => b n * ((n : ℝ) * t ^ (n - 1)))
      ((summable_nat_add_iff 1).mpr hsum_deriv)]
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
  rw [tsum_eq_zero_add' (f := fun n : ℕ => b n * (0 : ℝ) ^ n) hs,
    pow_zero, mul_one, hb0, zero_add]
  rw [tsum_congr hz, tsum_zero]

theorem Gser_one (b : ℕ → ℝ) : Gser b 1 = ∑' n, b n := by
  unfold Gser
  exact tsum_congr (fun n => by rw [one_pow, mul_one])

/-! ## IV-2 — the polynomial side and the FINITE CAUCHY:
    G′(t)·F(t) = F′(t) on 0 ≤ t < 1.

    CONCEPTUAL RECORD (architect's order): G′F is born as a
    potentially INFINITE series — it does NOT have finite support
    a priori. The finite-Cauchy theorem reorganizes it along the
    diagonal n = j + k with NO hypothesis on the coefficients;
    the recurrence then identifies the n-th coefficient as
    (n+1)·a_{n+1} (hrec enters at exactly ONE point:
    diagCoeff_eq); and only then, because a has finite support,
    the whole tail vanishes (hfin enters at exactly TWO points:
    inside diagCoeff_eq for n > M, and in the final truncation
    tsum_shifted_eq_Fderiv). The equation does the work.

    Edge cases audited: M = 0 gives Fderiv = empty sum = 0
    automatically; t = 0 needs no division (powers only, shifts
    by exact index arithmetic); b may have infinite support; a
    may have internal zeros (degree exactly M never assumed).
    Purity: still zero Real.exp/Real.log/Polymer/Ursell/KP/
    realZ/FormalPowerSeries; no hypothesis Fpoly t ≠ 0; no
    division anywhere. -/

/-- The polynomial side: finite sum, suporte in range (M+1). -/
noncomputable def Fpoly (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), a n * t ^ n

/-- Its derivative, SHIFTED like Gderiv (range M — the true
    derivative needs no support hypothesis). -/
noncomputable def Fderiv (a : ℕ → ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range M, ((n : ℝ) + 1) * a (n + 1) * t ^ n

theorem hasDerivAt_Fpoly (a : ℕ → ℝ) (M : ℕ) (t : ℝ) :
    HasDerivAt (Fpoly a M) (Fderiv a M t) t := by
  have h : HasDerivAt (Fpoly a M)
      (∑ n ∈ Finset.range (M + 1),
        a n * ((n : ℝ) * t ^ (n - 1))) t := by
    unfold Fpoly
    exact HasDerivAt.sum
      (A := fun (n : ℕ) (y : ℝ) => a n * y ^ n)
      (A' := fun n : ℕ => a n * ((n : ℝ) * t ^ (n - 1)))
      (fun n _ => (hasDerivAt_pow n t).const_mul (a n))
  convert h using 1
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  unfold Fderiv
  refine Finset.sum_congr rfl (fun n _ => ?_)
  push_cast [Nat.add_sub_cancel]
  ring

/-- Summability of the Gderiv terms at 0 ≤ t < 1 (the majorant
    lemma applied at r := t itself). -/
theorem summable_Gderiv_terms (b : ℕ → ℝ)
    (habs : Summable (fun n => |b n|)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * b (n + 1) * t ^ n) := by
  refine Summable.of_norm_bounded _
    (summable_deriv_majorant b habs ht0 ht1) (fun n => ?_)
  have h1 : |((n : ℝ) + 1)| = (n : ℝ) + 1 :=
    abs_of_nonneg (by positivity)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow,
    abs_of_nonneg ht0, h1]

/-- The diagonal coefficient of G′F (the reindexation n = j + k
    made explicit: row k contributes iff k ≤ n, with j := n − k). -/
noncomputable def diagCoeff (a b : ℕ → ℝ) (M n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (M + 1),
    if k ≤ n then
      (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k
    else 0

set_option maxHeartbeats 1600000 in
/-- **FINITE CAUCHY, BEFORE the recurrence**: G′(t)·F(t) equals
    the diagonal series — no hypothesis on a beyond none, no
    hrec, no hfin. The product is finite×infinite (F is a
    polynomial), so each row is a scalar multiple of the G′
    series, shifted by k through the injection (· + k). -/
theorem gderiv_mul_fpoly_eq_tsum_diag (a b : ℕ → ℝ) (M : ℕ)
    (habs : Summable (fun n => |b n|)) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Gderiv b t * Fpoly a M t
      = ∑' n : ℕ, diagCoeff a b M n * t ^ n := by
  have hsumG := summable_Gderiv_terms b habs ht0 ht1
  have hrow : ∀ k : ℕ, Summable (fun j : ℕ =>
      ((j : ℝ) + 1) * b (j + 1) * a k * t ^ (j + k)) := by
    intro k
    refine (hsumG.mul_right (a k * t ^ k)).congr (fun j => ?_)
    rw [pow_add]
    ring
  have hpoint : ∀ k j : ℕ,
      (fun n : ℕ => if k ≤ n then
        (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k * t ^ n
      else 0) (j + k)
      = ((j : ℝ) + 1) * b (j + 1) * a k * t ^ (j + k) := by
    intro k j
    simp only [if_pos (Nat.le_add_left k j), Nat.add_sub_cancel]
  have hvanish : ∀ (k n : ℕ), n ∉ Set.range (· + k) →
      (if k ≤ n then
        (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k * t ^ n
      else 0) = 0 := by
    intro k n hn
    exact if_neg (fun hkn => hn ⟨n - k, Nat.sub_add_cancel hkn⟩)
  have hesummable : ∀ k ∈ Finset.range (M + 1),
      Summable (fun n : ℕ => if k ≤ n then
        (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k * t ^ n
      else 0) := by
    intro k _
    refine (Function.Injective.summable_iff
      (add_left_injective k) (hvanish k)).mp ?_
    exact (hrow k).congr (fun j => (hpoint k j).symm)
  have hrow_eq : ∀ k ∈ Finset.range (M + 1),
      Gderiv b t * (a k * t ^ k)
      = ∑' n : ℕ, (if k ≤ n then
          (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k * t ^ n
        else 0) := by
    intro k _
    calc Gderiv b t * (a k * t ^ k)
        = ∑' j : ℕ,
            ((j : ℝ) + 1) * b (j + 1) * t ^ j * (a k * t ^ k) := by
          unfold Gderiv
          rw [← tsum_mul_right]
      _ = ∑' j : ℕ,
            ((j : ℝ) + 1) * b (j + 1) * a k * t ^ (j + k) := by
          refine tsum_congr (fun j => ?_)
          rw [pow_add]
          ring
      _ = ∑' n : ℕ, (if k ≤ n then
            (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k * t ^ n
          else 0) := by
          refine Eq.trans
            (tsum_congr (fun j => (hpoint k j).symm)) ?_
          exact Function.Injective.tsum_eq
            (add_left_injective k)
            (Function.support_subset_iff'.mpr (hvanish k))
  unfold Fpoly
  rw [Finset.mul_sum, Finset.sum_congr rfl hrow_eq,
    ← tsum_sum hesummable]
  refine tsum_congr (fun n => ?_)
  unfold diagCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  split_ifs with h
  · rfl
  · rw [zero_mul]

/-- **The recurrence identifies the coefficient** — hrec enters
    HERE and only here; hfin covers the rows k > n vs k > M
    mismatch when n > M. -/
theorem diagCoeff_eq (a b : ℕ → ℝ) (M : ℕ)
    (hfin : ∀ n, M < n → a n = 0)
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * a (n + 1)
      = ∑ j ∈ Finset.range (n + 1),
          ((j : ℝ) + 1) * b (j + 1) * a (n - j)) (n : ℕ) :
    diagCoeff a b M n = ((n : ℝ) + 1) * a (n + 1) := by
  have key : diagCoeff a b M n
      = ∑ k ∈ Finset.range (n + 1),
          (((n - k : ℕ) : ℝ) + 1) * b ((n - k) + 1) * a k := by
    unfold diagCoeff
    rw [← Finset.sum_filter]
    rcases le_or_lt n M with hnM | hMn
    · congr 1
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    · have hfe : (Finset.range (M + 1)).filter (fun k => k ≤ n)
          = Finset.range (M + 1) := by
        refine Finset.filter_true_of_mem ?_
        intro k hk
        rw [Finset.mem_range] at hk
        omega
      rw [hfe]
      refine Finset.sum_subset ?_ ?_
      · intro k hk
        rw [Finset.mem_range] at hk ⊢
        omega
      · intro k _ hknot
        rw [Finset.mem_range, not_lt] at hknot
        rw [hfin k (by omega), mul_zero]
  rw [key, hrec n, ← Finset.sum_range_reflect
    (fun j => ((j : ℝ) + 1) * b (j + 1) * a (n - j)) (n + 1)]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_range] at hi
  have e1 : n + 1 - 1 - i = n - i := by omega
  have e2 : n - (n - i) = i := by omega
  rw [e1]
  simp only [e2]

/-- **The tail vanishes by finite support** (hfin's second and
    last entrance): the identified series IS the polynomial
    derivative. -/
theorem tsum_shifted_eq_Fderiv (a : ℕ → ℝ) (M : ℕ)
    (hfin : ∀ n, M < n → a n = 0) (t : ℝ) :
    (∑' n : ℕ, ((n : ℝ) + 1) * a (n + 1) * t ^ n)
      = Fderiv a M t := by
  have hz : ∀ n ∉ Finset.range M,
      ((n : ℝ) + 1) * a (n + 1) * t ^ n = 0 := by
    intro n hn
    rw [Finset.mem_range, not_lt] at hn
    rw [hfin (n + 1) (by omega), mul_zero, zero_mul]
  rw [tsum_eq_sum hz]
  rfl

/-- **CAPSTONE IV-2**: F′(t) = G′(t)·F(t) on 0 ≤ t < 1 — no
    division, no nonvanishing, no exp. -/
theorem gderiv_mul_fpoly_eq_fderiv (a b : ℕ → ℝ) (M : ℕ)
    (hfin : ∀ n, M < n → a n = 0)
    (habs : Summable (fun n => |b n|))
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * a (n + 1)
      = ∑ j ∈ Finset.range (n + 1),
          ((j : ℝ) + 1) * b (j + 1) * a (n - j))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Gderiv b t * Fpoly a M t = Fderiv a M t := by
  have h1 : (∑' n : ℕ, diagCoeff a b M n * t ^ n)
      = ∑' n : ℕ, ((n : ℝ) + 1) * a (n + 1) * t ^ n :=
    tsum_congr (fun n => by rw [diagCoeff_eq a b M hfin hrec n])
  rw [gderiv_mul_fpoly_eq_tsum_diag a b M habs ht0 ht1, h1]
  exact tsum_shifted_eq_Fderiv a M hfin t

/-- Semantic form: the polynomial satisfies F′ = G′·F. -/
theorem hasDerivAt_Fpoly_mul (a b : ℕ → ℝ) (M : ℕ)
    (hfin : ∀ n, M < n → a n = 0)
    (habs : Summable (fun n => |b n|))
    (hrec : ∀ n : ℕ, ((n : ℝ) + 1) * a (n + 1)
      = ∑ j ∈ Finset.range (n + 1),
          ((j : ℝ) + 1) * b (j + 1) * a (n - j))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasDerivAt (Fpoly a M) (Gderiv b t * Fpoly a M t) t := by
  rw [gderiv_mul_fpoly_eq_fderiv a b M hfin habs hrec ht0 ht1]
  exact hasDerivAt_Fpoly a M t

end LatticeGauge
