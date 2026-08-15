/-
LatticeGauge/SeriesBridge.lean — stone 48, GATE A: THE ORDER→SERIES
BRIDGE (architecture: Sol/GPT-5.6; execution: Fable).

The first authorized passage M → ∞ of the whole program — and, by
the architect's rule ("do not duplicate theory Mathlib already
provides"), it is CONSUMED from the pinned library, not rebuilt.
CENSUS (v4.15.0, Mathlib/Topology/Algebra/InfiniteSum/Real.lean):

  theorem summable_of_sum_range_le {f : ℕ → ℝ} {c : ℝ}
      (hf : ∀ n, 0 ≤ f n)
      (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : Summable f
    -- line 85, root namespace

  theorem Real.tsum_le_of_sum_range_le {f : ℕ → ℝ} {c : ℝ}
      (hf : ∀ n, 0 ≤ f n)
      (h : ∀ n, ∑ i ∈ Finset.range n, f i ≤ c) : ∑' n, f n ≤ c
    -- line 91

Both are EXACTLY the demanded signatures (nonnegativity + uniformly
bounded range-partial sums), with no extra hypotheses; the second
consumes the first internally. This file introduces NO domain
definitions and NO new analytic theory: it records the census and
proves two sanity THEOREMS exercising the library lemmas directly
(the zero sequence; the single spike). Everything here is analysis of a plain
nonnegative sequence ℕ → ℝ: no Polymer, no kpTreeCoeff, no
kpPartialSum, no polymerWeight, no β, no KPSmallness, no Ursell, no
log, no partition function, no clustering. NO axioms.
-/
import Mathlib

namespace LatticeGauge

/-! ## 48A sanities (the library lemmas exercised end to end) -/

/-- Sanity 1: the zero sequence is summable with tsum bound 0. -/
theorem seriesBridge_sanity_zero :
    Summable (fun _ : ℕ => (0 : ℝ))
      ∧ (∑' _ : ℕ, (0 : ℝ)) ≤ 0 :=
  ⟨summable_of_sum_range_le (c := 0) (fun _ => le_refl 0)
      (fun n => by simp),
    Real.tsum_le_of_sum_range_le (c := 0) (fun _ => le_refl 0)
      (fun n => by simp)⟩

/-- Sanity 2: the single spike at 0 with height 0 ≤ c ≤ c. -/
theorem seriesBridge_sanity_spike {c : ℝ} (hc : 0 ≤ c) :
    (∑' n : ℕ, if n = 0 then c else 0) ≤ c :=
  Real.tsum_le_of_sum_range_le
    (fun n => by
      by_cases h : n = 0
      · simp [h, hc]
      · simp [h])
    (fun n => by
      rw [Finset.sum_ite_eq' (Finset.range n) 0
        (fun _ => c)]
      by_cases h : (0 : ℕ) ∈ Finset.range n
      · simp [h]
      · simp [h, hc])

end LatticeGauge
