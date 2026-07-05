/-
LatticeGauge/UnitaryChar.lean — Phase 3, eighth stone.

The physical character: the normalized real trace on the unitary group
U(n) of complex matrices (the compact gauge-group family containing
SU(n)). We prove χ(1) = 1, that χ is a class function, and |χ| ≤ 1 —
so ALL abstract theorems of the previous stones apply to genuine
matrix gauge groups. NO axioms; everything proved.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.GaugeInvariance

namespace LatticeGauge

open Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The normalized real trace character on U(n):
    χ(g) = Re(tr g) / n. -/
noncomputable def uChar (g : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  (Matrix.trace (g : Matrix (Fin n) (Fin n) ℂ)).re / n

/-- **Proved:** χ(1) = 1. -/
theorem uChar_one : uChar n (1 : Matrix.unitaryGroup (Fin n) ℂ) = 1 := by
  unfold uChar
  have hne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp [Matrix.trace_one, div_self hne]

/-- **Proved:** χ is a class function: χ(h u h⁻¹) = χ(u).
    Uses tr(ABC) = tr(CAB) and unitarity star(h)·h = 1. -/
theorem uChar_isClassFunction : IsClassFunction (uChar n) := by
  intro h u
  unfold uChar
  congr 2
  have hcoe : ((h * u * h⁻¹ : Matrix.unitaryGroup (Fin n) ℂ)
      : Matrix (Fin n) (Fin n) ℂ)
      = (h : Matrix (Fin n) (Fin n) ℂ) * u * star (h : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hcoe, Matrix.trace_mul_cycle]
  have hunit : star (h : Matrix (Fin n) (Fin n) ℂ) * h = 1 := h.prop.1
  rw [← Matrix.mul_assoc, hunit, Matrix.one_mul]

/-- **Proved:** every entry of a unitary matrix has |entry|² ≤ 1
    (columns are unit vectors). -/
theorem normSq_entry_le_one (g : Matrix.unitaryGroup (Fin n) ℂ) (i j : Fin n) :
    Complex.normSq ((g : Matrix (Fin n) (Fin n) ℂ) i j) ≤ 1 := by
  have hu : star (g : Matrix (Fin n) (Fin n) ℂ) * g = 1 := g.prop.1
  have hjj := congrFun (congrFun hu j) j
  rw [Matrix.mul_apply] at hjj
  have hsum : ∑ k : Fin n,
      Complex.normSq ((g : Matrix (Fin n) (Fin n) ℂ) k j) = 1 := by
    have : ∑ k : Fin n,
        (starRingEnd ℂ) ((g : Matrix (Fin n) (Fin n) ℂ) k j) *
          (g : Matrix (Fin n) (Fin n) ℂ) k j = 1 := by
      simpa [Matrix.star_apply] using hjj
    have hre := congrArg Complex.re this
    simpa [Complex.re_sum, Complex.normSq_eq_conj_mul_self] using hre.symm ▸ rfl
  calc Complex.normSq ((g : Matrix (Fin n) (Fin n) ℂ) i j)
      ≤ ∑ k : Fin n, Complex.normSq ((g : Matrix (Fin n) (Fin n) ℂ) k j) :=
        Finset.single_le_sum (fun k _ => Complex.normSq_nonneg _)
          (Finset.mem_univ i)
    _ = 1 := hsum

/-- **Proved:** |χ(g)| ≤ 1 on U(n). -/
theorem abs_uChar_le_one (g : Matrix.unitaryGroup (Fin n) ℂ) :
    |uChar n g| ≤ 1 := by
  have hne : (0 : ℝ) < n := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hentry : ∀ i : Fin n,
      |((g : Matrix (Fin n) (Fin n) ℂ) i i).re| ≤ 1 := by
    intro i
    calc |((g : Matrix (Fin n) (Fin n) ℂ) i i).re|
        ≤ Complex.abs ((g : Matrix (Fin n) (Fin n) ℂ) i i) :=
          Complex.abs_re_le_abs _
      _ ≤ 1 := by
          rw [Complex.abs_apply, ← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (normSq_entry_le_one n g i i)
  unfold uChar
  rw [abs_div, abs_of_pos hne, div_le_one hne]
  calc |(Matrix.trace (g : Matrix (Fin n) (Fin n) ℂ)).re|
      = |∑ i : Fin n, ((g : Matrix (Fin n) (Fin n) ℂ) i i).re| := by
        rw [Matrix.trace]
        simp [Matrix.diag, Complex.re_sum]
    _ ≤ ∑ i : Fin n, |((g : Matrix (Fin n) (Fin n) ℂ) i i).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => hentry i
    _ = n := by simp

end LatticeGauge
