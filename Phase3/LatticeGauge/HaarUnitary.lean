/-
LatticeGauge/HaarUnitary.lean — Phase 3, ninth stone.

The concrete Haar probability measure on the compact group U(n), with
left and right invariance, and the UNCONDITIONAL capstone: on U(n) with
Haar measure and the physical character, every Wilson loop expectation
satisfies |⟨W⟩| ≤ 1 — no measure-theoretic hypotheses left.
NO axioms; everything proved or provided by Mathlib instances.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation
import LatticeGauge.UnitaryChar

open MeasureTheory

namespace LatticeGauge

variable (n : ℕ) [NeZero n]

/-- Abbreviation for the unitary group U(n) over ℂ. -/
abbrev UG (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

noncomputable instance : MeasurableSpace (UG n) := borel _
instance : BorelSpace (UG n) := ⟨rfl⟩

/-- The Haar probability measure on the compact group U(n). -/
noncomputable def haarU : Measure (UG n) := MeasureTheory.Measure.haar

instance : (haarU n).IsMulLeftInvariant := by
  unfold haarU; infer_instance

instance : IsProbabilityMeasure (haarU n) := by
  unfold haarU; infer_instance

instance : (haarU n).IsMulRightInvariant := by
  unfold haarU; infer_instance

instance : SigmaFinite (haarU n) := by
  unfold haarU; infer_instance

/-- **Proved:** the physical character is continuous, hence measurable. -/
theorem continuous_uChar : Continuous (uChar n) := by
  unfold uChar
  apply Continuous.div_const
  apply Complex.continuous_re.comp
  have htrace : Continuous fun M : Matrix (Fin n) (Fin n) ℂ => Matrix.trace M := by
    unfold Matrix.trace
    exact continuous_finset_sum _ fun i _ =>
      ((continuous_apply i).comp (continuous_apply i)).comp continuous_id |>.congr
        (fun M => rfl)
  exact htrace.comp continuous_subtype_val

theorem measurable_uChar : Measurable (uChar n) :=
  (continuous_uChar n).measurable

/-- **UNCONDITIONAL CAPSTONE (proved): on U(n) with Haar measure,
    |⟨Wilson loop⟩| ≤ 1** for every β ≥ 0, every lattice size, every
    site and every path. No hypotheses about the measure or the
    character remain — everything is concrete. -/
theorem abs_wilsonLoopExpectation_le_one_unitary
    {N : ℕ} [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) (x : Site N) (p : List Step) :
    |gibbsExpectation (N := N) (haarU n) β (uChar n)
      (fun U => wilsonLoop (uChar n) U x p)| ≤ 1 :=
  abs_wilsonLoopExpectation_le_one (haarU n) (measurable_uChar n) hβ
    (abs_uChar_le_one n) x p

end LatticeGauge
