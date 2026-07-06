/-
LatticeGauge/HaarUnitary.lean — Phase 3, ninth stone.

Haar probability measure on U(n), from first principles on Mathlib
v4.15 (which lacks these instances): topological group structure,
compactness (Tychonoff polydisc + closedness), Haar probability, and
RIGHT invariance proved via uniqueness (a right translate of Haar is a
left-invariant probability measure, hence Haar itself). Capstones:
unconditional |⟨W⟩| ≤ 1 and unconditional gauge invariance of the
Gibbs expectation on U(n). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.GaugeInvariance
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation
import LatticeGauge.GaugeSymmetry
import LatticeGauge.UnitaryChar

open MeasureTheory

namespace LatticeGauge

variable (n : ℕ) [NeZero n]

/-- Abbreviation for the unitary group U(n) over ℂ. -/
abbrev UG (n : ℕ) := Matrix.unitaryGroup (Fin n) ℂ

instance : Nonempty (UG n) := ⟨1⟩

/-! ## Topological group structure (ported from post-4.15 Mathlib) -/

instance : ContinuousStar (UG n) where
  continuous_star := continuous_induced_rng.mpr continuous_subtype_val.star

instance : ContinuousInv (UG n) where
  continuous_inv := continuous_star

instance : TopologicalGroup (UG n) where

/-! ## Compactness -/

/-- **Proved:** entries of unitary matrices lie in the closed unit disc. -/
theorem abs_entry_le_one (g : UG n) (i j : Fin n) :
    Complex.abs ((g : Matrix (Fin n) (Fin n) ℂ) i j) ≤ 1 := by
  rw [Complex.abs_apply, ← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (normSq_entry_le_one n g i j)

/-- **Proved:** U(n) is compact — a closed subset of the compact
    polydisc (Tychonoff). -/
instance : CompactSpace (UG n) := by
  have hclosed : IsClosed (Matrix.unitaryGroup (Fin n) ℂ :
      Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hf : Continuous fun A : Matrix (Fin n) (Fin n) ℂ =>
        (star A * A, A * star A) :=
      (continuous_star.mul continuous_id).prod_mk
        (continuous_id.mul continuous_star)
    have hset : (Matrix.unitaryGroup (Fin n) ℂ :
        Set (Matrix (Fin n) (Fin n) ℂ))
        = (fun A : Matrix (Fin n) (Fin n) ℂ => (star A * A, A * star A)) ⁻¹'
          {(1, 1)} := by
      ext A
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq,
        SetLike.mem_coe, unitary.mem_iff]
    rw [hset]
    exact isClosed_singleton.preimage hf
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin n =>
      (Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1)) :=
    isCompact_univ_pi fun _ =>
      isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hsub : (Matrix.unitaryGroup (Fin n) ℂ :
      Set (Matrix (Fin n) (Fin n) ℂ))
      ⊆ Set.pi Set.univ fun _ : Fin n =>
        (Set.pi Set.univ fun _ : Fin n => Metric.closedBall (0 : ℂ) 1) := by
    intro A hA
    intro i _
    intro j _
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_eq_abs]
    exact abs_entry_le_one n ⟨A, hA⟩ i j
  have : IsCompact (Matrix.unitaryGroup (Fin n) ℂ :
      Set (Matrix (Fin n) (Fin n) ℂ)) :=
    hK.of_isClosed_subset hclosed hsub
  exact isCompact_iff_compactSpace.mp this

/-! ## Haar probability measure -/

noncomputable instance : MeasurableSpace (UG n) := borel _
instance : BorelSpace (UG n) := ⟨rfl⟩

/-- The whole group as a positive compact set. -/
def UGfull : TopologicalSpace.PositiveCompacts (UG n) :=
  ⟨⟨Set.univ, isCompact_univ⟩, by
    rw [TopologicalSpace.Compacts.coe_mk, interior_univ]
    exact Set.univ_nonempty⟩

/-- The Haar measure on U(n), normalized so that the whole group has
    measure 1. -/
noncomputable def haarU : Measure (UG n) :=
  Measure.haarMeasure (UGfull n)

instance : (haarU n).IsMulLeftInvariant := by
  unfold haarU; infer_instance

instance : IsProbabilityMeasure (haarU n) :=
  ⟨by simpa [UGfull] using Measure.haarMeasure_self (K₀ := UGfull n)⟩

/-- **Proved: RIGHT invariance of Haar on the compact group U(n).**
    The right translate of Haar is a left-invariant probability measure;
    by uniqueness of Haar measure it is Haar itself. -/
instance : (haarU n).IsMulRightInvariant := by
  constructor
  intro b
  haveI hprob : IsProbabilityMeasure ((haarU n).map (· * b)) :=
    isProbabilityMeasure_map (measurable_mul_const b).aemeasurable
  haveI hleft : ((haarU n).map (· * b)).IsMulLeftInvariant := by
    constructor
    intro a
    rw [Measure.map_map (measurable_const_mul a) (measurable_mul_const b)]
    have hcomp : ((a * ·) ∘ (· * b)) = ((· * b) ∘ (a * ·)) := by
      funext x
      simp [mul_assoc]
    rw [hcomp, ← Measure.map_map (measurable_mul_const b)
      (measurable_const_mul a), Measure.map_mul_left_eq_self (haarU n) a]
  have huniq := (Measure.haarMeasure_eq_iff (UGfull n)
    ((haarU n).map (· * b))).mpr (by
      have : (↑(UGfull n) : Set (UG n)) = Set.univ := rfl
      rw [this]
      exact measure_univ)
  calc (haarU n).map (· * b) = Measure.haarMeasure (UGfull n) := huniq.symm
    _ = haarU n := rfl

/-! ## The physical character is measurable -/

/-- **Proved:** the physical character is continuous. -/
theorem continuous_uChar : Continuous (uChar n) := by
  unfold uChar
  apply Continuous.div_const
  apply Complex.continuous_re.comp
  have htrace : Continuous fun M : Matrix (Fin n) (Fin n) ℂ =>
      Matrix.trace M := by
    unfold Matrix.trace Matrix.diag
    exact continuous_finset_sum _ fun i _ =>
      (continuous_apply i).comp (continuous_apply i)
  exact htrace.comp continuous_subtype_val

theorem measurable_uChar : Measurable (uChar n) :=
  (continuous_uChar n).measurable

/-! ## Unconditional capstones on U(n) -/

/-- **UNCONDITIONAL (proved): |⟨Wilson loop⟩| ≤ 1 on U(n) with Haar
    measure and the physical character — no hypotheses left beyond
    β ≥ 0.** -/
theorem abs_wilsonLoopExpectation_le_one_unitary
    {N : ℕ} [NeZero N] [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) (x : Site N) (p : List Step) :
    |gibbsExpectation (N := N) (haarU n) β (uChar n)
      (fun U => wilsonLoop (uChar n) U x p)| ≤ 1 :=
  abs_wilsonLoopExpectation_le_one (haarU n) (measurable_uChar n) hβ
    (abs_uChar_le_one n) x p

/-- **UNCONDITIONAL (proved): gauge invariance of the Gibbs expectation
    on U(n) with Haar measure** — for every observable and every gauge
    transformation. -/
theorem gibbsExpectation_gauge_invariant_unitary
    {N : ℕ} [NeZero N] [Fintype (Site N)] (β : ℝ)
    (g : GaugeTransform N (UG n)) (f : Config N (UG n) → ℝ) :
    gibbsExpectation (N := N) (haarU n) β (uChar n)
        (fun U => f (gaugeAct g U))
      = gibbsExpectation (N := N) (haarU n) β (uChar n) f :=
  gibbsExpectation_gauge_invariant (haarU n)
    (uChar_isClassFunction n) β g f

end LatticeGauge
