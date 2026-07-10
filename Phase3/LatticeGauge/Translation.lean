/-
LatticeGauge/Translation.lean — Phase 3, tenth stone.

Lattice translations: the last symmetry. We prove the Wilson action and
the Gibbs expectation are TRANSLATION INVARIANT, define truncated
(connected) correlations with an a-priori bound, and — for the first
time in this repository — give the FORMAL STATEMENT of the lattice mass
gap (exponential clustering). Stating is not proving: the final
definition is the project's open target, honestly labelled. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop
import LatticeGauge.Expectation
import LatticeGauge.WilsonExpectation

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **Proved:** shifting forward then backward returns to the start. -/
@[simp] theorem shiftBack_shift [NeZero N] (x : Site N) (μ : Dir) :
    shiftBack (shift x μ) μ = x := by
  fin_cases μ <;> simp [shift, shiftBack]

/-- Translation of sites by one lattice unit, as an equivalence. -/
def siteShift [NeZero N] (d : Dir) : Site N ≃ Site N where
  toFun x := shift x d
  invFun x := shiftBack x d
  left_inv x := shiftBack_shift x d
  right_inv x := shift_shiftBack x d

/-- Translation of links by one lattice unit, as an equivalence. -/
def linkShift [NeZero N] (d : Dir) : Link N ≃ Link N where
  toFun ℓ := (shift ℓ.1 d, ℓ.2)
  invFun ℓ := (shiftBack ℓ.1 d, ℓ.2)
  left_inv ℓ := by simp
  right_inv ℓ := by simp

/-- Translation acting on gauge configurations. -/
def translate [NeZero N] (d : Dir) (U : Config N G) : Config N G :=
  fun ℓ => U (shift ℓ.1 d, ℓ.2)

/-- **Proved:** plaquettes of a translated configuration are the
    plaquettes of the original at the translated site. -/
theorem plaquette_translate [NeZero N]
    (d : Dir) (U : Config N G) (x : Site N) (μ ν : Dir) :
    plaquette (translate d U) x μ ν = plaquette U (shift x d) μ ν := by
  unfold plaquette translate
  rw [shift_comm x μ d, shift_comm x ν d]

/-- **Proved: the Wilson action is translation invariant.** -/
theorem wilsonAction_translate [NeZero N] [Fintype (Site N)]
    (χ : G → ℝ) (d : Dir) (U : Config N G) :
    wilsonAction χ (translate d U) = wilsonAction χ U := by
  unfold wilsonAction
  calc ∑ x : Site N, ∑ μ : Dir, ∑ ν : Dir,
        (if μ.val < ν.val then 1 - χ (plaquette (translate d U) x μ ν) else 0)
      = ∑ x : Site N, ∑ μ : Dir, ∑ ν : Dir,
        (if μ.val < ν.val then 1 - χ (plaquette U (siteShift (N := N) d x) μ ν) else 0) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_congr rfl fun μ _ => ?_
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [plaquette_translate]
        rfl
    _ = ∑ x : Site N, ∑ μ : Dir, ∑ ν : Dir,
        (if μ.val < ν.val then 1 - χ (plaquette U x μ ν) else 0) :=
        Equiv.sum_comp (siteShift (N := N) d)
          (fun y => ∑ μ : Dir, ∑ ν : Dir,
            if μ.val < ν.val then 1 - χ (plaquette U y μ ν) else 0)

section Measure

variable [MeasurableSpace G] (μm : Measure G) [SigmaFinite μm]

/-- Translation as a measurable equivalence of configuration space. -/
noncomputable def translateEquiv [NeZero N] (d : Dir) :
    Config N G ≃ᵐ Config N G :=
  MeasurableEquiv.piCongrLeft (fun _ : Link N => G) (linkShift (N := N) d).symm

/-- **Proved:** the measurable-equivalence form agrees with `translate`. -/
theorem translateEquiv_coe [NeZero N] (d : Dir) :
    ⇑(translateEquiv (N := N) (G := G) d) = translate d := by
  funext U ℓ
  have h := MeasurableEquiv.piCongrLeft_apply_apply
    (linkShift (N := N) d).symm U ((linkShift (N := N) d) ℓ)
  simpa [translateEquiv, Equiv.symm_apply_apply, translate, linkShift] using h

/-- **Proved: translations preserve the product measure.** -/
theorem measurePreserving_translate [NeZero N] (d : Dir) :
    MeasurePreserving (translate (N := N) (G := G) d)
      (configMeasure μm N) (configMeasure μm N) := by
  rw [← translateEquiv_coe]
  exact measurePreserving_piCongrLeft (fun _ : Link N => μm)
    (linkShift (N := N) d).symm

/-- **Proved: the Gibbs expectation is translation invariant.** -/
theorem gibbsExpectation_translate [NeZero N] [Fintype (Site N)]
    {χ : G → ℝ} (β : ℝ) (d : Dir) (f : Config N G → ℝ) :
    gibbsExpectation (N := N) μm β χ (fun U => f (translate d U))
      = gibbsExpectation (N := N) μm β χ f := by
  have hmp := measurePreserving_translate (N := N) (G := G) μm d
  have hemb : MeasurableEmbedding (translate (N := N) (G := G) d) := by
    rw [← translateEquiv_coe]
    exact (translateEquiv (N := N) (G := G) d).measurableEmbedding
  unfold gibbsExpectation
  congr 1
  calc ∫ U : Config N G, f (translate d U) * gibbsWeight β χ U
        ∂(configMeasure μm N)
      = ∫ U : Config N G, f (translate d U) * gibbsWeight β χ (translate d U)
        ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        show f (translate d U) * gibbsWeight β χ U
            = f (translate d U) * gibbsWeight β χ (translate d U)
        have hw : gibbsWeight β χ (translate d U) = gibbsWeight β χ U := by
          unfold gibbsWeight
          rw [wilsonAction_translate χ d U]
        rw [hw]
    _ = ∫ V : Config N G, f V * gibbsWeight β χ V ∂(configMeasure μm N) :=
        hmp.integral_comp hemb (fun V => f V * gibbsWeight β χ V)

/-! ## Truncated correlations and THE TARGET -/

/-- Truncated (connected) two-point correlation:
    ⟨f·g⟩ − ⟨f⟩·⟨g⟩. -/
noncomputable def truncatedCorrelation [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f g : Config N G → ℝ) : ℝ :=
  gibbsExpectation (N := N) μm β χ (fun U => f U * g U)
    - gibbsExpectation (N := N) μm β χ f * gibbsExpectation (N := N) μm β χ g

variable [MeasurableMul₂ G] [MeasurableInv G] [IsProbabilityMeasure μm]

/-- **Proved: a-priori bound for truncated correlations of bounded
    observables:** |⟨fg⟩ − ⟨f⟩⟨g⟩| ≤ 2C². -/
theorem abs_truncatedCorrelation_le [NeZero N] [Fintype (Site N)]
    {χ : G → ℝ} (mχ : Measurable χ) {β B C : ℝ} (hβ : 0 ≤ β)
    (hχ : ∀ g : G, χ g ≤ 1) (hB : ∀ U : Config N G, wilsonAction χ U ≤ B)
    {f g : Config N G → ℝ} (mf : Measurable f) (mg : Measurable g)
    (hf : ∀ U, |f U| ≤ C) (hg : ∀ U, |g U| ≤ C) :
    |truncatedCorrelation (N := N) μm β χ f g| ≤ 2 * C ^ 2 := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hf (trivialConfig N G))
  have h1 : |gibbsExpectation (N := N) μm β χ (fun U => f U * g U)| ≤ C ^ 2 := by
    have := abs_gibbsExpectation_le (N := N) μm mχ hβ hχ hB (mf.mul mg)
      (f := fun U => f U * g U) (C := C ^ 2) ?_
    · exact this
    · intro U
      rw [abs_mul, sq]
      exact mul_le_mul (hf U) (hg U) (abs_nonneg _) hC
  have h2 : |gibbsExpectation (N := N) μm β χ f| ≤ C :=
    abs_gibbsExpectation_le (N := N) μm mχ hβ hχ hB mf hf
  have h3 : |gibbsExpectation (N := N) μm β χ g| ≤ C :=
    abs_gibbsExpectation_le (N := N) μm mχ hβ hχ hB mg hg
  unfold truncatedCorrelation
  calc |gibbsExpectation (N := N) μm β χ (fun U => f U * g U)
        - gibbsExpectation (N := N) μm β χ f * gibbsExpectation (N := N) μm β χ g|
      ≤ |gibbsExpectation (N := N) μm β χ (fun U => f U * g U)|
        + |gibbsExpectation (N := N) μm β χ f * gibbsExpectation (N := N) μm β χ g| :=
        abs_sub _ _
    _ ≤ C ^ 2 + C * C := by
        refine add_le_add h1 ?_
        rw [abs_mul]
        exact mul_le_mul h2 h3 (abs_nonneg _) hC
    _ = 2 * C ^ 2 := by ring

/-- **THE OPEN TARGET, formally stated (NOT proved — stating a
    definition is not progress on it):** the lattice theory has a mass
    gap `m` if truncated correlations of Wilson loops separated by `k`
    lattice translations decay like `e^(−m·k)`, uniformly in the loop.
    Proving `∃ m, HasLatticeMassGap … m` at strong coupling is the
    long-term goal of Phase 3 (Osterwalder–Seiler). -/
def HasLatticeMassGap [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (m : ℝ) : Prop :=
  0 < m ∧
  ∀ (x : Site N) (p : List Step) (d : Dir), ∃ Cc : ℝ,
    ∀ k : ℕ,
      |truncatedCorrelation (N := N) μm β χ
        (fun U => wilsonLoop χ U x p)
        (fun U => wilsonLoop χ ((translate d)^[k] U) x p)|
      ≤ Cc * Real.exp (-m * k)

end Measure

end LatticeGauge
