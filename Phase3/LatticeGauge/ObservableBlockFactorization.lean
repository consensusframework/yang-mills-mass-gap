/-
LatticeGauge/ObservableBlockFactorization.lean — PEDRA 50, Gate
50-A0: THE ATOMIC CANCELLATION UNIT (architecture: Sol/GPT-5.6;
execution: Fable).

SEMANTICS (only this): "Any Mayer connected block whose link
support is disjoint from the support of the inserted observable
factors completely from that observable under the β=0 product
measure." This is the formal unit of cancellation of the future
marked expansion — the piece that will strip every irrelevant
component from the inserted numerator. NOT stated: Z[f]
expansion, covariance cancellation, connector clusters, distance
decay, q^d. Geometry (plaquetteGraph distance) is on HARD HOLD
per the architect's order (SimpleGraph.dist has junk value 0 for
unreachable pairs — recorded).

ZERO duplication of β=0 clustering: integral_mul_of_disjoint_
support (Beta0:57) and the stone-11 clustering are CONSUMED,
never reproved; the covariance/truncatedCorrelation bridge is
definitional (rfl). Note the measure/activity split: the block
activity keeps its own β as a parameter — the Mayer expansion
integrates β-activities against the β=0 PRODUCT measure, exactly
as in stones 32–34.

ATA (architect's corrections recorded): dividing by realZ has
been legal since realZ_pos; the stone-49 novelty is that
1/Z = e^{−C} now follows from the expansion itself —
architectural independence, not first authorization. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Beta0
import LatticeGauge.Translation
import LatticeGauge.FiniteBetaResponse
import LatticeGauge.ComponentFactorization

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **API bridge**: the stone-24 covariance IS the stone-11
    truncated correlation — definitional, so the β=0 clustering
    already proved transfers for free. Stone 11 is consumed,
    never reproved. -/
theorem gibbsCovariance_eq_truncatedCorrelation (β : ℝ)
    (χ : G → ℝ) (f g : Config N G → ℝ) :
    gibbsCovariance (N := N) μm β χ f g
      = truncatedCorrelation (N := N) μm β χ f g := rfl

/-- A Mayer block touches an observable support iff their link
    supports meet. -/
def blockTouchesSupport (C : Finset (Site N × Dir × Dir))
    (s : Set (Link N)) : Prop :=
  ¬ Disjoint (blockLinkSupport (N := N) C) s

theorem not_blockTouchesSupport_iff
    {C : Finset (Site N × Dir × Dir)} {s : Set (Link N)} :
    ¬ blockTouchesSupport (N := N) C s
      ↔ Disjoint (blockLinkSupport (N := N) C) s :=
  not_not

/-- **CAPSTONE 50-A0**: a Mayer block that does not touch the
    support of the inserted observable factors completely from it
    under the β=0 product measure. The activity's β is free — the
    measure is the product one, as in the stone-32–34 expansion. -/
theorem integral_observable_mul_blockActivity
    (β : ℝ) {χ : G → ℝ} (mχ : Measurable χ)
    {s : Set (Link N)} [DecidablePred (· ∈ s)]
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f)
    {C : Finset (Site N × Dir × Dir)}
    (hC : ¬ blockTouchesSupport (N := N) C s) :
    ∫ U : Config N G, f U * blockActivity β χ C U
        ∂(configMeasure μm N)
      = (∫ U : Config N G, f U ∂(configMeasure μm N))
        * ∫ U : Config N G, blockActivity β χ C U
            ∂(configMeasure μm N) := by
  have hdisj := not_blockTouchesSupport_iff.mp hC
  have hsub : blockLinkSupport (N := N) C ⊆ sᶜ :=
    fun x hx => Set.disjoint_left.mp hdisj hx
  have hg : DependsOnlyOn
      (fun U : Config N G => blockActivity β χ C U) sᶜ :=
    dependsOnlyOn_mono (blockActivity_dependsOnlyOn β χ C) hsub
  exact integral_mul_of_disjoint_support (N := N) μm s hf hg
    mf (measurable_blockActivity β mχ C)

/-- The same factorization through the β=0 Gibbs expectation
    (gibbsExpectation_zero consumed on all three sides). -/
theorem gibbsExpectation_zero_observable_mul_blockActivity
    (β : ℝ) {χ : G → ℝ} (mχ : Measurable χ)
    {s : Set (Link N)} [DecidablePred (· ∈ s)]
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f)
    {C : Finset (Site N × Dir × Dir)}
    (hC : ¬ blockTouchesSupport (N := N) C s) :
    gibbsExpectation (N := N) μm 0 χ
        (fun U => f U * blockActivity β χ C U)
      = gibbsExpectation (N := N) μm 0 χ f
        * gibbsExpectation (N := N) μm 0 χ
            (fun U => blockActivity β χ C U) := by
  rw [gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ]
  exact integral_observable_mul_blockActivity μm β mχ hf mf hC

end LatticeGauge
