/-
LatticeGauge/PlaquetteActivity.lean — Phase 3, thirty-second stone.

FINITE PLAQUETTE-ACTIVITY EXPANSION (finite Mayer subset identity)
(architecture: Sol/GPT-5.6; execution: Fable). LEVEL (a) ONLY: exact
finite algebraic identities. The Wilson action decomposes as a sum of
local plaquette terms; the Gibbs weight is the product of
(1 + activity) over admissible plaquettes; expanding the product gives
an EXACT finite sum over SUBSETS of plaquettes (Finset.prod_add), and
realZ equals the finite sum of the integrals of activity products.
Subsets here are just subsets: NO connectivity, NO SimpleGraph, NO
"polymer" objects — those are reserved for the stone where
connectedness is formalized. The activities are SIGNED
(exp(−βs) − 1 ≤ 0 for β ≥ 0, s ≥ 0), which is why the integrated
identity uses realZ (a real Bochner integral) and NOT the
ℝ≥0∞-valued partitionFunction: ENNReal.ofReal is not additive over
signed sums. THIS IS NOT: a connected-cluster expansion; a
convergence estimate; uniform in the volume; a clustering or
mass-gap statement. Local bound: |activity| ≤ 2β under β ≥ 0 and
|χ| ≤ 1 (sharper than 2β·e^{2β}, obtained with no new machinery from
Real.add_one_le_exp). NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.FiniteSupportFactorizationBeta0

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **The admissible plaquette indices**: raw index Site × Dir × Dir,
    filtered by μ.val < ν.val — exactly the summands of wilsonAction.
    A subtype is deliberately avoided. -/
def admissiblePlaquettes (N : ℕ) [NeZero N] [Fintype (Site N)] :
    Finset (Site N × Dir × Dir) :=
  Finset.univ.filter (fun p => p.2.1.val < p.2.2.val)

/-- **The local plaquette action** 1 − χ(plaquette). -/
def localPlaquetteAction [NeZero N] (χ : G → ℝ) (U : Config N G)
    (p : Site N × Dir × Dir) : ℝ :=
  1 - χ (plaquette U p.1 p.2.1 p.2.2)

/-- **The plaquette activity** (Mayer factor) e^{−β·s_p} − 1. Signed:
    ≤ 0 for β ≥ 0 and s_p ≥ 0. -/
noncomputable def plaquetteActivity [NeZero N] (β : ℝ) (χ : G → ℝ)
    (U : Config N G) (p : Site N × Dir × Dir) : ℝ :=
  Real.exp (-β * localPlaquetteAction χ U p) - 1

/-- **A. Local decomposition of the Wilson action**: the action is
    exactly the sum of the local plaquette terms over the admissible
    indices. -/
theorem wilsonAction_eq_sum_localPlaquetteAction [NeZero N]
    [Fintype (Site N)] (χ : G → ℝ) (U : Config N G) :
    wilsonAction χ U
      = ∑ p ∈ admissiblePlaquettes N, localPlaquetteAction χ U p := by
  unfold wilsonAction admissiblePlaquettes localPlaquetteAction
  rw [Finset.sum_filter]
  simp only [Fintype.sum_prod_type]

/-- **B. Product identity**: the Gibbs weight is the product of
    (1 + activity) over admissible plaquettes. -/
theorem gibbsWeight_eq_prod_one_add_activity [NeZero N]
    [Fintype (Site N)] (β : ℝ) (χ : G → ℝ) (U : Config N G) :
    gibbsWeight β χ U
      = ∏ p ∈ admissiblePlaquettes N,
          (1 + plaquetteActivity β χ U p) := by
  have hpt : ∀ p ∈ admissiblePlaquettes N,
      (1 : ℝ) + plaquetteActivity β χ U p
        = Real.exp (-β * localPlaquetteAction χ U p) := by
    intro p _
    unfold plaquetteActivity
    ring
  rw [Finset.prod_congr rfl hpt, ← Real.exp_sum]
  unfold gibbsWeight
  congr 1
  rw [wilsonAction_eq_sum_localPlaquetteAction χ U, Finset.mul_sum]

/-- **C. FINITE MAYER SUBSET IDENTITY (capstone, level (a))**: the
    Gibbs weight is the EXACT finite sum, over all SUBSETS of
    admissible plaquettes, of the products of activities. Subsets are
    just subsets — no connectivity is involved. -/
theorem gibbsWeight_eq_sum_prod_activity [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (U : Config N G) :
    gibbsWeight β χ U
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∏ p ∈ A, plaquetteActivity β χ U p := by
  rw [gibbsWeight_eq_prod_one_add_activity β χ U]
  have hcomm : ∀ p ∈ admissiblePlaquettes N,
      (1 : ℝ) + plaquetteActivity β χ U p
        = plaquetteActivity β χ U p + 1 := fun p _ => by ring
  rw [Finset.prod_congr rfl hcomm, Finset.prod_add]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp

/-- **D. LOCAL BOUND on the activity**: |e^{−β·s_p} − 1| ≤ 2β for
    β ≥ 0 and |χ| ≤ 1 — the LOCAL bound (not the global action bound
    B), from Real.add_one_le_exp with no new machinery. -/
theorem abs_plaquetteActivity_le [NeZero N]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (hχabs : ∀ g : G, |χ g| ≤ 1)
    (U : Config N G) (p : Site N × Dir × Dir) :
    |plaquetteActivity β χ U p| ≤ 2 * β := by
  unfold plaquetteActivity localPlaquetteAction
  set s : ℝ := 1 - χ (plaquette U p.1 p.2.1 p.2.2) with hsdef
  have habs := abs_le.mp (hχabs (plaquette U p.1 p.2.1 p.2.2))
  have hs0 : 0 ≤ s := by rw [hsdef]; linarith [habs.2]
  have hs2 : s ≤ 2 := by rw [hsdef]; linarith [habs.1]
  have hx0 : 0 ≤ β * s := mul_nonneg hβ hs0
  have hexp1 : Real.exp (-β * s) ≤ 1 := by
    rw [neg_mul]
    calc Real.exp (-(β * s)) ≤ Real.exp 0 :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 := Real.exp_zero
  have hlow : 1 - β * s ≤ Real.exp (-β * s) := by
    have h := Real.add_one_le_exp (-(β * s))
    rw [neg_mul]
    linarith
  rw [abs_of_nonpos (by linarith : Real.exp (-β * s) - 1 ≤ 0)]
  have h2 : β * s ≤ β * 2 := mul_le_mul_of_nonneg_left hs2 hβ
  linarith

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **Measurability of the activity.** -/
theorem measurable_plaquetteActivity [NeZero N]
    (β : ℝ) {χ : G → ℝ} (mχ : Measurable χ)
    (p : Site N × Dir × Dir) :
    Measurable (fun U : Config N G =>
      plaquetteActivity β χ U p) := by
  unfold plaquetteActivity localPlaquetteAction
  exact ((Real.measurable_exp.comp
    (((measurable_const.sub
      (mχ.comp (measurable_plaquette p.1 p.2.1 p.2.2)))).const_mul
        (-β)))).sub measurable_const

/-- **E. FINITE EXPANSION OF THE REAL PARTITION FUNCTION**: realZ is
    the EXACT finite sum of the integrals of the activity products
    over all subsets. Uses realZ (real Bochner integral), NOT the
    ℝ≥0∞ partitionFunction: the activities are signed (≤ 0 for
    β ≥ 0), and ENNReal.ofReal is not additive over signed sums. -/
theorem realZ_eq_sum_integral_prod_activity [NeZero N]
    [Fintype (Site N)]
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) :
    realZ (N := N) μm β χ
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∫ U : Config N G, ∏ p ∈ A, plaquetteActivity β χ U p
            ∂(configMeasure μm N) := by
  classical
  have hprodbound : ∀ (A : Finset (Site N × Dir × Dir))
      (U : Config N G),
      |∏ p ∈ A, plaquetteActivity β χ U p| ≤ (2 * β) ^ A.card := by
    intro A U
    rw [Finset.abs_prod]
    calc ∏ p ∈ A, |plaquetteActivity β χ U p|
        ≤ ∏ _p ∈ A, (2 * β) :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _)
            (fun p _ => abs_plaquetteActivity_le hβ hχabs U p)
      _ = (2 * β) ^ A.card := Finset.prod_const _
  have hint : ∀ A ∈ (admissiblePlaquettes N).powerset,
      Integrable (fun U : Config N G =>
        ∏ p ∈ A, plaquetteActivity β χ U p) (configMeasure μm N) := by
    intro A _
    refine (integrable_const ((2 * β) ^ A.card)).mono'
      ((measurable_finsetProd A
        (fun p U => plaquetteActivity β χ U p)
        (fun p _ => measurable_plaquetteActivity β mχ p))
          .aestronglyMeasurable) ?_
    filter_upwards with U
    rw [Real.norm_eq_abs]
    exact hprodbound A U
  unfold realZ
  calc (∫ U : Config N G, gibbsWeight β χ U ∂(configMeasure μm N))
      = ∫ U : Config N G,
          (∑ A ∈ (admissiblePlaquettes N).powerset,
            ∏ p ∈ A, plaquetteActivity β χ U p)
          ∂(configMeasure μm N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
        exact gibbsWeight_eq_sum_prod_activity β χ U
    _ = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∫ U : Config N G, ∏ p ∈ A, plaquetteActivity β χ U p
            ∂(configMeasure μm N) :=
        integral_finset_sum _ hint

end Measure

end LatticeGauge
