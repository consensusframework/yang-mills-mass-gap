/-
LatticeGauge/RestrictedGas.lean — PEDRA 50, Gate 50-A3 (analytic
half): RESTRICTED ACTIVITIES, KP MONOTONICITY, AND THE GAS RATIO
AS AN EXPONENTIAL OF A CLUSTER DIFFERENCE
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's precision, kept): A3 performs the
first legitimate GLOBAL cancellation — the vacuum clusters common
to the restricted and the full gas cancel in the EXPONENT of the
gas ratio. A3 does NOT yet formalize the combinatorial support
localization ("difference ≠ 0 only if the cluster touches the
excluded region" — next gate), and much less "cluster connects
supp f to supp g" (two insertions/covariance — later). We do not
name the road sign two kilometres early.

Content: typedTouchesSupport; restrictedActivity z P (activity
kept on the ALLOWED predicate P, zeroed elsewhere — constraints
absorbed as zeros, no new set machinery); the pointwise bound
|restricted| ≤ |z|; KP MONOTONICITY (a smaller absolute activity
inherits the Kotecký–Preiss hypothesis — stone 46 NOT redone);
the restricted concrete specialization for 0 ≤ β ≤ 1/40000; the
restricted gas as an exponential (the 49C-V identity for GENERIC
activity, consumed); and the RATIO identity
  gas(restricted)/gas(full) = exp(C_restricted − C_full)
by Real.exp_sub — no division simplified, no nonvanishing
hypothesis anywhere.

HARD HOLD (not here): distance, SimpleGraph.dist, q^d,
exponential decay, second insertion g, covariance, connector
clusters between two supports, thermodynamic limit, continuum,
mass gap. No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.KPInduction
import LatticeGauge.KPSpecialization
import LatticeGauge.KPClusterExpansion
import LatticeGauge.ObservableGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A3.1 — typed support touching and restricted activities -/

/-- A typed polymer touches an observable support iff its raw
    shadow does. -/
def typedTouchesSupport (η : Polymer N) (s : Set (Link N)) :
    Prop :=
  blockTouchesSupport (N := N) η.val s

/-- Activity restricted to an ALLOWED predicate: kept on P,
    zeroed elsewhere — hard constraints absorbed as zeros. -/
noncomputable def restrictedActivity (z : Polymer N → ℝ)
    (P : Polymer N → Prop) : Polymer N → ℝ :=
  fun η => if P η then z η else 0

theorem abs_restrictedActivity_le (z : Polymer N → ℝ)
    (P : Polymer N → Prop) (η : Polymer N) :
    |restrictedActivity z P η| ≤ |z η| := by
  unfold restrictedActivity
  split_ifs
  · exact le_rfl
  · simp

/-! ## A3.2 — KP monotonicity: smaller absolute activity inherits
    the smallness hypothesis (stone 46 not redone) -/

theorem abstractKP_mono {ρ ρ' a : Polymer N → ℝ}
    (hle : ∀ η, ρ' η ≤ ρ η) (h0 : ∀ η, 0 ≤ ρ' η)
    (hKP : AbstractKPHypothesis (N := N) ρ a) :
    AbstractKPHypothesis (N := N) ρ' a := by
  intro γ₀
  refine le_trans (Finset.sum_le_sum ?_) (hKP γ₀)
  intro η _
  have hind : (0 : ℝ) ≤ (incompatibilityIndicator γ₀ η : ℝ) := by
    positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hle η) hind)
    (Real.exp_pos _).le

/-- Restriction preserves the abstract KP hypothesis. -/
theorem abstractKP_restrictedActivity {z a : Polymer N → ℝ}
    (P : Polymer N → Prop)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a) :
    AbstractKPHypothesis (N := N)
      (fun η => |restrictedActivity z P η|) a :=
  abstractKP_mono (fun η => abs_restrictedActivity_le z P η)
    (fun η => abs_nonneg _) hKP

/-- Concrete: for 0 ≤ β ≤ 1/40000, EVERY restriction of the
    polymer weight satisfies KP (stone 46/47 consumed through the
    49 specialization; monotonicity does the rest). -/
theorem abstractKP_restricted_polymerWeight {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) (P : Polymer N → Prop) :
    AbstractKPHypothesis (N := N)
      (fun η => |restrictedActivity
        (fun η => polymerWeight (N := N) μm β χ η.val) P η|)
      (fun η => ((η.val.card : ℕ) : ℝ)) :=
  abstractKP_restrictedActivity P
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)

/-! ## A3.3 — the restricted gas as an exponential and THE RATIO
    AS exp OF A CLUSTER DIFFERENCE -/

/-- The restricted gas is an exponential of its own cluster sum
    (the generic-activity 49C-V identity consumed). -/
theorem typedPolymerGas_restricted_eq_exp {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    typedPolymerGas (N := N) (restrictedActivity z P)
      = Real.exp (∑' n, kpSignedUnrootedCoeff n
          (restrictedActivity z P)) :=
  typedPolymerGas_eq_exp_tsum_of_KP ha
    (abstractKP_restrictedActivity P hKP)

/-- **CAPSTONE (analytic half of A3)**: the gas ratio is the
    exponential of the cluster DIFFERENCE — the vacuum clusters
    common to both gases cancel in the exponent. Division is
    rewritten by Real.exp_sub; nothing is assumed nonzero. -/
theorem typedPolymerGas_ratio_eq_exp_sub {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    typedPolymerGas (N := N) (restrictedActivity z P)
        / typedPolymerGas (N := N) z
      = Real.exp
          ((∑' n, kpSignedUnrootedCoeff n
              (restrictedActivity z P))
            - ∑' n, kpSignedUnrootedCoeff (N := N) n z) := by
  rw [typedPolymerGas_eq_exp_tsum_of_KP ha hKP,
    typedPolymerGas_restricted_eq_exp ha hKP P,
    ← Real.exp_sub]

end LatticeGauge
