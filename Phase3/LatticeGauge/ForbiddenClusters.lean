/-
LatticeGauge/ForbiddenClusters.lean — PEDRA 50, Gate 50-A4: WHO
SURVIVED IN THE DIFFERENCE — the forbidden-cluster localization
(architecture: Sol/GPT-5.6; execution: Fable).

After A3 we knew C_restricted − C_full was SOME difference of
cluster sums. After this gate the kernel says it literally:
  C_restricted − C_full = − Σ' (connected clusters containing at
                              least one forbidden polymer).
For the concrete restriction remoteAllowed T s, forbidden means
EXACTLY: touches the support s, OR is incompatible with some
member of the touching core T. This is LOCALIZATION WITHOUT ANY
METRIC — the stone-37 structural zero (disconnected ⟹ Ursell
coefficient 0) does all the work; no distance is defined, no
paths are counted, no geometric tail is proved.

NOT here: distance, plaquetteGraph/SimpleGraph.dist, q^d, path
counting, geometric tails, a second observable, covariance,
"connects s to t", thermodynamic limit, mass gap.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.KPUnrooted
import LatticeGauge.RestrictedGas

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A4.1 — allowed tuples and the product identity -/

def TupleAllowed (P : Polymer N → Prop) {k : ℕ}
    (δ : Fin k → Polymer N) : Prop :=
  ∀ i, P (δ i)

theorem prod_restrictedActivity_eq {k : ℕ}
    (z : Polymer N → ℝ) (P : Polymer N → Prop)
    (δ : Fin k → Polymer N) :
    (∏ i : Fin k, restrictedActivity z P (δ i))
      = if TupleAllowed P δ then ∏ i : Fin k, z (δ i) else 0 := by
  by_cases h : TupleAllowed P δ
  · rw [if_pos h]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    unfold restrictedActivity
    exact if_pos (h i)
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    unfold restrictedActivity
    exact if_neg hi

/-! ## A4.2 — the forbidden coefficient and the exact split -/

/-- The forbidden part of the unrooted coefficient: tuples that
    hit at least one forbidden polymer. -/
noncomputable def kpForbiddenUnrootedCoeff (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleAllowed P δ then 0 else
        ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
          * ∏ i : Fin k, z (δ i))
    / ((Nat.factorial k : ℕ) : ℝ)

/-- **The exact split**: full = restricted + forbidden, per k. -/
theorem kpSignedUnrootedCoeff_eq_restricted_add_forbidden
    (k : ℕ) (z : Polymer N → ℝ) (P : Polymer N → Prop) :
    kpSignedUnrootedCoeff (N := N) k z
      = kpSignedUnrootedCoeff k (restrictedActivity z P)
        + kpForbiddenUnrootedCoeff k z P := by
  unfold kpSignedUnrootedCoeff kpForbiddenUnrootedCoeff
  rw [div_add_div_same]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [prod_restrictedActivity_eq]
  by_cases h : TupleAllowed P δ
  · rw [if_pos h, if_pos h, add_zero]
  · rw [if_neg h, if_neg h, mul_zero, zero_add]

/-! ## A4.3 — CONNECTED-FORBIDDEN LOCALIZATION (stone 37 does the
    work: disconnected tuples contribute zero) -/

theorem kpForbiddenUnrootedCoeff_eq_connected_sum (k : ℕ)
    (z : Polymer N → ℝ) (P : Polymer N → Prop) :
    kpForbiddenUnrootedCoeff (N := N) k z P
      = (∑ δ ∈ Finset.univ.filter
          (fun δ : Fin k → Polymer N =>
            (polymerIncompatibilityGraph (N := N)
              (fun i => (δ i).val)).Connected
              ∧ ¬ TupleAllowed P δ),
          ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
            * ∏ i : Fin k, z (δ i))
        / ((Nat.factorial k : ℕ) : ℝ) := by
  unfold kpForbiddenUnrootedCoeff
  congr 1
  have h1 : (∑ δ : Fin k → Polymer N,
      if TupleAllowed P δ then 0 else
        ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
          * ∏ i : Fin k, z (δ i))
      = ∑ δ ∈ Finset.univ.filter
          (fun δ : Fin k → Polymer N => ¬ TupleAllowed P δ),
          ((ursellCoeff (N := N) (fun i => (δ i).val) : ℤ) : ℝ)
            * ∏ i : Fin k, z (δ i) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun δ _ => ?_)
    by_cases h : TupleAllowed P δ
    · rw [if_pos h, if_neg (not_not_intro h)]
    · rw [if_neg h, if_pos h]
  rw [h1]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro δ hδ
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hδ).2.2⟩
  · intro δ hδ hδnot
    have hnc : ¬ (polymerIncompatibilityGraph (N := N)
        (fun i => (δ i).val)).Connected := by
      intro hc
      exact hδnot (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,
          ⟨hc, (Finset.mem_filter.mp hδ).2⟩⟩)
    rw [ursellCoeff_of_not_connected _ hnc]
    simp

/-! ## A4.4 — the barrier characterization (no metric) -/

theorem not_remoteAllowed_iff (T : Finset (Polymer N))
    (s : Set (Link N)) (η : Polymer N) :
    ¬ remoteAllowed (N := N) T s η
      ↔ typedTouchesSupport (N := N) η s
        ∨ ∃ t ∈ T, ¬ PlaquetteCompatible (N := N) η.val t.val := by
  unfold remoteAllowed
  constructor
  · intro h
    by_cases ht : typedTouchesSupport (N := N) η s
    · exact Or.inl ht
    · refine Or.inr ?_
      by_contra hc
      push_neg at hc
      exact h ⟨ht, hc⟩
  · rintro (ht | ⟨t, htT, hnc⟩) ⟨hnt, hall⟩
    · exact hnt ht
    · exact hnc (hall t htT)

/-- **The barrier tuple characterization**: a tuple is forbidden
    for remoteAllowed T s iff SOME entry touches the support or
    is incompatible with some core member — localization stated
    with no distance anywhere. -/
theorem not_tupleAllowed_remoteAllowed_iff
    (T : Finset (Polymer N)) (s : Set (Link N)) {k : ℕ}
    (δ : Fin k → Polymer N) :
    ¬ TupleAllowed (remoteAllowed (N := N) T s) δ
      ↔ ∃ i, typedTouchesSupport (N := N) (δ i) s
          ∨ ∃ t ∈ T, ¬ PlaquetteCompatible (N := N)
              (δ i).val t.val := by
  unfold TupleAllowed
  rw [not_forall]
  exact exists_congr (fun i => not_remoteAllowed_iff T s (δ i))

/-! ## A4.5 — absolute summability and THE DIFFERENCE IDENTITY -/

theorem summable_abs_kpForbiddenUnrootedCoeff
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    Summable (fun k =>
      |kpForbiddenUnrootedCoeff (N := N) k z P|) := by
  have hforb : ∀ k, kpForbiddenUnrootedCoeff (N := N) k z P
      = kpSignedUnrootedCoeff k z
        - kpSignedUnrootedCoeff k (restrictedActivity z P) :=
    fun k => by
      rw [kpSignedUnrootedCoeff_eq_restricted_add_forbidden
        k z P]
      ring
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => ?_)
    ((summable_abs_kpSignedUnrootedCoeff ha hKP).add
      (summable_abs_kpSignedUnrootedCoeff ha
        (abstractKP_restrictedActivity P hKP)))
  rw [hforb k]
  exact abs_sub _ _

/-- **THE DIFFERENCE IDENTITY**: C_restricted − C_full is MINUS
    the absolutely convergent series of forbidden clusters. The
    vacuum that "disappeared" is no longer a metaphor. -/
theorem tsum_restricted_sub_full {z a : Polymer N → ℝ}
    (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (N := N) (fun η => |z η|) a)
    (P : Polymer N → Prop) :
    (∑' n, kpSignedUnrootedCoeff n (restrictedActivity z P))
        - ∑' n, kpSignedUnrootedCoeff (N := N) n z
      = - ∑' n, kpForbiddenUnrootedCoeff (N := N) n z P := by
  have hSfull : Summable
      (fun n => kpSignedUnrootedCoeff (N := N) n z) :=
    summable_kpSignedUnrootedCoeff ha hKP
  have hSrest : Summable
      (fun n => kpSignedUnrootedCoeff n
        (restrictedActivity z P)) :=
    summable_kpSignedUnrootedCoeff ha
      (abstractKP_restrictedActivity P hKP)
  rw [← tsum_sub hSrest hSfull,
    tsum_congr (fun k => by
      rw [kpSignedUnrootedCoeff_eq_restricted_add_forbidden
        k z P]
      ring
      : ∀ k : ℕ,
        kpSignedUnrootedCoeff k (restrictedActivity z P)
          - kpSignedUnrootedCoeff (N := N) k z
        = - kpForbiddenUnrootedCoeff (N := N) k z P),
    tsum_neg]

/-! ## A4.6 — THE A3 CAPSTONE REWRITTEN -/

/-- **CAPSTONE 50-A4**: each exponent of the A3 sum is an
    absolutely convergent series of CONNECTED clusters that hit
    the barrier (touch s, or clash with the core T). Localization
    without any metric — not yet exponential clustering. -/
theorem gibbsExpectation_eq_sum_core_mul_exp_neg_forbidden
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    gibbsExpectation (N := N) μm β χ f
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          typedMarkedCoreWeight μm β χ f T
            * Real.exp
                (- ∑' n, kpForbiddenUnrootedCoeff (N := N) n
                    (fun η => polymerWeight (N := N) μm β χ
                      η.val)
                    (remoteAllowed T s)) := by
  rw [gibbsExpectation_eq_sum_core_mul_exp μm hβ mχ hχabs
    hsmall hf mf hCf]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  congr 1
  congr 1
  exact tsum_restricted_sub_full
    (fun γ => Nat.cast_nonneg _)
    (abstractKP_of_beta_le_one_div_40000 μm hβ mχ hχabs hsmall)
    (remoteAllowed T s)

end LatticeGauge
