/-
LatticeGauge/ObservableMayer.lean — PEDRA 50, Gate 50-A1: THE
MARKED NUMERATOR AND THE TOUCH/REMOTE CLASSIFICATION
(architecture: Sol/GPT-5.6; execution: Fable).

A1a: observableNumerator Z[f] := ∫ f·gibbsWeight and its exact
finite Mayer expansion — stone 32 with an f hanging in front (the
pointwise subset identity and the integrability pattern of stone
32 consumed, never reproved), then components via the stone-34
pointwise factorization. A1b: the touching/remote classification
of Mayer components relative to the observable support, the
partition lemmas, the algebraic split, and the COLLECTIVE REMOTE
FACTORIZATION (route B: Finset induction reusing the 50-A0 atom,
with the support of the remaining observable enlarged at each
step — dependsOnlyOn_mul_union and dependsOnlyOn_finsetProd are
the small support interface, both preexisting).

The A0 gatehouse becomes a collective machine: a component that
does not touch the observable does not merely leave — it leaves
with its weight factored out.

NOT here (A2+): division by realZ, realZ_eq_exp_tsum_unrooted,
covariance, numerator/denominator cancellation, reindexing by
Polymer, Ursell, KP, distance, exponential decay.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PlaquetteActivity
import LatticeGauge.ComponentFactorization
import LatticeGauge.ObservableBlockFactorization

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A1a — the marked numerator and its Mayer expansion -/

/-- The inserted numerator Z[f] — no division anywhere. -/
noncomputable def observableNumerator (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) : ℝ :=
  ∫ U : Config N G, f U * gibbsWeight β χ U ∂(configMeasure μm N)

/-- **The marked Mayer expansion** — stone 32 with f in front. -/
theorem observableNumerator_eq_sum {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    observableNumerator μm β χ f
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∫ U : Config N G,
            f U * ∏ p ∈ A, plaquetteActivity β χ U p
              ∂(configMeasure μm N) := by
  have hCf0 : 0 ≤ Cf := (abs_nonneg _).trans (hCf (fun _ => 1))
  have hprodbound : ∀ (A : Finset (Site N × Dir × Dir))
      (U : Config N G),
      |∏ p ∈ A, plaquetteActivity β χ U p|
        ≤ (2 * β) ^ A.card := by
    intro A U
    rw [Finset.abs_prod]
    calc ∏ p ∈ A, |plaquetteActivity β χ U p|
        ≤ ∏ _p ∈ A, (2 * β) :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _)
            (fun p _ => abs_plaquetteActivity_le hβ hχabs U p)
      _ = (2 * β) ^ A.card := Finset.prod_const _
  have hint : ∀ A ∈ (admissiblePlaquettes N).powerset,
      Integrable (fun U : Config N G =>
        f U * ∏ p ∈ A, plaquetteActivity β χ U p)
        (configMeasure μm N) := by
    intro A _
    refine (integrable_const (Cf * (2 * β) ^ A.card)).mono'
      ?_ ?_
    · exact (mf.mul
        (measurable_blockActivity β mχ A)).aestronglyMeasurable
    · filter_upwards with U
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hCf U) (hprodbound A U)
        (abs_nonneg _) hCf0
  have hpt : (fun U : Config N G => f U * gibbsWeight β χ U)
      = fun U => ∑ A ∈ (admissiblePlaquettes N).powerset,
          f U * ∏ p ∈ A, plaquetteActivity β χ U p := by
    funext U
    rw [gibbsWeight_eq_sum_prod_activity β χ U, Finset.mul_sum]
  unfold observableNumerator
  rw [hpt, integral_finset_sum _ hint]

/-- The marked expansion in component form (stone 34 pointwise). -/
theorem observableNumerator_eq_sum_components {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    {f : Config N G → ℝ} (mf : Measurable f)
    {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    observableNumerator μm β χ f
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ∫ U : Config N G,
            f U * ∏ C ∈ componentFamily A,
              blockActivity β χ C U
              ∂(configMeasure μm N) := by
  rw [observableNumerator_eq_sum μm hβ mχ hχabs mf hCf]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  have hAsub := Finset.mem_powerset.mp hA
  congr 1
  funext U
  rw [prod_activity_eq_prod_blockActivity hAsub β χ U]

/-! ## A1b — the touching/remote classification -/

noncomputable def touchingComponents
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (componentFamily A).filter
    (fun C => blockTouchesSupport (N := N) C s)

noncomputable def remoteComponents
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  (componentFamily A).filter
    (fun C => ¬ blockTouchesSupport (N := N) C s)

theorem touchingComponents_union_remote
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    touchingComponents (N := N) A s ∪ remoteComponents A s
      = componentFamily A := by
  unfold touchingComponents remoteComponents
  exact Finset.filter_union_filter_neg_eq _ _

theorem disjoint_touchingComponents_remote
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    Disjoint (touchingComponents (N := N) A s)
      (remoteComponents A s) := by
  refine Finset.disjoint_left.mpr ?_
  intro C h1 h2
  exact (Finset.mem_filter.mp h2).2 (Finset.mem_filter.mp h1).2

/-- Algebraic split of the component product (pointwise). -/
theorem prod_components_eq_touch_mul_remote
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N))
    (β : ℝ) (χ : G → ℝ) (U : Config N G) :
    (∏ C ∈ componentFamily A, blockActivity β χ C U)
      = (∏ C ∈ touchingComponents (N := N) A s,
          blockActivity β χ C U)
        * ∏ C ∈ remoteComponents A s, blockActivity β χ C U := by
  unfold touchingComponents remoteComponents
  exact (Finset.prod_filter_mul_prod_filter_not
    (componentFamily A) _ _).symm

/-! ## A1b.3 — THE COLLECTIVE MACHINE (route B: induction over the
    remote family, the A0 atom applied with the support of the
    remaining observable enlarged at each step) -/

theorem integral_mul_prod_blockActivity_of_disjoint
    (β : ℝ) {χ : G → ℝ} (mχ : Measurable χ)
    {t : Set (Link N)} {g : Config N G → ℝ}
    (hg : DependsOnlyOn g t) (mg : Measurable g)
    (R : Finset (Finset (Site N × Dir × Dir)))
    (hRt : ∀ C ∈ R, Disjoint (blockLinkSupport (N := N) C) t)
    (hRR : ∀ C ∈ R, ∀ D ∈ R, C ≠ D →
      Disjoint (blockLinkSupport (N := N) C)
        (blockLinkSupport (N := N) D)) :
    ∫ U : Config N G, g U * ∏ C ∈ R, blockActivity β χ C U
        ∂(configMeasure μm N)
      = (∫ U : Config N G, g U ∂(configMeasure μm N))
        * ∏ C ∈ R, ∫ U : Config N G, blockActivity β χ C U
            ∂(configMeasure μm N) := by
  classical
  revert hRt hRR
  induction R using Finset.induction_on with
  | empty =>
    intro _ _
    simp
  | @insert C R' hCR' ih =>
    intro hRt hRR
    have hCt : Disjoint (blockLinkSupport (N := N) C) t :=
      hRt C (Finset.mem_insert_self C R')
    have hCD : ∀ D ∈ R',
        Disjoint (blockLinkSupport (N := N) C)
          (blockLinkSupport (N := N) D) :=
      fun D hD => hRR C (Finset.mem_insert_self _ _)
        D (Finset.mem_insert_of_mem hD)
        (fun h => hCR' (h ▸ hD))
    have hg' : DependsOnlyOn
        (fun U : Config N G =>
          g U * ∏ D ∈ R', blockActivity β χ D U)
        (t ∪ familySupport
          (fun D => blockLinkSupport (N := N) D) R') :=
      dependsOnlyOn_mul_union hg
        (dependsOnlyOn_finsetProd R' _ _
          (fun D _ => blockActivity_dependsOnlyOn β χ D))
    have hCt' : Disjoint (blockLinkSupport (N := N) C)
        (t ∪ familySupport
          (fun D => blockLinkSupport (N := N) D) R') := by
      rw [Set.disjoint_union_right]
      refine ⟨hCt, ?_⟩
      rw [Set.disjoint_left]
      intro x hx hxfam
      obtain ⟨D, hD, hxD⟩ := hxfam
      exact Set.disjoint_left.mp (hCD D hD) hx hxD
    have hgB : DependsOnlyOn
        (fun U : Config N G => blockActivity β χ C U)
        (t ∪ familySupport
          (fun D => blockLinkSupport (N := N) D) R')ᶜ :=
      dependsOnlyOn_mono (blockActivity_dependsOnlyOn β χ C)
        (fun x hx => Set.disjoint_left.mp hCt' hx)
    have hmeas : Measurable (fun U : Config N G =>
        g U * ∏ D ∈ R', blockActivity β χ D U) :=
      mg.mul (Finset.measurable_prod _
        (fun D _ => measurable_blockActivity β mχ D))
    have key := integral_mul_of_disjoint_support (N := N) μm
      (t ∪ familySupport
        (fun D => blockLinkSupport (N := N) D) R')
      hg' hgB hmeas (measurable_blockActivity β mχ C)
    have hre : (fun U : Config N G =>
        g U * ∏ D ∈ insert C R', blockActivity β χ D U)
        = fun U =>
            (g U * ∏ D ∈ R', blockActivity β χ D U)
              * blockActivity β χ C U := by
      funext U
      rw [Finset.prod_insert hCR']
      ring
    rw [hre, key,
      ih (fun D hD => hRt D (Finset.mem_insert_of_mem hD))
        (fun D hD E hE hne => hRR D
          (Finset.mem_insert_of_mem hD) E
          (Finset.mem_insert_of_mem hE) hne),
      Finset.prod_insert hCR']
    ring

/-- **CAPSTONE 50-A1**: the collective remote factorization —
    E₀[f · Π_all B_C] = E₀[f · Π_touch B_C] · Π_remote E₀[B_C].
    A component that does not touch the observable leaves the
    numerator with its weight factored out. -/
theorem observableNumerator_touch_remote_factorization
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    observableNumerator μm β χ f
      = ∑ A ∈ (admissiblePlaquettes N).powerset,
          ((∫ U : Config N G,
              f U * ∏ C ∈ touchingComponents (N := N) A s,
                blockActivity β χ C U ∂(configMeasure μm N))
            * ∏ C ∈ remoteComponents A s,
                ∫ U : Config N G, blockActivity β χ C U
                  ∂(configMeasure μm N)) := by
  rw [observableNumerator_eq_sum_components μm hβ mχ hχabs mf hCf]
  refine Finset.sum_congr rfl (fun A hA => ?_)
  have hAsub := Finset.mem_powerset.mp hA
  have hsplit : (fun U : Config N G =>
      f U * ∏ C ∈ componentFamily A, blockActivity β χ C U)
      = fun U =>
          (f U * ∏ C ∈ touchingComponents (N := N) A s,
            blockActivity β χ C U)
            * ∏ C ∈ remoteComponents A s,
                blockActivity β χ C U := by
    funext U
    rw [prod_components_eq_touch_mul_remote A s β χ U]
    ring
  rw [hsplit]
  refine integral_mul_prod_blockActivity_of_disjoint μm β mχ
    (dependsOnlyOn_mul_union hf
      (dependsOnlyOn_finsetProd _ _ _
        (fun C _ => blockActivity_dependsOnlyOn β χ C)))
    (mf.mul (Finset.measurable_prod _
      (fun C _ => measurable_blockActivity β mχ C)))
    (remoteComponents A s) ?_ ?_
  · intro C hC
    obtain ⟨hCfam, hCnot⟩ := Finset.mem_filter.mp hC
    rw [Set.disjoint_union_right]
    refine ⟨not_blockTouchesSupport_iff.mp hCnot, ?_⟩
    rw [Set.disjoint_left]
    intro x hx hxfam
    obtain ⟨D, hD, hxD⟩ := hxfam
    have hDfam := (Finset.mem_filter.mp hD).1
    have hne : C ≠ D := by
      rintro rfl
      exact hCnot (Finset.mem_filter.mp hD).2
    exact Set.disjoint_left.mp
      (componentFamily_blockLinkSupport_disjoint hAsub
        hCfam hDfam hne) hx hxD
  · intro C hC D hD hne
    exact componentFamily_blockLinkSupport_disjoint hAsub
      (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hne

end LatticeGauge
