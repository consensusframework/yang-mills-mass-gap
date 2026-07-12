/-
LatticeGauge/JointLawBeta0.lean — Phase 3, twenty-eighth stone.

MEASURE-LEVEL INDEPENDENCE AND JOINT LAW AT β = 0 (architecture:
Sol/GPT-5.6; execution: Fable). Stones 11/25/26 say certain products
of expectations factorize; THIS stone says the entire JOINT LAW is
the product of the marginal laws: observables with disjoint link
supports are independent in the official Mathlib sense (IndepFun),
and the pushforward of the pair equals the product of the pushforward
marginals — controlling ALL measurable events, not one chosen
integral. Executor's note: `indepFun_prod` does not exist in Mathlib
v4.15; the product-space step is proved locally in ten lines via
`indepFun_iff_measure_inter_preimage_eq_mul` + `Measure.prod_prod`
(same architecture: independence on the split space, pulled back).
Conceptual credit: stone 11 (binary expectation factorization),
stone 25 (Wilson geometric support API), stone 28 (measure-level
independence and joint-law formulation). LIMITS: exact probabilistic
independence under the β = 0 product state; link-disjoint supports;
paths may share vertices; no statement at β > 0; no
decay-with-distance claim; no mass gap; no area law; no confinement;
no nontrivial cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **B. Independence pulls back along a measure-preserving map.**
    Fully generic, reusable lemma. -/
theorem indepFun_comp_measurePreserving
    {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {ν : Measure Ω'}
    {T : Ω → Ω'} {X : Ω' → α} {Y : Ω' → β}
    (hT : MeasurePreserving T μ ν)
    (hXY : ProbabilityTheory.IndepFun X Y ν)
    (mX : Measurable X) (mY : Measurable Y) :
    ProbabilityTheory.IndepFun (X ∘ T) (Y ∘ T) μ := by
  rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  have hXA : MeasurableSet (X ⁻¹' A) := mX hA
  have hYB : MeasurableSet (Y ⁻¹' B) := mY hB
  have hset : (X ∘ T) ⁻¹' A ∩ (Y ∘ T) ⁻¹' B
      = T ⁻¹' (X ⁻¹' A ∩ Y ⁻¹' B) := by
    ext ω
    simp [Function.comp_def]
  calc μ ((X ∘ T) ⁻¹' A ∩ (Y ∘ T) ⁻¹' B)
      = μ (T ⁻¹' (X ⁻¹' A ∩ Y ⁻¹' B)) := by rw [hset]
    _ = ν (X ⁻¹' A ∩ Y ⁻¹' B) :=
        hT.measure_preimage (hXA.inter hYB).nullMeasurableSet
    _ = ν (X ⁻¹' A) * ν (Y ⁻¹' B) :=
        hXY.measure_inter_preimage_eq_mul A B hA hB
    _ = μ (T ⁻¹' (X ⁻¹' A)) * μ (T ⁻¹' (Y ⁻¹' B)) := by
        rw [hT.measure_preimage hXA.nullMeasurableSet,
          hT.measure_preimage hYB.nullMeasurableSet]
    _ = μ ((X ∘ T) ⁻¹' A) * μ ((Y ∘ T) ⁻¹' B) := by
        simp [Set.preimage_comp]

section Measure

variable [MeasurableSpace G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **A. The structural split of the configuration space**: the
    Mathlib theorem already used inside stone 11, now exposed as a
    named API — configMeasure decomposes as the product of the
    restrictions to a link set and its complement. -/
theorem measurePreserving_configSplit [NeZero N]
    (s : Set (Link N)) [DecidablePred (· ∈ s)] :
    MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : Link N => G) (· ∈ s))
      (configMeasure μm N)
      ((Measure.pi fun _ : {ℓ : Link N // ℓ ∈ s} => μm).prod
        (Measure.pi fun _ : {ℓ : Link N // ¬ ℓ ∈ s} => μm)) := by
  simpa [configMeasure] using
    (measurePreserving_piEquivPiSubtypeProd
      (μ := fun _ : Link N => μm) (· ∈ s))

/-- **C. Observables with complementary supports are INDEPENDENT** in
    the official Mathlib sense, under the β = 0 product state. -/
theorem indepFun_of_complementary_support [NeZero N]
    (s : Set (Link N))
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g sᶜ)
    (mf : Measurable f) (mg : Measurable g) :
    ProbabilityTheory.IndepFun f g (configMeasure μm N) := by
  classical
  set e := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : Link N => G) (· ∈ s) with he
  set F : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G) → ℝ :=
    fun y => f (fun ℓ => if h : ℓ ∈ s then y ⟨ℓ, h⟩ else 1) with hF
  set Gg : (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) → ℝ :=
    fun z => g (fun ℓ => if h : ℓ ∈ s then 1 else z ⟨ℓ, h⟩) with hG
  have hFmeas : Measurable F := by
    apply mf.comp
    apply measurable_pi_lambda
    intro ℓ
    by_cases h : ℓ ∈ s
    · simpa [h] using
        measurable_pi_apply (⟨ℓ, h⟩ : {ℓ : Link N // ℓ ∈ s})
    · simpa [h] using measurable_const
  have hGmeas : Measurable Gg := by
    apply mg.comp
    apply measurable_pi_lambda
    intro ℓ
    by_cases h : ℓ ∈ s
    · simpa [h] using measurable_const
    · simpa [h] using
        measurable_pi_apply (⟨ℓ, h⟩ : {ℓ : Link N // ¬ ℓ ∈ s})
  have hfF : ∀ U : Config N G, f U = F ((e U).1) := by
    intro U
    apply hf
    intro ℓ hℓ
    simp [he, hF, MeasurableEquiv.piEquivPiSubtypeProd, hℓ]
  have hgG : ∀ U : Config N G, g U = Gg ((e U).2) := by
    intro U
    apply hg
    intro ℓ hℓ
    simp only [Set.mem_compl_iff] at hℓ
    simp [he, hG, MeasurableEquiv.piEquivPiSubtypeProd, hℓ]
  -- independência no espaço já separado (prova local: indepFun_prod
  -- não existe na v4.15)
  have hProduct : ProbabilityTheory.IndepFun
      (fun w : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G)
        × (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) => F w.1)
      (fun w : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G)
        × (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) => Gg w.2)
      ((Measure.pi fun _ : {ℓ : Link N // ℓ ∈ s} => μm).prod
        (Measure.pi fun _ : {ℓ : Link N // ¬ ℓ ∈ s} => μm)) := by
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro A B hA hB
    have h1 : (fun w : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G)
        × (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) => F w.1) ⁻¹' A
        = (F ⁻¹' A) ×ˢ
          (Set.univ : Set (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G)) := by
      ext w
      simp [Set.mem_prod]
    have h2 : (fun w : (∀ _ : {ℓ : Link N // ℓ ∈ s}, G)
        × (∀ _ : {ℓ : Link N // ¬ ℓ ∈ s}, G) => Gg w.2) ⁻¹' B
        = (Set.univ : Set (∀ _ : {ℓ : Link N // ℓ ∈ s}, G))
          ×ˢ (Gg ⁻¹' B) := by
      ext w
      simp [Set.mem_prod]
    rw [h1, h2, Set.prod_inter_prod, Set.inter_univ, Set.univ_inter,
      Measure.prod_prod, Measure.prod_prod, Measure.prod_prod]
    simp [measure_univ]
  have hSplit := measurePreserving_configSplit (N := N) μm s
  have hPulled := indepFun_comp_measurePreserving hSplit hProduct
    (hFmeas.comp measurable_fst) (hGmeas.comp measurable_snd)
  exact hPulled.ae_eq
    (Filter.Eventually.of_forall fun U => (hfF U).symm)
    (Filter.Eventually.of_forall fun U => (hgG U).symm)

/-- **D. Observables with DISJOINT supports are independent** under
    the β = 0 product state. -/
theorem indepFun_of_disjoint_support [NeZero N]
    {s t : Set (Link N)} {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g t)
    (mf : Measurable f) (mg : Measurable g)
    (hdisj : Disjoint s t) :
    ProbabilityTheory.IndepFun f g (configMeasure μm N) := by
  classical
  have ht : t ⊆ sᶜ := by
    intro ℓ hℓt
    simp only [Set.mem_compl_iff]
    intro hℓs
    exact Set.disjoint_left.1 hdisj hℓs hℓt
  have hgc : DependsOnlyOn g sᶜ := dependsOnlyOn_mono hg ht
  exact indepFun_of_complementary_support (N := N) μm s hf hgc mf mg

/-- **E. THE JOINT LAW IS THE PRODUCT OF THE MARGINALS**: the
    pushforward of (f, g) equals (map f).prod (map g) — strictly
    stronger than moment factorization. Uses the official Mathlib
    equivalence; no Measure.ext reconstruction. -/
theorem map_pair_eq_prod_map_of_disjoint_support [NeZero N]
    {s t : Set (Link N)} {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g t)
    (mf : Measurable f) (mg : Measurable g)
    (hdisj : Disjoint s t) :
    Measure.map (fun U : Config N G => (f U, g U))
        (configMeasure μm N)
      = (Measure.map f (configMeasure μm N)).prod
          (Measure.map g (configMeasure μm N)) :=
  (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
    mf.aemeasurable mg.aemeasurable).1
    (indepFun_of_disjoint_support (N := N) μm hf hg mf mg hdisj)

/-- **F. Stone 11 recovered as a standard corollary of the new API**
    (demonstration only — does NOT replace stone 11). -/
theorem integral_mul_eq_mul_integral_of_disjoint_support_via_indepFun
    [NeZero N]
    {s t : Set (Link N)} {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g t)
    (mf : Measurable f) (mg : Measurable g)
    (hdisj : Disjoint s t)
    (hfInt : Integrable f (configMeasure μm N))
    (hgInt : Integrable g (configMeasure μm N)) :
    ∫ U : Config N G, f U * g U ∂(configMeasure μm N)
      = (∫ U : Config N G, f U ∂(configMeasure μm N))
        * ∫ U : Config N G, g U ∂(configMeasure μm N) := by
  have hind := indepFun_of_disjoint_support (N := N) μm hf hg mf mg hdisj
  have h := hind.integral_mul_of_integrable hfInt hgInt
  have hfg : (fun U : Config N G => f U * g U) = f * g := rfl
  rw [hfg]
  exact h

end Measure

/-! ## Wilson observables -/

section Wilson

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **G1. Link-disjoint Wilson paths are INDEPENDENT at β = 0.** -/
theorem indepFun_wilsonPaths_of_disjoint [NeZero N] (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    ProbabilityTheory.IndepFun
      (fun U : Config N G => wilsonLoop χ U x₁ p₁)
      (fun U : Config N G => wilsonLoop χ U x₂ p₂)
      (configMeasure μm N) :=
  indepFun_of_disjoint_support (N := N) μm
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₁ p₁)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₂ p₂)
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂) hdisj

/-- **G2. The joint law of two link-disjoint Wilson paths is the
    product of the marginal laws at β = 0.** -/
theorem map_pair_wilsonPaths_eq_prod_maps_of_disjoint [NeZero N]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    Measure.map (fun U : Config N G =>
        (wilsonLoop χ U x₁ p₁, wilsonLoop χ U x₂ p₂))
        (configMeasure μm N)
      = (Measure.map (fun U : Config N G => wilsonLoop χ U x₁ p₁)
            (configMeasure μm N)).prod
          (Measure.map (fun U : Config N G => wilsonLoop χ U x₂ p₂)
            (configMeasure μm N)) :=
  map_pair_eq_prod_map_of_disjoint_support (N := N) μm
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₁ p₁)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₂ p₂)
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂) hdisj

/-- **H1. Physical wrapper: closed link-disjoint Wilson loops are
    independent at β = 0.** -/
theorem indepFun_wilsonLoops_of_disjoint [NeZero N] (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    ProbabilityTheory.IndepFun
      (fun U : Config N G => wilsonLoop χ U x₁ p₁)
      (fun U : Config N G => wilsonLoop χ U x₂ p₂)
      (configMeasure μm N) :=
  indepFun_wilsonPaths_of_disjoint μm mχ x₁ x₂ p₁ p₂ hdisj

/-- **H2. Physical wrapper: joint law of closed link-disjoint Wilson
    loops at β = 0.** -/
theorem map_pair_wilsonLoops_eq_prod_maps_of_disjoint [NeZero N]
    (mχ : Measurable χ)
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    Measure.map (fun U : Config N G =>
        (wilsonLoop χ U x₁ p₁, wilsonLoop χ U x₂ p₂))
        (configMeasure μm N)
      = (Measure.map (fun U : Config N G => wilsonLoop χ U x₁ p₁)
            (configMeasure μm N)).prod
          (Measure.map (fun U : Config N G => wilsonLoop χ U x₂ p₂)
            (configMeasure μm N)) :=
  map_pair_wilsonPaths_eq_prod_maps_of_disjoint μm mχ x₁ x₂ p₁ p₂ hdisj

end Wilson

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **I1. UNCONDITIONAL on U(n): closed link-disjoint Wilson loops
    are independent at β = 0** — only structural conditions remain. -/
theorem indepFun_unitaryWilsonLoops_of_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    ProbabilityTheory.IndepFun
      (fun U : Config N (UG n) => wilsonLoop (uChar n) U x₁ p₁)
      (fun U : Config N (UG n) => wilsonLoop (uChar n) U x₂ p₂)
      (configMeasure (haarU n) N) :=
  indepFun_wilsonPaths_of_disjoint (haarU n) (measurable_uChar n)
    x₁ x₂ p₁ p₂ hdisj

/-- **I2. UNCONDITIONAL on U(n): the joint law of closed link-disjoint
    Wilson loops is the product of the marginals at β = 0.** -/
theorem map_pair_unitaryWilsonLoops_eq_prod_maps_of_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N]
    (x₁ x₂ : Site N) (p₁ p₂ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (hdisj : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂)) :
    Measure.map (fun U : Config N (UG n) =>
        (wilsonLoop (uChar n) U x₁ p₁, wilsonLoop (uChar n) U x₂ p₂))
        (configMeasure (haarU n) N)
      = (Measure.map
            (fun U : Config N (UG n) => wilsonLoop (uChar n) U x₁ p₁)
            (configMeasure (haarU n) N)).prod
          (Measure.map
            (fun U : Config N (UG n) => wilsonLoop (uChar n) U x₂ p₂)
            (configMeasure (haarU n) N)) :=
  map_pair_wilsonPaths_eq_prod_maps_of_disjoint (haarU n)
    (measurable_uChar n) x₁ x₂ p₁ p₂ hdisj

end LatticeGauge
