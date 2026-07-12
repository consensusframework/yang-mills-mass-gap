/-
LatticeGauge/ThirdConnectedBeta0.lean — Phase 3, twenty-seventh stone.

VANISHING OF THE THIRD CONNECTED CORRELATION AT β = 0 UNDER
ONE-VS-BLOCK SEPARATION (architecture: Sol/GPT-5.6; execution: Fable).
The main theorem does NOT require pairwise disjointness: it suffices
that ONE observable's support is disjoint from the UNION of the other
two — f₂ and f₃ may remain correlated, and the connected cumulant
still cancels. Pairwise link-disjointness is a corollary. ORDER 3
ONLY: no claim about higher cumulants is made (that would require a
partition/Möbius formalization — a future stone). Conceptual credit:
stone 11 (binary product-state factorization), stone 25 (geometric
support API), stone 26 (finite-family factorization), stone 27
(connected-cumulant algebra and the one-vs-block theorem). LIMITS:
exact third connected correlation at β = 0; no β > 0 result; no
distance decay; no mass gap; no area law; no confinement; not a
nontrivial cluster expansion. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.WilsonLoop
import LatticeGauge.Beta0
import LatticeGauge.WilsonExpectation
import LatticeGauge.WilsonDisjointBeta0
import LatticeGauge.FiniteSupportFactorizationBeta0
import LatticeGauge.UnitaryChar
import LatticeGauge.HaarUnitary

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-- **B. A product of two observables depends only on the union of
    their supports.** -/
theorem dependsOnlyOn_mul_union [NeZero N]
    {f g : Config N G → ℝ} {s t : Set (Link N)}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g t) :
    DependsOnlyOn (fun U : Config N G => f U * g U) (s ∪ t) := by
  intro U V hUV
  show f U * g U = f V * g V
  have hfs : f U = f V := hf U V (by
    intro ℓ hℓ
    exact hUV ℓ (Or.inl hℓ))
  have hgt : g U = g V := hg U V (by
    intro ℓ hℓ
    exact hUV ℓ (Or.inr hℓ))
  rw [hfs, hgt]

section Measure

variable [MeasurableSpace G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **A. The third joint connected correlation (third cumulant)** of
    three observables. Not to be confused with
    `gibbsActionThirdCumulant`, the dynamical specialization
    κ_β(f,S,S) of stone 21. -/
noncomputable def gibbsThirdConnected [NeZero N] [Fintype (Site N)]
    (β : ℝ) (χ : G → ℝ) (f₁ f₂ f₃ : Config N G → ℝ) : ℝ :=
  gibbsExpectation (N := N) μm β χ (fun U => f₁ U * f₂ U * f₃ U)
    - gibbsExpectation (N := N) μm β χ f₁
      * gibbsExpectation (N := N) μm β χ (fun U => f₂ U * f₃ U)
    - gibbsExpectation (N := N) μm β χ f₂
      * gibbsExpectation (N := N) μm β χ (fun U => f₁ U * f₃ U)
    - gibbsExpectation (N := N) μm β χ f₃
      * gibbsExpectation (N := N) μm β χ (fun U => f₁ U * f₂ U)
    + 2 * gibbsExpectation (N := N) μm β χ f₁
      * gibbsExpectation (N := N) μm β χ f₂
      * gibbsExpectation (N := N) μm β χ f₃

/-- **C. Ergonomic binary wrapper of stone 11**: observables with
    disjoint supports factorize at β = 0. NOT a new probabilistic
    independence — just the stone-11 theorem with two named sets. -/
theorem gibbsExpectation_mul_zero_of_disjoint_sets [NeZero N]
    [Fintype (Site N)] (χ : G → ℝ)
    {f g : Config N G → ℝ} {s t : Set (Link N)}
    (hf : DependsOnlyOn f s) (hg : DependsOnlyOn g t)
    (mf : Measurable f) (mg : Measurable g)
    (hdisj : Disjoint s t) :
    gibbsExpectation (N := N) μm 0 χ (fun U => f U * g U)
      = gibbsExpectation (N := N) μm 0 χ f
        * gibbsExpectation (N := N) μm 0 χ g := by
  classical
  have ht : t ⊆ sᶜ := by
    intro ℓ hℓt
    simp only [Set.mem_compl_iff]
    intro hℓs
    exact Set.disjoint_left.1 hdisj hℓs hℓt
  have hgc : DependsOnlyOn g sᶜ := dependsOnlyOn_mono hg ht
  rw [gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ,
    gibbsExpectation_zero (N := N) μm χ]
  exact integral_mul_of_disjoint_support (N := N) μm s hf hgc mf mg

/-- **D. MAIN THEOREM (pedra 27): ONE-VS-BLOCK vanishing of the third
    connected correlation at β = 0.** If s₁ is disjoint from s₂ ∪ s₃,
    the third cumulant vanishes — even if f₂ and f₃ remain correlated.
    ⟨f₂f₃⟩ is deliberately NOT factorized: that is the strength of the
    one-vs-block statement. -/
theorem gibbsThirdConnected_zero_of_first_disjoint_union [NeZero N]
    [Fintype (Site N)] (χ : G → ℝ)
    {f₁ f₂ f₃ : Config N G → ℝ} {s₁ s₂ s₃ : Set (Link N)}
    (hf₁ : DependsOnlyOn f₁ s₁) (hf₂ : DependsOnlyOn f₂ s₂)
    (hf₃ : DependsOnlyOn f₃ s₃)
    (mf₁ : Measurable f₁) (mf₂ : Measurable f₂) (mf₃ : Measurable f₃)
    (hsep : Disjoint s₁ (s₂ ∪ s₃)) :
    gibbsThirdConnected (N := N) μm 0 χ f₁ f₂ f₃ = 0 := by
  classical
  have h12 : Disjoint s₁ s₂ := by
    refine Set.disjoint_left.2 ?_
    intro ℓ hℓ₁ hℓ₂
    exact Set.disjoint_left.1 hsep hℓ₁ (Or.inl hℓ₂)
  have h13 : Disjoint s₁ s₃ := by
    refine Set.disjoint_left.2 ?_
    intro ℓ hℓ₁ hℓ₃
    exact Set.disjoint_left.1 hsep hℓ₁ (Or.inr hℓ₃)
  have hf₂₃ : DependsOnlyOn (fun U : Config N G => f₂ U * f₃ U)
      (s₂ ∪ s₃) := dependsOnlyOn_mul_union hf₂ hf₃
  have mf₂₃ : Measurable (fun U : Config N G => f₂ U * f₃ U) :=
    mf₂.mul mf₃
  have h123 := gibbsExpectation_mul_zero_of_disjoint_sets (N := N) μm χ
    hf₁ hf₂₃ mf₁ mf₂₃ hsep
  have h12fac := gibbsExpectation_mul_zero_of_disjoint_sets (N := N)
    μm χ hf₁ hf₂ mf₁ mf₂ h12
  have h13fac := gibbsExpectation_mul_zero_of_disjoint_sets (N := N)
    μm χ hf₁ hf₃ mf₁ mf₃ h13
  unfold gibbsThirdConnected
  -- reassociar f₁*(f₂*f₃) para (f₁*f₂)*f₃ da definição
  have h123' : gibbsExpectation (N := N) μm 0 χ
      (fun U => f₁ U * f₂ U * f₃ U)
      = gibbsExpectation (N := N) μm 0 χ f₁
        * gibbsExpectation (N := N) μm 0 χ
            (fun U => f₂ U * f₃ U) := by
    simpa [mul_assoc] using h123
  rw [h123', h12fac, h13fac]
  ring

/-- **E. Corollary: pairwise link-disjoint supports.** The h23
    hypothesis only certifies the pairwise condition of the public
    API; mathematically the stronger one-vs-block theorem does not
    need it. -/
theorem gibbsThirdConnected_zero_of_pairwise_disjoint_support
    [NeZero N] [Fintype (Site N)] (χ : G → ℝ)
    {f₁ f₂ f₃ : Config N G → ℝ} {s₁ s₂ s₃ : Set (Link N)}
    (hf₁ : DependsOnlyOn f₁ s₁) (hf₂ : DependsOnlyOn f₂ s₂)
    (hf₃ : DependsOnlyOn f₃ s₃)
    (mf₁ : Measurable f₁) (mf₂ : Measurable f₂) (mf₃ : Measurable f₃)
    (h12 : Disjoint s₁ s₂) (h13 : Disjoint s₁ s₃)
    (_h23 : Disjoint s₂ s₃) :
    gibbsThirdConnected (N := N) μm 0 χ f₁ f₂ f₃ = 0 := by
  apply gibbsThirdConnected_zero_of_first_disjoint_union (N := N) μm χ
    hf₁ hf₂ hf₃ mf₁ mf₂ mf₃
  refine Set.disjoint_left.2 ?_
  intro ℓ hℓ₁ hℓ₂₃
  rcases hℓ₂₃ with hℓ₂ | hℓ₃
  · exact Set.disjoint_left.1 h12 hℓ₁ hℓ₂
  · exact Set.disjoint_left.1 h13 hℓ₁ hℓ₃

end Measure

/-! ## Wilson observables -/

section Wilson

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]
variable {χ : G → ℝ}

/-- **F1. One-vs-block for Wilson paths at β = 0.** -/
theorem gibbsThirdConnected_wilsonPaths_zero_of_first_separated
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (hsep : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂ ∪ pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂)
      (fun U => wilsonLoop χ U x₃ p₃) = 0 :=
  gibbsThirdConnected_zero_of_first_disjoint_union (N := N) μm χ
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₁ p₁)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₂ p₂)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₃ p₃)
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂)
    (measurable_wilsonLoop mχ x₃ p₃)
    hsep

/-- **F2. Pairwise-disjoint version for Wilson paths at β = 0.** -/
theorem gibbsThirdConnected_wilsonPaths_zero_of_pairwise_disjoint
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (h12 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂))
    (h13 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₃ p₃))
    (h23 : Disjoint (pathLinkSet (N := N) x₂ p₂)
      (pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂)
      (fun U => wilsonLoop χ U x₃ p₃) = 0 :=
  gibbsThirdConnected_zero_of_pairwise_disjoint_support (N := N) μm χ
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₁ p₁)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₂ p₂)
    (wilsonPath_dependsOnlyOn_pathLinkSet χ x₃ p₃)
    (measurable_wilsonLoop mχ x₁ p₁)
    (measurable_wilsonLoop mχ x₂ p₂)
    (measurable_wilsonLoop mχ x₃ p₃)
    h12 h13 h23

/-- **G1. Physical wrapper: one-vs-block for closed Wilson loops.** -/
theorem gibbsThirdConnected_wilsonLoops_zero_of_first_separated
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (_hp₃ : IsClosed x₃ p₃)
    (hsep : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂ ∪ pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂)
      (fun U => wilsonLoop χ U x₃ p₃) = 0 :=
  gibbsThirdConnected_wilsonPaths_zero_of_first_separated
    μm mχ x₁ x₂ x₃ p₁ p₂ p₃ hsep

/-- **G2. Physical wrapper: pairwise-disjoint closed Wilson loops.** -/
theorem gibbsThirdConnected_wilsonLoops_zero_of_pairwise_disjoint
    [NeZero N] [Fintype (Site N)] (mχ : Measurable χ)
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (_hp₃ : IsClosed x₃ p₃)
    (h12 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂))
    (h13 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₃ p₃))
    (h23 : Disjoint (pathLinkSet (N := N) x₂ p₂)
      (pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) μm 0 χ
      (fun U => wilsonLoop χ U x₁ p₁)
      (fun U => wilsonLoop χ U x₂ p₂)
      (fun U => wilsonLoop χ U x₃ p₃) = 0 :=
  gibbsThirdConnected_wilsonPaths_zero_of_pairwise_disjoint
    μm mχ x₁ x₂ x₃ p₁ p₂ p₃ h12 h13 h23

end Wilson

/-! ## Concrete corollaries on U(n) with Haar measure -/

/-- **H1. UNCONDITIONAL on U(n): one-vs-block vanishing of the third
    connected correlation of closed Wilson loops at β = 0.** -/
theorem gibbsThirdConnected_unitaryWilsonLoops_zero_of_first_separated
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (_hp₃ : IsClosed x₃ p₃)
    (hsep : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂ ∪ pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) (haarU n) 0 (uChar n)
      (fun U => wilsonLoop (uChar n) U x₁ p₁)
      (fun U => wilsonLoop (uChar n) U x₂ p₂)
      (fun U => wilsonLoop (uChar n) U x₃ p₃) = 0 :=
  gibbsThirdConnected_wilsonPaths_zero_of_first_separated
    (haarU n) (measurable_uChar n) x₁ x₂ x₃ p₁ p₂ p₃ hsep

/-- **H2. UNCONDITIONAL on U(n): pairwise-disjoint closed Wilson
    loops at β = 0.** -/
theorem gibbsThirdConnected_unitaryWilsonLoops_zero_of_pairwise_disjoint
    (n : ℕ) [NeZero n] {N : ℕ} [NeZero N] [Fintype (Site N)]
    (x₁ x₂ x₃ : Site N) (p₁ p₂ p₃ : List Step)
    (_hp₁ : IsClosed x₁ p₁) (_hp₂ : IsClosed x₂ p₂)
    (_hp₃ : IsClosed x₃ p₃)
    (h12 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₂ p₂))
    (h13 : Disjoint (pathLinkSet (N := N) x₁ p₁)
      (pathLinkSet (N := N) x₃ p₃))
    (h23 : Disjoint (pathLinkSet (N := N) x₂ p₂)
      (pathLinkSet (N := N) x₃ p₃)) :
    gibbsThirdConnected (N := N) (haarU n) 0 (uChar n)
      (fun U => wilsonLoop (uChar n) U x₁ p₁)
      (fun U => wilsonLoop (uChar n) U x₂ p₂)
      (fun U => wilsonLoop (uChar n) U x₃ p₃) = 0 :=
  gibbsThirdConnected_wilsonPaths_zero_of_pairwise_disjoint
    (haarU n) (measurable_uChar n) x₁ x₂ x₃ p₁ p₂ p₃ h12 h13 h23

end LatticeGauge
