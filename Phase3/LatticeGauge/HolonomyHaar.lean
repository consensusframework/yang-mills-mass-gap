/-
LatticeGauge/HolonomyHaar.lean — Phase 3, fifteenth stone.

THE FRESH-LINK STONE (architecture: Sol/GPT-5.6; execution: Fable):
if the FIRST link of a path does not reappear in its tail, the holonomy
is Haar-distributed — one genuinely independent Haar factor erases the
memory of the entire tail. No probabilistic induction. The Nodup case
is a corollary. Requires Nonempty path (empty holonomy is Dirac at 1),
right-invariance and inv-invariance only. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.WilsonLoop
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.SingleLink

open MeasureTheory

namespace LatticeGauge

variable {N : ℕ} {G : Type*} [Group G]

/-! ## Bloco 1: suporte combinatório -/

/-- The link consumed by one step. -/
def stepLink [NeZero N] (x : Site N) : Step → Link N
  | (μ, true) => (x, μ)
  | (μ, false) => (shiftBack x μ, μ)

/-- The site reached after one step. -/
def stepNext [NeZero N] (x : Site N) : Step → Site N
  | (μ, true) => shift x μ
  | (μ, false) => shiftBack x μ

/-- The links visited by a path. -/
def pathLinks [NeZero N] (x : Site N) : List Step → List (Link N)
  | [] => []
  | s :: p => stepLink x s :: pathLinks (stepNext x s) p

/-- **Proved:** the holonomy depends only on the visited links. -/
theorem holonomy_congr_on_pathLinks [NeZero N] (p : List Step) :
    ∀ (x : Site N) (U V : Config N G),
      (∀ ℓ ∈ pathLinks x p, U ℓ = V ℓ) →
      holonomy U x p = holonomy V x p := by
  induction p with
  | nil => intro x U V _; simp [holonomy]
  | cons s p ih =>
    intro x U V h
    obtain ⟨μ, b⟩ := s
    have hhead := h (stepLink x (μ, b)) (by simp [pathLinks])
    have htail : ∀ ℓ ∈ pathLinks (stepNext x (μ, b)) p, U ℓ = V ℓ :=
      fun ℓ hℓ => h ℓ (by simp [pathLinks]; exact Or.inr hℓ)
    cases b
    · simp only [holonomy]
      rw [show U (shiftBack x μ, μ) = V (shiftBack x μ, μ) by
          simpa [stepLink] using hhead,
        ih _ _ _ (by simpa [stepNext] using htail)]
    · simp only [holonomy]
      rw [show U (x, μ) = V (x, μ) by simpa [stepLink] using hhead,
        ih _ _ _ (by simpa [stepNext] using htail)]

section Measure

variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## Bloco 2: absorvedores Haar -/

/-- **Proved (Haar absorption):** if X ~ μ (right-invariant) and Y ~ ν
    independent, then X·Y ~ μ. Route: swap → skew_product → snd. -/
theorem measurePreserving_haar_mul_right
    (ν : Measure G) [SigmaFinite ν] [IsProbabilityMeasure ν]
    [μm.IsMulRightInvariant] :
    MeasurePreserving (fun q : G × G => q.1 * q.2) (μm.prod ν) μm := by
  have hswap : MeasurePreserving Prod.swap (μm.prod ν) (ν.prod μm) :=
    ⟨measurable_swap, Measure.prod_swap⟩
  have hskew : MeasurePreserving
      (fun q : G × G => (q.1, q.2 * q.1)) (ν.prod μm) (ν.prod μm) := by
    have h := MeasurePreserving.skew_product (g := fun y x => x * y)
      (MeasurePreserving.id ν)
      (measurable_snd.mul measurable_fst)
      (Filter.Eventually.of_forall fun y =>
        (measurePreserving_mul_right μm y).map_eq)
    simpa using h
  have hsnd : MeasurePreserving
      (Prod.snd : G × G → G) (ν.prod μm) μm := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hcomp := (hsnd.comp hskew).comp hswap
  refine ⟨measurable_fst.mul measurable_snd, ?_⟩
  calc Measure.map (fun q : G × G => q.1 * q.2) (μm.prod ν)
      = Measure.map ((Prod.snd ∘ fun q : G × G => (q.1, q.2 * q.1))
          ∘ Prod.swap) (μm.prod ν) := by
        congr 1
    _ = μm := hcomp.map_eq

/-- **Proved (oriented absorption):** X⁻¹·Y ~ μ as well
    (inv-invariance). -/
theorem measurePreserving_haarInv_mul_right
    (ν : Measure G) [SigmaFinite ν] [IsProbabilityMeasure ν]
    [μm.IsMulRightInvariant] [μm.IsInvInvariant] :
    MeasurePreserving (fun q : G × G => q.1⁻¹ * q.2) (μm.prod ν) μm := by
  have hinvmp : MeasurePreserving (Inv.inv : G → G) μm μm :=
    ⟨measurable_inv, Measure.map_inv_eq_self μm⟩
  have hinv : MeasurePreserving
      (Prod.map (Inv.inv : G → G) (id : G → G)) (μm.prod ν) (μm.prod ν) :=
    hinvmp.prod (MeasurePreserving.id ν)
  have habs := measurePreserving_haar_mul_right μm ν
  have hcomp := habs.comp hinv
  refine ⟨measurable_fst.inv.mul measurable_snd, ?_⟩
  calc Measure.map (fun q : G × G => q.1⁻¹ * q.2) (μm.prod ν)
      = Measure.map ((fun q : G × G => q.1 * q.2)
          ∘ Prod.map (Inv.inv : G → G) (id : G → G)) (μm.prod ν) := by
        congr 1
    _ = μm := hcomp.map_eq

/-! ## Bloco 3: separação da configuração e o teorema do link fresco -/

variable [NeZero N]

/-- Fill the distinguished link with 1, keep the rest. -/
def extendOne (ℓ₀ : Link N)
    (z : ∀ _ : {a : Link N // ¬ a = ℓ₀}, G) : Config N G :=
  fun a => if h : a = ℓ₀ then 1 else z ⟨a, h⟩

/-- **Proved (evaluation marginal, singleton predicate):** evaluating
    the distinguished coordinate is measure preserving. -/
theorem measurePreserving_evalSingleton (ℓ₀ : Link N) :
    MeasurePreserving
      (fun y : ∀ _ : {a : Link N // a = ℓ₀}, G => y ⟨ℓ₀, rfl⟩)
      (Measure.pi fun _ : {a : Link N // a = ℓ₀} => μm) μm := by
  classical
  refine ⟨measurable_pi_apply _, ?_⟩
  ext t ht
  rw [Measure.map_apply (measurable_pi_apply _) ht]
  change Measure.pi (fun _ : {a : Link N // a = ℓ₀} => μm)
    ((Function.eval ⟨ℓ₀, rfl⟩) ⁻¹' t) = μm t
  rw [Set.eval_preimage, Measure.pi_pi]
  rw [Fintype.prod_eq_single (⟨ℓ₀, rfl⟩ : {a : Link N // a = ℓ₀})
    (fun j hj => absurd (Subtype.ext j.2) hj)]
  simp

/-- **Proved: THE FRESH-LINK THEOREM.** If the first link of the path
    does not reappear in the tail, the holonomy is Haar — regardless of
    what the tail does. -/
theorem measurePreserving_holonomy_of_fresh_head
    [μm.IsMulRightInvariant] [μm.IsInvInvariant]
    (x : Site N) (st : Step) (p : List Step)
    (hfresh : stepLink x st ∉ pathLinks (stepNext x st) p) :
    MeasurePreserving
      (fun U : Config N G => holonomy U x (st :: p))
      (configMeasure μm N) μm := by
  classical
  set ℓ₀ : Link N := stepLink x st with hℓ₀
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (μ := fun _ : Link N => μm) (fun a : Link N => a = ℓ₀)
  have h_eval := measurePreserving_evalSingleton (N := N) μm ℓ₀
  have htailmeas : Measurable
      (fun z : ∀ _ : {a : Link N // ¬ a = ℓ₀}, G =>
        holonomy (extendOne ℓ₀ z) (stepNext x st) p) := by
    apply (measurable_holonomy p (stepNext x st)).comp
    apply measurable_pi_lambda
    intro a
    by_cases h : a = ℓ₀
    · simp only [extendOne, dif_pos h]
      exact measurable_const
    · simp only [extendOne, dif_neg h]
      exact measurable_pi_apply _
  set ν : Measure G := Measure.map
    (fun z : ∀ _ : {a : Link N // ¬ a = ℓ₀}, G =>
      holonomy (extendOne ℓ₀ z) (stepNext x st) p)
    (Measure.pi fun _ : {a : Link N // ¬ a = ℓ₀} => μm) with hν
  haveI : IsProbabilityMeasure ν := by
    constructor
    rw [hν, Measure.map_apply htailmeas MeasurableSet.univ]
    simp
  haveI : SigmaFinite ν := inferInstance
  have h_tail : MeasurePreserving
      (fun z : ∀ _ : {a : Link N // ¬ a = ℓ₀}, G =>
        holonomy (extendOne ℓ₀ z) (stepNext x st) p)
      (Measure.pi fun _ : {a : Link N // ¬ a = ℓ₀} => μm) ν :=
    ⟨htailmeas, hν.symm⟩
  have hpair : MeasurePreserving
      ((Prod.map
        (fun y : ∀ _ : {a : Link N // a = ℓ₀}, G => y ⟨ℓ₀, rfl⟩)
        (fun z : ∀ _ : {a : Link N // ¬ a = ℓ₀}, G =>
          holonomy (extendOne ℓ₀ z) (stepNext x st) p)) ∘
        ⇑(MeasurableEquiv.piEquivPiSubtypeProd
          (fun _ : Link N => G) (fun a : Link N => a = ℓ₀)))
      (configMeasure μm N) (μm.prod ν) := by
    refine (h_eval.prod h_tail).comp ?_
    convert hsplit using 3
    all_goals exact Subsingleton.elim _ _
  -- a cauda da configuração original coincide com a cauda preenchida
  have htail_eq : ∀ U : Config N G,
      holonomy U (stepNext x st) p
        = holonomy (extendOne ℓ₀ (fun a => U a.1)) (stepNext x st) p := by
    intro U
    apply holonomy_congr_on_pathLinks
    intro ℓ hℓ
    have hne : ¬ ℓ = ℓ₀ := fun he => hfresh (he ▸ hℓ)
    simp [extendOne, dif_neg hne]
  -- montar o mapa final conforme a orientação do passo
  obtain ⟨μdir, b⟩ := st
  cases b
  · -- passo para trás: (U ℓ₀)⁻¹ * cauda
    have habs := measurePreserving_haarInv_mul_right μm ν
    have hfn : (fun U : Config N G => holonomy U x ((μdir, false) :: p))
        = (fun q : G × G => q.1⁻¹ * q.2) ∘
          ((fun w => (w.1 ⟨ℓ₀, rfl⟩,
            holonomy (extendOne ℓ₀ w.2) (stepNext x (μdir, false)) p)) ∘
            (MeasurableEquiv.piEquivPiSubtypeProd
              (fun _ : Link N => G) (fun a : Link N => a = ℓ₀))) := by
      funext U
      show holonomy U x ((μdir, false) :: p)
          = (U ℓ₀)⁻¹ * holonomy (extendOne ℓ₀ (fun a => U a.1))
              (stepNext x (μdir, false)) p
      rw [← htail_eq U]
      simp [holonomy, hℓ₀, stepLink, stepNext]
    rw [hfn] at *
    exact habs.comp hpair
  · -- passo para frente: (U ℓ₀) * cauda
    have habs := measurePreserving_haar_mul_right μm ν
    have hfn : (fun U : Config N G => holonomy U x ((μdir, true) :: p))
        = (fun q : G × G => q.1 * q.2) ∘
          ((fun w => (w.1 ⟨ℓ₀, rfl⟩,
            holonomy (extendOne ℓ₀ w.2) (stepNext x (μdir, true)) p)) ∘
            (MeasurableEquiv.piEquivPiSubtypeProd
              (fun _ : Link N => G) (fun a : Link N => a = ℓ₀))) := by
      funext U
      show holonomy U x ((μdir, true) :: p)
          = (U ℓ₀) * holonomy (extendOne ℓ₀ (fun a => U a.1))
              (stepNext x (μdir, true)) p
      rw [← htail_eq U]
      simp [holonomy, hℓ₀, stepLink, stepNext]
    rw [hfn] at *
    exact habs.comp hpair

/-- **CAPSTONE (pedra 15): holonomies of Nodup nonempty paths are
    Haar-distributed.** -/
theorem measurePreserving_holonomy_of_nodup
    [μm.IsMulRightInvariant] [μm.IsInvInvariant]
    (x : Site N) (p : List Step)
    (hp : p ≠ []) (hnd : (pathLinks x p).Nodup) :
    MeasurePreserving
      (fun U : Config N G => holonomy U x p)
      (configMeasure μm N) μm := by
  cases p with
  | nil => exact absurd rfl hp
  | cons s p =>
    have hfresh : stepLink x s ∉ pathLinks (stepNext x s) p := by
      have := hnd
      simp only [pathLinks, List.nodup_cons] at this
      exact this.1
    exact measurePreserving_holonomy_of_fresh_head μm x s p hfresh

/-! ## Pedra 16: a expectativa do Wilson loop em β = 0 -/

/-- **CAPSTONE (pedra 16): ⟨Wilson loop⟩₀ = ∫ χ dμ.** At infinite
    temperature, the expectation of any Wilson loop along a nonempty
    non-self-repeating path equals the single character integral —
    the first closed formula for a physical observable in this
    repository. Direct corollary of the fresh-link theorem (15) and
    the β = 0 Gibbs state (11). -/
theorem gibbsExpectation_wilsonLoop_zero
    [Fintype (Site N)]
    [μm.IsMulRightInvariant] [μm.IsInvInvariant]
    {χ : G → ℝ} (mχ : Measurable χ)
    (x : Site N) (p : List Step)
    (hp : p ≠ []) (hnd : (pathLinks x p).Nodup) :
    gibbsExpectation (N := N) μm 0 χ (fun U => wilsonLoop χ U x p)
      = linkCharacterIntegral μm χ := by
  rw [gibbsExpectation_zero (N := N) μm χ]
  have hmp := measurePreserving_holonomy_of_nodup (N := N) μm x p hp hnd
  unfold wilsonLoop linkCharacterIntegral
  calc ∫ U : Config N G, χ (holonomy U x p) ∂(configMeasure μm N)
      = ∫ g, χ g ∂(Measure.map (fun U : Config N G => holonomy U x p)
          (configMeasure μm N)) :=
        (integral_map (measurable_holonomy p x).aemeasurable
          mχ.aestronglyMeasurable).symm
    _ = ∫ g, χ g ∂μm := by rw [hmp.map_eq]

end Measure

end LatticeGauge
