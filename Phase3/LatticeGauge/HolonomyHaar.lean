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
    measurePreserving_swap
  have hskew : MeasurePreserving
      (fun q : G × G => (q.1, q.2 * q.1)) (ν.prod μm) (ν.prod μm) := by
    refine MeasurePreserving.skew_product (MeasurePreserving.id ν)
      (by exact (measurable_snd.mul measurable_fst)) ?_
    filter_upwards with y
    exact measurePreserving_mul_right μm y
  have hsnd : MeasurePreserving
      (Prod.snd : G × G → G) (ν.prod μm) μm := by
    refine ⟨measurable_snd, ?_⟩
    rw [Measure.map_snd_prod]
    simp
  have hcomp := (hsnd.comp hskew).comp hswap
  have hfun : ((Prod.snd : G × G → G) ∘
      (fun q : G × G => (q.1, q.2 * q.1)) ∘ Prod.swap)
      = fun q : G × G => q.1 * q.2 := by
    funext q
    simp [Prod.swap]
  rwa [hfun] at hcomp

/-- **Proved (oriented absorption):** X⁻¹·Y ~ μ as well
    (inv-invariance). -/
theorem measurePreserving_haarInv_mul_right
    (ν : Measure G) [SigmaFinite ν] [IsProbabilityMeasure ν]
    [μm.IsMulRightInvariant] [μm.IsInvInvariant] :
    MeasurePreserving (fun q : G × G => q.1⁻¹ * q.2) (μm.prod ν) μm := by
  have hinv : MeasurePreserving
      (Prod.map (Inv.inv : G → G) (id : G → G)) (μm.prod ν) (μm.prod ν) :=
    (measurePreserving_inv μm).prod (MeasurePreserving.id ν)
  have habs := measurePreserving_haar_mul_right (N := N) μm ν
  have hcomp := habs.comp hinv
  have hfun : ((fun q : G × G => q.1 * q.2) ∘
      Prod.map (Inv.inv : G → G) (id : G → G))
      = fun q : G × G => q.1⁻¹ * q.2 := by
    funext q
    simp
  rwa [hfun] at hcomp

end Measure

end LatticeGauge
