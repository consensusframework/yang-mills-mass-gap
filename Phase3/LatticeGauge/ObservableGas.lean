/-
LatticeGauge/ObservableGas.lean — PEDRA 50, Gate 50-A2: THE
MARKED FINITE POLYMER GAS AND THE EXACT NORMALIZATION
(architecture: Sol/GPT-5.6; execution: Fable).

CONCEPTUAL RECORD (architect's correction, kept): A1 showed that
remote components FACTOR inside each term. That does NOT license
term-by-term cancellation against Z — the denominator sums over
DIFFERENT families. The true cancellation of disconnected
contributions belongs to the connected/Ursell/ratio level (A3+).
A2 is FINITE and EXACT: it organizes the marked numerator as a
sum over compatible polymer families (stone 36 bijection, marked
weight), transports it to the typed Polymer N universe (49C-I
machinery, via a GENERIC raw↔typed sum bridge), normalizes f = 1
back to the ordinary gas, and records the free ratio bridge
gibbsExpectation = marked gas / gas — a pure definitional
rewrite, nothing simplified, nothing cancelled.

A0: "didn't touch the observable? leave." A1: "and take your
factored weight with you." A2: "now everyone lines up in polymer
families, and here is exactly where you sit in the sum."

NOT here (A3+): global cancellation of remote factors, connected
marked Ursell coefficients, KP, absolute convergence, connector
clusters, distance, q^d, covariance, exponential clustering.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.KPTypedGas
import LatticeGauge.ObservableMayer

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A2a — families split and the integral↔weight bridge -/

noncomputable def touchingFamily
    (Γ : Finset (Finset (Site N × Dir × Dir)))
    (s : Set (Link N)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  Γ.filter (fun C => blockTouchesSupport (N := N) C s)

noncomputable def remoteFamily
    (Γ : Finset (Finset (Site N × Dir × Dir)))
    (s : Set (Link N)) :
    Finset (Finset (Site N × Dir × Dir)) :=
  Γ.filter (fun C => ¬ blockTouchesSupport (N := N) C s)

theorem touchingComponents_eq_touchingFamily
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    touchingComponents (N := N) A s
      = touchingFamily (componentFamily A) s := rfl

theorem remoteComponents_eq_remoteFamily
    (A : Finset (Site N × Dir × Dir)) (s : Set (Link N)) :
    remoteComponents (N := N) A s
      = remoteFamily (componentFamily A) s := rfl

/-- The stone-35 polymer weight IS the β=0 integral of the block
    activity (gibbsExpectation_zero consumed — the bridge that
    lets A1's remote factors be read as polymer weights). -/
theorem polymerWeight_eq_integral (β : ℝ) (χ : G → ℝ)
    (C : Finset (Site N × Dir × Dir)) :
    polymerWeight (N := N) μm β χ C
      = ∫ U : Config N G, blockActivity β χ C U
          ∂(configMeasure μm N) := by
  unfold polymerWeight
  exact gibbsExpectation_zero (N := N) μm χ _

/-! ## A2b — the marked family weight and the raw capstone -/

/-- The marked weight of a family: the observable integrates
    JOINTLY with its touching polymers; the remote polymers
    contribute their ordinary weights. -/
noncomputable def markedRawFamilyWeight (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N))
    (Γ : Finset (Finset (Site N × Dir × Dir))) : ℝ :=
  (∫ U : Config N G,
      f U * ∏ C ∈ touchingFamily (N := N) Γ s,
        blockActivity β χ C U ∂(configMeasure μm N))
    * ∏ C ∈ remoteFamily Γ s, polymerWeight (N := N) μm β χ C

/-- **CAPSTONE A2 (raw)**: the marked numerator as a sum over
    compatible polymer families — the stone-36 bijection with the
    marked weight riding along. -/
theorem observableNumerator_eq_sum_markedFamilies {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    observableNumerator μm β χ f
      = ∑ Γ ∈ compatiblePolymerFamilies N,
          markedRawFamilyWeight μm β χ f s Γ := by
  rw [observableNumerator_touch_remote_factorization μm hβ mχ
    hχabs hf mf hCf]
  refine Finset.sum_bij (fun A _ => componentFamily A)
    (fun A ha => componentFamily_mem_compatiblePolymerFamilies
      (Finset.mem_powerset.mp ha))
    (fun A₁ h₁ A₂ h₂ heq => componentFamily_inj
      (Finset.mem_powerset.mp h₁) (Finset.mem_powerset.mp h₂) heq)
    (fun Γ hΓ => ⟨polymerUnion Γ,
      Finset.mem_powerset.mpr (polymerUnion_subset_admissible
        (mem_compatiblePolymerFamilies.mp hΓ)),
      componentFamily_polymerUnion_eq
        (mem_compatiblePolymerFamilies.mp hΓ)⟩)
    (fun A ha => ?_)
  unfold markedRawFamilyWeight
  rw [← touchingComponents_eq_touchingFamily,
    ← remoteComponents_eq_remoteFamily]
  congr 1
  exact Finset.prod_congr rfl
    (fun C _ => (polymerWeight_eq_integral μm β χ C).symm)

/-! ## A2c — the generic raw↔typed bridge and the typed capstone -/

/-- **Generic bridge**: any weight functional of the raw family
    sums equally over the typed universe (the 49C-I bijection,
    once and for all — value condition definitional). -/
theorem sum_typed_eq_sum_raw
    (F : Finset (Finset (Site N × Dir × Dir)) → ℝ) :
    (∑ Γ ∈ typedCompatiblePolymerFamilies N, F (rawFamily Γ))
      = ∑ Γ ∈ compatiblePolymerFamilies N, F Γ := by
  refine Finset.sum_bij (fun Γ _ => rawFamily Γ) ?_ ?_ ?_ ?_
  · intro Γ hΓ
    exact mem_compatiblePolymerFamilies.mpr
      (isCompatible_rawFamily_iff.mpr
        (mem_typedCompatiblePolymerFamilies.mp hΓ))
  · intro Γ₁ _ Γ₂ _ h
    exact rawFamily_injective h
  · intro Γraw hraw
    have hcomp := mem_compatiblePolymerFamilies.mp hraw
    refine ⟨Γraw.attach.image (fun C =>
      (⟨C.val, mem_all_of_isPolymer
        (hcomp.1 C.val C.property)⟩ : Polymer N)), ?_, ?_⟩
    · refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ hθ hne
      obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hη
      obtain ⟨D, _, rfl⟩ := Finset.mem_image.mp hθ
      exact hcomp.2 C.val C.property D.val D.property
        (fun h => hne (Subtype.ext h))
    · show Finset.image Subtype.val
        (Γraw.attach.image (fun C =>
          (⟨C.val, mem_all_of_isPolymer
            (hcomp.1 C.val C.property)⟩ : Polymer N))) = Γraw
      rw [Finset.image_image]
      exact Finset.attach_image_val
  · intro Γ _
    rfl

/-- The marked gas over the typed polymer universe. -/
noncomputable def typedMarkedPolymerGas (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) : ℝ :=
  ∑ Γ ∈ typedCompatiblePolymerFamilies N,
    markedRawFamilyWeight μm β χ f s (rawFamily Γ)

/-- **CAPSTONE A2 (typed)**: Z[f] = typed marked polymer gas. -/
theorem observableNumerator_eq_typedMarkedGas {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    observableNumerator μm β χ f
      = typedMarkedPolymerGas μm β χ f s := by
  rw [observableNumerator_eq_sum_markedFamilies μm hβ mχ hχabs
    hf mf hCf,
    ← sum_typed_eq_sum_raw
      (fun Γ => markedRawFamilyWeight μm β χ f s Γ)]
  rfl

/-! ## A2d — normalization: f = 1 recovers the ordinary gas -/

theorem not_blockTouchesSupport_empty
    (C : Finset (Site N × Dir × Dir)) :
    ¬ blockTouchesSupport (N := N) C (∅ : Set (Link N)) := by
  unfold blockTouchesSupport
  simp

theorem markedRawFamilyWeight_one_empty (β : ℝ) (χ : G → ℝ)
    (Γ : Finset (Finset (Site N × Dir × Dir))) :
    markedRawFamilyWeight μm β χ (fun _ => 1)
        (∅ : Set (Link N)) Γ
      = ∏ C ∈ Γ, polymerWeight (N := N) μm β χ C := by
  unfold markedRawFamilyWeight touchingFamily remoteFamily
  rw [Finset.filter_false_of_mem
      (fun C _ => not_blockTouchesSupport_empty C),
    Finset.filter_true_of_mem
      (fun C _ => not_blockTouchesSupport_empty C)]
  simp

/-- **Normalization**: with f = 1 and empty support the typed
    marked gas IS the ordinary typed polymer gas. -/
theorem typedMarkedPolymerGas_one_empty (β : ℝ) (χ : G → ℝ) :
    typedMarkedPolymerGas μm β χ (fun _ => 1)
        (∅ : Set (Link N))
      = typedPolymerGas (N := N)
          (fun η => polymerWeight (N := N) μm β χ η.val) := by
  unfold typedMarkedPolymerGas typedPolymerGas
  refine Finset.sum_congr rfl (fun Γ _ => ?_)
  rw [markedRawFamilyWeight_one_empty]
  unfold rawFamily
  exact Finset.prod_image
    (fun a _ b _ h => Subtype.val_injective h)

/-! ## A2c.1 — the ratio bridge (free: rfl + two rw; nothing
    simplified, nothing cancelled) -/

theorem gibbsExpectation_eq_observableNumerator_div
    (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ) :
    gibbsExpectation (N := N) μm β χ f
      = observableNumerator μm β χ f
        / realZ (N := N) μm β χ := rfl

/-- **The exact normalized form**: ⟨f⟩ = marked gas / gas — a
    definitional rewrite only. The division is NOT simplified;
    remote families are NOT cancelled; no exp, no log, no KP. -/
theorem gibbsExpectation_eq_markedGas_div_gas {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {s : Set (Link N)}
    {f : Config N G → ℝ} (hf : DependsOnlyOn f s)
    (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf) :
    gibbsExpectation (N := N) μm β χ f
      = typedMarkedPolymerGas μm β χ f s
        / typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val) := by
  rw [gibbsExpectation_eq_observableNumerator_div,
    observableNumerator_eq_typedMarkedGas μm hβ mχ hχabs
      hf mf hCf,
    realZ_eq_typed_polymer_gas μm hβ mχ hχabs]

end LatticeGauge
