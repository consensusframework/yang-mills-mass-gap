/-
LatticeGauge/KPSmallness.lean — Phase 3, forty-sixth stone.

THE FINITE GEOMETRIC MAJORANT AND THE CONCRETE KOTECKÝ–PREISS
SMALLNESS HYPOTHESIS (architecture: Sol/GPT-5.6; execution: Fable).
The 44→45 chain is summed: the finite-volume rooted-link sum is
decomposed EXACTLY by polymer size (a disjoint union over
m ∈ range P — every polymer is nonempty and contained in the finite
plaquette universe), each size slice is normalized to 16·q·r^m with
  q := 2β·e^α   and   r := 4096·q   (4096 = 64², from the walk count;
the OTHER 64 below is 4·16 — links per plaquette times plaquettes per
link — numerically equal to the local degree by coincidence of this
library, not by identity), and the FINITE partial sum is majorized by
the volume-free geometric bound
  Σ_{m<P} r^m ≤ 1/(1−r)     (r < 1; (1−r)·Σ = 1−r^P ≤ 1; NO series,
no Summable, no HasSum, no limits — a uniform majorant of all finite
partial sums). Combining with the 45a gate:
  Σ_{D incompatible with C} |w_β(D)|·e^{α|D|} ≤ |C|·64q/(1−r),
and under the visible scalar condition 64q/(1−r) ≤ α this is the
KOTECKÝ–PREISS SMALLNESS HYPOTHESIS
  Σ_{D ≁ C} |w_β(D)|·e^{α|D|} ≤ α·|C|,
here VERIFIED — with the exact symbolic threshold for α = 1:
  β ≤ 1/(8320·e)  ⟹  q ≤ 1/4160, r ≤ 64/65, 64q ≤ 1/65, scalar ≤ 1,
and the rational specialization β ≤ 1/40000 (via exp 1 < 4, derived
from the library bound exp_one_lt_d9 — norm_num only does the
rational arithmetic afterwards, never a transcendental bound).

EPISTEMIC STATUS, mandatory. PROVED HERE: the finite size
decomposition; the volume-uniform geometric majorant; the abstract KP
inequality under the scalar condition; the exact α = 1 threshold; the
rational threshold 1/40000. NOT PROVED (next chapter): the abstract
Kotecký–Preiss THEOREM, absolute convergence of the cluster
expansion, identification with log realZ, non-vanishing of realZ,
thermodynamic limit, exponential clustering, mass gap. The correct
sentence is "the Kotecký–Preiss smallness hypothesis is verified";
the forbidden sentence is "the cluster expansion converges".
Sanity: β = 0 kills every term (stone 44); C = ∅ gives 0 ≤ 0; C need
not be a polymer (the polymer version is an interpretive corollary).
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.Gibbs
import LatticeGauge.Expectation
import LatticeGauge.Beta0
import LatticeGauge.PlaquetteActivity
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.ComponentFactorization
import LatticeGauge.PolymerGeometry
import LatticeGauge.PolymerGas
import LatticeGauge.PolymerActivityBound
import LatticeGauge.LinkCovering
import LatticeGauge.LocalGeometry
import LatticeGauge.PolymerWalkCount

open MeasureTheory
open scoped Classical

namespace LatticeGauge

/-! ## 4. The scalar variables (no N anywhere) -/

noncomputable def kpQ (β α : ℝ) : ℝ := 2 * β * Real.exp α

/-- 4096 = 64², from the doubled-walk count. -/
noncomputable def kpR (β α : ℝ) : ℝ := 4096 * kpQ β α

theorem kpQ_nonneg {β : ℝ} (hβ : 0 ≤ β) (α : ℝ) : 0 ≤ kpQ β α := by
  unfold kpQ
  positivity

theorem kpR_nonneg {β : ℝ} (hβ : 0 ≤ β) (α : ℝ) : 0 ≤ kpR β α := by
  unfold kpR
  have := kpQ_nonneg hβ α
  linarith

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 2. The disjoint size decomposition -/

theorem polymer_card_bounds {D : Finset (Site N × Dir × Dir)}
    (hD : D ∈ allPlaquettePolymers N) :
    1 ≤ D.card ∧ D.card ≤ (admissiblePlaquettes N).card := by
  unfold allPlaquettePolymers at hD
  rw [Finset.mem_filter, Finset.mem_powerset] at hD
  exact ⟨Finset.card_pos.mpr hD.2.1, Finset.card_le_card hD.1⟩

theorem polymersUsingLink_eq_biUnion (ℓ : Link N) :
    polymersUsingLink ℓ
      = (Finset.range (admissiblePlaquettes N).card).biUnion
          (fun m => rootedLinkPolymersOfSize ℓ m) := by
  ext D
  rw [Finset.mem_biUnion]
  constructor
  · intro hD
    have hall := (mem_polymersUsingLink.mp hD).1
    obtain ⟨h1, h2⟩ := polymer_card_bounds hall
    obtain ⟨m, hm⟩ : ∃ m, D.card = m + 1 := ⟨D.card - 1, by omega⟩
    exact ⟨m, Finset.mem_range.mpr (by omega),
      mem_rootedLinkPolymersOfSize.mpr ⟨hD, hm⟩⟩
  · rintro ⟨m, -, hD⟩
    exact (mem_rootedLinkPolymersOfSize.mp hD).1

theorem rootedLinkPolymersOfSize_pairwiseDisjoint (ℓ : Link N) :
    Set.PairwiseDisjoint
      (↑(Finset.range (admissiblePlaquettes N).card) : Set ℕ)
      (fun m => rootedLinkPolymersOfSize ℓ m) := by
  intro m₁ _ m₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro D h1 h2
  have e1 := (mem_rootedLinkPolymersOfSize.mp h1).2
  have e2 := (mem_rootedLinkPolymersOfSize.mp h2).2
  exact hne (by omega)

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## 3. Exact finite decomposition of the sum -/

theorem rootedLink_kp_sum_decompose
    (β : ℝ) (χ : G → ℝ) (α : ℝ) (ℓ : Link N) :
    (∑ D ∈ polymersUsingLink ℓ, kpActivityWeight μm β χ α D)
      = ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
          ∑ D ∈ rootedLinkPolymersOfSize ℓ m,
            kpActivityWeight μm β χ α D := by
  rw [polymersUsingLink_eq_biUnion ℓ]
  exact Finset.sum_biUnion (rootedLinkPolymersOfSize_pairwiseDisjoint ℓ)

/-! ## 5. Normalization of the slice bound to 16·q·r^m -/

private theorem normalize_slice (β α : ℝ) (m : ℕ) :
    ((16 * 64 ^ (2 * m) : ℕ) : ℝ)
        * ((2 * β) ^ (m + 1) * Real.exp (α * (m + 1)))
      = 16 * kpQ β α * kpR β α ^ m := by
  unfold kpQ kpR
  push_cast
  have h64 : ((64 : ℝ)) ^ (2 * m) = 4096 ^ m := by
    rw [pow_mul]
    norm_num
  have hexp : Real.exp (α * ((m : ℝ) + 1))
      = Real.exp α ^ m * Real.exp α := by
    rw [mul_add, mul_one, Real.exp_add, mul_comm α (m : ℝ),
      Real.exp_nat_mul]
  rw [h64, pow_succ, hexp, mul_pow, mul_pow]
  ring

theorem slice_bound_normalized
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (α : ℝ) (ℓ : Link N) (m : ℕ) :
    (∑ D ∈ rootedLinkPolymersOfSize ℓ m,
        kpActivityWeight μm β χ α D)
      ≤ 16 * kpQ β α * kpR β α ^ m := by
  have h := rootedLinkPolymers_kp_slice_le μm hβ mχ hχabs α ℓ m
  rwa [normalize_slice β α m] at h

/-! ## 7. The finite geometric majorant (no series, no limits) -/

theorem geom_sum_le_inv_one_sub {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1)
    (P : ℕ) :
    (∑ m ∈ Finset.range P, r ^ m) ≤ 1 / (1 - r) := by
  have hpos : 0 < 1 - r := by linarith
  have hkey : (∑ m ∈ Finset.range P, r ^ m) * (1 - r)
      = 1 - r ^ P := by
    calc (∑ m ∈ Finset.range P, r ^ m) * (1 - r)
        = -((∑ m ∈ Finset.range P, r ^ m) * (r - 1)) := by ring
      _ = -(r ^ P - 1) := by rw [geom_sum_mul]
      _ = 1 - r ^ P := by ring
  have hpow : 0 ≤ r ^ P := pow_nonneg h0 P
  have hle : (∑ m ∈ Finset.range P, r ^ m) * (1 - r) ≤ 1 := by
    rw [hkey]; linarith
  first
  | · rw [le_div_iff₀ hpos]
      exact hle
  | · rw [le_div_iff hpos]
      exact hle

/-! ## 8. Rooted-link bound, uniform in the volume -/

/-- The left sum is finite and volume-dependent; the right majorant
    contains no N. -/
theorem rootedLink_kp_sum_geometric_bound
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {α : ℝ}
    (hr : kpR β α < 1) (ℓ : Link N) :
    (∑ D ∈ polymersUsingLink ℓ, kpActivityWeight μm β χ α D)
      ≤ 16 * kpQ β α / (1 - kpR β α) := by
  rw [rootedLink_kp_sum_decompose μm β χ α ℓ]
  have hq0 : 0 ≤ 16 * kpQ β α := by
    have := kpQ_nonneg hβ α
    linarith
  calc (∑ m ∈ Finset.range (admissiblePlaquettes N).card,
        ∑ D ∈ rootedLinkPolymersOfSize ℓ m,
          kpActivityWeight μm β χ α D)
      ≤ ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
          16 * kpQ β α * kpR β α ^ m :=
        Finset.sum_le_sum (fun m _ =>
          slice_bound_normalized μm hβ mχ hχabs α ℓ m)
    _ = 16 * kpQ β α
          * ∑ m ∈ Finset.range (admissiblePlaquettes N).card,
              kpR β α ^ m := by
        rw [Finset.mul_sum]
    _ ≤ 16 * kpQ β α * (1 / (1 - kpR β α)) :=
        mul_le_mul_of_nonneg_left
          (geom_sum_le_inv_one_sub (kpR_nonneg hβ α) hr _) hq0
    _ = 16 * kpQ β α / (1 - kpR β α) := by ring

/-! ## 9. The incompatible-neighbourhood bound: 64 = 4·16 (links per
    plaquette × plaquettes per link — NOT the local degree, despite
    the numeric coincidence in this library) -/

theorem incompatible_kp_sum_geometric_bound
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) {α : ℝ}
    (hr : kpR β α < 1) (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C, kpActivityWeight μm β χ α D)
      ≤ (C.card : ℝ)
          * (64 * kpQ β α / (1 - kpR β α)) := by
  have hpos : 0 < 1 - kpR β α := by linarith
  have hB : 0 ≤ 16 * kpQ β α / (1 - kpR β α) := by
    have := kpQ_nonneg hβ α
    positivity
  have h := incompatible_kpActivity_sum_le_four_mul μm β χ α C hB
    (fun ℓ _ => rootedLink_kp_sum_geometric_bound μm hβ mχ hχabs hr ℓ)
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-! ## 11. THE ABSTRACT KP SMALLNESS HYPOTHESIS -/

/-- **THE KOTECKÝ–PREISS SMALLNESS HYPOTHESIS, VERIFIED under the
    visible scalar condition.** This is the inequality that appears
    as the HYPOTHESIS of the Kotecký–Preiss criterion; the abstract
    theorem that turns it into convergence of the cluster expansion
    is NOT yet formalized. C need not be a polymer. -/
theorem kp_hypothesis
    {β : ℝ} (hβ : 0 ≤ β) {α : ℝ} (hα : 0 ≤ α)
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hr : kpR β α < 1)
    (hscalar : 64 * kpQ β α / (1 - kpR β α) ≤ α)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp (α * D.card))
      ≤ α * C.card := by
  have h := incompatible_kp_sum_geometric_bound μm hβ mχ hχabs hr C
  unfold kpActivityWeight at h
  refine h.trans ?_
  calc (C.card : ℝ) * (64 * kpQ β α / (1 - kpR β α))
      ≤ (C.card : ℝ) * α :=
        mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg _)
    _ = α * C.card := mul_comm _ _

/-- Interpretive corollary for genuine polymers. -/
theorem kp_hypothesis_of_isPlaquettePolymer
    {β : ℝ} (hβ : 0 ≤ β) {α : ℝ} (hα : 0 ≤ α)
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hr : kpR β α < 1)
    (hscalar : 64 * kpQ β α / (1 - kpR β α) ≤ α)
    {C : Finset (Site N × Dir × Dir)} (_hC : IsPlaquettePolymer C) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp (α * D.card))
      ≤ α * C.card :=
  kp_hypothesis μm hβ hα mχ hχabs hr hscalar C

/-! ## 12. The exact symbolic threshold for α = 1 (no decimals:
    4096/4160 = 64/65) -/

theorem kp_smallness_alpha_one {β : ℝ} (hβ : 0 ≤ β)
    (hsmall : β ≤ 1 / (8320 * Real.exp 1)) :
    kpR β 1 < 1 ∧ 64 * kpQ β 1 / (1 - kpR β 1) ≤ 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hq : kpQ β 1 ≤ 1 / 4160 := by
    unfold kpQ
    have h1 : β * Real.exp 1
        ≤ (1 / (8320 * Real.exp 1)) * Real.exp 1 :=
      mul_le_mul_of_nonneg_right hsmall he.le
    have h2 : (1 / (8320 * Real.exp 1)) * Real.exp 1
        = 1 / 8320 := by
      field_simp
    rw [h2] at h1
    linarith
  have hq0 : 0 ≤ kpQ β 1 := kpQ_nonneg hβ 1
  have hrle : kpR β 1 ≤ 64 / 65 := by
    unfold kpR
    linarith
  refine ⟨by linarith, ?_⟩
  have hpos : 0 < 1 - kpR β 1 := by linarith
  rw [div_le_one hpos]
  unfold kpR
  linarith

/-- **The symbolic capstone**: β ≤ 1/(8320·e) verifies the KP
    hypothesis with a(C) = |C|. -/
theorem kp_hypothesis_alpha_one
    {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ 1 / (8320 * Real.exp 1))
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp (D.card : ℝ))
      ≤ C.card := by
  obtain ⟨hr, hs⟩ := kp_smallness_alpha_one hβ hsmall
  have h := kp_hypothesis μm hβ (by norm_num) mχ hχabs hr hs C
  simpa using h

/-! ## 13. The rational threshold β ≤ 1/40000 (exp 1 < 4 from the
    library decimal bound; norm_num only does rational arithmetic) -/

theorem exp_one_lt_four : Real.exp 1 < 4 := by
  have h := Real.exp_one_lt_d9
  norm_num at h
  linarith

/-- **The concrete rational capstone**: β ≤ 1/40000 verifies the KP
    smallness hypothesis. No optimality claimed anywhere. -/
theorem kp_hypothesis_beta_le_one_div_40000
    {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        |polymerWeight (N := N) μm β χ D|
          * Real.exp (D.card : ℝ))
      ≤ C.card := by
  refine kp_hypothesis_alpha_one μm hβ mχ hχabs ?_ C
  have he4 := exp_one_lt_four
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : 8320 * Real.exp 1 < 40000 := by nlinarith
  have h2 : (1 : ℝ) / 40000 ≤ 1 / (8320 * Real.exp 1) := by
    first
    | · rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        nlinarith
    | · rw [div_le_div_iff (by norm_num) (by positivity)]
        nlinarith
  linarith

/-! ## 15-16. Sanity -/

/-- β = 0: every incompatible term vanishes (stone 44 consumed). -/
theorem kp_sum_beta_zero
    {χ : G → ℝ} (mχ : Measurable χ) (hχabs : ∀ g : G, |χ g| ≤ 1)
    (α : ℝ) (C : Finset (Site N × Dir × Dir)) :
    (∑ D ∈ incompatiblePolymers C,
        kpActivityWeight μm 0 χ α D) = 0 := by
  refine Finset.sum_eq_zero ?_
  intro D hD
  have hall := (mem_incompatiblePolymers.mp hD).1
  have hne : D.Nonempty := by
    unfold allPlaquettePolymers at hall
    rw [Finset.mem_filter] at hall
    exact hall.2.1
  unfold kpActivityWeight
  rw [polymerWeight_zero_of_nonempty μm mχ hχabs hne, abs_zero,
    zero_mul]

/-- C = ∅: both sides vanish (45a emptiness consumed). -/
theorem kp_sum_empty_block (β : ℝ) (χ : G → ℝ) (α : ℝ) :
    (∑ D ∈ incompatiblePolymers
        (∅ : Finset (Site N × Dir × Dir)),
      kpActivityWeight μm β χ α D) = 0 := by
  rw [incompatiblePolymers_empty]
  exact Finset.sum_empty

end LatticeGauge
