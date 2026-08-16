/-
LatticeGauge/KPGasCoefficients.lean — stone 49C-II: GAS
COEFFICIENTS Aₙ (architecture: Sol/GPT-5.6; execution: Fable).

The typed hard-core gas of 49C-I is decomposed exactly into
labelled-tuple coefficients built ON THE GRAPH SIDE, as the
architect ordered: graphAllEdgeCoeff sums (−1)^|E| over ALL edge
subsets of the SAME ambient (availableEdges G).powerset whose
connected filter defines the Ursell coefficient (Stone 37) — so
Aₙ and Bₙ live in one universe, ready for the root-component
split. The Stone-37 inclusion–exclusion key
sum_powerset_neg_one_pow_card is consumed to collapse the all-edge
sum to the compatibility indicator; a polymer is never compatible
with itself (nonempty link support), hence a pairwise-compatible
tuple is INJECTIVE, and the n! of enumerations cancels the 1/n!
of Aₙ exactly (audited fiber count, no set partitions).
PRECISION (recorded on the architect's order): repetitions
annihilate only on the Aₙ side, AFTER the cancellation; the Ursell
universe of Bₙ keeps repeated occurrences by design since Stone 37
— the graph distinguishes indices even when the polymer repeats.
CAPSTONE: typedPolymerGas z = Σ_{n ≤ card(Polymer N)} Aₙ(z), a
FINITE identity. NOT here (49C-III+): Real.exp, Real.log,
logPartition, KP smallness, β ≤ 1/40000, Summable/tsum of B,
cluster-expansion identity, positivity from clusters. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.PolymerGeometry
import LatticeGauge.PlaquetteConnectivity
import LatticeGauge.PolymerGas
import LatticeGauge.UrsellCoefficients
import LatticeGauge.KPTypedGas

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 49C-II.1 — the all-edge coefficient and the Stone-37 key -/

/-- The ALL-graph analogue of `graphUrsellCoeff`: the signed sum
    over EVERY edge subset of the same ambient whose connected
    filter defines the Ursell coefficient. -/
noncomputable def graphAllEdgeCoeff {n : ℕ}
    (G : SimpleGraph (Fin n)) : ℤ :=
  ∑ E ∈ (availableEdges G).powerset, (-1 : ℤ) ^ E.card

/-- **The Stone-37 key consumed**: the all-edge sum collapses to
    the indicator of "no available edges". -/
theorem graphAllEdgeCoeff_eq_ite {n : ℕ} (G : SimpleGraph (Fin n)) :
    graphAllEdgeCoeff G
      = if availableEdges G = ∅ then 1 else 0 :=
  sum_powerset_neg_one_pow_card (availableEdges G)

/-! ## 49C-II.2 — self-incompatibility and injectivity -/

/-- A nonempty plaquette block has nonempty link support (its
    first plaquette already contributes a link). -/
theorem blockLinkSupport_nonempty
    {C : Finset (Site N × Dir × Dir)} (hC : C.Nonempty) :
    (blockLinkSupport (N := N) C).Nonempty := by
  obtain ⟨p, hp⟩ := hC
  refine ⟨(p.1, p.2.1), ?_⟩
  unfold blockLinkSupport familySupport
  exact ⟨p, hp, by simp [plaqLinkSet]⟩

/-- **A polymer is never compatible with itself**: compatibility
    is disjointness of link supports, and the support is nonempty. -/
theorem not_plaquetteCompatible_self
    {C : Finset (Site N × Dir × Dir)} (hC : C.Nonempty) :
    ¬ PlaquetteCompatible (N := N) C C := by
  intro h
  unfold PlaquetteCompatible at h
  obtain ⟨ℓ, hℓ⟩ := blockLinkSupport_nonempty (N := N) hC
  exact Set.disjoint_left.mp h hℓ hℓ

/-- Pairwise compatibility of a tuple of polymers (distinct
    indices only — repetitions are killed by the previous lemma). -/
def TupleCompatible {n : ℕ} (δ : Fin n → Polymer N) : Prop :=
  ∀ i j : Fin n, i ≠ j →
    PlaquetteCompatible (N := N) (δ i).val (δ j).val

/-- **A pairwise-compatible tuple is injective** — a repetition
    would make a polymer compatible with itself. -/
theorem tupleCompatible_injective {n : ℕ}
    {δ : Fin n → Polymer N} (h : TupleCompatible δ) :
    Function.Injective δ := by
  intro i j hij
  by_contra hne
  have hcompat := h i j hne
  rw [hij] at hcompat
  exact not_plaquetteCompatible_self
    (isPolymer_of_mem_all (δ j).property).1 hcompat

/-! ## 49C-II.3 — the cancellation becomes the compatibility
    indicator -/

theorem availableEdges_eq_empty_iff {n : ℕ}
    {δ : Fin n → Polymer N} :
    availableEdges (polymerIncompatibilityGraph (N := N)
        (fun m => (δ m).val)) = ∅
      ↔ TupleCompatible δ := by
  constructor
  · intro h i j hne
    by_contra hnc
    rcases hne.lt_or_lt with hlt | hlt
    · have hmem : (⟨(i, j), hlt⟩ : OrderedEdge n)
          ∈ availableEdges (polymerIncompatibilityGraph (N := N)
              (fun m => (δ m).val)) :=
        mem_availableEdges.mpr ⟨ne_of_lt hlt, hnc⟩
      rw [h] at hmem
      exact absurd hmem (Finset.not_mem_empty _)
    · have hmem : (⟨(j, i), hlt⟩ : OrderedEdge n)
          ∈ availableEdges (polymerIncompatibilityGraph (N := N)
              (fun m => (δ m).val)) :=
        mem_availableEdges.mpr ⟨ne_of_lt hlt,
          fun hc => hnc (plaquetteCompatible_symm hc)⟩
      rw [h] at hmem
      exact absurd hmem (Finset.not_mem_empty _)
  · intro h
    refine Finset.eq_empty_iff_forall_not_mem.mpr ?_
    intro e hmem
    obtain ⟨hne, hnc⟩ := mem_availableEdges.mp hmem
    exact hnc (h e.val.1 e.val.2 hne)

/-- **Cancellation → compatibility indicator.** -/
theorem graphAllEdgeCoeff_incompat_eq_indicator {n : ℕ}
    (δ : Fin n → Polymer N) :
    graphAllEdgeCoeff (polymerIncompatibilityGraph (N := N)
        (fun m => (δ m).val))
      = if TupleCompatible δ then 1 else 0 := by
  rw [graphAllEdgeCoeff_eq_ite]
  simp only [availableEdges_eq_empty_iff]

/-! ## 49C-II.4 — the gas coefficient Aₙ (graph side) -/

/-- **Aₙ**: normalized labelled-tuple sum with the ALL-edge
    coefficient — same shape as `kpSignedUnrootedCoeff`, with the
    connected sum replaced by the full powerset sum. -/
noncomputable def kpGasCoeff (n : ℕ) (z : Polymer N → ℝ) : ℝ :=
  (∑ δ : Fin n → Polymer N,
      ((graphAllEdgeCoeff (polymerIncompatibilityGraph (N := N)
          (fun m => (δ m).val)) : ℤ) : ℝ)
        * ∏ i : Fin n, z (δ i))
    / ((Nat.factorial n : ℕ) : ℝ)

/-- **Indicator form**: Aₙ is the normalized sum over
    pairwise-compatible tuples. -/
theorem kpGasCoeff_eq_filter_sum (n : ℕ) (z : Polymer N → ℝ) :
    kpGasCoeff n z
      = (∑ δ ∈ Finset.univ.filter
            (fun δ : Fin n → Polymer N => TupleCompatible δ),
          ∏ i : Fin n, z (δ i))
        / ((Nat.factorial n : ℕ) : ℝ) := by
  unfold kpGasCoeff
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro δ _
  rw [graphAllEdgeCoeff_incompat_eq_indicator δ]
  split_ifs with h
  · simp
  · simp

/-! ## 49C-II.5 — the n!-audit: fibers over typed families -/

/-- The card-n slice of the typed gas. -/
noncomputable def typedGasCardCoeff (n : ℕ) (z : Polymer N → ℝ) :
    ℝ :=
  ∑ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.card = n),
    ∏ η ∈ Γ, z η

/-- **THE EXPLICIT n! AUDIT**: the compatible tuples with a fixed
    typed image Γ of cardinality n are exactly the enumerations of
    Γ — there are n! of them (bijection with `Fin n ≃ Γ`, counted
    by `Fintype.card_equiv`; no set partitions anywhere). -/
theorem card_compatTuple_fiber {n : ℕ} {Γ : Finset (Polymer N)}
    (hΓ : Γ ∈ typedCompatiblePolymerFamilies N)
    (hcard : Γ.card = n) :
    (Finset.univ.filter (fun δ : Fin n → Polymer N =>
        TupleCompatible δ ∧ Finset.univ.image δ = Γ)).card
      = Nat.factorial n := by
  have hΓt := mem_typedCompatiblePolymerFamilies.mp hΓ
  have key : ∀ δ : Fin n → Polymer N,
      (TupleCompatible δ ∧ Finset.univ.image δ = Γ) →
      ∀ k : Fin n, δ k ∈ Γ := by
    intro δ h k
    rw [← h.2]
    exact Finset.mem_image_of_mem δ (Finset.mem_univ k)
  have hbij : (Finset.univ.filter (fun δ : Fin n → Polymer N =>
      TupleCompatible δ ∧ Finset.univ.image δ = Γ)).card
      = (Finset.univ : Finset (Fin n ≃ ↥Γ)).card := by
    refine Finset.card_bij
      (i := fun δ hδ => Equiv.ofBijective
        (fun k => (⟨δ k,
          key δ (Finset.mem_filter.mp hδ).2 k⟩ : ↥Γ))
        (by
          refine (Fintype.bijective_iff_injective_and_card _).mpr
            ⟨?_, ?_⟩
          · intro a b hab
            exact tupleCompatible_injective
              (Finset.mem_filter.mp hδ).2.1
              (congrArg Subtype.val hab)
          · simp [Fintype.card_coe, hcard]))
      ?_ ?_ ?_
    · intro δ hδ
      exact Finset.mem_univ _
    · intro δ₁ h₁ δ₂ h₂ heq
      funext k
      exact congrArg
        (fun e : Fin n ≃ ↥Γ => ((e k : ↥Γ) : Polymer N)) heq
    · intro e he
      have hinj : Function.Injective
          (fun k : Fin n => ((e k : ↥Γ) : Polymer N)) :=
        fun a b hab => e.injective (Subtype.ext hab)
      refine ⟨fun k => ((e k : ↥Γ) : Polymer N),
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, ⟨?_, ?_⟩⟩, ?_⟩
      · intro i j hne
        exact hΓt ((e i : ↥Γ) : Polymer N) (e i).property
          ((e j : ↥Γ) : Polymer N) (e j).property
          (fun hv => hne (e.injective (Subtype.ext hv)))
      · refine Finset.eq_of_subset_of_card_le ?_ ?_
        · intro x hx
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
          exact (e k).property
        · rw [Finset.card_image_of_injective _ hinj,
            Finset.card_univ, Fintype.card_fin]
          exact hcard.le
      · exact Equiv.ext (fun k => Subtype.ext rfl)
  rw [hbij, Finset.card_univ,
    Fintype.card_equiv ((Fintype.equivFinOfCardEq
      (by rw [Fintype.card_coe, hcard])).symm),
    Fintype.card_fin]

/-- **Aₙ = card-n slice of the typed gas** — the n! of the fiber
    cancels the 1/n! of the definition, exactly. -/
theorem kpGasCoeff_eq_typedGasCardCoeff (n : ℕ)
    (z : Polymer N → ℝ) :
    kpGasCoeff n z = typedGasCardCoeff n z := by
  have hmaps : ∀ δ ∈ Finset.univ.filter
      (fun δ : Fin n → Polymer N => TupleCompatible δ),
      Finset.univ.image δ
        ∈ (typedCompatiblePolymerFamilies N).filter
            (fun Γ => Γ.card = n) := by
    intro δ hδ
    have hcomp := (Finset.mem_filter.mp hδ).2
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ hθ hne
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hη
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hθ
      exact hcomp i j (fun hij => hne (congrArg δ hij))
    · rw [Finset.card_image_of_injective _
        (tupleCompatible_injective hcomp),
        Finset.card_univ, Fintype.card_fin]
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun δ : Fin n → Polymer N => ∏ i : Fin n, z (δ i))
  rw [kpGasCoeff_eq_filter_sum, ← hfib]
  have hper : ∀ Γ ∈ (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.card = n),
      (∑ δ ∈ (Finset.univ.filter
          (fun δ : Fin n → Polymer N => TupleCompatible δ)).filter
            (fun δ => Finset.univ.image δ = Γ),
        ∏ i : Fin n, z (δ i))
        = ((Nat.factorial n : ℕ) : ℝ) * ∏ η ∈ Γ, z η := by
    intro Γ hΓ
    obtain ⟨hΓt, hΓc⟩ := Finset.mem_filter.mp hΓ
    rw [Finset.filter_filter]
    have hconst : ∀ δ ∈ Finset.univ.filter
        (fun δ : Fin n → Polymer N =>
          TupleCompatible δ ∧ Finset.univ.image δ = Γ),
        (∏ i : Fin n, z (δ i)) = ∏ η ∈ Γ, z η := by
      intro δ hδ
      obtain ⟨-, hcomp, himg⟩ := Finset.mem_filter.mp hδ
      rw [← himg]
      exact (Finset.prod_image
        (fun a _ b _ h => tupleCompatible_injective hcomp h)).symm
    rw [Finset.sum_congr rfl hconst, Finset.sum_const,
      card_compatTuple_fiber hΓt hΓc, nsmul_eq_mul]
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum]
  unfold typedGasCardCoeff
  exact mul_div_cancel_left₀ _
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-! ## 49C-II.6 — sanities (consumed through the identity) -/

/-- **A₀ = 1** (the empty family). -/
theorem kpGasCoeff_zero (z : Polymer N → ℝ) :
    kpGasCoeff (N := N) 0 z = 1 := by
  rw [kpGasCoeff_eq_typedGasCardCoeff]
  unfold typedGasCardCoeff
  have h : (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.card = 0) = {∅} := by
    ext Γ
    constructor
    · intro hΓ
      exact Finset.mem_singleton.mpr
        (Finset.card_eq_zero.mp (Finset.mem_filter.mp hΓ).2)
    · intro hΓ
      rw [Finset.mem_singleton] at hΓ
      subst hΓ
      refine Finset.mem_filter.mpr ⟨?_, Finset.card_empty⟩
      exact mem_typedCompatiblePolymerFamilies.mpr
        (fun η hη θ hθ hne =>
          absurd hη (Finset.not_mem_empty _))
  rw [h, Finset.sum_singleton, Finset.prod_empty]

/-- **A₁ = Σ z** (the singleton families). -/
theorem kpGasCoeff_one (z : Polymer N → ℝ) :
    kpGasCoeff (N := N) 1 z = ∑ η : Polymer N, z η := by
  rw [kpGasCoeff_eq_typedGasCardCoeff]
  unfold typedGasCardCoeff
  have h : (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.card = 1)
      = Finset.univ.image
          (fun η : Polymer N => ({η} : Finset (Polymer N))) := by
    ext Γ
    constructor
    · intro hΓ
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp
        (Finset.mem_filter.mp hΓ).2
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩
    · intro hΓ
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hΓ
      refine Finset.mem_filter.mpr
        ⟨?_, Finset.card_singleton a⟩
      refine mem_typedCompatiblePolymerFamilies.mpr ?_
      intro η hη θ hθ hne
      rw [Finset.mem_singleton] at hη hθ
      subst hη; subst hθ
      exact absurd rfl hne
  rw [h, Finset.sum_image
    (fun a _ b _ hab => Finset.singleton_injective hab)]
  simp

/-- **Finite support in finite volume**: beyond the polymer count
    there are no injective tuples, hence Aₙ = 0. -/
theorem kpGasCoeff_eq_zero_of_gt (n : ℕ) (z : Polymer N → ℝ)
    (hn : Fintype.card (Polymer N) < n) :
    kpGasCoeff (N := N) n z = 0 := by
  rw [kpGasCoeff_eq_typedGasCardCoeff]
  unfold typedGasCardCoeff
  have h : (typedCompatiblePolymerFamilies N).filter
      (fun Γ => Γ.card = n) = ∅ := by
    refine Finset.eq_empty_iff_forall_not_mem.mpr ?_
    intro Γ hΓ
    have hc := (Finset.mem_filter.mp hΓ).2
    have h1 : Γ.card ≤ Fintype.card (Polymer N) :=
      Finset.card_le_univ Γ
    omega
  rw [h, Finset.sum_empty]

/-! ## 49C-II.7 — THE CAPSTONE -/

/-- **The finite typed hard-core gas decomposes exactly into the
    all-graph coefficients Aₙ** — a FINITE sum, no tsum, no
    analysis. -/
theorem typedPolymerGas_eq_sum_gasCoeff (z : Polymer N → ℝ) :
    typedPolymerGas (N := N) z
      = ∑ n ∈ Finset.range (Fintype.card (Polymer N) + 1),
          kpGasCoeff n z := by
  unfold typedPolymerGas
  have hmaps : ∀ Γ ∈ typedCompatiblePolymerFamilies N,
      Γ.card ∈ Finset.range (Fintype.card (Polymer N) + 1) := by
    intro Γ _
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Finset.card_le_univ Γ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun Γ : Finset (Polymer N) => ∏ η ∈ Γ, z η)]
  refine Finset.sum_congr rfl ?_
  intro n _
  rw [kpGasCoeff_eq_typedGasCardCoeff]
  unfold typedGasCardCoeff
  rfl

end LatticeGauge
