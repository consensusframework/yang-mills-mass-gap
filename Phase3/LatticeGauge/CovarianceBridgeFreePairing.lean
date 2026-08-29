/-
LatticeGauge/CovarianceBridgeFreePairing.lean — PEDRA 50, Gate
50-A18a: THE BRIDGE-FREE DICTIONARY (architecture: Sol;
execution: Fable).

The exact finite bijection between (i) families touching s ∪ s'
with empty bridgeCore, and (ii) pairs (T, T') where T touches
only s, T' touches only s', and all crossed members are
compatible. Pure exact combinatorics; NO bound anywhere. Pairs
live in the native Prod (Finset.product) — no structure, no
lists, no multisets, no quotients, no representatives. The
crossed compatibility stays EXPLICIT in GoodCorePair (not hidden
in TypedCompatible (T ∪ T')), so the future classification of
bad pairs can negate it condition by condition. The capstone
reindexes any AddCommMonoid-valued sum via Finset.sum_bij with
both inverses explicit.

NOT here (hard hold): no spurious pair, no defect
classification, no mass or separation n, no observable /
integral / gas / quotient, no polymerWeight / Mayer / tilt / A17
analytics, no connector, no exp(C) − 1, no numerator, no
covariance, no frozen file touched.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceCoreLocalBudget

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A18a.1 — touching a union of supports -/

theorem typedTouchesSupport_union_iff {η : Polymer N}
    {s s' : Set (Link N)} :
    typedTouchesSupport (N := N) η (s ∪ s')
      ↔ typedTouchesSupport (N := N) η s
        ∨ typedTouchesSupport (N := N) η s' := by
  unfold typedTouchesSupport blockTouchesSupport
  rw [Set.disjoint_union_right, not_and_or]

/-! ## A18a.2 — remoteAllowed splits over the union (no extra
    hypothesis) -/

theorem remoteAllowed_union_iff {T T' : Finset (Polymer N)}
    {s s' : Set (Link N)} {η : Polymer N} :
    remoteAllowed (N := N) (T ∪ T') (s ∪ s') η
      ↔ remoteAllowed (N := N) T s η
        ∧ remoteAllowed (N := N) T' s' η := by
  unfold remoteAllowed
  rw [typedTouchesSupport_union_iff, Finset.forall_mem_union]
  tauto

/-! ## A18a.3 — the corresponding restricted activities agree
    (fully generic weight; the exact predicate form the A5
    cross-ratio consumes) -/

theorem restrictedActivity_union_eq (z : Polymer N → ℝ)
    (T T' : Finset (Polymer N)) (s s' : Set (Link N)) :
    restrictedActivity z
        (remoteAllowed (N := N) (T ∪ T') (s ∪ s'))
      = restrictedActivity z
          (fun η => remoteAllowed (N := N) T s η
            ∧ remoteAllowed (N := N) T' s' η) := by
  funext η
  unfold restrictedActivity
  by_cases h : remoteAllowed (N := N) (T ∪ T') (s ∪ s') η
  · rw [if_pos h, if_pos (remoteAllowed_union_iff.mp h)]
  · rw [if_neg h,
      if_neg (fun hc => h (remoteAllowed_union_iff.mpr hc))]

/-! ## A18a.4 — the three finite objects -/

noncomputable def bridgeFreeTouchingFamilies
    (s s' : Set (Link N)) : Finset (Finset (Polymer N)) :=
  (typedTouchingFamilies (N := N) (s ∪ s')).filter
    (fun Γ => bridgeCore Γ s s' = ∅)

theorem mem_bridgeFreeTouchingFamilies
    {s s' : Set (Link N)} {Γ : Finset (Polymer N)} :
    Γ ∈ bridgeFreeTouchingFamilies s s'
      ↔ Γ ∈ typedTouchingFamilies (N := N) (s ∪ s')
        ∧ bridgeCore Γ s s' = ∅ :=
  Finset.mem_filter

/-- The good pair: T avoids s', T' avoids s, all crossed members
    compatible — the three conditions kept EXPLICIT. -/
def GoodCorePair (T T' : Finset (Polymer N))
    (s s' : Set (Link N)) : Prop :=
  (∀ η ∈ T, ¬ typedTouchesSupport (N := N) η s')
    ∧ (∀ θ ∈ T', ¬ typedTouchesSupport (N := N) θ s)
    ∧ (∀ η ∈ T, ∀ θ ∈ T',
        PlaquetteCompatible (N := N) η.val θ.val)

noncomputable def typedTouchingFamilyPairs
    (s s' : Set (Link N)) :
    Finset (Finset (Polymer N) × Finset (Polymer N)) :=
  typedTouchingFamilies (N := N) s
    ×ˢ typedTouchingFamilies (N := N) s'

noncomputable def goodCorePairs (s s' : Set (Link N)) :
    Finset (Finset (Polymer N) × Finset (Polymer N)) :=
  (typedTouchingFamilyPairs s s').filter
    (fun p => GoodCorePair p.1 p.2 s s')

theorem mem_goodCorePairs {s s' : Set (Link N)}
    {p : Finset (Polymer N) × Finset (Polymer N)} :
    p ∈ goodCorePairs s s'
      ↔ (p.1 ∈ typedTouchingFamilies (N := N) s
          ∧ p.2 ∈ typedTouchingFamilies (N := N) s')
        ∧ GoodCorePair p.1 p.2 s s' := by
  unfold goodCorePairs typedTouchingFamilyPairs
  rw [Finset.mem_filter, Finset.mem_product]

/-! ## A18a.5 — from the family to the pair -/

theorem remoteBothCore_eq_empty_of_touching
    {s s' : Set (Link N)} {Γ : Finset (Polymer N)}
    (hΓ : Γ ∈ typedTouchingFamilies (N := N) (s ∪ s')) :
    remoteBothCore Γ s s' = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro η hη
  have h := mem_remoteBothCore.mp hη
  have ht := (Finset.mem_filter.mp hΓ).2 η h.1
  rcases typedTouchesSupport_union_iff.mp ht with h1 | h2
  · exact h.2.1 h1
  · exact h.2.2 h2

theorem leftOnly_union_rightOnly_of_bridgeFree
    {s s' : Set (Link N)} {Γ : Finset (Polymer N)}
    (hΓ : Γ ∈ typedTouchingFamilies (N := N) (s ∪ s'))
    (hb : bridgeCore Γ s s' = ∅) :
    leftOnlyCore Γ s s' ∪ rightOnlyCore Γ s s' = Γ := by
  have h := core_partition Γ s s'
  rw [hb, Finset.union_empty,
    remoteBothCore_eq_empty_of_touching hΓ,
    Finset.union_empty] at h
  exact h

theorem corePair_mem_goodCorePairs
    {s s' : Set (Link N)} {Γ : Finset (Polymer N)}
    (hΓ : Γ ∈ typedTouchingFamilies (N := N) (s ∪ s'))
    (hb : bridgeCore Γ s s' = ∅) :
    (leftOnlyCore Γ s s', rightOnlyCore Γ s s')
      ∈ goodCorePairs s s' := by
  have hΓc : TypedCompatible Γ :=
    mem_typedCompatiblePolymerFamilies.mp
      (Finset.mem_filter.mp hΓ).1
  have hmono : ∀ {A : Finset (Polymer N)}, A ⊆ Γ →
      TypedCompatible A :=
    fun hA η hη θ hθ hne => hΓc η (hA hη) θ (hA hθ) hne
  refine mem_goodCorePairs.mpr ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · refine Finset.mem_filter.mpr
      ⟨mem_typedCompatiblePolymerFamilies.mpr
        (hmono (Finset.filter_subset _ _)), ?_⟩
    exact fun η hη => (mem_leftOnlyCore.mp hη).2.1
  · refine Finset.mem_filter.mpr
      ⟨mem_typedCompatiblePolymerFamilies.mpr
        (hmono (Finset.filter_subset _ _)), ?_⟩
    exact fun θ hθ => (mem_rightOnlyCore.mp hθ).2.2
  · exact fun η hη => (mem_leftOnlyCore.mp hη).2.2
  · exact fun θ hθ => (mem_rightOnlyCore.mp hθ).2.1
  · intro η hη θ hθ
    have hne : η ≠ θ := fun he =>
      (mem_rightOnlyCore.mp hθ).2.1
        (he ▸ (mem_leftOnlyCore.mp hη).2.1)
    exact hΓc η (mem_leftOnlyCore.mp hη).1
      θ (mem_rightOnlyCore.mp hθ).1 hne

/-! ## A18a.6 — from the pair to the family -/

theorem union_mem_bridgeFreeTouchingFamilies
    {s s' : Set (Link N)}
    {p : Finset (Polymer N) × Finset (Polymer N)}
    (hp : p ∈ goodCorePairs s s') :
    p.1 ∪ p.2 ∈ bridgeFreeTouchingFamilies s s' := by
  obtain ⟨⟨h1, h2⟩, hgood⟩ := mem_goodCorePairs.mp hp
  have h1c : TypedCompatible p.1 :=
    mem_typedCompatiblePolymerFamilies.mp
      (Finset.mem_filter.mp h1).1
  have h2c : TypedCompatible p.2 :=
    mem_typedCompatiblePolymerFamilies.mp
      (Finset.mem_filter.mp h2).1
  have h1t := (Finset.mem_filter.mp h1).2
  have h2t := (Finset.mem_filter.mp h2).2
  refine mem_bridgeFreeTouchingFamilies.mpr ⟨?_, ?_⟩
  · refine Finset.mem_filter.mpr
      ⟨mem_typedCompatiblePolymerFamilies.mpr ?_, ?_⟩
    · intro η hη θ hθ hne
      rcases Finset.mem_union.mp hη with hη1 | hη2 <;>
        rcases Finset.mem_union.mp hθ with hθ1 | hθ2
      · exact h1c η hη1 θ hθ1 hne
      · exact hgood.2.2 η hη1 θ hθ2
      · exact plaquetteCompatible_symm (hgood.2.2 θ hθ1 η hη2)
      · exact h2c η hη2 θ hθ2 hne
    · intro η hη
      rcases Finset.mem_union.mp hη with hη1 | hη2
      · exact typedTouchesSupport_union_iff.mpr
          (Or.inl (h1t η hη1))
      · exact typedTouchesSupport_union_iff.mpr
          (Or.inr (h2t η hη2))
  · rw [Finset.eq_empty_iff_forall_not_mem]
    intro η hη
    have h := mem_bridgeCore.mp hη
    rcases Finset.mem_union.mp h.1 with hη1 | hη2
    · exact hgood.1 η hη1 h.2.2
    · exact hgood.2.1 η hη2 h.2.1

theorem leftOnlyCore_union_eq {s s' : Set (Link N)}
    {p : Finset (Polymer N) × Finset (Polymer N)}
    (hp : p ∈ goodCorePairs s s') :
    leftOnlyCore (p.1 ∪ p.2) s s' = p.1 := by
  obtain ⟨⟨h1, h2⟩, hgood⟩ := mem_goodCorePairs.mp hp
  have h1t := (Finset.mem_filter.mp h1).2
  ext η
  rw [mem_leftOnlyCore]
  constructor
  · rintro ⟨hmem, hts, hnts'⟩
    rcases Finset.mem_union.mp hmem with hη1 | hη2
    · exact hη1
    · exact absurd hts (hgood.2.1 η hη2)
  · intro hη
    exact ⟨Finset.mem_union_left _ hη, h1t η hη,
      hgood.1 η hη⟩

theorem rightOnlyCore_union_eq {s s' : Set (Link N)}
    {p : Finset (Polymer N) × Finset (Polymer N)}
    (hp : p ∈ goodCorePairs s s') :
    rightOnlyCore (p.1 ∪ p.2) s s' = p.2 := by
  obtain ⟨⟨h1, h2⟩, hgood⟩ := mem_goodCorePairs.mp hp
  have h2t := (Finset.mem_filter.mp h2).2
  ext θ
  rw [mem_rightOnlyCore]
  constructor
  · rintro ⟨hmem, hnts, hts'⟩
    rcases Finset.mem_union.mp hmem with hθ1 | hθ2
    · exact absurd hts' (hgood.1 θ hθ1)
    · exact hθ2
  · intro hθ
    exact ⟨Finset.mem_union_right _ hθ,
      hgood.2.1 θ hθ, h2t θ hθ⟩

/-! ## A18a.7 — CAPSTONE: the generic reindexation -/

/-- **CAPSTONE 50-A18a**: any additive sum over bridge-free
    touching families IS the sum over good core pairs — both
    inverses explicit, no new Equiv, no new family structure. -/
theorem sum_bridgeFree_eq_sum_goodPairs {M : Type*}
    [AddCommMonoid M] (s s' : Set (Link N))
    (F : Finset (Polymer N) → M) :
    (∑ Γ ∈ bridgeFreeTouchingFamilies (N := N) s s', F Γ)
      = ∑ p ∈ goodCorePairs (N := N) s s', F (p.1 ∪ p.2) := by
  refine Finset.sum_bij
    (i := fun Γ _ => (leftOnlyCore Γ s s', rightOnlyCore Γ s s'))
    ?_ ?_ ?_ ?_
  · intro Γ hΓ
    obtain ⟨hΓt, hb⟩ := mem_bridgeFreeTouchingFamilies.mp hΓ
    exact corePair_mem_goodCorePairs hΓt hb
  · intro Γ₁ hΓ₁ Γ₂ hΓ₂ h
    obtain ⟨hΓ₁t, hb₁⟩ := mem_bridgeFreeTouchingFamilies.mp hΓ₁
    obtain ⟨hΓ₂t, hb₂⟩ := mem_bridgeFreeTouchingFamilies.mp hΓ₂
    injection h with h1 h2
    calc Γ₁ = leftOnlyCore Γ₁ s s' ∪ rightOnlyCore Γ₁ s s' :=
          (leftOnly_union_rightOnly_of_bridgeFree hΓ₁t hb₁).symm
      _ = leftOnlyCore Γ₂ s s' ∪ rightOnlyCore Γ₂ s s' := by
          rw [h1, h2]
      _ = Γ₂ :=
          leftOnly_union_rightOnly_of_bridgeFree hΓ₂t hb₂
  · intro p hp
    refine ⟨p.1 ∪ p.2,
      union_mem_bridgeFreeTouchingFamilies hp, ?_⟩
    show (leftOnlyCore (p.1 ∪ p.2) s s',
        rightOnlyCore (p.1 ∪ p.2) s s') = p
    rw [leftOnlyCore_union_eq hp, rightOnlyCore_union_eq hp]
  · intro Γ hΓ
    obtain ⟨hΓt, hb⟩ := mem_bridgeFreeTouchingFamilies.mp hΓ
    exact congrArg F
      (leftOnly_union_rightOnly_of_bridgeFree hΓt hb).symm

#print axioms remoteAllowed_union_iff
#print axioms sum_bridgeFree_eq_sum_goodPairs

end LatticeGauge
