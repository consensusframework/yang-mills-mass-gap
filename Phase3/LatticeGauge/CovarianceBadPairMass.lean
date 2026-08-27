/-
LatticeGauge/CovarianceBadPairMass.lean — PEDRA 50, Gate 50-A18b:
THE TOLL OF THE BAD PAIRS (architecture: Sol; execution: Fable).

The exact classification of the complement of GoodCorePair —
the three defects stay visible:
  (i) some member of T touches s';
  (ii) some member of T' touches s;
  (iii) some crossed pair is incompatible —
and the single mass capstone: under WalkBarrierSeparated s s' n,
every bad pair pays
  n ≤ familyTotalCard p.1 + familyTotalCard p.2.
Defects (i)/(ii) are A14's bridge polymer; defect (iii) glues the
two polymers through their shared link (A6's incompatible-blocks
glue, no Fin 2, no new graph, no new walk machine) and pays via
card_union_le. Finite logic and geometry ONLY; no analytic sum.
No Disjoint s s' hypothesis anywhere.

NOT here (hard hold): no observable / integral / gas, no weight /
Mayer / tilt / A17 analytics, no connector, no exp(C) − 1, no
numerator, no covariance, no A18c, no new pair structure — if the
classification had needed quotients, lists or ordered families,
this file would have been a surrender report instead.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceBridgeFreePairing

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A18b.1 — the bad pairs -/

def BadCorePair (T T' : Finset (Polymer N))
    (s s' : Set (Link N)) : Prop :=
  ¬ GoodCorePair T T' s s'

noncomputable def badCorePairs (s s' : Set (Link N)) :
    Finset (Finset (Polymer N) × Finset (Polymer N)) :=
  (typedTouchingFamilyPairs s s').filter
    (fun p => BadCorePair p.1 p.2 s s')

theorem mem_badCorePairs {s s' : Set (Link N)}
    {p : Finset (Polymer N) × Finset (Polymer N)} :
    p ∈ badCorePairs s s'
      ↔ (p.1 ∈ typedTouchingFamilies (N := N) s
          ∧ p.2 ∈ typedTouchingFamilies (N := N) s')
        ∧ BadCorePair p.1 p.2 s s' := by
  unfold badCorePairs typedTouchingFamilyPairs
  rw [Finset.mem_filter, Finset.mem_product]

/-! ## A18b.2 — the exact classification: three visible defects -/

theorem badCorePair_iff {T T' : Finset (Polymer N)}
    {s s' : Set (Link N)} :
    BadCorePair T T' s s'
      ↔ (∃ η ∈ T, typedTouchesSupport (N := N) η s')
        ∨ (∃ θ ∈ T', typedTouchesSupport (N := N) θ s)
        ∨ (∃ η ∈ T, ∃ θ ∈ T',
            ¬ PlaquetteCompatible (N := N) η.val θ.val) := by
  unfold BadCorePair GoodCorePair
  constructor
  · intro h
    by_cases h1 : ∀ η ∈ T, ¬ typedTouchesSupport (N := N) η s'
    · by_cases h2 : ∀ θ ∈ T',
          ¬ typedTouchesSupport (N := N) θ s
      · refine Or.inr (Or.inr ?_)
        by_contra h3
        push_neg at h3
        exact h ⟨h1, h2, h3⟩
      · push_neg at h2
        exact Or.inr (Or.inl h2)
    · push_neg at h1
      exact Or.inl h1
  · rintro (⟨η, hη, ht⟩ | ⟨θ, hθ, ht⟩ | ⟨η, hη, θ, hθ, hinc⟩)
      hgood
    · exact hgood.1 η hη ht
    · exact hgood.2.1 θ hθ ht
    · exact hinc (hgood.2.2 η hη θ hθ)

/-! ## A18b.3 — partition, disjointness, generic sum split -/

theorem good_union_bad (s s' : Set (Link N)) :
    goodCorePairs (N := N) s s' ∪ badCorePairs s s'
      = typedTouchingFamilyPairs s s' := by
  unfold goodCorePairs badCorePairs
  ext p
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases hg : GoodCorePair p.1 p.2 s s'
    · exact Or.inl ⟨h, hg⟩
    · exact Or.inr ⟨h, hg⟩

theorem good_disjoint_bad (s s' : Set (Link N)) :
    Disjoint (goodCorePairs (N := N) s s')
      (badCorePairs s s') := by
  rw [Finset.disjoint_left]
  intro p hg hb
  exact (mem_badCorePairs.mp hb).2 (mem_goodCorePairs.mp hg).2

/-- The generic split of any additive pair sum into good + bad. -/
theorem sum_pairs_eq_good_add_bad {M : Type*} [AddCommMonoid M]
    (s s' : Set (Link N))
    (F : Finset (Polymer N) × Finset (Polymer N) → M) :
    (∑ p ∈ typedTouchingFamilyPairs (N := N) s s', F p)
      = (∑ p ∈ goodCorePairs (N := N) s s', F p)
        + ∑ p ∈ badCorePairs s s', F p := by
  rw [← good_union_bad s s',
    Finset.sum_union (good_disjoint_bad s s')]

/-! ## A18b.4 — the geometry of the third defect: incompatible
    blocks glue into one connected set (A6 consumed; no Fin 2,
    no new graph, no new walk machine) -/

theorem union_intrinsicallyConnected_of_incompatible
    {C D : Finset (Site N × Dir × Dir)}
    (hC : IntrinsicallyConnected (N := N) C)
    (hD : IntrinsicallyConnected (N := N) D)
    (h : ¬ PlaquetteCompatible (N := N) C D) :
    IntrinsicallyConnected (N := N) (C ∪ D) := by
  intro p hp q hq
  rcases Finset.mem_union.mp hp with hpC | hpD <;>
    rcases Finset.mem_union.mp hq with hqC | hqD
  · exact connectedWithin_mono Finset.subset_union_left
      (hC p hpC q hqC)
  · exact connectedWithin_of_incompatible_blocks
      Finset.subset_union_left Finset.subset_union_right
      hC hD h hpC hqD
  · exact connectedWithin_symm
      (connectedWithin_of_incompatible_blocks
        Finset.subset_union_left Finset.subset_union_right
        hC hD h hqC hpD)
  · exact connectedWithin_mono Finset.subset_union_right
      (hD p hpD q hqD)

/-- **The crossed-incompatibility toll**: η touching s, θ
    touching s', sharing a link, under walk separation — the
    glued set is one connected witness with both contacts, so
    n ≤ card(η ∪ θ) ≤ card η + card θ. -/
theorem incompatible_cross_card_ge {s s' : Set (Link N)} {n : ℕ}
    {η θ : Polymer N}
    (hηs : typedTouchesSupport (N := N) η s)
    (hθs' : typedTouchesSupport (N := N) θ s')
    (hinc : ¬ PlaquetteCompatible (N := N) η.val θ.val)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    n ≤ (η.val).card + (θ.val).card := by
  have hconn := union_intrinsicallyConnected_of_incompatible
    (isPolymer_of_mem_all η.property).2.2
    (isPolymer_of_mem_all θ.property).2.2 hinc
  have hp : ∃ p ∈ η.val ∪ θ.val, ¬ Disjoint
      (↑(plaqLinkSet (N := N) p) : Set (Link N)) s := by
    obtain ⟨p, hpη, hpt⟩ := exists_plaquette_touching hηs
    exact ⟨p, Finset.mem_union_left _ hpη, hpt⟩
  have hq : ∃ q ∈ η.val ∪ θ.val, ¬ Disjoint
      (↑(plaqLinkSet (N := N) q) : Set (Link N)) s' := by
    obtain ⟨q, hqθ, hqt⟩ := exists_plaquette_touching hθs'
    exact ⟨q, Finset.mem_union_right _ hqθ, hqt⟩
  exact le_trans
    (walkBarrierSeparated_barrierSeparation hwsep
      (η.val ∪ θ.val) hconn hp hq)
    (Finset.card_union_le _ _)

/-! ## A18b.5 — transport to families -/

theorem card_le_familyTotalCard {T : Finset (Polymer N)}
    {η : Polymer N} (hη : η ∈ T) :
    (η.val).card ≤ familyTotalCard T :=
  Finset.single_le_sum
    (f := fun η : Polymer N => (η.val).card)
    (fun _ _ => Nat.zero_le _) hη

/-! ## A18b.6 — CAPSTONE: every bad pair pays the toll -/

/-- **CAPSTONE 50-A18b**: under walk separation, every bad core
    pair carries total mass at least n — defects (i)/(ii) through
    A14's bridge polymer, defect (iii) through the glued
    incompatible pair. No Disjoint s s' hypothesis. -/
theorem badCorePair_familyTotalCard_ge
    {s s' : Set (Link N)} {n : ℕ}
    {p : Finset (Polymer N) × Finset (Polymer N)}
    (hp : p ∈ badCorePairs s s')
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    n ≤ familyTotalCard p.1 + familyTotalCard p.2 := by
  obtain ⟨⟨h1, h2⟩, hbad⟩ := mem_badCorePairs.mp hp
  have h1t := (Finset.mem_filter.mp h1).2
  have h2t := (Finset.mem_filter.mp h2).2
  rcases badCorePair_iff.mp hbad with
    ⟨η, hη, ht'⟩ | ⟨θ, hθ, ht⟩ | ⟨η, hη, θ, hθ, hinc⟩
  · exact le_trans
      (bridgePolymer_card_ge (h1t η hη) ht' hwsep)
      (le_trans (card_le_familyTotalCard hη)
        (Nat.le_add_right _ _))
  · exact le_trans
      (bridgePolymer_card_ge ht (h2t θ hθ) hwsep)
      (le_trans (card_le_familyTotalCard hθ)
        (Nat.le_add_left _ _))
  · exact le_trans
      (incompatible_cross_card_ge (h1t η hη) (h2t θ hθ)
        hinc hwsep)
      (Nat.add_le_add (card_le_familyTotalCard hη)
        (card_le_familyTotalCard hθ))

#print axioms incompatible_cross_card_ge
#print axioms badCorePair_familyTotalCard_ge

end LatticeGauge
