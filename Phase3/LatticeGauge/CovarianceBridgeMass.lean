/-
LatticeGauge/CovarianceBridgeMass.lean — PEDRA 50, Gate 50-A14:
THE BRIDGE WITNESS HAS MASS (architecture: Sol; execution:
Fable).

Purely geometric: if the bridge class of a family is nonempty,
some single polymer touches BOTH supports; being intrinsically
connected (it is a polymer — A7's separation applies to it
directly, no Fin 1 tuple detour), its cardinality is at least
the walk separation n; hence the total mass of the family is at
least n. THE EXACT DICHOTOMY: under WalkBarrierSeparated s s' n,
  bridgeCore Γ s s' = ∅ ∨ n ≤ familyTotalCard Γ —
the left branch is where A13 factorizes; the right branch is
where the future tilt charges the family mass. DELIBERATELY
ABSENT hypotheses: TypedCompatible, Disjoint s s', β, χ, μm,
observables — the mass comes from ONE polymer touching both
sides. familyTotalCard sums over a Finset of DISTINCT polymers —
not an Ursell tuple with repetitions (tupleTotalCard is a
different object).

NOT here (hard hold): no β/χ/μm/polymerWeight, no
twoMarkedFamilyIntegral estimate, no sum over families, no
massTiltActivity, no ConnectorClusters, no A12 tail, no T/T'
regrouping, no covariance, no SimpleGraph.dist, no covariance
decay/clustering, no thermodynamic limit, no continuum, no mass
gap, no Clay claim. A13 stays frozen.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceMayerWiring

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A14.1 — the additive mass of a family -/

noncomputable def familyTotalCard (Γ : Finset (Polymer N)) : ℕ :=
  ∑ η ∈ Γ, (η.val).card

/-- Nonnegativity (trivial in ℕ — recorded for the ledger). -/
theorem familyTotalCard_nonneg (Γ : Finset (Polymer N)) :
    0 ≤ familyTotalCard Γ :=
  Nat.zero_le _

/-- The inclusion monotonicity actually consumed below (ℕ sums:
    no nonnegativity side condition needed). -/
theorem familyTotalCard_mono {Γ Γ' : Finset (Polymer N)}
    (h : Γ ⊆ Γ') :
    familyTotalCard Γ ≤ familyTotalCard Γ' :=
  Finset.sum_le_sum_of_subset h

/-! ## A14.2 — a single bridge polymer is already large -/

/-- **A polymer touching both supports has at least n
    plaquettes** — its own intrinsic connectivity feeds A7's
    BarrierSeparation directly; no tuple, no walk rebuilt. -/
theorem bridgePolymer_card_ge {s s' : Set (Link N)} {n : ℕ}
    {η : Polymer N}
    (hs : typedTouchesSupport (N := N) η s)
    (hs' : typedTouchesSupport (N := N) η s')
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    n ≤ (η.val).card := by
  have hconn : IntrinsicallyConnected (N := N) η.val :=
    (isPolymer_of_mem_all η.property).2.2
  exact walkBarrierSeparated_barrierSeparation hwsep η.val hconn
    (exists_plaquette_touching hs)
    (exists_plaquette_touching hs')

/-! ## A14.3 — the witness inside the bridgeCore (the witness is
    the one Finset.Nonempty provides — no silent choice) -/

theorem exists_bridge_witness_card_ge {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    ∃ η ∈ bridgeCore Γ s s', n ≤ (η.val).card := by
  obtain ⟨η, hη⟩ := hne
  have h := mem_bridgeCore.mp hη
  exact ⟨η, hη, bridgePolymer_card_ge h.2.1 h.2.2 hwsep⟩

/-! ## A14.4 — from the witness to the total mass (two visible
    steps) -/

/-- Step 1: the bridge class carries mass ≥ n. -/
theorem bridgeCore_sum_card_ge {Γ : Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hne : (bridgeCore Γ s s').Nonempty)
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    n ≤ ∑ η ∈ bridgeCore Γ s s', (η.val).card := by
  obtain ⟨η, hη, hcard⟩ := exists_bridge_witness_card_ge hne hwsep
  exact le_trans hcard
    (Finset.single_le_sum
      (f := fun η : Polymer N => (η.val).card)
      (fun _ _ => Nat.zero_le _) hη)

/-- Step 2: the bridge class is included in the family. -/
theorem bridgeCore_sum_le_familyTotalCard
    (Γ : Finset (Polymer N)) (s s' : Set (Link N)) :
    (∑ η ∈ bridgeCore Γ s s', (η.val).card)
      ≤ familyTotalCard Γ := by
  have hsub : bridgeCore Γ s s' ⊆ Γ := Finset.filter_subset _ _
  exact Finset.sum_le_sum_of_subset hsub

/-! ## A14.5 — CAPSTONE: the exact dichotomy -/

/-- **CAPSTONE 50-A14**: under walk separation, every family is
    either bridge-free (A13 factorizes it) or carries total mass
    at least n (the future tilt charges it). TypedCompatible,
    Disjoint s s', β, χ, μm, observables: deliberately absent —
    one polymer touching both sides suffices. -/
theorem bridgeFree_or_familyTotalCard_ge
    {Γ : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hwsep : WalkBarrierSeparated (N := N) s s' n) :
    bridgeCore Γ s s' = ∅ ∨ n ≤ familyTotalCard Γ := by
  rcases Finset.eq_empty_or_nonempty (bridgeCore Γ s s')
    with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (bridgeCore_sum_card_ge h hwsep)
      (bridgeCore_sum_le_familyTotalCard Γ s s'))

#print axioms bridgePolymer_card_ge
#print axioms bridgeFree_or_familyTotalCard_ge

end LatticeGauge
