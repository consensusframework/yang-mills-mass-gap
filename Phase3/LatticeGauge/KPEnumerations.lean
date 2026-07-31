/-
LatticeGauge/KPEnumerations.lean — Phase 3, stone 47 (b-iiB), GATE I.

TREES STRATIFIED BY THE ROOT DEGREE, AND THE k! MULTIPLICITY OF
ENUMERATIONS (architecture: Sol/GPT-5.6, six internal gates with the
hard stop at Gate V; execution: Fable). GATE I ONLY: the spanning
trees over Fin (n+1) are stratified by the number k of root
neighbours (k ≤ n; k ≥ 1 for n > 0; strata pairwise disjoint and
exhaustive; the k = 0 stratum empty for n > 0 — the n = 0 case stays
separate with T₀ = 1); a base enumeration Fin k ≃ rootNeighbors ET
is built CANONICALLY from Finset.equivFin composed with finCongr (no
opaque classical choice); the type of ALL enumerations has cardinal
EXACTLY k! — by the confirmed v4.15 theorem `Fintype.card_equiv`
(Data/Fintype/Perm.lean:164), which counts the equivalence type
given a witness (it is NOT a mere card_congr); and the weighted
multiplicity: for any weight independent of the enumeration,
Σ_e W = k!·W (sum_const + the cardinal — multiplicative, NO division
by k!). NOT in this gate: ordered components, weight factorization,
F(B), ordered partitions, the recurrence (Gates II-VI); no S_M, no
KP hypothesis, no Real.exp, no Summable. NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.UrsellSymmetry
import LatticeGauge.UrsellBounds
import LatticeGauge.EdgeFibers
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.RootDecomposition

open scoped Classical

namespace LatticeGauge

variable {n : ℕ}

/-! ## Gate I, item 1: the strata -/

/-- Spanning trees whose root has exactly k neighbours. -/
noncomputable def treesWithKRootNeighbors (n k : ℕ) :
    Finset (Finset (OrderedEdge (n + 1))) :=
  (spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))).filter
    (fun ET => (rootNeighbors ET).card = k)

theorem mem_treesWithKRootNeighbors {k : ℕ}
    {ET : Finset (OrderedEdge (n + 1))} :
    ET ∈ treesWithKRootNeighbors n k
      ↔ ET ∈ spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1)))
        ∧ (rootNeighbors ET).card = k := by
  unfold treesWithKRootNeighbors
  simp [Finset.mem_filter]

/-- k ≤ n: the neighbours live in Fin n. -/
theorem rootNeighbors_card_le (ET : Finset (OrderedEdge (n + 1))) :
    (rootNeighbors ET).card ≤ n := by
  have h := Finset.card_le_card
    (Finset.subset_univ (rootNeighbors ET))
  simpa using h

theorem stratum_le {k : ℕ} {ET : Finset (OrderedEdge (n + 1))}
    (h : ET ∈ treesWithKRootNeighbors n k) : k ≤ n := by
  obtain ⟨-, hcard⟩ := mem_treesWithKRootNeighbors.mp h
  rw [← hcard]
  exact rootNeighbors_card_le ET

/-- For n > 0 every spanning tree has k ≥ 1 root neighbours. -/
theorem stratum_pos {k : ℕ} {ET : Finset (OrderedEdge (n + 1))}
    (hn : 0 < n) (h : ET ∈ treesWithKRootNeighbors n k) : 1 ≤ k := by
  obtain ⟨hET, hcard⟩ := mem_treesWithKRootNeighbors.mp h
  have hne := rootNeighbors_nonempty hET hn
  have := Finset.card_pos.mpr hne
  omega

/-- The k = 0 stratum is empty for n > 0. -/
theorem treesWithKRootNeighbors_zero (hn : 0 < n) :
    treesWithKRootNeighbors n 0
      = (∅ : Finset (Finset (OrderedEdge (n + 1)))) := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ET hET
  have := stratum_pos hn hET
  omega

/-- Distinct strata are disjoint. -/
theorem treesWithKRootNeighbors_disjoint {k₁ k₂ : ℕ}
    (hne : k₁ ≠ k₂) :
    Disjoint (treesWithKRootNeighbors n k₁)
      (treesWithKRootNeighbors n k₂) := by
  rw [Finset.disjoint_left]
  intro ET h1 h2
  have e1 := (mem_treesWithKRootNeighbors.mp h1).2
  have e2 := (mem_treesWithKRootNeighbors.mp h2).2
  exact hne (e1.symm.trans e2)

/-- The strata for 0 ≤ k ≤ n exhaust the spanning trees. -/
theorem biUnion_treesWithKRootNeighbors :
    (Finset.range (n + 1)).biUnion
        (fun k => treesWithKRootNeighbors n k)
      = spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (n + 1))) := by
  ext ET
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, -, hET⟩
    exact (mem_treesWithKRootNeighbors.mp hET).1
  · intro hET
    refine ⟨(rootNeighbors ET).card,
      Finset.mem_range.mpr ?_,
      mem_treesWithKRootNeighbors.mpr ⟨hET, rfl⟩⟩
    have := rootNeighbors_card_le ET
    omega

/-! ## Gate I, item 2: the canonical base enumeration -/

/-- The canonical witness enumeration — Finset.equivFin composed with
    finCongr, no opaque classical choice. -/
noncomputable def baseEnumeration {k : ℕ}
    {ET : Finset (OrderedEdge (n + 1))}
    (h : (rootNeighbors ET).card = k) :
    Fin k ≃ {i // i ∈ rootNeighbors ET} :=
  (finCongr h.symm).trans (rootNeighbors ET).equivFin.symm

/-! ## Gate I, item 3: the cardinal of all enumerations -/

/-- The type of enumerations of the root neighbours. -/
abbrev RootEnumeration (ET : Finset (OrderedEdge (n + 1)))
    (k : ℕ) : Type _ :=
  Fin k ≃ {i // i ∈ rootNeighbors ET}

/-- **The enumeration count**: exactly k! enumerations — via the
    confirmed `Fintype.card_equiv` with the base enumeration as
    witness (the theorem counts the TYPE of all equivalences; it is
    not a mere card_congr). -/
theorem card_rootEnumeration {k : ℕ}
    {ET : Finset (OrderedEdge (n + 1))}
    (h : (rootNeighbors ET).card = k) :
    Fintype.card (RootEnumeration ET k) = Nat.factorial k := by
  rw [Fintype.card_equiv (baseEnumeration h), Fintype.card_fin]

/-! ## Gate I, item 4: the weighted multiplicity — CAPSTONE -/

/-- **GATE I CAPSTONE: Σ_e W = k!·W** for any weight independent of
    the enumeration. Multiplicative: no division by k! anywhere. -/
theorem enumerations_weighted_multiplicity {k : ℕ}
    {ET : Finset (OrderedEdge (n + 1))}
    (h : (rootNeighbors ET).card = k) (W : ℝ) :
    (∑ _e : RootEnumeration ET k, W)
      = (Nat.factorial k : ℝ) * W := by
  rw [Finset.sum_const, Finset.card_univ, card_rootEnumeration h,
    nsmul_eq_mul]

end LatticeGauge
