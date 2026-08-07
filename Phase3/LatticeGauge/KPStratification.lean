/-
LatticeGauge/KPStratification.lean — stone 47 (b-iiB), GATE VI-A,
increment 1: STRATIFICATION BY ROOT DEGREE AND SIZE PROFILES
(architecture: Sol/GPT-5.6; execution: Fable).

The unnormalized contribution of each root degree k is defined for
ALL k, and the rooted tree sum is stratified over the PRIMITIVE
index `Finset.range (n + 1)` (the architect's ruling: no biUnion
architecture; the degree is a classifying function and the
stratification is `Finset.sum_fiberwise_of_maps_to`, censused at
Mathlib/Algebra/BigOperators/Group/Finset.lean:704). Empty strata
are separate theorems: k = 0 dies for n > 0 (through the Gate-II
edge case n_eq_zero_of_k_zero, no new graph theory), k > n dies
because the root has at most n neighbours. The enumerated data
(tree in the stratum + root enumeration + global assignment) is a
FINITE type whose weighted sum is exactly k! times the stratum
contribution — the Gate-I multiplicity consumed for the FULL
contribution, assignments included, with no division. Size
profiles are the architect's finite type
{s : Fin k → Fin (n+1) // Σ ((s j : ℕ) + 1) = n} — Fintype for
free, no artificial filters on an infinite ambient type, no
truncated subtraction, robust at k = 0 and n = 0.
NOT in this increment: the profiled equivalence, the weight
preservation (VI-A.5–VI-A.7); no F(B) substitution, no multinomial
consumption, no recurrence, no 1/k!, no KP, no exp, no Summable.
NO axioms.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.UrsellCoefficients
import LatticeGauge.PolymerTreeBound
import LatticeGauge.KPCoefficients
import LatticeGauge.RootDecomposition
import LatticeGauge.KPEnumerations
import LatticeGauge.KPOrderedDecomposition
import LatticeGauge.KPWeightFactorization
import LatticeGauge.KPRootedTransport
import LatticeGauge.KPBlockSum
import LatticeGauge.KPMarkedBlock
import LatticeGauge.KPPartitionCount

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {n k : ℕ}

/-! ## VI-A.1 — the contribution of one root degree -/

/-- The UNNORMALIZED contribution of the trees whose root has
    exactly k neighbours — defined for ALL k; the empty strata are
    theorems, not definitional cases. -/
noncomputable def rootDegreeContribution (n k : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) : ℝ :=
  ∑ ET ∈ treesWithKRootNeighbors n k,
    ∑ γ : Fin n → Polymer N,
      rootedTreeWeight ρ γ₀ γ ET

/-- **VI-A.1 stratification**: the rooted tree sum decomposes over
    the primitive index `range (n + 1)` — each tree counted in the
    unique stratum of its root degree. -/
theorem rootedTreeSum_eq_sum_rootDegreeContribution
    (n : ℕ) (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    rootedTreeSum n ρ γ₀
      = ∑ k ∈ Finset.range (n + 1),
          rootDegreeContribution n k ρ γ₀ := by
  unfold rootedTreeSum rootDegreeContribution
    treesWithKRootNeighbors
  rw [Finset.sum_comm]
  refine (Finset.sum_fiberwise_of_maps_to
    (g := fun ET => (rootNeighbors ET).card)
    (fun ET _ => Finset.mem_range.mpr ?_) _).symm
  show (rootNeighbors ET).card < n + 1
  have h1 : (rootNeighbors ET).card ≤ n := by
    calc (rootNeighbors ET).card
        ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  omega

/-- The k = 0 stratum is EMPTY for n > 0: a tree in it would
    decompose into zero components covering n vertices
    (the Gate-II edge case, no new graph theory). -/
theorem treesWithKRootNeighbors_zero_eq_empty (hn : 0 < n) :
    treesWithKRootNeighbors n 0 = (∅ : Finset _) := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ET hET
  have hcard : (rootNeighbors ET).card = 0 :=
    (mem_treesWithKRootNeighbors.mp hET).2
  have hOD : OrderedDecomposition n 0 :=
    decompose hET (baseEnumeration hcard)
  have h0 := hOD.n_eq_zero_of_k_zero
  omega

/-- **VI-A.1 empty stratum, k = 0**: no contribution for n > 0. -/
theorem rootDegreeContribution_zero_of_pos (hn : 0 < n)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    rootDegreeContribution n 0 ρ γ₀ = 0 := by
  unfold rootDegreeContribution
  rw [treesWithKRootNeighbors_zero_eq_empty hn, Finset.sum_empty]

/-- The k > n stratum is empty: the root of a spanning tree on
    Fin (n + 1) has at most n neighbours. -/
theorem treesWithKRootNeighbors_eq_empty_of_gt (hk : n < k) :
    treesWithKRootNeighbors n k = (∅ : Finset _) := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  intro ET hET
  have hcard : (rootNeighbors ET).card = k :=
    (mem_treesWithKRootNeighbors.mp hET).2
  have h1 : (rootNeighbors ET).card ≤ n := by
    calc (rootNeighbors ET).card
        ≤ Fintype.card (Fin n) := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  omega

/-- **VI-A.1 empty stratum, k > n**: no contribution. -/
theorem rootDegreeContribution_eq_zero_of_gt (hk : n < k)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    rootDegreeContribution n k ρ γ₀ = 0 := by
  unfold rootDegreeContribution
  rw [treesWithKRootNeighbors_eq_empty_of_gt hk, Finset.sum_empty]

/-! ## VI-A.2 — the enumerated weighted data and its k!
    multiplicity -/

/-- Fintype for the enumerated trees, by injection into the plain
    pair (edge set, list of neighbour values) — the extensionality
    of Gate II makes the injectivity immediate. -/
noncomputable instance : Fintype (EnumeratedTree n k) :=
  Fintype.ofInjective
    (fun T =>
      ((T.ET, fun j => ((T.enum j : {i // i ∈ rootNeighbors T.ET})
          : Fin n))
        : Finset (OrderedEdge (n + 1)) × (Fin k → Fin n)))
    (fun T₁ T₂ h => by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only at h1 h2
      exact EnumeratedTree.ext' h1 (fun j => congrFun h2 j))

/-- The enumerated weighted data of a stratum: an enumerated tree
    of root degree k together with a global assignment — a plain
    product, so the Fintype is automatic. -/
abbrev EnumeratedRootDegreeData (N : ℕ) [NeZero N]
    [Fintype (Site N)] (n k : ℕ) : Type _ :=
  EnumeratedTree n k × (Fin n → Polymer N)

/-- The weight of one enumerated datum — the enumeration carries no
    weight; only the tree and the assignment do. -/
noncomputable def enumeratedDataWeight (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (X : EnumeratedRootDegreeData N n k) : ℝ :=
  rootedTreeWeight ρ γ₀ X.2 X.1.ET

/-- The enumerated trees, repackaged as a sigma over the stratum —
    both roundtrips are definitional. -/
noncomputable def enumeratedTreeEquivSigma (n k : ℕ) :
    EnumeratedTree n k
      ≃ Σ E : {E // E ∈ treesWithKRootNeighbors n k},
          RootEnumeration E.val k where
  toFun T := ⟨⟨T.ET, T.mem⟩, T.enum⟩
  invFun X := ⟨X.1.val, X.1.property, X.2⟩
  left_inv T := rfl
  right_inv X := rfl

/-- **VI-A.2 CAPSTONE: the k! multiplicity for the FULL
    contribution** — summing the weight over all enumerated data
    (assignments included) gives exactly k! times the stratum
    contribution. Gate I consumed; card_rootEnumeration NOT
    reproved. -/
theorem sum_enumeratedRootDegreeData_weight
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    (∑ X : EnumeratedRootDegreeData N n k,
        enumeratedDataWeight ρ γ₀ X)
      = (Nat.factorial k : ℝ)
          * rootDegreeContribution n k ρ γ₀ := by
  unfold enumeratedDataWeight
  calc
    (∑ X : EnumeratedRootDegreeData N n k,
        rootedTreeWeight ρ γ₀ X.2 X.1.ET)
        = ∑ T : EnumeratedTree n k,
            ∑ γ : Fin n → Polymer N,
              rootedTreeWeight ρ γ₀ γ T.ET :=
        Fintype.sum_prod_type _
    _ = ∑ X : (Σ E : {E // E ∈ treesWithKRootNeighbors n k},
            RootEnumeration E.val k),
          ∑ γ : Fin n → Polymer N,
            rootedTreeWeight ρ γ₀ γ X.1.val :=
        Fintype.sum_equiv (enumeratedTreeEquivSigma n k)
          (fun T => ∑ γ : Fin n → Polymer N,
            rootedTreeWeight ρ γ₀ γ T.ET)
          (fun X => ∑ γ : Fin n → Polymer N,
            rootedTreeWeight ρ γ₀ γ X.1.val)
          (fun T => rfl)
    _ = ∑ E : {E // E ∈ treesWithKRootNeighbors n k},
          ∑ _e : RootEnumeration E.val k,
            ∑ γ : Fin n → Polymer N,
              rootedTreeWeight ρ γ₀ γ E.val := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    _ = ∑ E : {E // E ∈ treesWithKRootNeighbors n k},
          (Nat.factorial k : ℝ)
            * ∑ γ : Fin n → Polymer N,
                rootedTreeWeight ρ γ₀ γ E.val := by
        refine Finset.sum_congr rfl (fun E _ => ?_)
        exact enumerations_weighted_multiplicity
          (mem_treesWithKRootNeighbors.mp E.property).2 _
    _ = (Nat.factorial k : ℝ)
          * ∑ E : {E // E ∈ treesWithKRootNeighbors n k},
              ∑ γ : Fin n → Polymer N,
                rootedTreeWeight ρ γ₀ γ E.val := by
        rw [Finset.mul_sum]
    _ = (Nat.factorial k : ℝ)
          * rootDegreeContribution n k ρ γ₀ := by
        unfold rootDegreeContribution
        exact congrArg (fun z => (Nat.factorial k : ℝ) * z)
          (Finset.sum_coe_sort
            (s := treesWithKRootNeighbors n k)
            (f := fun E => ∑ γ : Fin n → Polymer N,
              rootedTreeWeight ρ γ₀ γ E))

/-! ## VI-A.3 — the finite size profiles -/

/-- The architect's finite profile type: k block sizes (each stored
    as the TAIL size, in Fin (n+1)) whose (+1)-sum is exactly n.
    Fintype for free; no filters on an infinite ambient type; no
    truncated subtraction; robust at k = 0 and n = 0. -/
def SizeProfile (n k : ℕ) : Type :=
  {s : Fin k → Fin (n + 1) // (∑ j, ((s j : ℕ) + 1)) = n}

noncomputable instance : Fintype (SizeProfile n k) := by
  unfold SizeProfile
  infer_instance

noncomputable instance : DecidableEq (SizeProfile n k) := by
  unfold SizeProfile
  infer_instance

/-- Extensionality by the values of the profile. -/
theorem SizeProfile.ext' {s₁ s₂ : SizeProfile n k}
    (h : ∀ j, s₁.1 j = s₂.1 j) : s₁ = s₂ :=
  Subtype.ext (funext h)

/-- The profile as plain natural sizes (the interface consumed by
    `OrderedPartition`). -/
def profileNat (s : SizeProfile n k) : Fin k → ℕ :=
  fun j => (s.1 j : ℕ)

@[simp]
theorem sum_profileNat_add_one (s : SizeProfile n k) :
    (∑ j, (profileNat s j + 1)) = n := s.2

/-- k = 0 forces n = 0: the empty profile has nothing to sum. -/
theorem SizeProfile.n_eq_zero_of_k_zero (s : SizeProfile n 0) :
    n = 0 := by
  have h := s.2
  simpa using h.symm

/-- k = 1: the single tail size is determined, s₀ + 1 = n. -/
theorem SizeProfile.k_one_val (s : SizeProfile n 1) :
    (s.1 0 : ℕ) + 1 = n := by
  have h := s.2
  rwa [Fin.sum_univ_one] at h

/-! ## VI-A.4a — the generic connectivity lower bound: a block
    reachable to its mark through confined edges has at most
    |edges| + 1 vertices (transport to Fin (c+1) and consumption of
    the stone-40b BFS bound; no trees, no new graph theory) -/

/-- Confinement of one ambient edge with both endpoints in S. -/
def confineEdge {S : Finset (Fin (n + 1))}
    (ed : OrderedEdge (n + 1)) (h1 : ed.val.1 ∈ S)
    (h2 : ed.val.2 ∈ S) : OrderedEdgeOn {x // x ∈ S} :=
  ⟨(⟨ed.val.1, h1⟩, ⟨ed.val.2, h2⟩),
    Subtype.mk_lt_mk.mpr ed.property⟩

/-- Confinement of a whole edge set (through attach — the
    membership proofs travel with the edges). -/
noncomputable def confineSet {S : Finset (Fin (n + 1))}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S) :
    Finset (OrderedEdgeOn {x // x ∈ S}) :=
  E.attach.image (fun x =>
    confineEdge x.val (hsub x.val x.property).1
      (hsub x.val x.property).2)

theorem card_confineSet_le {S : Finset (Fin (n + 1))}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S) :
    (confineSet E hsub).card ≤ E.card := by
  calc (confineSet E hsub).card
      ≤ E.attach.card := Finset.card_image_le
    _ = E.card := Finset.card_attach

theorem confineEdge_mem_confineSet {S : Finset (Fin (n + 1))}
    {E : Finset (OrderedEdge (n + 1))}
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S)
    {ed : OrderedEdge (n + 1)} (hed : ed ∈ E) :
    confineEdge ed (hsub ed hed).1 (hsub ed hed).2
      ∈ confineSet E hsub := by
  unfold confineSet
  exact Finset.mem_image.mpr ⟨⟨ed, hed⟩, Finset.mem_attach _ _, rfl⟩

/-- One ambient adjacency confines (proof irrelevance aligns the
    subtype points). -/
theorem confined_adj {S : Finset (Fin (n + 1))}
    {E : Finset (OrderedEdge (n + 1))}
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S)
    {u w : Fin (n + 1)} (hadj : (graphOfEdges E).Adj u w)
    (hu : u ∈ S) (hw : w ∈ S) :
    (graphOfEdgesOn (confineSet E hsub)).Adj ⟨u, hu⟩ ⟨w, hw⟩ := by
  show (∃ h : (⟨u, hu⟩ : {x // x ∈ S}) < ⟨w, hw⟩,
      (⟨(⟨u, hu⟩, ⟨w, hw⟩), h⟩ : OrderedEdgeOn {x // x ∈ S})
        ∈ confineSet E hsub)
    ∨ (∃ h : (⟨w, hw⟩ : {x // x ∈ S}) < ⟨u, hu⟩,
      (⟨(⟨w, hw⟩, ⟨u, hu⟩), h⟩ : OrderedEdgeOn {x // x ∈ S})
        ∈ confineSet E hsub)
  rcases graphOfEdges_adj.mp hadj with ⟨hlt, hmem⟩ | ⟨hlt, hmem⟩
  · exact Or.inl ⟨Subtype.mk_lt_mk.mpr hlt,
      confineEdge_mem_confineSet hsub hmem⟩
  · exact Or.inr ⟨Subtype.mk_lt_mk.mpr hlt,
      confineEdge_mem_confineSet hsub hmem⟩

/-- Ambient walks confine: every vertex they touch lies in S, and
    each step transports (ascending edge-by-edge, support in S by
    construction — the 45b-ii style, no `mapLe`). -/
theorem walk_confine {S : Finset (Fin (n + 1))}
    {E : Finset (OrderedEdge (n + 1))}
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S) :
    ∀ {u v : Fin (n + 1)}, (graphOfEdges E).Walk u v →
      ∀ (hu : u ∈ S),
      ∃ hv : v ∈ S,
        (graphOfEdgesOn (confineSet E hsub)).Reachable
          ⟨u, hu⟩ ⟨v, hv⟩ := by
  intro u v p
  induction p with
  | nil =>
      intro hu
      exact ⟨hu, SimpleGraph.Reachable.refl _⟩
  | @cons a b c hadj p ih =>
      intro ha
      have hb : b ∈ S := by
        rcases graphOfEdges_adj.mp hadj with ⟨hlt, hmem⟩
          | ⟨hlt, hmem⟩
        · exact (hsub _ hmem).2
        · exact (hsub _ hmem).1
      obtain ⟨hc, hr⟩ := ih hb
      exact ⟨hc, SimpleGraph.Reachable.trans
        (SimpleGraph.Adj.reachable (confined_adj hsub hadj ha hb))
        hr⟩

/-- The confined graph of a marked, internally-reachable block is
    CONNECTED on the subtype of the succ-image. -/
theorem confined_connected {B : Finset (Fin n)}
    {E : Finset (OrderedEdge (n + 1))} {m : Fin n} (hm : m ∈ B)
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ)
    (hconn : ∀ v ∈ B,
      (graphOfEdges E).Reachable v.succ m.succ) :
    (graphOfEdgesOn (confineSet E hsub)).Connected := by
  rw [SimpleGraph.connected_iff]
  constructor
  · rintro ⟨xv, hxv⟩ ⟨yv, hyv⟩
    obtain ⟨bx, hbx, rfl⟩ := Finset.mem_image.mp hxv
    obtain ⟨by', hby, rfl⟩ := Finset.mem_image.mp hyv
    obtain ⟨px⟩ := hconn bx hbx
    obtain ⟨py⟩ := hconn by' hby
    obtain ⟨hmx, hrx⟩ := walk_confine hsub px hxv
    obtain ⟨hmy, hry⟩ := walk_confine hsub py hyv
    exact SimpleGraph.Reachable.trans hrx
      (SimpleGraph.Reachable.symm hry)
  · exact ⟨⟨m.succ, Finset.mem_image_of_mem _ hm⟩⟩

/-- **VI-A.4a CAPSTONE (the generic lower bound)**: a block whose
    vertices all reach the mark through edges confined to the block
    has at most |E| + 1 elements — relabel the block to Fin (c+1)
    (Gate IV-A transport) and consume the stone-40b BFS bound.
    No spanning trees, no acyclicity, no new BFS. -/
theorem block_card_le_edges_add_one {B : Finset (Fin n)}
    {E : Finset (OrderedEdge (n + 1))} {m : Fin n} (hm : m ∈ B)
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ)
    (hconn : ∀ v ∈ B,
      (graphOfEdges E).Reachable v.succ m.succ) :
    B.card ≤ E.card + 1 := by
  obtain ⟨c, hc⟩ : ∃ c, B.card = c + 1 := by
    have hpos : 0 < B.card := Finset.card_pos.mpr ⟨m, hm⟩
    exact ⟨B.card - 1, by omega⟩
  have hS : (B.image Fin.succ).card = c + 1 := by
    rw [Finset.card_image_of_injective _ (Fin.succ_injective n)]
    exact hc
  let σ : {x // x ∈ B.image Fin.succ} ≃ Fin (c + 1) :=
    (B.image Fin.succ).equivFin.trans (finCongr hS)
  have h1 : (graphOfEdgesOn
      (relabelSetOn σ (confineSet E hsub))).Connected :=
    (graphOfEdgesOn_relabel_connected_iff σ
      (confineSet E hsub)).mpr
      (confined_connected hm hsub hconn)
  rw [graphOfEdgesOn_fin] at h1
  have h2 := connected_card_availableEdges_ge h1
  rw [availableEdges_graphOfEdges] at h2
  rw [card_relabelSetOn] at h2
  have h3 := card_confineSet_le E hsub
  omega

/-! ## VI-A.4b — the per-block PINCH: connectivity forces each
    block to have EXACTLY |itree| + 1 vertices (pointwise ≤ from
    the generic bound, equality from the two global sum identities
    — the 40b argument distributed over the blocks) -/

/-- The sum of the block cardinalities of any ordered
    decomposition is n (the blocks partition Fin n). -/
theorem OrderedDecomposition.sum_card_block
    (OD : OrderedDecomposition n k) :
    (∑ j, (OD.block j).card) = n := by
  have hcover : Finset.univ.biUnion OD.block
      = (Finset.univ : Finset (Fin n)) := by
    ext v
    constructor
    · intro _
      exact Finset.mem_univ v
    · intro _
      obtain ⟨j, hj⟩ := OD.cover v
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hj⟩
  have hdisj : ∀ j₁ ∈ (Finset.univ : Finset (Fin k)),
      ∀ j₂ ∈ (Finset.univ : Finset (Fin k)), j₁ ≠ j₂ →
      Disjoint (OD.block j₁) (OD.block j₂) :=
    fun j₁ _ j₂ _ h => OD.disj j₁ j₂ h
  have h := Finset.card_biUnion hdisj
  rw [hcover] at h
  rw [← h, Finset.card_univ, Fintype.card_fin]

/-- **VI-A.4b CAPSTONE (the pinch)**: in every ordered
    decomposition each internal tree has exactly one edge less than
    its block has vertices. Pointwise ≤ from the generic bound; the
    global cardSum and the partition sum close the gap through
    `Finset.sum_lt_sum`. -/
theorem OrderedDecomposition.card_itree_add_one
    (OD : OrderedDecomposition n k) (j : Fin k) :
    (OD.itree j).card + 1 = (OD.block j).card := by
  have hle : ∀ i : Fin k,
      (OD.block i).card ≤ (OD.itree i).card + 1 :=
    fun i => block_card_le_edges_add_one (OD.marked_mem i)
      (OD.sub i) (OD.conn i)
  have hsum1 : (∑ i, (OD.block i).card) = n :=
    OD.sum_card_block
  have hsum2 : (∑ i : Fin k, ((OD.itree i).card + 1)) = n := by
    rw [Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    exact OD.cardSum
  by_contra hne
  have hlt : (OD.block j).card < (OD.itree j).card + 1 := by
    have := hle j
    omega
  have hstrict := Finset.sum_lt_sum
    (f := fun i => (OD.block i).card)
    (g := fun i => (OD.itree i).card + 1)
    (fun i _ => hle i) ⟨j, Finset.mem_univ j, hlt⟩
  have h5 : (∑ i : Fin k, (OD.block i).card)
      < (∑ i : Fin k, ((OD.itree i).card + 1)) := hstrict
  omega

/-- The decompose-image form: internal trees of a spanning tree
    have exactly componentSize edges. -/
theorem card_orderedInternalTree
    {ET : Finset (OrderedEdge (n + 1))}
    (hET : ET ∈ treesWithKRootNeighbors n k)
    (e : RootEnumeration ET k) (j : Fin k) :
    (orderedInternalTree ET e j).card = componentSize ET e j := by
  have h1 := (decompose hET e).card_itree_add_one j
  have h2 := card_orderedRootBlock ET e j
  -- decompose fields are definitionally the ordered pieces
  have h3 : (decompose hET e).itree j = orderedInternalTree ET e j :=
    rfl
  have h4 : (decompose hET e).block j = orderedRootBlock ET e j :=
    rfl
  rw [h3, h4] at h1
  omega

/-! ## VI-A.5 — the per-block datum (fully local: no global
    coupling; the cardinal is a FIELD, delivered by the pinch) -/

/-- All the local data of one labelled block: the mark, the
    internal tree (with its confinement, reachability and EXACT
    cardinal), the root value and the tail values. Everything a
    block contributes to the weight, nothing global. -/
structure BlockDatum (N : ℕ) [NeZero N] [Fintype (Site N)]
    {n : ℕ} (B : Finset (Fin n)) : Type where
  marked : Fin n
  marked_mem : marked ∈ B
  itree : Finset (OrderedEdge (n + 1))
  sub : ∀ ed ∈ itree,
    ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ
  conn : ∀ v ∈ B,
    (graphOfEdges itree).Reachable v.succ marked.succ
  cardEq : itree.card + 1 = B.card
  rootValue : Polymer N
  tailValue : {x // x ∈ B.erase marked} → Polymer N

/-- Extensionality through the EXTENDED tail function (the
    dif-extension aligns the dependent domains; the atlas pattern
    of reconstructAssignment). -/
theorem BlockDatum.ext_of_extended {B : Finset (Fin n)}
    {D₁ D₂ : BlockDatum N B}
    (hm : D₁.marked = D₂.marked) (hi : D₁.itree = D₂.itree)
    (hr : D₁.rootValue = D₂.rootValue)
    (ht : (fun v : Fin n =>
        if h : v ∈ B.erase D₁.marked then D₁.tailValue ⟨v, h⟩
        else D₁.rootValue)
      = (fun v : Fin n =>
        if h : v ∈ B.erase D₂.marked then D₂.tailValue ⟨v, h⟩
        else D₂.rootValue)) : D₁ = D₂ := by
  obtain ⟨m₁, mm₁, i₁, s₁, c₁, ce₁, r₁, t₁⟩ := D₁
  obtain ⟨m₂, mm₂, i₂, s₂, c₂, ce₂, r₂, t₂⟩ := D₂
  dsimp only at hm hi hr ht
  subst hm
  subst hi
  subst hr
  have h5 : t₁ = t₂ := by
    funext x
    have h6 := congrFun ht x.val
    rw [dif_pos x.property, dif_pos x.property] at h6
    exact h6
  subst h5
  rfl

/-- Fintype for the block data, by injection into a plain
    quadruple (the tail extended by dif to a total function). -/
noncomputable instance {B : Finset (Fin n)} :
    Fintype (BlockDatum N B) :=
  Fintype.ofInjective
    (fun D =>
      ((D.marked, D.itree, D.rootValue,
        fun v : Fin n =>
          if h : v ∈ B.erase D.marked then D.tailValue ⟨v, h⟩
          else D.rootValue)
        : Fin n × Finset (OrderedEdge (n + 1)) × Polymer N
            × (Fin n → Polymer N)))
    (fun D₁ D₂ h => by
      have h1 : D₁.marked = D₂.marked :=
        congrArg (fun x => x.1) h
      have h2 : D₁.itree = D₂.itree :=
        congrArg (fun x => x.2.1) h
      have h3 : D₁.rootValue = D₂.rootValue :=
        congrArg (fun x => x.2.2.1) h
      have h4 := congrArg (fun x => x.2.2.2) h
      exact BlockDatum.ext_of_extended h1 h2 h3 h4)

/-! ## VI-A.5b — assembly and extraction (the two directions of the
    profiled repackaging, all fields shuffled, nothing recomputed) -/

theorem OrderedDecomposition.erase_card_add_one
    (OD : OrderedDecomposition n k) (j : Fin k) :
    ((OD.block j).erase (OD.marked j)).card + 1
      = (OD.block j).card := by
  have h2 := Finset.card_erase_of_mem (OD.marked_mem j)
  have h3 : 0 < (OD.block j).card :=
    Finset.card_pos.mpr ⟨OD.marked j, OD.marked_mem j⟩
  omega

theorem OrderedDecomposition.blockTail_card_lt
    (OD : OrderedDecomposition n k) (j : Fin k) :
    ((OD.block j).erase (OD.marked j)).card < n + 1 := by
  have h1 : ((OD.block j).erase (OD.marked j)).card
      ≤ Fintype.card (Fin n) := Finset.card_le_univ _
  rw [Fintype.card_fin] at h1
  omega

/-- The size profile READ OFF a decomposition (tail cardinalities —
    no truncated subtraction anywhere). -/
noncomputable def profileOfOD (OD : OrderedDecomposition n k) :
    SizeProfile n k :=
  ⟨fun j => ⟨((OD.block j).erase (OD.marked j)).card,
      OD.blockTail_card_lt j⟩, by
    show (∑ j : Fin k,
        (((OD.block j).erase (OD.marked j)).card + 1)) = n
    calc (∑ j : Fin k,
        (((OD.block j).erase (OD.marked j)).card + 1))
        = ∑ j, (OD.block j).card :=
          Finset.sum_congr rfl
            (fun j _ => OD.erase_card_add_one j)
      _ = n := OD.sum_card_block⟩

/-- The ordered partition READ OFF a decomposition. -/
noncomputable def partitionOfOD (OD : OrderedDecomposition n k) :
    OrderedPartition (profileNat (profileOfOD OD)) n where
  block := OD.block
  card_block := fun j => by
    show (OD.block j).card
      = ((OD.block j).erase (OD.marked j)).card + 1
    exact (OD.erase_card_add_one j).symm
  cover := OD.cover
  disj := OD.disj

/-- The per-block data READ OFF a decomposition and an assignment
    (the pinch delivers the cardinal field). -/
noncomputable def datumOfOD (OD : OrderedDecomposition n k)
    (A : OrderedAssignmentData (N := N) OD) (j : Fin k) :
    BlockDatum N ((partitionOfOD OD).block j) where
  marked := OD.marked j
  marked_mem := OD.marked_mem j
  itree := OD.itree j
  sub := OD.sub j
  conn := OD.conn j
  cardEq := by
    show (OD.itree j).card + 1 = (OD.block j).card
    exact OD.card_itree_add_one j
  rootValue := A.rootValue j
  tailValue := A.tailValue j

/-- The decomposition ASSEMBLED from profiled data (cardSum derived
    from the per-block cardinal fields and the profile identity —
    the blocks are fully independent). -/
noncomputable def assembledOD {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) :
    OrderedDecomposition n k where
  block := P.block
  marked := fun j => (D j).marked
  itree := fun j => (D j).itree
  marked_mem := fun j => (D j).marked_mem
  marked_inj := by
    intro j₁ j₂ h
    have h' : (D j₁).marked = (D j₂).marked := h
    by_contra hne
    have h1 := (D j₁).marked_mem
    have h2 : (D j₁).marked ∈ P.block j₂ := by
      rw [h']
      exact (D j₂).marked_mem
    exact Finset.disjoint_left.mp (P.disj j₁ j₂ hne) h1 h2
  cover := P.cover
  disj := P.disj
  sub := fun j => (D j).sub
  conn := fun j => (D j).conn
  cardSum := by
    have h1 : ∀ j : Fin k,
        ((D j).itree).card = profileNat s j := by
      intro j
      have h2 := (D j).cardEq
      have h3 := P.card_block j
      omega
    calc (∑ j, ((D j).itree).card) + k
        = (∑ j, profileNat s j) + k :=
          congrArg (· + k)
            (Finset.sum_congr rfl (fun j _ => h1 j))
      _ = ∑ j, (profileNat s j + 1) := by
          rw [Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_univ, Fintype.card_fin, smul_eq_mul,
            mul_one]
      _ = n := s.2

/-- The assignment data ASSEMBLED from profiled data. -/
noncomputable def assembledData {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) :
    OrderedAssignmentData (N := N) (assembledOD P D) where
  rootValue := fun j => (D j).rootValue
  tailValue := fun j => (D j).tailValue

/-! ## VI-A.6 — the CENTRAL EQUIVALENCE -/

/-- The architect's alias: profile + labelled partition + fully
    local per-block data (the three-storey sigma, packaged). -/
abbrev ProfiledDecompositionData (N : ℕ) [NeZero N]
    [Fintype (Site N)] (n k : ℕ) : Type _ :=
  Σ s : SizeProfile n k,
    Σ P : OrderedPartition (profileNat s) n,
      ∀ j : Fin k, BlockDatum N (P.block j)

/-- Dependent extensionality for profiled data: profile values,
    blocks, then data (HEq resolved AFTER both substitutions — the
    circular-subst trap avoided by destructuring both sides). -/
theorem profiledData_ext {X Y : ProfiledDecompositionData N n k}
    (hs : X.1 = Y.1)
    (hblock : ∀ j, X.2.1.block j = Y.2.1.block j)
    (hdatum : ∀ j, HEq (X.2.2 j) (Y.2.2 j)) : X = Y := by
  obtain ⟨s₁, P₁, D₁⟩ := X
  obtain ⟨s₂, P₂, D₂⟩ := Y
  dsimp only at hs hblock hdatum
  subst hs
  have hP : P₁ = P₂ := OrderedPartition.ext' (funext hblock)
  subst hP
  have hD : D₁ = D₂ := funext (fun j => eq_of_heq (hdatum j))
  subst hD
  rfl

/-- **VI-A.6 CAPSTONE part 1: (decomposition, assignment) ≃
    profiled data** — both inverses; the decomposition roundtrip is
    definitional (structure and function eta); the profiled
    roundtrip needs exactly one propositional step, the REAL block
    cardinalities identifying the profile, as the architect
    demanded. -/
noncomputable def decompositionDataEquivProfiled :
    (Σ OD : OrderedDecomposition n k,
        OrderedAssignmentData (N := N) OD)
      ≃ ProfiledDecompositionData N n k where
  toFun X := ⟨profileOfOD X.1, partitionOfOD X.1,
    datumOfOD X.1 X.2⟩
  invFun Y := ⟨assembledOD Y.2.1 Y.2.2,
    assembledData Y.2.1 Y.2.2⟩
  left_inv X := by
    obtain ⟨OD, A⟩ := X
    rfl
  right_inv Y := by
    obtain ⟨s, P, D⟩ := Y
    refine profiledData_ext ?_ (fun j => rfl) (fun j => HEq.rfl)
    refine SizeProfile.ext' (fun j => Fin.ext ?_)
    show ((P.block j).erase ((D j).marked)).card = (s.1 j : ℕ)
    have h1 := Finset.card_erase_of_mem (D j).marked_mem
    have h2 := P.card_block j
    have h2' : (P.block j).card = (s.1 j : ℕ) + 1 := h2
    have h3 : 0 < (P.block j).card :=
      Finset.card_pos.mpr ⟨(D j).marked, (D j).marked_mem⟩
    omega

/-- **VI-A.6 CAPSTONE: the central equivalence** — enumerated tree
    + global assignment ≃ profile + partition + local block data,
    assembled from Gates II and III and the profiled repackaging;
    every arrow an equivalence, no surjection-and-count. -/
noncomputable def enumeratedDataEquivProfiled :
    EnumeratedRootDegreeData N n k
      ≃ ProfiledDecompositionData N n k :=
  (Equiv.prodCongr enumeratedTree_equiv_orderedDecomposition
      (Equiv.refl (Fin n → Polymer N))).trans
    ((Equiv.sigmaEquivProd (OrderedDecomposition n k)
        (Fin n → Polymer N)).symm.trans
      ((Equiv.sigmaCongrRight
          (fun OD => globalAssignmentEquivOrderedAssignments
            (N := N) OD)).trans
        decompositionDataEquivProfiled))

/-! ## VI-A.7 — weight preservation -/

/-- The weight of profiled data: a PRODUCT of local factors — each
    factor depends on one block's datum (the mark's activity and
    incompatibility explicitly; the internal weight through the
    Gate-III local weight of the assembled decomposition). -/
noncomputable def profiledWeight (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (Y : ProfiledDecompositionData N n k) : ℝ :=
  ∏ j : Fin k,
    (incompatibilityIndicator γ₀ ((Y.2.2 j).rootValue)
      * ρ ((Y.2.2 j).rootValue)
      * orderedInternalRootedWeight ρ γ₀
          (reconstructAssignment (assembledOD Y.2.1 Y.2.2)
            (assembledData Y.2.1 Y.2.2))
          (assembledOD Y.2.1 Y.2.2) j)

/-- **VI-A.7, pointwise**: the central equivalence preserves the
    weight EXACTLY (Gate III consumed; the only propositional step
    is the Gate-III roundtrip of the assignment). -/
theorem enumeratedDataWeight_eq_profiledWeight
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N)
    (X : EnumeratedRootDegreeData N n k) :
    enumeratedDataWeight ρ γ₀ X
      = profiledWeight ρ γ₀ (enumeratedDataEquivProfiled X) := by
  obtain ⟨T, γ⟩ := X
  have hγ : reconstructAssignment (decompose T.mem T.enum)
      (decomposeAssignment (decompose T.mem T.enum) γ) = γ :=
    (globalAssignmentEquivOrderedAssignments
      (N := N) (decompose T.mem T.enum)).left_inv γ
  calc enumeratedDataWeight ρ γ₀ (T, γ)
      = rootedTreeWeight ρ γ₀ γ T.ET := rfl
    _ = ∏ j : Fin k,
          (incompatibilityIndicator γ₀
              (orderedRootValue γ (decompose T.mem T.enum) j)
            * ρ (orderedRootValue γ (decompose T.mem T.enum) j)
            * orderedInternalRootedWeight ρ γ₀ γ
                (decompose T.mem T.enum) j) :=
        enumeratedTreeWeight_factorization ρ γ₀ γ T.mem T.enum
    _ = profiledWeight ρ γ₀
          (enumeratedDataEquivProfiled (T, γ)) := by
        unfold profiledWeight
        refine Finset.prod_congr rfl (fun j _ => ?_)
        show incompatibilityIndicator γ₀
              (orderedRootValue γ (decompose T.mem T.enum) j)
            * ρ (orderedRootValue γ (decompose T.mem T.enum) j)
            * orderedInternalRootedWeight ρ γ₀ γ
                (decompose T.mem T.enum) j
          = incompatibilityIndicator γ₀
              (orderedRootValue γ (decompose T.mem T.enum) j)
            * ρ (orderedRootValue γ (decompose T.mem T.enum) j)
            * orderedInternalRootedWeight ρ γ₀
                (reconstructAssignment (decompose T.mem T.enum)
                  (decomposeAssignment
                    (decompose T.mem T.enum) γ))
                (decompose T.mem T.enum) j
        rw [hγ]

/-- **VI-A.7 CAPSTONE: the sums coincide** — one reindexation by
    the central equivalence, nothing else. -/
theorem enumeratedData_sum_eq_profiledData_sum
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    (∑ X : EnumeratedRootDegreeData N n k,
        enumeratedDataWeight ρ γ₀ X)
      = ∑ Y : ProfiledDecompositionData N n k,
          profiledWeight ρ γ₀ Y := by
  rw [← Equiv.sum_comp
    (enumeratedDataEquivProfiled (N := N) (n := n) (k := k))
    (profiledWeight ρ γ₀)]
  exact Finset.sum_congr rfl
    (fun X _ => enumeratedDataWeight_eq_profiledWeight ρ γ₀ X)

/-! ## VI-B.0a — the per-block tree correspondence: ambient
    confined trees ↔ intrinsic trees on ↥B (the bridge that lets
    Gate IV-B's fixedRootBlockSum consume the profiled data; edge
    maps with both roundtrips, no counting arguments) -/

/-- The order equivalence between a block and its succ-image. -/
noncomputable def blockSuccEquiv (B : Finset (Fin n)) :
    {x // x ∈ B} ≃ {y // y ∈ B.image Fin.succ} :=
  Equiv.ofBijective
    (fun v => ⟨v.val.succ, Finset.mem_image_of_mem _ v.property⟩)
    ⟨fun a b h => Subtype.ext
        (Fin.succ_injective n (congrArg Subtype.val h)),
      fun y => by
        obtain ⟨b, hb, hy⟩ := Finset.mem_image.mp y.property
        exact ⟨⟨b, hb⟩, Subtype.ext hy⟩⟩

theorem blockSuccEquiv_strictMono (B : Finset (Fin n)) :
    StrictMono (blockSuccEquiv B) := by
  intro a b h
  exact Fin.strictMono_succ h

theorem blockSuccEquiv_symm_lt {B : Finset (Fin n)}
    {x y : {y // y ∈ B.image Fin.succ}} (h : x < y) :
    (blockSuccEquiv B).symm x < (blockSuccEquiv B).symm y := by
  rw [← (blockSuccEquiv_strictMono B).lt_iff_lt,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h

theorem blockSuccEquiv_symm_val_succ {B : Finset (Fin n)}
    (y : {y // y ∈ B.image Fin.succ}) :
    ((blockSuccEquiv B).symm y).val.succ = y.val := by
  have h := (blockSuccEquiv B).apply_symm_apply y
  exact congrArg Subtype.val h

/-- Confinement is edge-injective, so the cardinal is EXACT. -/
theorem card_confineSet_eq {S : Finset (Fin (n + 1))}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E, ed.val.1 ∈ S ∧ ed.val.2 ∈ S) :
    (confineSet E hsub).card = E.card := by
  unfold confineSet
  rw [Finset.card_image_of_injective _ ?inj, Finset.card_attach]
  case inj =>
    intro x y h
    have h2 := congrArg (fun e : OrderedEdgeOn {z // z ∈ S} =>
      (((e.val.1 : Fin (n + 1)), (e.val.2 : Fin (n + 1)))
        : Fin (n + 1) × Fin (n + 1))) h
    dsimp only [confineEdge] at h2
    exact Subtype.ext (Subtype.ext h2)

/-- The intrinsic tree of an ambient confined edge set: confine,
    then relabel the succ-image back onto the block. -/
noncomputable def intrinsicBlockTree {B : Finset (Fin n)}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ) :
    Finset (OrderedEdgeOn {x // x ∈ B}) :=
  relabelSetOn (blockSuccEquiv B).symm (confineSet E hsub)

theorem card_intrinsicBlockTree {B : Finset (Fin n)}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ) :
    (intrinsicBlockTree E hsub).card = E.card := by
  unfold intrinsicBlockTree
  rw [card_relabelSetOn, card_confineSet_eq]

/-- **Membership in the intrinsic tree universe**: a block datum's
    tree lands in connTreesOn ↥B (connectivity from the confined
    walks; the cardinal from the pinch field). -/
theorem intrinsicBlockTree_mem_connTreesOn {B : Finset (Fin n)}
    {m : Fin n} (hm : m ∈ B)
    {E : Finset (OrderedEdge (n + 1))}
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ)
    (hconn : ∀ v ∈ B, (graphOfEdges E).Reachable v.succ m.succ)
    (hcard : E.card + 1 = B.card) :
    intrinsicBlockTree E hsub ∈ connTreesOn {x // x ∈ B} := by
  refine mem_connTreesOn.mpr ⟨?_, ?_⟩
  · exact (graphOfEdgesOn_relabel_connected_iff
      (blockSuccEquiv B).symm (confineSet E hsub)).mpr
      (confined_connected hm hsub hconn)
  · rw [card_intrinsicBlockTree, Fintype.card_coe]
    exact hcard

/-- Ambientization of one intrinsic edge (succ of both endpoints —
    strictly monotone, so the orientation survives). -/
def ambientEdge {B : Finset (Fin n)}
    (ed : OrderedEdgeOn {x // x ∈ B}) : OrderedEdge (n + 1) :=
  ⟨(ed.val.1.val.succ, ed.val.2.val.succ),
    Fin.strictMono_succ ed.property⟩

theorem ambientEdge_injective {B : Finset (Fin n)} :
    Function.Injective (ambientEdge (B := B)) := by
  intro x y h
  have h2 := congrArg
    (fun e : OrderedEdge (n + 1) => (e.val.1, e.val.2)) h
  dsimp only [ambientEdge] at h2
  have h3 : x.val.1.val.succ = y.val.1.val.succ :=
    congrArg Prod.fst h2
  have h4 : x.val.2.val.succ = y.val.2.val.succ :=
    congrArg Prod.snd h2
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact Subtype.ext (Fin.succ_injective n h3)
  · exact Subtype.ext (Fin.succ_injective n h4)

/-- Ambientization of an intrinsic edge set. -/
noncomputable def ambientBlockTree {B : Finset (Fin n)}
    (F : Finset (OrderedEdgeOn {x // x ∈ B})) :
    Finset (OrderedEdge (n + 1)) :=
  F.image ambientEdge

theorem card_ambientBlockTree {B : Finset (Fin n)}
    (F : Finset (OrderedEdgeOn {x // x ∈ B})) :
    (ambientBlockTree F).card = F.card :=
  Finset.card_image_of_injective _ ambientEdge_injective

theorem ambientBlockTree_sub {B : Finset (Fin n)}
    (F : Finset (OrderedEdgeOn {x // x ∈ B})) :
    ∀ ed ∈ ambientBlockTree F,
      ed.val.1 ∈ B.image Fin.succ
        ∧ ed.val.2 ∈ B.image Fin.succ := by
  intro ed hed
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hed
  constructor
  · exact Finset.mem_image_of_mem _ f.val.1.property
  · exact Finset.mem_image_of_mem _ f.val.2.property

/-- Intrinsic adjacency ambientizes (per edge, both
    orientations). -/
theorem ambient_adj_of_intrinsic {B : Finset (Fin n)}
    {F : Finset (OrderedEdgeOn {x // x ∈ B})}
    {a b : {x // x ∈ B}} (h : (graphOfEdgesOn F).Adj a b) :
    (graphOfEdges (ambientBlockTree F)).Adj
      a.val.succ b.val.succ := by
  rcases h with ⟨hlt, hmem⟩ | ⟨hlt, hmem⟩
  · refine Or.inl ⟨Fin.strictMono_succ hlt, ?_⟩
    exact Finset.mem_image_of_mem _ hmem
  · refine Or.inr ⟨Fin.strictMono_succ hlt, ?_⟩
    exact Finset.mem_image_of_mem _ hmem

/-- Intrinsic walks ambientize step by step. -/
theorem ambient_reachable_of_intrinsic {B : Finset (Fin n)}
    {F : Finset (OrderedEdgeOn {x // x ∈ B})}
    {a b : {x // x ∈ B}}
    (h : (graphOfEdgesOn F).Reachable a b) :
    (graphOfEdges (ambientBlockTree F)).Reachable
      a.val.succ b.val.succ := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons x y z hadj p ih =>
      exact SimpleGraph.Reachable.trans
        (SimpleGraph.Adj.reachable
          (ambient_adj_of_intrinsic hadj)) ih

/-- **The ambient conn field from intrinsic connectivity**: every
    block vertex reaches the mark through the ambientized tree. -/
theorem ambientBlockTree_conn {B : Finset (Fin n)} {m : Fin n}
    (hm : m ∈ B) {F : Finset (OrderedEdgeOn {x // x ∈ B})}
    (hF : (graphOfEdgesOn F).Connected) :
    ∀ v ∈ B, (graphOfEdges (ambientBlockTree F)).Reachable
      v.succ m.succ := by
  intro v hv
  exact ambient_reachable_of_intrinsic (hF.preconnected ⟨v, hv⟩ ⟨m, hm⟩)

/-! ## VI-B.0a — the two roundtrips (edge level, then set level) -/

/-- Edge roundtrip 1: ambientize after confine-and-relabel is the
    identity (the strict monotonicity keeps every canonicalization
    in its of_lt branch). -/
theorem relabel_confine_ambient_edge {B : Finset (Fin n)}
    {ed : OrderedEdge (n + 1)}
    (h1 : ed.val.1 ∈ B.image Fin.succ)
    (h2 : ed.val.2 ∈ B.image Fin.succ) :
    ambientEdge (relabelFunOn (blockSuccEquiv B).symm
      (confineEdge ed h1 h2)) = ed := by
  unfold relabelFunOn confineEdge
  rw [canonicalOrderedEdgeOn_of_lt
    (blockSuccEquiv_symm_lt (Subtype.mk_lt_mk.mpr ed.property))]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact blockSuccEquiv_symm_val_succ ⟨ed.val.1, h1⟩
  · exact blockSuccEquiv_symm_val_succ ⟨ed.val.2, h2⟩

/-- Edge roundtrip 2: confine-and-relabel after ambientize is the
    identity. -/
theorem confine_relabel_ambient_edge {B : Finset (Fin n)}
    (f : OrderedEdgeOn {x // x ∈ B})
    (h1 : (ambientEdge f).val.1 ∈ B.image Fin.succ)
    (h2 : (ambientEdge f).val.2 ∈ B.image Fin.succ) :
    relabelFunOn (blockSuccEquiv B).symm
      (confineEdge (ambientEdge f) h1 h2) = f := by
  unfold relabelFunOn confineEdge
  have hx : (⟨(ambientEdge f).val.1, h1⟩
      : {y // y ∈ B.image Fin.succ}) = blockSuccEquiv B f.val.1 :=
    Subtype.ext rfl
  have hy : (⟨(ambientEdge f).val.2, h2⟩
      : {y // y ∈ B.image Fin.succ}) = blockSuccEquiv B f.val.2 :=
    Subtype.ext rfl
  have hlt : (blockSuccEquiv B).symm
        (⟨(ambientEdge f).val.1, h1⟩ : {y // y ∈ B.image Fin.succ})
      < (blockSuccEquiv B).symm ⟨(ambientEdge f).val.2, h2⟩ := by
    rw [hx, hy, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact f.property
  rw [canonicalOrderedEdgeOn_of_lt hlt]
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show (blockSuccEquiv B).symm ⟨(ambientEdge f).val.1, h1⟩
      = f.val.1
    rw [hx, Equiv.symm_apply_apply]
  · show (blockSuccEquiv B).symm ⟨(ambientEdge f).val.2, h2⟩
      = f.val.2
    rw [hy, Equiv.symm_apply_apply]

/-- Set roundtrip 1: ambientizing the intrinsic tree recovers the
    ambient edge set. -/
theorem ambient_intrinsicBlockTree {B : Finset (Fin n)}
    (E : Finset (OrderedEdge (n + 1)))
    (hsub : ∀ ed ∈ E,
      ed.val.1 ∈ B.image Fin.succ ∧ ed.val.2 ∈ B.image Fin.succ) :
    ambientBlockTree (intrinsicBlockTree E hsub) = E := by
  ext ed
  unfold ambientBlockTree intrinsicBlockTree
  constructor
  · intro hed
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hed
    have hf2 := mem_relabelSetOn.mp hf
    -- hf2 : relabelFunOn σ.symm.symm f ∈ confineSet E hsub
    rw [Equiv.symm_symm] at hf2
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hf2
    -- hx : confineEdge x.val … = relabelFunOn (blockSuccEquiv B) f
    have h3 : relabelFunOn (blockSuccEquiv B).symm
        (confineEdge x.val (hsub x.val x.property).1
          (hsub x.val x.property).2)
        = relabelFunOn (blockSuccEquiv B).symm
            (relabelFunOn (blockSuccEquiv B) f) :=
      congrArg _ hx
    rw [relabelFunOn_symm_cancel] at h3
    rw [← h3, relabel_confine_ambient_edge]
    exact x.property
  · intro hed
    refine Finset.mem_image.mpr
      ⟨relabelFunOn (blockSuccEquiv B).symm
        (confineEdge ed (hsub ed hed).1 (hsub ed hed).2), ?_, ?_⟩
    · exact mem_relabelSetOn.mpr (by
        rw [Equiv.symm_symm, relabelFunOn_symm_cancel']
        exact confineEdge_mem_confineSet hsub hed)
    · exact relabel_confine_ambient_edge (hsub ed hed).1
        (hsub ed hed).2

/-- Set roundtrip 2: the intrinsic tree of an ambientized set is
    the original intrinsic set. -/
theorem intrinsic_ambientBlockTree {B : Finset (Fin n)}
    (F : Finset (OrderedEdgeOn {x // x ∈ B})) :
    intrinsicBlockTree (ambientBlockTree F)
      (ambientBlockTree_sub F) = F := by
  ext g
  unfold intrinsicBlockTree
  rw [mem_relabelSetOn, Equiv.symm_symm]
  unfold confineSet
  constructor
  · intro hg
    obtain ⟨x, -, hx⟩ := Finset.mem_image.mp hg
    obtain ⟨xv, hxv⟩ := x
    obtain ⟨f, hf, hfx⟩ := Finset.mem_image.mp hxv
    subst hfx
    have h5 := congrArg (relabelFunOn (blockSuccEquiv B).symm) hx
    rw [relabelFunOn_symm_cancel] at h5
    rw [confine_relabel_ambient_edge] at h5
    rw [← h5]
    exact hf
  · intro hg
    refine Finset.mem_image.mpr
      ⟨⟨ambientEdge g, Finset.mem_image_of_mem _ hg⟩,
        Finset.mem_attach _ _, ?_⟩
    have h8 := congrArg (relabelFunOn (blockSuccEquiv B)) 
      (confine_relabel_ambient_edge g
        ((ambientBlockTree_sub F) (ambientEdge g)
          (Finset.mem_image_of_mem _ hg)).1
        ((ambientBlockTree_sub F) (ambientEdge g)
          (Finset.mem_image_of_mem _ hg)).2)
    rw [relabelFunOn_symm_cancel'] at h8
    exact h8

/-! ## VI-B.0b — the block sum lands EXACTLY on
    fixedRootBlockSum: local assignment extension, the (r, η) fiber
    equivalence with EXACT weight preservation (the architect's hard
    stop: no cardinality-only arguments), and the capstone that
    produces markedBlockContribution by literally summing r and η.
    NO factorial in this subgate. -/

/-- The local assignment of a block datum on ↥B (mark ↦ root value,
    tail ↦ tail values — the dif-extension). -/
noncomputable def blockAssign {B : Finset (Fin n)}
    (d : BlockDatum N B) : {x // x ∈ B} → Polymer N :=
  fun v =>
    if h : v.val ∈ B.erase d.marked then d.tailValue ⟨v.val, h⟩
    else d.rootValue

/-- The payload extension for a FIXED mark and root value. -/
noncomputable def extendTail {B : Finset (Fin n)} (r : {x // x ∈ B})
    (η : Polymer N)
    (t : {x // x ∈ B.erase r.val} → Polymer N) :
    {x // x ∈ B} → Polymer N :=
  fun v =>
    if h : v.val ∈ B.erase r.val then t ⟨v.val, h⟩ else η

theorem extendTail_root {B : Finset (Fin n)} (r : {x // x ∈ B})
    (η : Polymer N)
    (t : {x // x ∈ B.erase r.val} → Polymer N) :
    extendTail r η t r = η := by
  unfold extendTail
  rw [dif_neg]
  intro h
  exact (Finset.mem_erase.mp h).1 rfl

/-- Term-level evaluation on the tail (dif_pos, no tactics — the
    beta-reduction vaccine). -/
theorem extendTail_tail {B : Finset (Fin n)} (r : {x // x ∈ B})
    (η : Polymer N) (t : {x // x ∈ B.erase r.val} → Polymer N)
    (v : {x // x ∈ B}) (hv : v.val ∈ B.erase r.val) :
    extendTail r η t v = t ⟨v.val, hv⟩ :=
  dif_pos hv

/-- The internal weight of a block datum: intrinsic tree indicator
    (through the VI-B.0a correspondence) times the TAIL activities —
    the mark carries no activity here. -/
noncomputable def internalBlockWeight (ρ : Polymer N → ℝ)
    {B : Finset (Fin n)} (d : BlockDatum N B) : ℝ :=
  ((treeIndicatorOn (blockAssign d)
      (intrinsicBlockTree d.itree d.sub) : ℕ) : ℝ)
    * ∏ v : {x // x ∈ B.erase d.marked}, ρ (d.tailValue v)

/-- The full weight of a block datum: the mark's incompatibility
    with the external root and its activity stay OUTSIDE the
    internal weight. -/
noncomputable def blockDatumWeight (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {B : Finset (Fin n)}
    (d : BlockDatum N B) : ℝ :=
  (incompatibilityIndicator γ₀ d.rootValue : ℝ) * ρ d.rootValue
    * internalBlockWeight ρ d

/-- **VI-B.0b item 3: the fiber equivalence** — block data ≃
    (mark, root value, tail assignment, intrinsic rooted tree); the
    tree part consumes the VI-B.0a roundtrips, everything else is a
    field shuffle. -/
noncomputable def blockDatumEquivPayload (B : Finset (Fin n)) :
    BlockDatum N B
      ≃ Σ _r : {x // x ∈ B}, Σ _η : Polymer N,
          ({x // x ∈ B.erase _r.val} → Polymer N)
            × {E : Finset (OrderedEdgeOn {x // x ∈ B}) //
                E ∈ connTreesOn {x // x ∈ B}} where
  toFun d := ⟨⟨d.marked, d.marked_mem⟩, d.rootValue,
    (d.tailValue,
      ⟨intrinsicBlockTree d.itree d.sub,
        intrinsicBlockTree_mem_connTreesOn d.marked_mem d.sub
          d.conn d.cardEq⟩)⟩
  invFun X :=
    { marked := X.1.val
      marked_mem := X.1.property
      itree := ambientBlockTree X.2.2.2.val
      sub := ambientBlockTree_sub X.2.2.2.val
      conn := ambientBlockTree_conn X.1.property
        (mem_connTreesOn.mp X.2.2.2.property).1
      cardEq := by
        rw [card_ambientBlockTree]
        have h := (mem_connTreesOn.mp X.2.2.2.property).2
        rw [Fintype.card_coe] at h
        exact h
      rootValue := X.2.1
      tailValue := X.2.2.1 }
  left_inv d := by
    refine BlockDatum.ext_of_extended rfl ?_ rfl rfl
    exact ambient_intrinsicBlockTree d.itree d.sub
  right_inv X := by
    obtain ⟨r, η, t, E⟩ := X
    exact congrArg
      (fun z : {E : Finset (OrderedEdgeOn {x // x ∈ B}) //
          E ∈ connTreesOn {x // x ∈ B}} =>
        (⟨r, η, (t, z)⟩ : Σ _r : {x // x ∈ B},
          Σ _η : Polymer N,
            ({x // x ∈ B.erase _r.val} → Polymer N)
              × {E : Finset (OrderedEdgeOn {x // x ∈ B}) //
                  E ∈ connTreesOn {x // x ∈ B}}))
      (Subtype.ext (intrinsic_ambientBlockTree E.val))

/-- The weight of an assembled payload, computed: the propositional
    step is exactly the VI-B.0a set roundtrip. -/
theorem blockDatumWeight_symm_payload (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {B : Finset (Fin n)} (r : {x // x ∈ B})
    (η : Polymer N) (t : {x // x ∈ B.erase r.val} → Polymer N)
    (E : {E : Finset (OrderedEdgeOn {x // x ∈ B}) //
        E ∈ connTreesOn {x // x ∈ B}}) :
    blockDatumWeight ρ γ₀
        ((blockDatumEquivPayload B).symm ⟨r, η, (t, E)⟩)
      = (incompatibilityIndicator γ₀ η : ℝ) * ρ η
          * (((treeIndicatorOn (extendTail r η t) E.val : ℕ) : ℝ)
              * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v)) := by
  show (incompatibilityIndicator γ₀ η : ℝ) * ρ η
      * (((treeIndicatorOn (extendTail r η t)
            (intrinsicBlockTree (ambientBlockTree E.val)
              (ambientBlockTree_sub E.val)) : ℕ) : ℝ)
          * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v))
    = (incompatibilityIndicator γ₀ η : ℝ) * ρ η
        * (((treeIndicatorOn (extendTail r η t) E.val : ℕ) : ℝ)
            * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v))
  rw [intrinsic_ambientBlockTree E.val]

/-- **VI-B.0b item 4 (the hard stop): the (r, η)-fiber sum IS the
    fixedRootBlockSum** — δ-space reindexed by tail assignments
    (extend/restrict, both inverses inside the sum_bij), the
    indicator carried verbatim, the activity reindexed along the
    erase bijection. ρ(η) and γ₀ do NOT enter. -/
theorem sum_tail_tree_eq_fixedRootBlockSum (ρ : Polymer N → ℝ)
    {B : Finset (Fin n)} (r : {x // x ∈ B}) (η : Polymer N) :
    (∑ t : {x // x ∈ B.erase r.val} → Polymer N,
      ∑ E ∈ connTreesOn {x // x ∈ B},
        ((treeIndicatorOn (extendTail r η t) E : ℕ) : ℝ)
          * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v))
      = fixedRootBlockSum ρ B r η := by
  unfold fixedRootBlockSum rootedTreeSumOn
  refine (Finset.sum_bij
    (i := fun t _ => extendTail r η t) ?hi ?inj ?surj ?wt).symm.symm
  case hi =>
    intro t _
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, extendTail_root r η t⟩
  case inj =>
    intro t₁ _ t₂ _ h
    have h' : extendTail r η t₁ = extendTail r η t₂ := h
    funext v
    have h2 := congrFun h'
      ⟨v.val, Finset.mem_of_mem_erase v.property⟩
    exact ((extendTail_tail r η t₁
        ⟨v.val, Finset.mem_of_mem_erase v.property⟩
        v.property).symm.trans h2).trans
      (extendTail_tail r η t₂
        ⟨v.val, Finset.mem_of_mem_erase v.property⟩ v.property)
  case surj =>
    intro δ hδ
    rw [Finset.mem_filter] at hδ
    refine ⟨fun u => δ ⟨u.val, Finset.mem_of_mem_erase u.property⟩,
      Finset.mem_univ _, ?_⟩
    show extendTail r η
      (fun u => δ ⟨u.val, Finset.mem_of_mem_erase u.property⟩) = δ
    funext v
    by_cases hv : v.val ∈ B.erase r.val
    · exact extendTail_tail r η _ v hv
    · have hvr : v = r := by
        refine Subtype.ext ?_
        by_contra hne
        exact hv (Finset.mem_erase.mpr ⟨hne, v.property⟩)
      rw [hvr]
      exact (extendTail_root r η _).trans hδ.2.symm
  case wt =>
    intro t _
    refine Finset.sum_congr rfl (fun E _ => ?_)
    unfold rootedTreeWeightOn rootedActivityOn
    congr 1
    refine (Finset.prod_bij
      (i := fun (v : {x // x ∈ B}) (hv : v ∈ Finset.univ.erase r) =>
        (⟨v.val, Finset.mem_erase.mpr
          ⟨fun h => (Finset.mem_erase.mp hv).1 (Subtype.ext h),
            v.property⟩⟩ : {x // x ∈ B.erase r.val}))
      ?_ ?_ ?_ ?_).symm
    · intro v _
      exact Finset.mem_univ _
    · intro v₁ hv₁ v₂ hv₂ h
      have h2 := congrArg
        (fun z : {x // x ∈ B.erase r.val} => z.val) h
      have h3 : v₁.val = v₂.val := h2
      exact Subtype.ext h3
    · intro u _
      refine ⟨⟨u.val, Finset.mem_of_mem_erase u.property⟩,
        Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, ?_⟩
      · intro h
        exact (Finset.mem_erase.mp u.property).1
          (congrArg Subtype.val h)
      · exact Subtype.ext rfl
    · intro v hv
      have hvv : v.val ∈ B.erase r.val := Finset.mem_erase.mpr
        ⟨fun h => (Finset.mem_erase.mp hv).1 (Subtype.ext h),
          v.property⟩
      exact congrArg ρ (extendTail_tail r η t v hvv)

/-- **VI-B.0b CAPSTONE: the block sum IS the marked-block
    contribution** — summing the mark and the root value over the
    fiber identity; markedBlockContribution consumed by DEFINITION
    only. No factorial, no kpTreeCoeff, no partitions. -/
theorem sum_blockDatumWeight_eq_markedBlockContribution
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) (B : Finset (Fin n)) :
    (∑ d : BlockDatum N B, blockDatumWeight ρ γ₀ d)
      = markedBlockContribution ρ γ₀ B := by
  rw [← Equiv.sum_comp (blockDatumEquivPayload (N := N) B).symm
    (blockDatumWeight ρ γ₀)]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  unfold markedBlockContribution
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Fintype.sum_prod_type]
  calc (∑ t : {x // x ∈ B.erase r.val} → Polymer N,
        ∑ E : {E : Finset (OrderedEdgeOn {x // x ∈ B}) //
            E ∈ connTreesOn {x // x ∈ B}},
          blockDatumWeight ρ γ₀
            ((blockDatumEquivPayload B).symm ⟨r, η, (t, E)⟩))
      = ∑ t : {x // x ∈ B.erase r.val} → Polymer N,
          ∑ E ∈ connTreesOn {x // x ∈ B},
            (incompatibilityIndicator γ₀ η : ℝ) * ρ η
              * (((treeIndicatorOn (extendTail r η t) E : ℕ) : ℝ)
                  * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v)) := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.sum_coe_sort
          (s := connTreesOn {x // x ∈ B})
          (f := fun E =>
            (incompatibilityIndicator γ₀ η : ℝ) * ρ η
              * (((treeIndicatorOn (extendTail r η t) E : ℕ) : ℝ)
                  * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v)))
          |>.symm.symm.symm]
        exact Finset.sum_congr rfl (fun E _ =>
          blockDatumWeight_symm_payload ρ γ₀ r η t E)
    _ = (incompatibilityIndicator γ₀ η : ℝ) * ρ η
          * ∑ t : {x // x ∈ B.erase r.val} → Polymer N,
              ∑ E ∈ connTreesOn {x // x ∈ B},
                ((treeIndicatorOn (extendTail r η t) E : ℕ) : ℝ)
                  * ∏ v : {x // x ∈ B.erase r.val}, ρ (t v) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun t _ => ?_)
        rw [Finset.mul_sum]
    _ = (incompatibilityIndicator γ₀ η : ℝ) * ρ η
          * fixedRootBlockSum ρ B r η := by
        rw [sum_tail_tree_eq_fixedRootBlockSum]

/-! ## VI-B.0c — the profiled weight IS the product of block datum
    weights (the ambient/intrinsic indicator identification as its
    own theorem — NOT hidden inside the B.1 simp) -/

/-- Term-level evaluations of the block assignment (the dif
    vaccine). -/
theorem blockAssign_tail {B : Finset (Fin n)} (d : BlockDatum N B)
    (u : {x // x ∈ B}) (hv : u.val ∈ B.erase d.marked) :
    blockAssign d u = d.tailValue ⟨u.val, hv⟩ :=
  dif_pos hv

theorem blockAssign_root {B : Finset (Fin n)} (d : BlockDatum N B)
    (u : {x // x ∈ B}) (hv : ¬ u.val ∈ B.erase d.marked) :
    blockAssign d u = d.rootValue :=
  dif_neg hv

theorem reconstruct_eq_blockAssign {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) (j : Fin k)
    (u : {x // x ∈ P.block j}) :
    reconstructAssignment (assembledOD P D) (assembledData P D)
        u.val
      = blockAssign (D j) u := by
  by_cases hv : u.val ∈ (P.block j).erase ((D j).marked)
  · exact (reconstructAssignment_tail (assembledOD P D)
      (assembledData P D) (j := j) hv).trans
      (blockAssign_tail (D j) u hv).symm
  · have hu : u.val = (D j).marked := by
      by_contra hne
      exact hv (Finset.mem_erase.mpr ⟨hne, u.property⟩)
    rw [hu]
    exact (reconstructAssignment_marked (assembledOD P D)
      (assembledData P D) j).trans
      (blockAssign_root (D j) u hv).symm

/-- Per-edge identification: the ambient hard-core indicator on a
    confined edge equals the intrinsic edge indicator of the
    relabeled edge (rootedTuple_succ + the local values; the
    orientation survives, no symmetry needed). -/
theorem hcei_eq_edgeIndicatorOn (γ₀ : Polymer N)
    {s : SizeProfile n k} (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) (j : Fin k)
    {ed : OrderedEdge (n + 1)}
    (h1 : ed.val.1 ∈ (P.block j).image Fin.succ)
    (h2 : ed.val.2 ∈ (P.block j).image Fin.succ) :
    hardCoreEdgeIndicator
        (rootedTuple γ₀ (reconstructAssignment (assembledOD P D)
          (assembledData P D))) ed
      = edgeIndicatorOn (blockAssign (D j))
          (relabelFunOn (blockSuccEquiv (P.block j)).symm
            (confineEdge ed h1 h2)) := by
  unfold relabelFunOn confineEdge
  rw [canonicalOrderedEdgeOn_of_lt
    (blockSuccEquiv_symm_lt (Subtype.mk_lt_mk.mpr ed.property))]
  unfold hardCoreEdgeIndicator edgeIndicatorOn
  have h1s : ((blockSuccEquiv (P.block j)).symm
      ⟨ed.val.1, h1⟩).val.succ = ed.val.1 :=
    blockSuccEquiv_symm_val_succ ⟨ed.val.1, h1⟩
  have h2s : ((blockSuccEquiv (P.block j)).symm
      ⟨ed.val.2, h2⟩).val.succ = ed.val.2 :=
    blockSuccEquiv_symm_val_succ ⟨ed.val.2, h2⟩
  have e1 : rootedTuple γ₀ (reconstructAssignment (assembledOD P D)
      (assembledData P D)) ed.val.1
      = (blockAssign (D j)
          ((blockSuccEquiv (P.block j)).symm ⟨ed.val.1, h1⟩)).val := by
    rw [← h1s, rootedTuple_succ, reconstruct_eq_blockAssign P D j]
  have e2 : rootedTuple γ₀ (reconstructAssignment (assembledOD P D)
      (assembledData P D)) ed.val.2
      = (blockAssign (D j)
          ((blockSuccEquiv (P.block j)).symm ⟨ed.val.2, h2⟩)).val := by
    rw [← h2s, rootedTuple_succ, reconstruct_eq_blockAssign P D j]
  rw [e1, e2]

/-- The ambient internal indicator of an assembled decomposition IS
    the intrinsic tree indicator of the block datum. -/
theorem orderedInternalTreeIndicator_eq_treeIndicatorOn
    (γ₀ : Polymer N) {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) (j : Fin k) :
    orderedInternalTreeIndicator γ₀
        (reconstructAssignment (assembledOD P D)
          (assembledData P D)) (assembledOD P D) j
      = treeIndicatorOn (blockAssign (D j))
          (intrinsicBlockTree (D j).itree (D j).sub) := by
  unfold orderedInternalTreeIndicator treeIndicatorOn
  show (∏ ed ∈ (D j).itree, _) = _
  refine Finset.prod_bij
    (i := fun ed hed => relabelFunOn (blockSuccEquiv (P.block j)).symm
      (confineEdge ed ((D j).sub ed hed).1 ((D j).sub ed hed).2))
    ?_ ?_ ?_ ?_
  · intro ed hed
    exact mem_relabelSetOn.mpr (by
      rw [Equiv.symm_symm, relabelFunOn_symm_cancel']
      exact confineEdge_mem_confineSet (D j).sub hed)
  · intro ed₁ hed₁ ed₂ hed₂ h
    dsimp only at h
    have h2 := congrArg ambientEdge h
    rw [relabel_confine_ambient_edge, relabel_confine_ambient_edge]
      at h2
    exact h2
  · intro f hf
    have hmem : ambientEdge f ∈ (D j).itree := by
      rw [← ambient_intrinsicBlockTree (D j).itree (D j).sub]
      exact Finset.mem_image_of_mem _ hf
    refine ⟨ambientEdge f, hmem, ?_⟩
    dsimp only
    exact confine_relabel_ambient_edge f _ _
  · intro ed hed
    exact hcei_eq_edgeIndicatorOn γ₀ P D j
      ((D j).sub ed hed).1 ((D j).sub ed hed).2

/-- The ambient internal rooted weight equals the intrinsic
    internal block weight (indicator + tail activities; the mark
    and γ₀ carry no activity on either side). -/
theorem oIRW_eq_internalBlockWeight (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) (j : Fin k) :
    orderedInternalRootedWeight ρ γ₀
        (reconstructAssignment (assembledOD P D)
          (assembledData P D)) (assembledOD P D) j
      = internalBlockWeight ρ (D j) := by
  unfold orderedInternalRootedWeight internalBlockWeight
  rw [orderedInternalTreeIndicator_eq_treeIndicatorOn γ₀ P D j]
  exact congrArg
    (fun z => ((treeIndicatorOn (blockAssign (D j))
      (intrinsicBlockTree (D j).itree (D j).sub) : ℕ) : ℝ) * z)
    (Finset.prod_congr rfl (fun v _ => congrArg ρ
      (reconstructAssignment_tail (assembledOD P D)
        (assembledData P D) v.property)))

/-- **VI-B.0c CAPSTONE**: the VI-A profiled weight is EXACTLY the
    product of the local block datum weights. -/
theorem profiledWeight_eq_prod_blockDatumWeight (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n)
    (D : ∀ j : Fin k, BlockDatum N (P.block j)) :
    profiledWeight ρ γ₀ ⟨s, P, D⟩
      = ∏ j : Fin k, blockDatumWeight ρ γ₀ (D j) := by
  unfold profiledWeight blockDatumWeight
  refine Finset.prod_congr rfl (fun j _ => ?_)
  show (incompatibilityIndicator γ₀ ((D j).rootValue) : ℝ)
      * ρ ((D j).rootValue)
      * orderedInternalRootedWeight ρ γ₀
          (reconstructAssignment (assembledOD P D)
            (assembledData P D)) (assembledOD P D) j
    = (incompatibilityIndicator γ₀ ((D j).rootValue) : ℝ)
        * ρ ((D j).rootValue) * internalBlockWeight ρ (D j)
  rw [oIRW_eq_internalBlockWeight ρ γ₀ P D j]

/-! ## VI-B.1 — sum of products = product of sums -/

/-- The reusable dependent distributivity (prod_univ_sum +
    piFinset_univ, censused — no ad hoc induction). -/
theorem sum_pi_prod {k : ℕ} {A : Fin k → Type*} [∀ j, Fintype (A j)]
    (f : ∀ j, A j → ℝ) :
    (∑ d : ∀ j, A j, ∏ j, f j (d j))
      = ∏ j, ∑ x : A j, f j x := by
  rw [← Fintype.piFinset_univ]
  exact (Finset.prod_univ_sum _ _).symm

/-- **VI-B.1 CAPSTONE**: the local data sum factorizes over the
    labelled blocks. -/
theorem localBlockData_sum_eq_prod_markedBlockContribution
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n) :
    (∑ D : ∀ j : Fin k, BlockDatum N (P.block j),
        ∏ j, blockDatumWeight ρ γ₀ (D j))
      = ∏ j, markedBlockContribution ρ γ₀ (P.block j) := by
  rw [sum_pi_prod]
  exact Finset.prod_congr rfl (fun j _ =>
    sum_blockDatumWeight_eq_markedBlockContribution ρ γ₀
      (P.block j))

/-! ## VI-B.2 — F(B) block by block -/

/-- The single definition of G (the future kernel of the
    recurrence). -/
noncomputable def kpG (ρ : Polymer N → ℝ) (γ₀ : Polymer N)
    (m : ℕ) : ℝ :=
  ∑ η : Polymer N,
    (incompatibilityIndicator γ₀ η : ℝ) * ρ η * kpTreeCoeff m ρ η

/-- **VI-B.2**: the factorials of Gate IV-C separate from the G
    product. No division. -/
theorem localBlockData_sum_eq_factorials_mul (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {s : SizeProfile n k}
    (P : OrderedPartition (profileNat s) n) :
    (∑ D : ∀ j : Fin k, BlockDatum N (P.block j),
        ∏ j, blockDatumWeight ρ γ₀ (D j))
      = (∏ j, ((Nat.factorial (profileNat s j + 1) : ℕ) : ℝ))
          * ∏ j, kpG ρ γ₀ (profileNat s j) := by
  rw [localBlockData_sum_eq_prod_markedBlockContribution,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  exact markedBlockContribution_eq_factorial_mul ρ γ₀
    (P.card_block j)

/-! ## VI-B.3/4 — sum over partitions, Gate V enters ONCE -/

/-- **VI-B.3 + VI-B.4**: the partition sum is constant; Gate V
    converts card × factorials into n! — exactly, once, with the
    hypothesis carried by the profile itself. -/
theorem contributionOfProfile_eq (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (s : SizeProfile n k) :
    (∑ P : OrderedPartition (profileNat s) n,
      ∑ D : ∀ j : Fin k, BlockDatum N (P.block j),
        ∏ j, blockDatumWeight ρ γ₀ (D j))
      = ((Nat.factorial n : ℕ) : ℝ)
          * ∏ j, kpG ρ γ₀ (profileNat s j) := by
  calc (∑ P : OrderedPartition (profileNat s) n,
      ∑ D : ∀ j : Fin k, BlockDatum N (P.block j),
        ∏ j, blockDatumWeight ρ γ₀ (D j))
      = ∑ _P : OrderedPartition (profileNat s) n,
          (∏ j, ((Nat.factorial (profileNat s j + 1) : ℕ) : ℝ))
            * ∏ j, kpG ρ γ₀ (profileNat s j) :=
        Finset.sum_congr rfl (fun P _ =>
          localBlockData_sum_eq_factorials_mul ρ γ₀ P)
    _ = ((Fintype.card (OrderedPartition (profileNat s) n) : ℕ) : ℝ)
          * ((∏ j, ((Nat.factorial (profileNat s j + 1) : ℕ) : ℝ))
            * ∏ j, kpG ρ γ₀ (profileNat s j)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (((Fintype.card (OrderedPartition (profileNat s) n)
            : ℕ) : ℝ)
          * ∏ j, ((Nat.factorial (profileNat s j + 1) : ℕ) : ℝ))
          * ∏ j, kpG ρ γ₀ (profileNat s j) := by
        rw [mul_assoc]
    _ = ((Nat.factorial n : ℕ) : ℝ)
          * ∏ j, kpG ρ γ₀ (profileNat s j) := by
        have hs : (∑ j, (profileNat s j + 1)) = n := s.2
        rw [orderedPartitions_card_mul_factorials_real
          (s := profileNat s) hs]

/-! ## VI-B.5 — the UNIVERSAL capstone -/

/-- **VI-B CAPSTONE (universal — no hypotheses on n, k)**:
    k! · R_{n,k} = n! · Σ_profiles Π_j G(s_j). The k! is Gate I's
    enumeration multiplicity; the reindexation is VI-A; the weight
    bridge is 0b/0c; each block factorial is Gate IV-C; Gate V
    converts card × factorials into n!, once. NO division anywhere;
    ρ arbitrary in ℝ. -/
theorem rootDegreeContribution_factorial_identity (n k : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    ((Nat.factorial k : ℕ) : ℝ) * rootDegreeContribution n k ρ γ₀
      = ((Nat.factorial n : ℕ) : ℝ)
          * ∑ s : SizeProfile n k,
              ∏ j : Fin k, kpG ρ γ₀ (profileNat s j) := by
  calc ((Nat.factorial k : ℕ) : ℝ)
        * rootDegreeContribution n k ρ γ₀
      = ∑ X : EnumeratedRootDegreeData N n k,
          enumeratedDataWeight ρ γ₀ X :=
        (sum_enumeratedRootDegreeData_weight ρ γ₀).symm
    _ = ∑ Y : ProfiledDecompositionData N n k,
          profiledWeight ρ γ₀ Y :=
        enumeratedData_sum_eq_profiledData_sum ρ γ₀
    _ = ∑ s : SizeProfile n k,
          ∑ P : OrderedPartition (profileNat s) n,
            ∑ D : ∀ j : Fin k, BlockDatum N (P.block j),
              ∏ j, blockDatumWeight ρ γ₀ (D j) := by
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
        refine Finset.sum_congr rfl (fun P _ => ?_)
        refine Finset.sum_congr rfl (fun D _ => ?_)
        exact profiledWeight_eq_prod_blockDatumWeight ρ γ₀ P D
    _ = ∑ s : SizeProfile n k,
          ((Nat.factorial n : ℕ) : ℝ)
            * ∏ j, kpG ρ γ₀ (profileNat s j) :=
        Finset.sum_congr rfl (fun s _ =>
          contributionOfProfile_eq ρ γ₀ s)
    _ = ((Nat.factorial n : ℕ) : ℝ)
          * ∑ s : SizeProfile n k,
              ∏ j : Fin k, kpG ρ γ₀ (profileNat s j) := by
        rw [Finset.mul_sum]

/-! ## Sanities of the universal form -/

/-- k > n: the profile type is empty (each of the k blocks needs at
    least one vertex). -/
theorem sizeProfile_isEmpty_of_gt (hk : n < k) :
    IsEmpty (SizeProfile n k) := by
  refine ⟨fun s => ?_⟩
  have h := s.2
  have h2 : k ≤ (∑ j : Fin k, ((s.1 j : ℕ) + 1)) := by
    calc k = ∑ _j : Fin k, 1 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            smul_eq_mul, mul_one]
      _ ≤ ∑ j : Fin k, ((s.1 j : ℕ) + 1) :=
          Finset.sum_le_sum (fun j _ => by omega)
  omega

/-- k > n: both sides of the universal identity vanish. -/
theorem rootDegree_identity_zero_of_gt (hk : n < k)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    ((Nat.factorial k : ℕ) : ℝ) * rootDegreeContribution n k ρ γ₀
      = 0 := by
  rw [rootDegreeContribution_eq_zero_of_gt hk, mul_zero]

end LatticeGauge
