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
    _ = E.card := Finset.card_attach _

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
      u ∈ S →
      ∃ hv : v ∈ S,
        (graphOfEdgesOn (confineSet E hsub)).Reachable
          ⟨u, ‹u ∈ S›⟩ ⟨v, hv⟩ := by
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

end LatticeGauge
