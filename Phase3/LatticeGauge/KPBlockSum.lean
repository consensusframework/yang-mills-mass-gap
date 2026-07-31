/-
LatticeGauge/KPBlockSum.lean — stone 47 (b-iiB), GATE IV-B.

THE BLOCK SUM IS THE STANDARD ROOTED SUM — NO FACTORIAL YET
(architecture: Sol/GPT-5.6; execution: Fable). The mandatory chain:
  fixedRootBlockSum = rootedTreeSumOn (Fin (m+1), 0) = rootedTreeSum m
and ONLY THEN the normalized corollary
  fixedRootBlockSum = m! · kpTreeCoeff m,
with m := (B.erase r.val).card and B.card = m + 1 as the primary
interface (no truncated subtraction in the central proofs).
The three cares of the brief, each a named lemma: (1) the rooted
equivalence σ : Fin (m+1) ≃ ↥B with σ 0 = r PROVED IMMEDIATELY
(`rootedBlockEquiv_zero` — equivFin, whose orientation ↥B ≃ Fin
B.card was confirmed at Gate I, composed with finCongr and the swap
taking 0 to the root index; correct also when the index is already
0, since swap a a is harmless); (2) the assignment bridge
{δ // δ 0 = η} ≃ (Fin m → P) EXPLICITLY by Fin.tail and Fin.cons η
(as a sum reindexation, the dependent equality at index 0 handled by
cons_self_tail, never hidden in simp); (3) the tree universes EQUAL
AS FINSETS: connTreesOn (Fin (m+1)) = spanningTreeEdgeSets ⊤, the
hard inclusion consuming the stone-40b cardinal converse exactly as
planned (IsTree never transported on generic types — the two graph
constructors coincide definitionally at Fin, recorded by a rfl
lemma). Sanity: the unit block gives m = 0 and fixedRootBlockSum = 1
(via the Gate-47b-i zero case), the marked root never carries an
activity, and the final formula depends only on m and η. NOT here:
no sums over r or η, no markedBlockContribution, no (m+1)!, no
partitions, no recurrence, no KP, no exp, no Summable; branch stays
unmerged. NO axioms.
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

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)] {n : ℕ}

/-! ## IV-B.1 — the block cardinality interface -/

noncomputable def blockTailCard (B : Finset (Fin n)) (r : {x // x ∈ B}) :
    ℕ :=
  (B.erase r.val).card

theorem blockCard_eq (B : Finset (Fin n)) (r : {x // x ∈ B}) :
    B.card = blockTailCard B r + 1 := by
  unfold blockTailCard
  have h := Finset.card_erase_of_mem r.2
  have hpos := Finset.card_pos.mpr ⟨r.val, r.2⟩
  omega

/-! ## IV-B.2 — the rooted equivalence, root equation first -/

noncomputable def rootedBlockEquiv (B : Finset (Fin n))
    (r : {x // x ∈ B}) :
    Fin (blockTailCard B r + 1) ≃ {x // x ∈ B} :=
  (finCongr (blockCard_eq B r).symm).trans
    ((Equiv.swap ((finCongr (blockCard_eq B r).symm) 0)
        (B.equivFin r)).trans B.equivFin.symm)

/-- **The root equation, immediately.** -/
theorem rootedBlockEquiv_zero (B : Finset (Fin n))
    (r : {x // x ∈ B}) :
    rootedBlockEquiv B r 0 = r := by
  unfold rootedBlockEquiv
  show B.equivFin.symm
    (Equiv.swap ((finCongr (blockCard_eq B r).symm) 0)
      (B.equivFin r) ((finCongr (blockCard_eq B r).symm) 0)) = r
  rw [Equiv.swap_apply_left, Equiv.symm_apply_apply]

/-! ## IV-B.3 — the block sum and its transport to Fin -/

/-- The fixed-root block sum IS the generic rooted sum on ↥B (a
    definitional identity, recorded). -/
noncomputable def fixedRootBlockSum (ρ : Polymer N → ℝ)
    (B : Finset (Fin n)) (r : {x // x ∈ B}) (η : Polymer N) : ℝ :=
  rootedTreeSumOn (V := {x // x ∈ B}) ρ r η

theorem fixedRootBlockSum_def (ρ : Polymer N → ℝ)
    (B : Finset (Fin n)) (r : {x // x ∈ B}) (η : Polymer N) :
    fixedRootBlockSum ρ B r η
      = rootedTreeSumOn (V := {x // x ∈ B}) ρ r η := rfl

theorem fixedRootBlockSum_eq_finSum (ρ : Polymer N → ℝ)
    (B : Finset (Fin n)) (r : {x // x ∈ B}) (η : Polymer N) :
    fixedRootBlockSum ρ B r η
      = rootedTreeSumOn (V := Fin (blockTailCard B r + 1)) ρ 0 η :=
  (rootedTreeSumOn_congr (rootedBlockEquiv B r)
    (rootedBlockEquiv_zero B r) ρ η).symm

/-! ## IV-B.4A — the tree universes coincide at Fin (as Finsets) -/

/-- The two graph constructors coincide definitionally at Fin. -/
theorem graphOfEdgesOn_fin {M : ℕ}
    (E : Finset (OrderedEdgeOn (Fin M))) :
    graphOfEdgesOn E = graphOfEdges (n := M) E := rfl

/-- **Equality of Finsets** — the hard inclusion consumes the
    stone-40b cardinal converse. -/
theorem connTreesOn_fin_eq (m : ℕ) :
    connTreesOn (Fin (m + 1))
      = spanningTreeEdgeSets (⊤ : SimpleGraph (Fin (m + 1))) := by
  ext E
  rw [mem_connTreesOn, mem_spanningTreeEdgeSets]
  constructor
  · rintro ⟨hconn, hcard⟩
    rw [Fintype.card_fin] at hcard
    rw [graphOfEdgesOn_fin] at hconn
    refine ⟨?_, ?_⟩
    · rw [availableEdges_top]
      exact Finset.subset_univ _
    · refine isTree_of_connected_card hconn ?_
      rw [availableEdges_graphOfEdges]
      omega
  · rintro ⟨hsub, hTree⟩
    have hmem : E ∈ spanningTreeEdgeSets
        (⊤ : SimpleGraph (Fin (m + 1))) :=
      mem_spanningTreeEdgeSets.mpr ⟨hsub, hTree⟩
    have hcard : E.card = m := card_of_mem_spanningTreeEdgeSets hmem
    refine ⟨?_, ?_⟩
    · rw [graphOfEdgesOn_fin]
      exact hTree.isConnected
    · rw [Fintype.card_fin]
      omega

/-! ## IV-B.4B/C — the assignment bridge and the weight match -/

theorem rootedTuple_eq_val_comp (η : Polymer N) {m : ℕ}
    (γ' : Fin m → Polymer N) :
    rootedTuple η γ'
      = fun i => ((Fin.cons η γ' : Fin (m + 1) → Polymer N) i).val := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rw [rootedTuple_zero, Fin.cons_zero]
  · intro j
    rw [rootedTuple_succ, Fin.cons_succ]

/-- The weight of a cons-assignment on Fin (m+1) with root 0 is the
    stone-47b-i rooted weight (root activity excluded on both
    sides). -/
theorem rootedTreeWeightOn_cons (ρ : Polymer N → ℝ) (η : Polymer N)
    {m : ℕ} (γ' : Fin m → Polymer N)
    (E : Finset (OrderedEdgeOn (Fin (m + 1)))) :
    rootedTreeWeightOn ρ (0 : Fin (m + 1)) (Fin.cons η γ') E
      = rootedTreeWeight ρ η γ' E := by
  set δc : Fin (m + 1) → Polymer N := Fin.cons η γ' with hδc
  unfold rootedTreeWeightOn rootedTreeWeight treeIndicatorOn
    hardCoreTreeIndicator rootedActivityOn
  have hind : ∀ ed ∈ E,
      edgeIndicatorOn δc ed
        = hardCoreEdgeIndicator (rootedTuple η γ') ed := by
    intro ed _
    rw [rootedTuple_eq_val_comp, hδc]
    rfl
  rw [Finset.prod_congr rfl hind]
  have hact : (∏ v ∈ Finset.univ.erase (0 : Fin (m + 1)),
      ρ (δc v)) = ∏ i : Fin m, ρ (γ' i) := by
    refine (Finset.prod_bij
      (fun (i : Fin m) _ => i.succ) ?_ ?_ ?_ ?_).symm
    · intro i _
      rw [Finset.mem_erase]
      exact ⟨Fin.succ_ne_zero i, Finset.mem_univ _⟩
    · intro i₁ _ i₂ _ h
      exact Fin.succ_injective m h
    · intro v hv
      rw [Finset.mem_erase] at hv
      obtain ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ v).resolve_left hv.1
      exact ⟨j, Finset.mem_univ j, rfl⟩
    · intro i _
      show ρ (γ' i) = ρ (δc i.succ)
      have hcs : δc i.succ = γ' i := by
        rw [hδc]
        exact Fin.cons_succ ..
      rw [hcs]
  rw [hact]

/-- **IV-B.4D: the Fin rooted sum IS the stone-47b-i coefficient
    sum** — trees by the Finset equality, assignments by the
    explicit tail/cons bridge. -/
theorem rootedTreeSumOn_fin_eq_rootedTreeSum (ρ : Polymer N → ℝ)
    (η : Polymer N) (m : ℕ) :
    rootedTreeSumOn (V := Fin (m + 1)) ρ 0 η
      = rootedTreeSum m ρ η := by
  unfold rootedTreeSumOn rootedTreeSum
  rw [connTreesOn_fin_eq m]
  refine Finset.sum_bij (fun δ _ => Fin.tail δ) ?_ ?_ ?_ ?_
  · intro δ _
    exact Finset.mem_univ _
  · intro δ₁ h₁ δ₂ h₂ h
    rw [Finset.mem_filter] at h₁ h₂
    have e₁ : δ₁ = Fin.cons η (Fin.tail δ₁) := by
      rw [← h₁.2]
      exact (Fin.cons_self_tail δ₁).symm
    have e₂ : δ₂ = Fin.cons η (Fin.tail δ₂) := by
      rw [← h₂.2]
      exact (Fin.cons_self_tail δ₂).symm
    rw [e₁, e₂]
    simp only [] at h
    rw [h]
  · intro γ' _
    refine ⟨Fin.cons η γ', ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Fin.cons_zero .. 
    · show Fin.tail (Fin.cons η γ') = γ'
      exact Fin.tail_cons η γ'
  · intro δ hδ
    rw [Finset.mem_filter] at hδ
    have e : δ = Fin.cons η (Fin.tail δ) := by
      rw [← hδ.2]
      exact (Fin.cons_self_tail δ).symm
    refine Finset.sum_congr rfl (fun E _ => ?_)
    calc rootedTreeWeightOn ρ 0 δ E
        = rootedTreeWeightOn ρ 0 (Fin.cons η (Fin.tail δ)) E := by
          rw [← e]
      _ = rootedTreeWeight ρ η (Fin.tail δ) E :=
          rootedTreeWeightOn_cons ρ η (Fin.tail δ) E

/-! ## IV-B.5 — CAPSTONE WITHOUT FACTORIAL -/

/-- **Block → Fin(m+1) preserving the root, then root-fixed →
    tail; no normalization used anywhere.** -/
theorem fixedRootBlockSum_eq_rootedTreeSum (ρ : Polymer N → ℝ)
    (B : Finset (Fin n)) (r : {x // x ∈ B}) (η : Polymer N) :
    fixedRootBlockSum ρ B r η
      = rootedTreeSum (blockTailCard B r) ρ η := by
  rw [fixedRootBlockSum_eq_finSum,
    rootedTreeSumOn_fin_eq_rootedTreeSum]

/-! ## IV-B.6 — the normalized corollary -/

theorem factorial_cast_ne_zero (m : ℕ) :
    ((Nat.factorial m : ℕ) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)

/-- The short arithmetic lemma, isolated (no blanket field_simp). -/
theorem eq_factorial_mul_div (x : ℝ) (m : ℕ) :
    x = ((Nat.factorial m : ℕ) : ℝ)
      * (x / ((Nat.factorial m : ℕ) : ℝ)) := by
  rw [mul_comm, div_mul_cancel₀ x (factorial_cast_ne_zero m)]

theorem fixedRootBlockSum_eq_factorial_mul_kpTreeCoeff
    (ρ : Polymer N → ℝ) (B : Finset (Fin n)) (r : {x // x ∈ B})
    (η : Polymer N) :
    fixedRootBlockSum ρ B r η
      = ((Nat.factorial (blockTailCard B r) : ℕ) : ℝ)
        * kpTreeCoeff (blockTailCard B r) ρ η := by
  rw [fixedRootBlockSum_eq_rootedTreeSum]
  unfold kpTreeCoeff
  exact eq_factorial_mul_div _ _

/-! ## Sanities -/

/-- The unit block: m = 0 and the sum is exactly 1 (empty internal
    tree, no tail activities, 0! = 1 — via the 47b-i zero case). -/
theorem fixedRootBlockSum_unit (ρ : Polymer N → ℝ)
    {B : Finset (Fin n)} {a : Fin n} (hB : B = {a})
    (r : {x // x ∈ B}) (η : Polymer N) :
    fixedRootBlockSum ρ B r η = 1 := by
  have hm : blockTailCard B r = 0 := by
    unfold blockTailCard
    have hcard : B.card = 1 := by
      rw [hB]
      exact Finset.card_singleton a
    have herase := Finset.card_erase_of_mem r.2
    omega
  rw [fixedRootBlockSum_eq_rootedTreeSum, hm]
  exact rootedTreeSum_zero ρ η

end LatticeGauge
