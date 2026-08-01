/-
LatticeGauge/KPPartitionCount.lean — stone 47 (b-iiB2), GATE V-A.

THE STANDARD BLOCK DOMAIN, ORDERED PARTITIONS, AND THE FIBER
EQUIVALENCE (architecture: Sol/GPT-5.6; execution: Fable). The
multinomial demoted to something more basic: a global enumeration of
the standard domain Ω_s = Σ j, Fin (s j + 1) IS an ordered partition
of the n labels together with an internal enumeration of each block.
GATE V-A delivers the structural half: the domain and its cardinal n
(under the robust hypothesis Σ (s j + 1) = n — no truncated
subtraction anywhere); the witness equivalence to Fin n; the n!
count of global enumerations (Gate-I's Fintype.card_equiv again);
ordered partitions as a structure with labelled blocks (indices
j : Fin k stay labelled — equal-sized blocks in different positions
are DIFFERENT partitions, no stabilizers, no quotients); the
partition induced by an enumeration (block j = image of the standard
fiber); the forgetful map; internal enumerations of one block with
their (s j + 1)! count; and THE STRUCTURAL CAPSTONE
`enumerationFiberEquivInternalEnumerations`: the fiber of the
forgetful map over P is EQUIVALENT (both roundtrips) to the
dependent product of internal enumerations — the P-rewrites audited
through ONE block-level lemma, never element-by-element transports.
Edge cases: k = 0 forces n = 0 (empty sum) with the empty partition;
k = 1 noted. NOT here (Gate V-B): the cardinal of the dependent
product, the constant fiber count, the sigma decomposition and the
multiplicative identity card·Π(s j+1)! = n!. NOT anywhere in Gate V:
tree weights, markedBlockContribution, degree sums, the recurrence,
1/k!, partial sums, KP, exp, Summable. NO axioms.
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

open scoped Classical

namespace LatticeGauge

variable {k n : ℕ}

/-! ## V-A.2/3 — the standard block domain -/

def StandardBlockDomain (s : Fin k → ℕ) : Type :=
  (j : Fin k) × Fin (s j + 1)

noncomputable instance (s : Fin k → ℕ) :
    Fintype (StandardBlockDomain s) := by
  unfold StandardBlockDomain
  infer_instance

noncomputable instance (s : Fin k → ℕ) :
    DecidableEq (StandardBlockDomain s) := by
  unfold StandardBlockDomain
  infer_instance

theorem card_standardBlockDomain (s : Fin k → ℕ) :
    Fintype.card (StandardBlockDomain s) = ∑ j, (s j + 1) := by
  unfold StandardBlockDomain
  simp

theorem card_standardBlockDomain_eq (s : Fin k → ℕ)
    (hs : (∑ j, (s j + 1)) = n) :
    Fintype.card (StandardBlockDomain s) = n := by
  rw [card_standardBlockDomain s, hs]

noncomputable def standardDomainEquivFin (s : Fin k → ℕ)
    (hs : (∑ j, (s j + 1)) = n) :
    StandardBlockDomain s ≃ Fin n :=
  Fintype.equivFinOfCardEq (card_standardBlockDomain_eq s hs)

/-! ## V-A.4 — the global enumerations and their n! count -/

abbrev GlobalEnumeration (s : Fin k → ℕ) (n : ℕ) : Type :=
  StandardBlockDomain s ≃ Fin n

theorem card_globalEnumeration (s : Fin k → ℕ)
    (hs : (∑ j, (s j + 1)) = n) :
    Fintype.card (GlobalEnumeration s n) = Nat.factorial n := by
  rw [Fintype.card_equiv (standardDomainEquivFin s hs),
    card_standardBlockDomain_eq s hs]

/-! ## V-A.5 — ordered partitions (labelled blocks, no quotients) -/

structure OrderedPartition (s : Fin k → ℕ) (n : ℕ) where
  block : Fin k → Finset (Fin n)
  card_block : ∀ j, (block j).card = s j + 1
  cover : ∀ v : Fin n, ∃ j, v ∈ block j
  disj : ∀ j₁ j₂ : Fin k, j₁ ≠ j₂ → Disjoint (block j₁) (block j₂)

theorem OrderedPartition.ext' {s : Fin k → ℕ}
    {P₁ P₂ : OrderedPartition s n} (h : P₁.block = P₂.block) :
    P₁ = P₂ := by
  cases P₁
  cases P₂
  dsimp only at h
  subst h
  rfl

/-! ## V-A.6/7 — the induced partition and the forgetful map -/

theorem enum_fiber_injective {s : Fin k → ℕ}
    (e : GlobalEnumeration s n) (j : Fin k) :
    Function.Injective
      (fun x : Fin (s j + 1) => e ⟨j, x⟩) := by
  intro x y hxy
  have h2 := e.injective hxy
  exact eq_of_heq (Sigma.mk.inj h2).2

noncomputable def partitionOfEnumeration {s : Fin k → ℕ}
    (e : GlobalEnumeration s n) : OrderedPartition s n where
  block j := Finset.univ.image (fun x : Fin (s j + 1) => e ⟨j, x⟩)
  card_block j := by
    rw [Finset.card_image_of_injective _ (enum_fiber_injective e j),
      Finset.card_univ, Fintype.card_fin]
  cover v := by
    refine ⟨(e.symm v).1, ?_⟩
    rw [Finset.mem_image]
    refine ⟨(e.symm v).2, Finset.mem_univ _, ?_⟩
    show e ⟨(e.symm v).1, (e.symm v).2⟩ = v
    exact e.apply_symm_apply v
  disj j₁ j₂ hne := by
    rw [Finset.disjoint_left]
    intro v h1 h2
    rw [Finset.mem_image] at h1 h2
    obtain ⟨x, -, hx⟩ := h1
    obtain ⟨y, -, hy⟩ := h2
    have h3 := e.injective (hx.trans hy.symm)
    exact hne (Sigma.mk.inj h3).1

/-- The forgetful map: keep the blocks, forget the internal
    enumerations. -/
noncomputable def forgetInternalEnumerations {s : Fin k → ℕ}
    (e : GlobalEnumeration s n) : OrderedPartition s n :=
  partitionOfEnumeration e

/-! ## V-A.8/9 — internal enumerations of one block -/

abbrev InternalEnumeration {s : Fin k → ℕ}
    (P : OrderedPartition s n) (j : Fin k) : Type :=
  Fin (s j + 1) ≃ {x // x ∈ P.block j}

noncomputable def internalWitness {s : Fin k → ℕ}
    (P : OrderedPartition s n) (j : Fin k) :
    InternalEnumeration P j :=
  (finCongr (P.card_block j).symm).trans (P.block j).equivFin.symm

theorem card_internalEnumeration {s : Fin k → ℕ}
    (P : OrderedPartition s n) (j : Fin k) :
    Fintype.card (InternalEnumeration P j)
      = Nat.factorial (s j + 1) := by
  rw [Fintype.card_equiv (internalWitness P j), Fintype.card_fin]

abbrev InternalEnumerations {s : Fin k → ℕ}
    (P : OrderedPartition s n) : Type :=
  ∀ j : Fin k, InternalEnumeration P j

/-! ## V-A.10 — the fiber of the forgetful map -/

def EnumerationFiber {s : Fin k → ℕ} (P : OrderedPartition s n) :
    Type :=
  {e : GlobalEnumeration s n // forgetInternalEnumerations e = P}

/-! ## V-A.11/12/13 — THE STRUCTURAL CAPSTONE -/

/-- The single block-level rewrite (P rewritten by extensionality
    ONCE — no element-by-element transports). -/
theorem block_of_fiber {s : Fin k → ℕ} {P : OrderedPartition s n}
    (e : EnumerationFiber P) (j : Fin k) :
    P.block j
      = Finset.univ.image
          (fun x : Fin (s j + 1) => e.val ⟨j, x⟩) := by
  rw [← e.2]
  rfl

theorem mem_block_of_fiber {s : Fin k → ℕ}
    {P : OrderedPartition s n} (e : EnumerationFiber P) (j : Fin k)
    (x : Fin (s j + 1)) :
    e.val ⟨j, x⟩ ∈ P.block j := by
  rw [block_of_fiber e j, Finset.mem_image]
  exact ⟨x, Finset.mem_univ _, rfl⟩

/-- Fiber → internal enumerations: restrict the global enumeration
    to each standard fiber. -/
noncomputable def fiberToInternal {s : Fin k → ℕ}
    {P : OrderedPartition s n} (e : EnumerationFiber P) :
    InternalEnumerations P := fun j =>
  Equiv.ofBijective
    (fun x => ⟨e.val ⟨j, x⟩, mem_block_of_fiber e j x⟩)
    (by
      constructor
      · intro x y hxy
        exact enum_fiber_injective e.val j
          (congrArg Subtype.val hxy)
      · rintro ⟨v, hv⟩
        rw [block_of_fiber e j, Finset.mem_image] at hv
        obtain ⟨x, -, hx⟩ := hv
        exact ⟨x, Subtype.ext hx⟩)

/-- The glued global enumeration from a family of internal
    enumerations. -/
noncomputable def internalToGlobal {s : Fin k → ℕ}
    {P : OrderedPartition s n} (h : InternalEnumerations P) :
    GlobalEnumeration s n :=
  Equiv.ofBijective
    (fun p : StandardBlockDomain s => (h p.1 p.2).val)
    (by
      constructor
      · rintro ⟨j₁, x₁⟩ ⟨j₂, x₂⟩ hxy
        dsimp only at hxy
        by_cases hj : j₁ = j₂
        · subst hj
          have hx : x₁ = x₂ :=
            (h j₁).injective (Subtype.ext hxy)
          rw [hx]
        · exfalso
          have m1 := (h j₁ x₁).2
          have m2 := (h j₂ x₂).2
          rw [hxy] at m1
          exact Finset.disjoint_left.mp (P.disj j₁ j₂ hj) m1 m2
      · intro v
        obtain ⟨j, hj⟩ := P.cover v
        refine ⟨⟨j, (h j).symm ⟨v, hj⟩⟩, ?_⟩
        show ((h j) ((h j).symm ⟨v, hj⟩)).val = v
        rw [Equiv.apply_symm_apply])

theorem forget_internalToGlobal {s : Fin k → ℕ}
    {P : OrderedPartition s n} (h : InternalEnumerations P) :
    forgetInternalEnumerations (internalToGlobal h) = P := by
  refine OrderedPartition.ext' ?_
  funext j
  show Finset.univ.image
      (fun x : Fin (s j + 1) => internalToGlobal h ⟨j, x⟩)
    = P.block j
  ext v
  rw [Finset.mem_image]
  constructor
  · rintro ⟨x, -, hx⟩
    rw [← hx]
    show ((h j x) : Fin n) ∈ P.block j
    exact (h j x).2
  · intro hv
    refine ⟨(h j).symm ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
    show ((h j) ((h j).symm ⟨v, hv⟩)).val = v
    rw [Equiv.apply_symm_apply]

/-- **GATE V-A CAPSTONE: the fiber of the forgetful map over P is
    equivalent to the dependent product of internal enumerations —
    both roundtrips proved.** -/
noncomputable def enumerationFiberEquivInternalEnumerations
    {s : Fin k → ℕ} (P : OrderedPartition s n) :
    EnumerationFiber P ≃ InternalEnumerations P where
  toFun := fiberToInternal
  invFun h := ⟨internalToGlobal h, forget_internalToGlobal h⟩
  left_inv e := by
    refine Subtype.ext ?_
    refine Equiv.ext ?_
    rintro ⟨j, x⟩
    rfl
  right_inv h := by
    funext j
    refine Equiv.ext ?_
    intro x
    refine Subtype.ext ?_
    rfl

/-! ## V-A.14 — edge cases -/

/-- k = 0 forces n = 0 (empty sum). -/
theorem n_eq_zero_of_k_zero {s : Fin 0 → ℕ}
    (hs : (∑ j, (s j + 1)) = n) : n = 0 := by
  simpa using hs.symm

/-- The empty partition for k = 0 (all fields vacuous). -/
noncomputable def emptyOrderedPartition (s : Fin 0 → ℕ) :
    OrderedPartition s 0 where
  block j := j.elim0
  card_block j := j.elim0
  cover v := v.elim0
  disj j₁ := j₁.elim0

end LatticeGauge
