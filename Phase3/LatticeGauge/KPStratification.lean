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

end LatticeGauge
