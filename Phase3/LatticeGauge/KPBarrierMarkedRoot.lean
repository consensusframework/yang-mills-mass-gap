/-
LatticeGauge/KPBarrierMarkedRoot.lean — PEDRA 50, Gate 50-A9
(module 2/3, editorial split 50-A9E; architecture: Sol;
execution: Fable).

A9.3 — MARKING THE OCCURRENCES. Every connector tuple has a
P-forbidden occurrence; ALL occurrences are summed (never chosen
— "the first forbidden occurrence" would hide the multiplicity
that cancels the factorial), each transported to position 0 by
Equiv.swap with the stone-38 weight invariance; the factor n+1
stays visible and cancels (n+1)! into n! exclusively through
succ_mul_div_factorial_succ. Central majorants:
  filtered connector at n+1 ≤ P-forbidden-root sum (and Q).
No orbits, no quotients, no stabilizers, no group-action theory.

RULING (architect): two-root KP is NOT necessary at this stage.
One P-forbidden root localizes the envelope; the Q-forbidden
occurrence stays inside the connector predicate for the future
geometry/mass gate, and is only then forgotten by monotonicity.
KPMarkedBlock remains stone-47 tree combinatorics and does not
appear in executable code here.

Hard holds as in KPBarrierConnectorPositive.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPBarrierConnectorPositive

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A9.3 — MARKING THE OCCURRENCES -/

/-- **Weight invariance under permutation** (stone 38 consumed
    for the natAbs weight; activities via Equiv.prod_comp). -/
theorem kpAbsSummand_comp_perm {k : ℕ} (ρ : Polymer N → ℝ)
    (δ : Fin k → Polymer N) (σ : Equiv.Perm (Fin k)) :
    kpAbsSummand ρ (δ ∘ ⇑σ) = kpAbsSummand ρ δ := by
  unfold kpAbsSummand
  have hu : ursellCoeff (N := N) (fun j => ((δ ∘ ⇑σ) j).val)
      = ursellCoeff (N := N) (fun j => (δ j).val) :=
    ursellCoeff_perm (fun j => (δ j).val) σ
  have hp : (∏ j : Fin k, ρ ((δ ∘ ⇑σ) j))
      = ∏ j : Fin k, ρ (δ j) :=
    Equiv.prod_comp σ (fun j => ρ (δ j))
  rw [hu, hp]

/-- **The P-forbidden witness, majorized by ALL marks**: the
    connector summand is at most the sum over every P-forbidden
    occurrence — no silent choice of "the first one". -/
theorem connector_summand_le_marked_sum {k : ℕ}
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) (δ : Fin k → Polymer N) :
    (if TupleHitsBothForbidden P Q δ then kpAbsSummand ρ δ else 0)
      ≤ ∑ i : Fin k,
          if ¬ P (δ i) then kpAbsSummand ρ δ else 0 := by
  have hterm : ∀ i : Fin k,
      (0 : ℝ) ≤ if ¬ P (δ i) then kpAbsSummand ρ δ else 0 := by
    intro i
    by_cases hp : ¬ P (δ i)
    · rw [if_pos hp]; exact kpAbsSummand_nonneg hρ δ
    · rw [if_neg hp]
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h]
    have h1 : ¬ ∀ i : Fin k, P (δ i) := h.1
    obtain ⟨i₀, hi₀⟩ := not_forall.mp h1
    have hsingle : (if ¬ P (δ i₀) then kpAbsSummand ρ δ else 0)
        ≤ ∑ i : Fin k,
            if ¬ P (δ i) then kpAbsSummand ρ δ else 0 :=
      Finset.single_le_sum
        (f := fun i : Fin k =>
          if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
        (fun i _ => hterm i) (Finset.mem_univ i₀)
    rwa [if_pos hi₀] at hsingle
  · rw [if_neg h]
    exact Finset.sum_nonneg (fun i _ => hterm i)

/-- The swap reindexation of tuples (local, non-dependent). -/
def swapTupleEquiv (n : ℕ) (i : Fin (n + 1)) :
    (Fin (n + 1) → Polymer N) ≃ (Fin (n + 1) → Polymer N) where
  toFun δ := δ ∘ ⇑(Equiv.swap 0 i)
  invFun δ := δ ∘ ⇑(Equiv.swap 0 i)
  left_inv δ := by
    funext j
    simp only [Function.comp_apply, Equiv.swap_apply_self]
  right_inv δ := by
    funext j
    simp only [Function.comp_apply, Equiv.swap_apply_self]

/-- **Transport of the mark i → 0**: each marked index carries
    the same rooted contribution (Equiv.swap + stone 38). -/
theorem marked_sum_index_transport (n : ℕ) (ρ : Polymer N → ℝ)
    (P : Polymer N → Prop) (i : Fin (n + 1)) :
    (∑ δ : Fin (n + 1) → Polymer N,
        if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
      = ∑ δ : Fin (n + 1) → Polymer N,
          if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 := by
  refine Fintype.sum_equiv (swapTupleEquiv (N := N) n i)
    (fun δ => if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
    (fun δ => if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
    (fun δ => ?_)
  simp only [swapTupleEquiv, Equiv.coe_fn_mk]
  rw [show (δ ∘ ⇑(Equiv.swap (0 : Fin (n + 1)) i)) 0 = δ i from by
      rw [Function.comp_apply, Equiv.swap_apply_left],
    kpAbsSummand_comp_perm ρ δ (Equiv.swap 0 i)]

/-- The marked-root sum, repackaged as the forbidden-root
    coefficient (consTupleEquiv of 49A consumed via
    sum_pairs_eq_sum_tuples; the A8 summand lemma reused). -/
theorem sum_marked_root_eq (n : ℕ) (ρ : Polymer N → ℝ)
    (P : Polymer N → Prop) :
    (∑ δ : Fin (n + 1) → Polymer N,
        if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
      / ((Nat.factorial n : ℕ) : ℝ)
      = kpForbiddenRootCoeff n ρ P := by
  have hnum : (∑ γ₀ : Polymer N,
      if ¬ P γ₀ then
        ρ γ₀ * ∑ γ : Fin n → Polymer N,
          ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
            * ∏ i : Fin n, ρ (γ i)
      else 0)
      = ∑ δ : Fin (n + 1) → Polymer N,
          if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 := by
    calc (∑ γ₀ : Polymer N,
        if ¬ P γ₀ then
          ρ γ₀ * ∑ γ : Fin n → Polymer N,
            ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
              * ∏ i : Fin n, ρ (γ i)
        else 0)
        = ∑ γ₀ : Polymer N, ∑ γ : Fin n → Polymer N,
            if ¬ P γ₀ then
              ((ursellCoeff (rootedTuple γ₀ γ)).natAbs : ℝ)
                * (ρ γ₀ * ∏ i : Fin n, ρ (γ i))
            else 0 := by
          refine Finset.sum_congr rfl (fun γ₀ _ => ?_)
          by_cases h : ¬ P γ₀
          · rw [if_pos h, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun γ _ => ?_)
            rw [if_pos h]; ring
          · rw [if_neg h]
            simp only [if_neg h]
            rw [Finset.sum_const_zero]
      _ = ∑ p : Polymer N × (Fin n → Polymer N),
            if ¬ P p.1 then
              ((ursellCoeff (rootedTuple p.1 p.2)).natAbs : ℝ)
                * (ρ p.1 * ∏ i : Fin n, ρ (p.2 i))
            else 0 :=
          (Fintype.sum_prod_type
            (fun p : Polymer N × (Fin n → Polymer N) =>
              if ¬ P p.1 then
                ((ursellCoeff (rootedTuple p.1 p.2)).natAbs : ℝ)
                  * (ρ p.1 * ∏ i : Fin n, ρ (p.2 i))
              else 0)).symm
      _ = ∑ p : Polymer N × (Fin n → Polymer N),
            if ¬ P ((Fin.cons p.1 p.2 : Fin (n + 1) → Polymer N) 0)
            then kpAbsSummand ρ (Fin.cons p.1 p.2) else 0 := by
          refine Finset.sum_congr rfl ?_
          rintro ⟨γ₀, γ⟩ -
          dsimp only
          rw [Fin.cons_zero]
          exact if_congr Iff.rfl
            (abs_rooted_summand_eq n ρ γ₀ γ) rfl
      _ = ∑ δ : Fin (n + 1) → Polymer N,
            if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 :=
          sum_pairs_eq_sum_tuples n
            (fun δ => if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
  rw [← hnum, Finset.sum_div]
  unfold kpForbiddenRootCoeff
  refine Finset.sum_congr rfl (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_neg (not_not_intro h), if_pos h, zero_div]
  · rw [if_pos h, if_neg h, mul_div_assoc]
    rfl

/-- **A9.3 CENTRAL MAJORANT**: the filtered connector at k = n+1
    is bounded by the P-forbidden-root sum. The n+1 marks cancel
    (n+1)! into n! exclusively via succ_mul_div_factorial_succ —
    the factor stays visible. -/
theorem kpAbsConnector_succ_le_forbiddenRoot (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff (n + 1) ρ P Q
      ≤ kpForbiddenRootCoeff n ρ P := by
  have hswap : (∑ δ : Fin (n + 1) → Polymer N,
      ∑ i : Fin (n + 1),
        if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
      = ((n + 1 : ℕ) : ℝ) * ∑ δ : Fin (n + 1) → Polymer N,
          if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 := by
    rw [Finset.sum_comm]
    calc (∑ i : Fin (n + 1), ∑ δ : Fin (n + 1) → Polymer N,
        if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
        = ∑ _i : Fin (n + 1), ∑ δ : Fin (n + 1) → Polymer N,
            if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 :=
          Finset.sum_congr rfl (fun i _ =>
            marked_sum_index_transport n ρ P i)
      _ = ((n + 1 : ℕ) : ℝ) * ∑ δ : Fin (n + 1) → Polymer N,
            if ¬ P (δ 0) then kpAbsSummand ρ δ else 0 := by
          rw [Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
  rw [kpAbsConnectorUnrootedCoeff_eq]
  calc (∑ δ : Fin (n + 1) → Polymer N,
      if TupleHitsBothForbidden P Q δ then kpAbsSummand ρ δ
      else 0) / ((Nat.factorial (n + 1) : ℕ) : ℝ)
      ≤ (∑ δ : Fin (n + 1) → Polymer N, ∑ i : Fin (n + 1),
          if ¬ P (δ i) then kpAbsSummand ρ δ else 0)
        / ((Nat.factorial (n + 1) : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum (fun δ _ =>
            connector_summand_le_marked_sum hρ P Q δ))
          (by positivity)
    _ = (((n + 1 : ℕ) : ℝ) * ∑ δ : Fin (n + 1) → Polymer N,
          if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
        / ((Nat.factorial (n + 1) : ℕ) : ℝ) := by rw [hswap]
    _ = ((n + 1 : ℕ) : ℝ)
          * ((∑ δ : Fin (n + 1) → Polymer N,
              if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
            / ((Nat.factorial (n + 1) : ℕ) : ℝ)) :=
        mul_div_assoc _ _ _
    _ = (∑ δ : Fin (n + 1) → Polymer N,
          if ¬ P (δ 0) then kpAbsSummand ρ δ else 0)
        / ((Nat.factorial n : ℕ) : ℝ) :=
        succ_mul_div_factorial_succ n _
    _ = kpForbiddenRootCoeff n ρ P := sum_marked_root_eq n ρ P

/-- The symmetric corollary: the Q-forbidden root. -/
theorem kpAbsConnector_succ_le_forbiddenRoot_Q (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff (n + 1) ρ P Q
      ≤ kpForbiddenRootCoeff n ρ Q := by
  rw [kpAbsConnectorUnrootedCoeff_symm]
  exact kpAbsConnector_succ_le_forbiddenRoot n hρ Q P

#print axioms kpAbsConnector_succ_le_forbiddenRoot

end LatticeGauge
