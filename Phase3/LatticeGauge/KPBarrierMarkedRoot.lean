/-
LatticeGauge/KPBarrierMarkedRoot.lean — PEDRA 50, Gate 50-A9:
THE BARRIER-MARKED ROOT — LOCALIZING THE KP ENVELOPE
(architecture: Sol; execution: Fable).

Every connector tuple has a P-forbidden OCCURRENCE; summing over
all possible marks produces the factor k, which legitimately
cancels k! into (k-1)! and a genuine root. Hence:
  signed connector ≤ positive filtered connector
    ≤ forbidden-root local sum ≤ P-localized KP envelope.
The mark is NEVER chosen ("first forbidden occurrence" would hide
the multiplicity that cancels the factorial): ALL occurrences are
summed, each transported to position 0 by Equiv.swap, with the
weight invariance of stone 38 (ursellCoeff_perm) — no orbits, no
quotients, no stabilizers, no group-action theory.

RULING (architect): two-root KP is NOT necessary at this stage.
One P-forbidden root localizes the envelope; the Q-forbidden
occurrence stays inside the connector predicate for the future
geometry/mass gate, and is only then forgotten by monotonicity.
KPMarkedBlock remains stone-47 tree combinatorics and does not
appear in executable code here.

NOT here (hard hold): no tilted activity, no exp(λ·card), no
tupleTotalCard, no WalkBarrierSeparated, no tail in n, no
exp(-n)/q^n/rate, no geometric estimate of the forbidden-root
set, no 64^d / 16·64^(2m) / Stone 45 on clusters, no two-root KP,
no covariance, no second insertion, no SimpleGraph.dist/edist/
cdist/confinedLengths, no clustering, no thermodynamic limit, no
continuum, no mass gap, no Clay claim. Real.exp (a γ) appears
ONLY in the inherited KP envelope — it is not a tilt.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.KPAbsoluteUnrooted

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A9.1 — the filtered positive connector -/

noncomputable def kpAbsConnectorUnrootedCoeff (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) : ℝ :=
  (∑ δ : Fin k → Polymer N,
      if TupleHitsBothForbidden P Q δ then
        (((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℕ) : ℝ)
          * ∏ i : Fin k, ρ (δ i)
      else 0)
    / ((Nat.factorial k : ℕ) : ℝ)

/-- The positive tuple weight (named so every lemma below is
    first-order; definitionally the summand above). -/
noncomputable def kpAbsSummand {k : ℕ} (ρ : Polymer N → ℝ)
    (δ : Fin k → Polymer N) : ℝ :=
  ((ursellCoeff (N := N) (fun i => (δ i).val)).natAbs : ℝ)
    * ∏ i : Fin k, ρ (δ i)

theorem kpAbsConnectorUnrootedCoeff_eq (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      = (∑ δ : Fin k → Polymer N,
          if TupleHitsBothForbidden P Q δ then kpAbsSummand ρ δ
          else 0)
        / ((Nat.factorial k : ℕ) : ℝ) := rfl

theorem kpAbsSummand_nonneg {k : ℕ} {ρ : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (δ : Fin k → Polymer N) :
    0 ≤ kpAbsSummand ρ δ :=
  mul_nonneg (Nat.cast_nonneg _)
    (Finset.prod_nonneg (fun i _ => hρ (δ i)))

theorem kpAbsConnectorUnrootedCoeff_zero (ρ : Polymer N → ℝ)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff 0 ρ P Q = 0 := by
  unfold kpAbsConnectorUnrootedCoeff
  rw [Finset.univ_unique, Finset.sum_singleton,
    if_neg (fun h => h.1 (fun i => i.elim0)), zero_div]

theorem kpAbsConnectorUnrootedCoeff_nonneg (k : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    0 ≤ kpAbsConnectorUnrootedCoeff k ρ P Q := by
  rw [kpAbsConnectorUnrootedCoeff_eq]
  refine div_nonneg (Finset.sum_nonneg (fun δ _ => ?_))
    (Nat.cast_nonneg _)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h]; exact kpAbsSummand_nonneg hρ δ
  · rw [if_neg h]

/-- **P/Q symmetry** (the connector predicate is a conjunction). -/
theorem kpAbsConnectorUnrootedCoeff_symm (k : ℕ)
    (ρ : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      = kpAbsConnectorUnrootedCoeff k ρ Q P := by
  unfold kpAbsConnectorUnrootedCoeff
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h,
      if_pos (show TupleHitsBothForbidden Q P δ from ⟨h.2, h.1⟩)]
  · rw [if_neg h,
      if_neg (fun h' : TupleHitsBothForbidden Q P δ =>
        h ⟨h'.2, h'.1⟩)]

/-- **Filtered domination**: the signed connector is dominated
    coefficient-wise WITH the barrier information preserved. -/
theorem abs_kpConnectorUnrootedCoeff_le_filtered (k : ℕ)
    (z : Polymer N → ℝ) (P Q : Polymer N → Prop) :
    |kpConnectorUnrootedCoeff (N := N) k z P Q|
      ≤ kpAbsConnectorUnrootedCoeff k (fun η => |z η|) P Q := by
  unfold kpConnectorUnrootedCoeff kpAbsConnectorUnrootedCoeff
  rw [abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  refine le_trans (Finset.abs_sum_le_sum_abs _ _)
    (Finset.sum_le_sum (fun δ _ => ?_))
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h, if_pos h, abs_mul, Finset.abs_prod,
      ← Int.cast_abs, Int.abs_eq_natAbs, Int.cast_natCast]
  · rw [if_neg h, if_neg h, abs_zero]

/-- **Forgetting the filter**: filtered ≤ global B⁺ (A8). -/
theorem kpAbsConnectorUnrootedCoeff_le_abs (k : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P Q : Polymer N → Prop) :
    kpAbsConnectorUnrootedCoeff k ρ P Q
      ≤ kpAbsUnrootedCoeff k ρ := by
  unfold kpAbsConnectorUnrootedCoeff kpAbsUnrootedCoeff
  refine div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun δ _ => ?_)) (by positivity)
  by_cases h : TupleHitsBothForbidden P Q δ
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (Nat.cast_nonneg _)
      (Finset.prod_nonneg (fun i _ => hρ (δ i)))

/-! ## A9.2 — the forbidden-root coefficient and envelope -/

noncomputable def kpForbiddenRootCoeff (n : ℕ)
    (ρ : Polymer N → ℝ) (P : Polymer N → Prop) : ℝ :=
  ∑ γ₀ : Polymer N,
    if P γ₀ then 0
    else ρ γ₀ * kpUrsellCoeff n ρ γ₀

noncomputable def kpForbiddenRootEnvelope
    (ρ a : Polymer N → ℝ) (P : Polymer N → Prop) : ℝ :=
  ∑ γ₀ : Polymer N,
    if P γ₀ then 0
    else ρ γ₀ * Real.exp (a γ₀)

theorem kpForbiddenRootCoeff_nonneg (n : ℕ)
    {ρ : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P : Polymer N → Prop) :
    0 ≤ kpForbiddenRootCoeff n ρ P := by
  refine Finset.sum_nonneg (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (hρ γ₀) (kpUrsellCoeff_nonneg n hρ γ₀)

theorem kpForbiddenRootEnvelope_nonneg
    {ρ a : Polymer N → ℝ} (hρ : ∀ η, 0 ≤ ρ η)
    (P : Polymer N → Prop) :
    0 ≤ kpForbiddenRootEnvelope ρ a P := by
  refine Finset.sum_nonneg (fun γ₀ _ => ?_)
  by_cases h : P γ₀
  · rw [if_pos h]
  · rw [if_neg h]
    exact mul_nonneg (hρ γ₀) (Real.exp_pos _).le

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

/-! ## A9.4 — the LOCAL rooted KP package (47/48 consumed) -/

theorem sum_range_kpAbsConnector_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    ∀ K : ℕ, (∑ k ∈ Finset.range K,
        kpAbsConnectorUnrootedCoeff k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a P := by
  intro K
  rcases K with _ | M
  · rw [Finset.range_zero, Finset.sum_empty]
    exact kpForbiddenRootEnvelope_nonneg hρ P
  · rw [Finset.sum_range_succ'
      (fun k => kpAbsConnectorUnrootedCoeff k ρ P Q) M,
      kpAbsConnectorUnrootedCoeff_zero, add_zero]
    calc (∑ n ∈ Finset.range M,
        kpAbsConnectorUnrootedCoeff (n + 1) ρ P Q)
        ≤ ∑ n ∈ Finset.range M, kpForbiddenRootCoeff n ρ P :=
          Finset.sum_le_sum (fun n _ =>
            kpAbsConnector_succ_le_forbiddenRoot n hρ P Q)
      _ ≤ kpForbiddenRootEnvelope ρ a P := by
          unfold kpForbiddenRootCoeff kpForbiddenRootEnvelope
          rw [Finset.sum_comm]
          refine Finset.sum_le_sum (fun γ₀ _ => ?_)
          by_cases h : P γ₀
          · simp only [if_pos h]
            rw [Finset.sum_const_zero]
          · simp only [if_neg h]
            rw [← Finset.mul_sum]
            refine mul_le_mul_of_nonneg_left ?_ (hρ γ₀)
            calc (∑ n ∈ Finset.range M, kpUrsellCoeff n ρ γ₀)
                ≤ ∑' n : ℕ, kpUrsellCoeff n ρ γ₀ :=
                  sum_le_tsum (Finset.range M)
                    (fun n _ => kpUrsellCoeff_nonneg n hρ γ₀)
                    (summable_kpUrsellCoeff hρ ha hKP γ₀)
              _ ≤ Real.exp (a γ₀) :=
                  tsum_kpUrsellCoeff_le_exp hρ ha hKP γ₀

theorem summable_kpAbsConnectorUnrootedCoeff
    {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    Summable (fun k =>
      kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q) :=
  summable_of_sum_range_le
    (fun k => kpAbsConnectorUnrootedCoeff_nonneg k hρ P Q)
    (sum_range_kpAbsConnector_le hρ ha hKP P Q)

/-- **A9.4 positive capstone (P side)**. -/
theorem tsum_kpAbsConnector_le {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a P :=
  Real.tsum_le_of_sum_range_le
    (fun k => kpAbsConnectorUnrootedCoeff_nonneg k hρ P Q)
    (sum_range_kpAbsConnector_le hρ ha hKP P Q)

/-- **A9.4 positive capstone (Q side)** — by P/Q symmetry. -/
theorem tsum_kpAbsConnector_le_Q {ρ a : Polymer N → ℝ}
    (hρ : ∀ η, 0 ≤ ρ η) (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis ρ a) (P Q : Polymer N → Prop) :
    (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      ≤ kpForbiddenRootEnvelope ρ a Q :=
  calc (∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ P Q)
      = ∑' k : ℕ, kpAbsConnectorUnrootedCoeff (N := N) k ρ Q P :=
        tsum_congr (fun k =>
          kpAbsConnectorUnrootedCoeff_symm k ρ P Q)
    _ ≤ kpForbiddenRootEnvelope ρ a Q :=
        tsum_kpAbsConnector_le hρ ha hKP Q P

/-! ## A9.5 — the SIGNED local capstones (the domination passes
    through the FILTERED positive connector — the global B⁺ of A8
    has already forgotten where the barrier is) -/

/-- **CAPSTONE 50-A9 (P side)**. -/
theorem tsum_abs_kpConnectorUnrootedCoeff_le
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z P Q|)
      ≤ kpForbiddenRootEnvelope (fun η => |z η|) a P := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k =>
          abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
        (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
      (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
    (tsum_kpAbsConnector_le hρ ha hKP P Q)

/-- **CAPSTONE 50-A9 (Q side)**. -/
theorem tsum_abs_kpConnectorUnrootedCoeff_le_Q
    {z a : Polymer N → ℝ} (ha : ∀ γ, 0 ≤ a γ)
    (hKP : AbstractKPHypothesis (fun η => |z η|) a)
    (P Q : Polymer N → Prop) :
    (∑' k : ℕ, |kpConnectorUnrootedCoeff (N := N) k z P Q|)
      ≤ kpForbiddenRootEnvelope (fun η => |z η|) a Q := by
  have hρ : ∀ η : Polymer N, 0 ≤ |z η| := fun η => abs_nonneg _
  exact le_trans
    (tsum_le_tsum
      (fun k => abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
      (Summable.of_nonneg_of_le (fun k => abs_nonneg _)
        (fun k =>
          abs_kpConnectorUnrootedCoeff_le_filtered k z P Q)
        (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
      (summable_kpAbsConnectorUnrootedCoeff hρ ha hKP P Q))
    (tsum_kpAbsConnector_le_Q hρ ha hKP P Q)

#print axioms kpAbsConnector_succ_le_forbiddenRoot
#print axioms tsum_abs_kpConnectorUnrootedCoeff_le
#print axioms tsum_abs_kpConnectorUnrootedCoeff_le_Q

end LatticeGauge
