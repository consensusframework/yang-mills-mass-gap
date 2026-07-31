/-
LatticeGauge/KPMarkedBlock.lean — stone 47 (b-iiB), GATE IV-C.

F(B): THE MARKED-BLOCK CONTRIBUTION AND THE (m+1)! FACTOR
(architecture: Sol/GPT-5.6; execution: Fable). The factor audit that
closes the A-package: summing the fixed-root block sum over the m+1
possible marks turns m! into (m+1)!. ORIGIN OF EACH FACTOR, recorded:
m! comes EXCLUSIVELY from the normalization of kpTreeCoeff (Gate
IV-B); m+1 comes EXCLUSIVELY from the choice of the mark r in the
block (the door through which the component meets the global root);
their product is (m+1)!; ρ(η) appears exactly once, η being the
internal root of the component; the external root γ₀ carries no
activity; NO component enumeration was counted here and NO ordered
partition was used (those are Gates V-VI). The key rewriting step:
for EVERY r : ↥B, blockTailCard B r = m follows from |B| = m + 1
(named lemma, plain-ℕ rewrite — no dependent motive), after which
the inner sum is literally constant in r; counting the marks uses
Fintype.card ↥B = B.card = m + 1 with the three cardinalities kept
distinct; the factorial identity (m+1)·m! = (m+1)! is a separate
arithmetic lemma consuming Nat.factorial_succ, never hidden in ring.
This gate proves an exact algebraic identity: NO nonnegativity of ρ
is required. Sanities: |B| = 1 collapses to Σ_η incompat·ρ(η)
(kpTreeCoeff 0 = 1, 1! = 1); |B| = 2 exhibits the explicit 2!.
NOT here: no ordered partitions, no Σ j Fin (s j + 1), no
multinomial, no weak compositions, no degree strata sums, no
recurrence, no 1/k!, no partial sums, no KP, no exp, no Summable.
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

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)] {n : ℕ}

/-! ## IV-C.1 — the marked-block contribution -/

/-- The contribution of a block with VARIABLE mark: sum over the
    mark r and the internal root value η of the incompatibility
    switch against γ₀, the single activity ρ(η), and the fixed-root
    block sum. The external root γ₀ carries no activity. -/
noncomputable def markedBlockContribution (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) (B : Finset (Fin n)) : ℝ :=
  ∑ r : {x // x ∈ B}, ∑ η : Polymer N,
    (incompatibilityIndicator γ₀ η : ℝ) * ρ η
      * fixedRootBlockSum ρ B r η

/-! ## IV-C.2 — the tail cardinality for every mark -/

theorem blockTailCard_eq {B : Finset (Fin n)} {m : ℕ}
    (hB : B.card = m + 1) (r : {x // x ∈ B}) :
    blockTailCard B r = m := by
  unfold blockTailCard
  have h := Finset.card_erase_of_mem r.2
  omega

/-! ## IV-C.3 — the uniform substitution of the IV-B capstone -/

/-- After the tail rewrite the right side is literally independent
    of r. -/
theorem fixedRootBlockSum_eq_uniform_factorial_mul
    (ρ : Polymer N → ℝ) {B : Finset (Fin n)} {m : ℕ}
    (hB : B.card = m + 1) (r : {x // x ∈ B}) (η : Polymer N) :
    fixedRootBlockSum ρ B r η
      = ((Nat.factorial m : ℕ) : ℝ) * kpTreeCoeff m ρ η := by
  have h := fixedRootBlockSum_eq_factorial_mul_kpTreeCoeff ρ B r η
  rwa [blockTailCard_eq hB r] at h

/-! ## IV-C.5 — the factorial identity, visible -/

theorem cast_succ_mul_factorial (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * ((Nat.factorial m : ℕ) : ℝ)
      = ((Nat.factorial (m + 1) : ℕ) : ℝ) := by
  rw [← Nat.cast_mul]
  congr 1

/-! ## IV-C.4/6 — CAPSTONE: F(B) -/

/-- **F(B), formal**: one mark among m+1 possibilities × m! internal
    normalizations = (m+1)!. Factor audit: m! from kpTreeCoeff's
    normalization only; m+1 from the choice of the mark only; ρ(η)
    exactly once (η = internal root); γ₀ activity absent; no
    component enumerations, no ordered partitions. -/
theorem markedBlockContribution_eq_factorial_mul
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) {B : Finset (Fin n)}
    {m : ℕ} (hB : B.card = m + 1) :
    markedBlockContribution ρ γ₀ B
      = ((Nat.factorial (m + 1) : ℕ) : ℝ)
        * ∑ η : Polymer N,
            (incompatibilityIndicator γ₀ η : ℝ) * ρ η
              * kpTreeCoeff m ρ η := by
  unfold markedBlockContribution
  have hinner : ∀ r : {x // x ∈ B},
      (∑ η : Polymer N,
          (incompatibilityIndicator γ₀ η : ℝ) * ρ η
            * fixedRootBlockSum ρ B r η)
        = ((Nat.factorial m : ℕ) : ℝ)
          * ∑ η : Polymer N,
              (incompatibilityIndicator γ₀ η : ℝ) * ρ η
                * kpTreeCoeff m ρ η := by
    intro r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun η _ => ?_)
    rw [fixedRootBlockSum_eq_uniform_factorial_mul ρ hB r η]
    ring
  calc (∑ r : {x // x ∈ B}, ∑ η : Polymer N,
        (incompatibilityIndicator γ₀ η : ℝ) * ρ η
          * fixedRootBlockSum ρ B r η)
      = ∑ _r : {x // x ∈ B},
          ((Nat.factorial m : ℕ) : ℝ)
            * ∑ η : Polymer N,
                (incompatibilityIndicator γ₀ η : ℝ) * ρ η
                  * kpTreeCoeff m ρ η :=
        Finset.sum_congr rfl (fun r _ => hinner r)
    _ = (Fintype.card {x // x ∈ B})
          • (((Nat.factorial m : ℕ) : ℝ)
            * ∑ η : Polymer N,
                (incompatibilityIndicator γ₀ η : ℝ) * ρ η
                  * kpTreeCoeff m ρ η) := by
        rw [Finset.sum_const, Finset.card_univ]
    _ = ((m + 1 : ℕ) : ℝ)
          * (((Nat.factorial m : ℕ) : ℝ)
            * ∑ η : Polymer N,
                (incompatibilityIndicator γ₀ η : ℝ) * ρ η
                  * kpTreeCoeff m ρ η) := by
        rw [nsmul_eq_mul, Fintype.card_coe, hB]
    _ = ((Nat.factorial (m + 1) : ℕ) : ℝ)
          * ∑ η : Polymer N,
              (incompatibilityIndicator γ₀ η : ℝ) * ρ η
                * kpTreeCoeff m ρ η := by
        rw [← mul_assoc, cast_succ_mul_factorial]

/-! ## Sanities -/

/-- m = 0: one mark, empty interior, contribution
    Σ_η incompat·ρ(η). -/
theorem markedBlockContribution_card_one (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {B : Finset (Fin n)} (hB : B.card = 1) :
    markedBlockContribution ρ γ₀ B
      = ∑ η : Polymer N,
          (incompatibilityIndicator γ₀ η : ℝ) * ρ η := by
  have h := markedBlockContribution_eq_factorial_mul ρ γ₀
    (m := 0) hB
  rw [h]
  have hcoeff : ∀ η : Polymer N, kpTreeCoeff 0 ρ η = 1 :=
    fun η => kpTreeCoeff_zero ρ η
  rw [Finset.sum_congr rfl (fun η _ => by rw [hcoeff η, mul_one])]
  norm_num [Nat.factorial]

/-- m = 1: two marks, each interior worth 1!, explicit total factor
    2!. -/
theorem markedBlockContribution_card_two (ρ : Polymer N → ℝ)
    (γ₀ : Polymer N) {B : Finset (Fin n)} (hB : B.card = 2) :
    markedBlockContribution ρ γ₀ B
      = ((Nat.factorial 2 : ℕ) : ℝ)
        * ∑ η : Polymer N,
            (incompatibilityIndicator γ₀ η : ℝ) * ρ η
              * kpTreeCoeff 1 ρ η :=
  markedBlockContribution_eq_factorial_mul ρ γ₀ (m := 1) hB

end LatticeGauge
