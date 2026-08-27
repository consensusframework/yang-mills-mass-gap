/-
LatticeGauge/CovarianceNumeratorLedger.lean — PEDRA 50, Gate
50-A18c: THE EXACT LEDGER OF THE NUMERATOR (architecture: Sol;
execution: Fable).

An exact FINITE identity in ℝ — no estimate, no absolute value,
no decay anywhere:
  M_fg·Z − M_f·M_g
    = Σ_{(T,T') good} W_f(T)·W_g(T')·(R_{T∪T'}^∪·Z − R_T·R'_{T'})
    + Σ_{Γ bridged}   W_fg(Γ)·R_Γ^∪·Z
    − Σ_{(T,T') bad}  (W_f(T)·R_T)·(W_g(T')·R'_{T'}),
where M is the marked gas (A2/A3), Z the full gas, W the
typedMarkedCoreWeight and R the core-restricted gas.
coreRestrictedGas and markedCoreGasTerm are TRANSPARENT
abbreviations of the published expressions (definitional only).
Good pairs factorize their joint core weight through A13's
bridge-free factorization with the A18a roundtrips; bridge
families are carried exactly; bad pairs are subtracted exactly.

NOT here (hard hold): no connector, no exp(C) − 1, no
β ≤ 1/40000 hypothesis, no KP / A12 / A16 / A17 analytics, no
absolute value, no mass, no n, no tilt, no covariance bound, no
new index structure, no frozen file rewritten.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceBadPairMass

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A18c.1 — transparent abbreviations -/

noncomputable def coreRestrictedGas (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s : Set (Link N)) : ℝ :=
  typedPolymerGas (N := N) (restrictedActivity
    (fun η => polymerWeight (N := N) μm β χ η.val)
    (remoteAllowed (N := N) T s))

noncomputable def markedCoreGasTerm (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N))
    (T : Finset (Polymer N)) : ℝ :=
  typedMarkedCoreWeight μm β χ f T
    * coreRestrictedGas μm β χ T s

/-- The published A3 core sum, in the abbreviated dress
    (definitional repackaging only). -/
theorem typedMarkedPolymerGas_eq_sum_terms (β : ℝ) (χ : G → ℝ)
    (f : Config N G → ℝ) (s : Set (Link N)) :
    typedMarkedPolymerGas μm β χ f s
      = ∑ T ∈ typedTouchingFamilies (N := N) s,
          markedCoreGasTerm μm β χ f s T :=
  typedMarkedPolymerGas_eq_sum_core_mul_restricted μm β χ f s

/-! ## A18c.2 — the bridged families (exact complement) -/

noncomputable def bridgeTouchingFamilies (s s' : Set (Link N)) :
    Finset (Finset (Polymer N)) :=
  (typedTouchingFamilies (N := N) (s ∪ s')).filter
    (fun Γ => bridgeCore Γ s s' ≠ ∅)

theorem mem_bridgeTouchingFamilies {s s' : Set (Link N)}
    {Γ : Finset (Polymer N)} :
    Γ ∈ bridgeTouchingFamilies s s'
      ↔ Γ ∈ typedTouchingFamilies (N := N) (s ∪ s')
        ∧ bridgeCore Γ s s' ≠ ∅ :=
  Finset.mem_filter

theorem free_union_bridge (s s' : Set (Link N)) :
    bridgeFreeTouchingFamilies (N := N) s s'
        ∪ bridgeTouchingFamilies s s'
      = typedTouchingFamilies (N := N) (s ∪ s') := by
  unfold bridgeFreeTouchingFamilies bridgeTouchingFamilies
  ext Γ
  rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro h
    by_cases hb : bridgeCore Γ s s' = ∅
    · exact Or.inl ⟨h, hb⟩
    · exact Or.inr ⟨h, hb⟩

theorem free_disjoint_bridge (s s' : Set (Link N)) :
    Disjoint (bridgeFreeTouchingFamilies (N := N) s s')
      (bridgeTouchingFamilies s s') := by
  rw [Finset.disjoint_left]
  intro Γ hfree hbr
  exact (mem_bridgeTouchingFamilies.mp hbr).2
    (mem_bridgeFreeTouchingFamilies.mp hfree).2

/-- Generic split of any additive sum over the touching families
    of the union into bridge-free + bridged. -/
theorem sum_touchingUnion_eq_free_add_bridge {M : Type*}
    [AddCommMonoid M] (s s' : Set (Link N))
    (F : Finset (Polymer N) → M) :
    (∑ Γ ∈ typedTouchingFamilies (N := N) (s ∪ s'), F Γ)
      = (∑ Γ ∈ bridgeFreeTouchingFamilies (N := N) s s', F Γ)
        + ∑ Γ ∈ bridgeTouchingFamilies s s', F Γ := by
  rw [← free_union_bridge s s',
    Finset.sum_union (free_disjoint_bridge s s')]

/-! ## A18c.3 — the good pair factorizes its joint core weight
    (A13 through the A18a roundtrips; no integral refactored) -/

theorem goodPair_coreWeight_factorizes
    {β : ℝ} {χ : G → ℝ} (mχ : Measurable χ)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g)
    {p : Finset (Polymer N) × Finset (Polymer N)}
    (hp : p ∈ goodCorePairs (N := N) s s') :
    typedMarkedCoreWeight μm β χ (fun U => f U * g U)
        (p.1 ∪ p.2)
      = typedMarkedCoreWeight μm β χ f p.1
        * typedMarkedCoreWeight μm β χ g p.2 := by
  have hmem := union_mem_bridgeFreeTouchingFamilies hp
  obtain ⟨ht, hb⟩ := mem_bridgeFreeTouchingFamilies.mp hmem
  have hΓc : TypedCompatible (p.1 ∪ p.2) :=
    mem_typedCompatiblePolymerFamilies.mp
      (Finset.mem_filter.mp ht).1
  have hfact := twoMarkedFamilyIntegral_factorizes (β := β)
    μm mχ hss' hf mf hg mg hΓc hb
  rw [leftOnlyCore_union_eq hp, rightOnlyCore_union_eq hp,
    remoteBothCore_eq_empty_of_touching ht,
    Finset.prod_empty, mul_one] at hfact
  exact hfact

/-! ## A18c.4 — THE CAPSTONE: the exact ledger -/

/-- **CAPSTONE 50-A18c**: the literal ℝ-identity
    M_fg·Z − M_f·M_g = good bracket + bridged − bad. No
    inequality, no absolute value, no decay. -/
theorem covariance_numerator_ledger
    {β : ℝ} {χ : G → ℝ} (mχ : Measurable χ)
    {s s' : Set (Link N)} (hss' : Disjoint s s')
    {f g : Config N G → ℝ}
    (hf : DependsOnlyOn f s) (mf : Measurable f)
    (hg : DependsOnlyOn g s') (mg : Measurable g) :
    typedMarkedPolymerGas μm β χ (fun U => f U * g U) (s ∪ s')
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val)
      - typedMarkedPolymerGas μm β χ f s
        * typedMarkedPolymerGas μm β χ g s'
      = (∑ p ∈ goodCorePairs (N := N) s s',
          typedMarkedCoreWeight μm β χ f p.1
            * typedMarkedCoreWeight μm β χ g p.2
            * (coreRestrictedGas μm β χ (p.1 ∪ p.2) (s ∪ s')
                * typedPolymerGas (N := N)
                    (fun η => polymerWeight (N := N) μm β χ η.val)
              - coreRestrictedGas μm β χ p.1 s
                * coreRestrictedGas μm β χ p.2 s'))
        + (∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
            markedCoreGasTerm μm β χ (fun U => f U * g U)
                (s ∪ s') Γ
              * typedPolymerGas (N := N)
                  (fun η => polymerWeight (N := N) μm β χ η.val))
        - ∑ p ∈ badCorePairs (N := N) s s',
            markedCoreGasTerm μm β χ f s p.1
              * markedCoreGasTerm μm β χ g s' p.2 := by
  have hpairs : typedTouchingFamilyPairs (N := N) s s'
      = typedTouchingFamilies (N := N) s
        ×ˢ typedTouchingFamilies (N := N) s' := rfl
  rw [typedMarkedPolymerGas_eq_sum_terms μm β χ
      (fun U => f U * g U) (s ∪ s'),
    typedMarkedPolymerGas_eq_sum_terms μm β χ f s,
    typedMarkedPolymerGas_eq_sum_terms μm β χ g s',
    Finset.sum_mul,
    sum_touchingUnion_eq_free_add_bridge s s'
      (fun Γ => markedCoreGasTerm μm β χ (fun U => f U * g U)
          (s ∪ s') Γ
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val)),
    sum_bridgeFree_eq_sum_goodPairs s s'
      (fun Γ => markedCoreGasTerm μm β χ (fun U => f U * g U)
          (s ∪ s') Γ
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val)),
    Finset.sum_mul_sum, ← Finset.sum_product', ← hpairs,
    sum_pairs_eq_good_add_bad s s'
      (fun p => markedCoreGasTerm μm β χ f s p.1
        * markedCoreGasTerm μm β χ g s' p.2)]
  have hAC : (∑ p ∈ goodCorePairs (N := N) s s',
      markedCoreGasTerm μm β χ (fun U => f U * g U)
          (s ∪ s') (p.1 ∪ p.2)
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val))
      - (∑ p ∈ goodCorePairs (N := N) s s',
          markedCoreGasTerm μm β χ f s p.1
            * markedCoreGasTerm μm β χ g s' p.2)
      = ∑ p ∈ goodCorePairs (N := N) s s',
          typedMarkedCoreWeight μm β χ f p.1
            * typedMarkedCoreWeight μm β χ g p.2
            * (coreRestrictedGas μm β χ (p.1 ∪ p.2) (s ∪ s')
                * typedPolymerGas (N := N)
                    (fun η => polymerWeight (N := N) μm β χ η.val)
              - coreRestrictedGas μm β χ p.1 s
                * coreRestrictedGas μm β χ p.2 s') := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    unfold markedCoreGasTerm
    rw [goodPair_coreWeight_factorizes μm mχ hss'
      hf mf hg mg hp]
    ring
  linarith [hAC]

#print axioms goodPair_coreWeight_factorizes
#print axioms covariance_numerator_ledger

end LatticeGauge
