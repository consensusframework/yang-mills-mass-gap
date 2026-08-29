/-
LatticeGauge/CovarianceConnectorLedger.lean — PEDRA 50, Gate
50-A18d: EXACT CONNECTOR NORMALIZATION (architecture: Sol;
execution: Fable).

An exact-interface gate: NO estimate enters. The good-pair
bracket of the A18c ledger is replaced LITERALLY by
  R_T·R'_{T'}·(e^{C(T,T')} − 1)
through the A5 cross-ratio, with the denominators cleared by KP
POSITIVITY of the restricted gases (concrete KP → restricted KP
by monotonicity → gas = exp > 0 → ne_of_gt → mul_ne_zero →
div_eq_iff): nonvanishing is an OUTPUT, never a hypothesis. The
published connector-normalized ledger hands A19 three ready
columns: good → connector, bridge and bad textually unchanged.

NOT here (hard hold): no abs, no inequality, no bound of
exp x − 1, no |C| ≤ 1 hypothesis, no A12/A15/A16/A17 analytics
(A16 stays reserved for the A19 ratio bounds), no
WalkBarrierSeparated / n / mass / tilt, no division by Z², no
gibbsCovariance, no covariance bound, no new combinatorial
classification, no new pair structure, no frozen file touched,
no global field_simp.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceNumeratorLedger

open MeasureTheory
open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-! ## A18d.1 — the single transparent connector abbreviation
    (order T T' s s' literally as in A5/A12; A19 consumes the
    A12 bound through `unfold coreConnectorSum` alone) -/

noncomputable def coreConnectorSum (β : ℝ) (χ : G → ℝ)
    (T T' : Finset (Polymer N)) (s s' : Set (Link N)) : ℝ :=
  connectorClusterSum (N := N)
    (fun η => polymerWeight (N := N) μm β χ η.val)
    (remoteAllowed (N := N) T s)
    (remoteAllowed (N := N) T' s')

/-- Definitional dress of the core-restricted gas (bookkeeping
    only — lets rw target the A5 denominators). -/
theorem coreRestrictedGas_def (β : ℝ) (χ : G → ℝ)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    coreRestrictedGas μm β χ T s
      = typedPolymerGas (N := N) (restrictedActivity
          (fun η => polymerWeight (N := N) μm β χ η.val)
          (remoteAllowed (N := N) T s)) := rfl

/-! ## A18d.2 — the union-gas bridge (A18a's activity equality
    consumed; no GoodCorePair, no disjointness, no analysis) -/

theorem coreRestrictedGas_union_eq_and (β : ℝ) (χ : G → ℝ)
    (T T' : Finset (Polymer N)) (s s' : Set (Link N)) :
    coreRestrictedGas μm β χ (T ∪ T') (s ∪ s')
      = typedPolymerGas (N := N)
          (restrictedActivity
            (fun η => polymerWeight (N := N) μm β χ η.val)
            (fun η => remoteAllowed (N := N) T s η
              ∧ remoteAllowed (N := N) T' s' η)) := by
  unfold coreRestrictedGas
  rw [restrictedActivity_union_eq]

/-! ## A18d.3 — positivity of the restricted gas (the mandated
    direct route: concrete KP → restricted KP → gas = exp > 0) -/

theorem coreRestrictedGas_pos {β : ℝ} (hβ : 0 ≤ β)
    {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T : Finset (Polymer N)) (s : Set (Link N)) :
    0 < coreRestrictedGas μm β χ T s := by
  have hKP := abstractKP_of_beta_le_one_div_40000
    (N := N) μm hβ mχ hχabs hsmall
  have ha : ∀ γ : Polymer N, 0 ≤ ((γ.val.card : ℕ) : ℝ) :=
    fun γ => Nat.cast_nonneg _
  exact typedPolymerGas_pos_of_KP ha
    (abstractKP_restrictedActivity
      (remoteAllowed (N := N) T s) hKP)

/-! ## A18d.4 — THE EXACT BRACKET IDENTITY (generic in T, T',
    s, s'; no good-pair hypothesis, no observables) -/

theorem coreRestrictedGas_bracket_eq_connector {β : ℝ}
    (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
    (T T' : Finset (Polymer N)) (s s' : Set (Link N)) :
    coreRestrictedGas μm β χ (T ∪ T') (s ∪ s')
        * typedPolymerGas (N := N)
            (fun η => polymerWeight (N := N) μm β χ η.val)
      - coreRestrictedGas μm β χ T s
        * coreRestrictedGas μm β χ T' s'
      = coreRestrictedGas μm β χ T s
        * coreRestrictedGas μm β χ T' s'
        * (Real.exp (coreConnectorSum μm β χ T T' s s')
            - 1) := by
  have hRT := coreRestrictedGas_pos μm hβ mχ hχabs hsmall T s
  have hRT' := coreRestrictedGas_pos μm hβ mχ hχabs hsmall T' s'
  have hden : coreRestrictedGas μm β χ T s
      * coreRestrictedGas μm β χ T' s' ≠ 0 :=
    mul_ne_zero (ne_of_gt hRT) (ne_of_gt hRT')
  have hcross := polymer_cross_ratio_eq_exp_connector μm hβ mχ
    hχabs hsmall T T' s s'
  rw [← coreRestrictedGas_union_eq_and μm β χ T T' s s',
    ← coreRestrictedGas_def μm β χ T s,
    ← coreRestrictedGas_def μm β χ T' s'] at hcross
  have hmul := (div_eq_iff hden).mp hcross
  unfold coreConnectorSum
  linear_combination hmul

/-! ## A18d.5 — CAPSTONE: the connector-normalized ledger -/

/-- **CAPSTONE 50-A18d**: the A18c ledger with the good column
    literally normalized to (e^C − 1); bridge and bad columns
    textually unchanged. Exact identity — no inequality. -/
theorem covariance_numerator_connector_ledger
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1)
    (hsmall : β ≤ (1 : ℝ) / 40000)
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
          markedCoreGasTerm μm β χ f s p.1
            * markedCoreGasTerm μm β χ g s' p.2
            * (Real.exp
                (coreConnectorSum μm β χ p.1 p.2 s s') - 1))
        + (∑ Γ ∈ bridgeTouchingFamilies (N := N) s s',
            markedCoreGasTerm μm β χ (fun U => f U * g U)
                (s ∪ s') Γ
              * typedPolymerGas (N := N)
                  (fun η => polymerWeight (N := N) μm β χ η.val))
        - ∑ p ∈ badCorePairs (N := N) s s',
            markedCoreGasTerm μm β χ f s p.1
              * markedCoreGasTerm μm β χ g s' p.2 := by
  rw [covariance_numerator_ledger μm mχ hss' hf mf hg mg]
  have hgood : (∑ p ∈ goodCorePairs (N := N) s s',
      typedMarkedCoreWeight μm β χ f p.1
        * typedMarkedCoreWeight μm β χ g p.2
        * (coreRestrictedGas μm β χ (p.1 ∪ p.2) (s ∪ s')
            * typedPolymerGas (N := N)
                (fun η => polymerWeight (N := N) μm β χ η.val)
          - coreRestrictedGas μm β χ p.1 s
            * coreRestrictedGas μm β χ p.2 s'))
      = ∑ p ∈ goodCorePairs (N := N) s s',
          markedCoreGasTerm μm β χ f s p.1
            * markedCoreGasTerm μm β χ g s' p.2
            * (Real.exp
                (coreConnectorSum μm β χ p.1 p.2 s s') - 1) := by
    refine Finset.sum_congr rfl (fun p hp => ?_)
    unfold markedCoreGasTerm
    rw [coreRestrictedGas_bracket_eq_connector μm hβ mχ hχabs
      hsmall p.1 p.2 s s']
    ring
  rw [hgood]

#print axioms coreRestrictedGas_bracket_eq_connector
#print axioms covariance_numerator_connector_ledger

end LatticeGauge
