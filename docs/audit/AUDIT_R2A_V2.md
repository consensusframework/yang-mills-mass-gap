# AUDIT_R2A_V2.md — triagem com metodologia corrigida (parecer Sol #3)

REGRAS: theorem/lemma com TIPO COMPLETO igual = mesma proposição
(duplicata de enunciado, ainda que nomes/provas difiram; podem virar
alias). def/abbrev: mesmo tipo NÃO implica mesmo objeto — comparação de
CORPO. Assinaturas truncadas = NEEDS_KERNEL_CHECK. Canônica: nunca
GeminiValidation; preferir módulo matematicamente nomeado.

ZERO remoções nesta rodada.

## Grupo 1 [PROPOSIÇÃO] (2 ativas, 6 em archive)
- `mass_gap_numerical_consistency` (theorem) — Phase1/YangMills/EntropicPrinciple_Standalone.lean:164
- `mass_gap_numerical_consistency` (theorem) — Phase1/YangMills/EntropicTest.lean:52
- assinatura: `: abs (predicted_mass_gap - experimental_mass_gap) / experimental_mass_gap < 0.02`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `mass_gap_numerical_consistency` @ Phase1/YangMills/EntropicPrinciple_Standalone.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CLASSIFY_ONLY (Phase1 sem CI)**

## Grupo 2 [DEF/DADO] (5 ativas, 0 em archive)
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation12.lean:84
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation13.lean:91
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:21
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:85
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:99
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Filter.Tendsto (fun a : ℝ => mass_gap g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (D`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 3 [DEF/DADO] (4 ativas, 0 em archive)
- `lowestEigenvalue` (axiom) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:114
- `spectralZetaFunction_derivative_at_zero` (axiom) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:154
- `fpDeterminant` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:160
- `signOfDeterminant` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:164
- assinatura: `(M_FP : FPOperator M N P) (A : Connection M N P) : ℝ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 4 [DEF/DADO] (4 ativas, 0 em archive)
- `continuum_mass_gap_lower_bound` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:62
- `mass_gap_lower_bound_continuum` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:207
- `mass_gap_lower_bound_continuum` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:245
- `continuum_mass_gap_lower_bound` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:77
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : (0.5 : ℝ) ≤ Delta0 g`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 5 [DEF/DADO] (2 ativas, 1 em archive)
- `mutual_information` (axiom) — Phase1/YangMills/EntropicPrinciple_Standalone.lean:60
- `mutual_information` (axiom) — Phase1/YangMills/EntropicTest.lean:18
- assinatura: `: DensityMatrix → DensityMatrix → ℝ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 6 [DEF/DADO] (3 ativas, 0 em archive)
- `orientationReversalPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:68
- `conjugationReflectionPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:80
- `hodgeDualPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:92
- assinatura: `(M : Manifold4D) (N : ℕ) (P : PrincipalBundle M N) : PairingMap M N P where map A`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 7 [PROPOSIÇÃO] (3 ativas, 0 em archive)
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:39
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:121
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:123
- assinatura: `: Set.Ioc (0 : ℝ) 0.2 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `Ioc_mem_nhdsWithin_Ioi_zero` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CONSOLIDATE→alias (PR pequeno, 3 jobs verdes)**

## Grupo 8 [DEF/DADO] (2 ativas, 0 em archive)
- `yangMillsAction` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M3_Compactness.lean:200
- `yangMillsAction` (def) — Phase1/YangMills/Gap2/AtiyahSinger/BRST_Exactness.lean:129
- assinatura: `{M : Manifold4D} {N : ℕ} {P : PrincipalBundle M N} (A : Connection M N P) : ℝ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 9 [DEF/DADO] (2 ativas, 0 em archive)
- `BRSTClosed` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M5_BRSTCohomology.lean:66
- `BRSTExact` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M5_BRSTCohomology.lean:70
- assinatura: `(Q : BRSTOperator M N) (ω : Connection M N) : Prop`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 10 [DEF/DADO] (2 ativas, 0 em archive)
- `fpDeterminant` (def) — Phase1/YangMills/Gap2/AtiyahSinger/FP_DeterminantParity.lean:45
- `pathIntegralMeasure` (def) — Phase1/YangMills/Gap2/AtiyahSinger/FP_DeterminantParity.lean:115
- assinatura: `{M : Manifold4D} {N : ℕ} {P : PrincipalBundle M N} {A : Connection M N P} (M_FP : FPOperator A) : ℝ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 11 [DEF/DADO] (2 ativas, 0 em archive)
- `chernClass2` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:105
- `instantonNumber` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:110
- assinatura: `{M : Manifold4D} {N : ℕ} {P : PrincipalBundle M N} (A : Connection M N P) : ℤ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 12 [DEF/DADO] (2 ativas, 0 em archive)
- `topologicalSector` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:136
- `moduliSector` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:133
- assinatura: `(M : Manifold4D) (N : ℕ) (P : PrincipalBundle M N) (k : ℤ) : Type*`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 13 [DEF/DADO] (2 ativas, 0 em archive)
- `faddeevPopovDeterminant` (def) — Phase1/YangMills/Gap2/GribovCancellation.lean:31
- `gribovFunctional` (def) — Phase1/YangMills/Gap2/GribovCancellation.lean:34
- assinatura: `(F : Type*) [GaugeTheoryFields F] : F`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 14 [DEF/DADO] (2 ativas, 0 em archive)
- `laplacian` (def) — Phase1/YangMills/Gap4/RicciLimit.lean:3
- `topological_term` (def) — Phase1/YangMills/Gap4/RicciLimit.lean:7
- assinatura: `{A : Type*} [ConnectionSpace A] (h : TangentVector A) : ℝ`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 15 [DEF/DADO] (2 ativas, 0 em archive)
- `mass_gap_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation12.lean:75
- `mass_gap_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:76
- assinatura: `(g₁ g₂ a : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) (ha : 0 < a ∧ a ≤ 0.2) : |mass_gap g₁ a - mass_g`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 16 [DEF/DADO] (2 ativas, 0 em archive)
- `mass_gap_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation13.lean:81
- `mass_gap_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:89
- assinatura: `(g₁ g₂ a : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) (hg_order : g₁ < g₂) (ha : 0 < a ∧ a ≤ 0.2) : ma`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 17 [DEF/DADO] (2 ativas, 0 em archive)
- `mass_gap_A_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:80
- `mass_gap_A_tendsto` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:90
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Filter.Tendsto (fun a : ℝ => mass_gap_A g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds `
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 18 [DEF/DADO] (2 ativas, 0 em archive)
- `mass_gap_B_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:90
- `mass_gap_B_tendsto` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:99
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Filter.Tendsto (fun a : ℝ => mass_gap_B g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds `
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 19 [DEF/DADO] (2 ativas, 0 em archive)
- `scheme_diff_order_a` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:101
- `scheme_diff_O_a` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:119
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : ∃ C : ℝ, 0 < C ∧ ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), |mass_gap_A g a - mass_gap_`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 20 [PROPOSIÇÃO] (2 ativas, 0 em archive)
- `gemini_scheme_agreement_trivial` (theorem) — Phase2/RGFlow_Work/GeminiValidation14.lean:111
- `rg_invariance` (theorem) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:190
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Delta0 g = Delta0 g`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `rg_invariance` @ Phase2/RGFlow_Work/Theorem14_RGInvariance.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CONSOLIDATE→alias (PR pequeno, 3 jobs verdes)**

## Grupo 21 [DEF/DADO] (2 ativas, 0 em archive)
- `continuum_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:67
- `continuum_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:82
- assinatura: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) : |Delta0 g₁ - Delta0 g₂| ≤ 2.0 * |g₁ - g₂|`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 22 [DEF/DADO] (2 ativas, 0 em archive)
- `continuum_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:74
- `continuum_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:89
- assinatura: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) (h_order : g₁ < g₂) : Delta0 g₂ < Delta0 g₁`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Grupo 23 [PROPOSIÇÃO] (2 ativas, 0 em archive)
- `continuum_mass_gap_positive` (theorem) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:98
- `mass_gap_strictly_positive_strong` (theorem) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:167
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : (0 : ℝ) < Delta0 g`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `continuum_mass_gap_positive` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CONSOLIDATE→alias (PR pequeno, 3 jobs verdes)**

## Grupo 24 [PROPOSIÇÃO] (2 ativas, 0 em archive)
- `continuum_mass_gap_ne_zero` (theorem) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:107
- `mass_gap_never_vanishes` (theorem) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:183
- assinatura: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Delta0 g ≠ 0`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `continuum_mass_gap_ne_zero` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CONSOLIDATE→alias (PR pequeno, 3 jobs verdes)**

## Grupo 25 [PROPOSIÇÃO] (2 ativas, 0 em archive)
- `mass_gap_diff_tendsto` (lemma) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:97
- `gap_diff_tendsto` (lemma) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:144
- assinatura: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) : Filter.Tendsto (fun a : ℝ => mass_gap g₁ a - mas`
- Mesma proposição (tipos completos idênticos). Canônica proposta: `mass_gap_diff_tendsto` @ Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean (política: módulo matemático, nunca GeminiValidation).
- **Ação: CONSOLIDATE→alias (PR pequeno, 3 jobs verdes)**

## Grupo 26 [DEF/DADO] (2 ativas, 0 em archive)
- `shift` (def) — Phase3/LatticeGauge/Basic.lean:31
- `shiftBack` (def) — Phase3/LatticeGauge/WilsonLoop.lean:17
- assinatura: `(x : Site N) (μ : Dir) [NeZero N] : Site N`
- Corpos distintos (ex.: shift/shiftBack têm a mesma assinatura) → **Ação: NOT_DUPLICATE (mesmo tipo, objetos diferentes)**

## Resumo: 26 grupos ativos triados; consolidações aguardam kernel-check e PRs individuais.