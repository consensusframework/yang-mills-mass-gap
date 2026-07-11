# AUDIT_R2A_V3.md — classificação pelo SORT do tipo (parecer Sol #2, rodada 3)

REGRA: theorem/lemma/AXIOM com conclusão em Prop → PROPOSITIONAL
(tipos completos iguais = MESMO ENUNCIADO; para axiomas = mesmo
PRESSUPOSTO assumido duas vezes). def/abbrev/opaque/axiom não-Prop →
DATA (tipos iguais não implicam mesmo objeto; axiomas não têm corpo).
Detecção de Prop é heurística sintática — confirmação final no kernel.
ZERO consolidações nesta rodada.

## Grupo 1 [PROPOSITIONAL] (2 ativas; kinds: theorem)
- `mass_gap_numerical_consistency` (theorem) — Phase1/YangMills/EntropicPrinciple_Standalone.lean:164
- `mass_gap_numerical_consistency` (theorem) — Phase1/YangMills/EntropicTest.lean:52
- conclusão: `abs (predicted_mass_gap - experimental_mass_gap) / experimental_mass_gap < 0.02`
- Mesmo enunciado provado múltiplas vezes. Canônica: `mass_gap_numerical_consistency` @ Phase1/YangMills/EntropicPrinciple_Standalone.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 2 [PROPOSITIONAL] (5 ativas; kinds: axiom)
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation12.lean:84
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation13.lean:91
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:21
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:85
- `mass_gap_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:99
- conclusão: `Filter.Tendsto (fun a : ℝ => mass_gap g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Delta0 g))`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 3 [PROPOSITIONAL] (5 ativas; kinds: axiom,theorem)
- `continuum_mass_gap_lower_bound` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:62
- `continuum_mass_gap_lower_bound` (theorem) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:79
- `mass_gap_lower_bound_continuum` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:207
- `mass_gap_lower_bound_continuum` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:245
- `continuum_mass_gap_lower_bound` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:77
- conclusão: `(0.5 : ℝ) ≤ Delta0 g`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 4 [DATA] (4 ativas; kinds: axiom,def)
- `lowestEigenvalue` (axiom) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:114
- `spectralZetaFunction_derivative_at_zero` (axiom) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:154
- `fpDeterminant` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:160
- `signOfDeterminant` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean:164
- conclusão: `ℝ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 5 [UNCLEAR] (2 ativas; kinds: axiom)
- `mutual_information` (axiom) — Phase1/YangMills/EntropicPrinciple_Standalone.lean:60
- `mutual_information` (axiom) — Phase1/YangMills/EntropicTest.lean:18
- conclusão: `DensityMatrix → DensityMatrix → ℝ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 6 [DATA] (3 ativas; kinds: def)
- `orientationReversalPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:68
- `conjugationReflectionPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:80
- `hodgeDualPairing` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:92
- conclusão: `PairingMap M N P where map A`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 7 [PROPOSITIONAL] (3 ativas; kinds: axiom,theorem)
- `continuum_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:67
- `continuum_lipschitz_in_g` (theorem) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:159
- `continuum_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:82
- conclusão: `|Delta0 g₁ - Delta0 g₂| ≤ 2.0 * |g₁ - g₂|`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 8 [PROPOSITIONAL] (3 ativas; kinds: axiom,theorem)
- `continuum_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation15.lean:74
- `continuum_monotonic_in_g` (theorem) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:188
- `continuum_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:89
- conclusão: `Delta0 g₂ < Delta0 g₁`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 9 [PROPOSITIONAL] (3 ativas; kinds: lemma)
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:39
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:121
- `Ioc_mem_nhdsWithin_Ioi_zero` (lemma) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:123
- conclusão: `Set.Ioc (0 : ℝ) 0.2 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)`
- Mesmo enunciado provado múltiplas vezes. Canônica: `Ioc_mem_nhdsWithin_Ioi_zero` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 10 [DATA] (2 ativas; kinds: def)
- `yangMillsAction` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M3_Compactness.lean:200
- `yangMillsAction` (def) — Phase1/YangMills/Gap2/AtiyahSinger/BRST_Exactness.lean:129
- conclusão: `ℝ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 11 [PROPOSITIONAL] (2 ativas; kinds: def)
- `BRSTClosed` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M5_BRSTCohomology.lean:66
- `BRSTExact` (def) — Phase1/YangMills/Gap1/BRSTMeasure/M5_BRSTCohomology.lean:70
- conclusão: `Prop`
- Mesmo enunciado provado múltiplas vezes. Canônica: `BRSTClosed` @ Phase1/YangMills/Gap1/BRSTMeasure/M5_BRSTCohomology.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 12 [DATA] (2 ativas; kinds: def)
- `fpDeterminant` (def) — Phase1/YangMills/Gap2/AtiyahSinger/FP_DeterminantParity.lean:45
- `pathIntegralMeasure` (def) — Phase1/YangMills/Gap2/AtiyahSinger/FP_DeterminantParity.lean:115
- conclusão: `ℝ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 13 [DATA] (2 ativas; kinds: def)
- `chernClass2` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:105
- `instantonNumber` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:110
- conclusão: `ℤ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 14 [DATA] (2 ativas; kinds: def)
- `topologicalSector` (def) — Phase1/YangMills/Gap2/AtiyahSinger/IndexTheorem.lean:136
- `moduliSector` (def) — Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean:133
- conclusão: `Type*`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 15 [DATA] (2 ativas; kinds: def)
- `faddeevPopovDeterminant` (def) — Phase1/YangMills/Gap2/GribovCancellation.lean:31
- `gribovFunctional` (def) — Phase1/YangMills/Gap2/GribovCancellation.lean:34
- conclusão: `F`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 16 [DATA] (2 ativas; kinds: def)
- `laplacian` (def) — Phase1/YangMills/Gap4/RicciLimit.lean:3
- `topological_term` (def) — Phase1/YangMills/Gap4/RicciLimit.lean:7
- conclusão: `ℝ`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Grupo 17 [PROPOSITIONAL] (2 ativas; kinds: axiom)
- `mass_gap_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation12.lean:75
- `mass_gap_lipschitz_in_g` (axiom) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:76
- conclusão: `|mass_gap g₁ a - mass_gap g₂ a| ≤ 2.0 * |g₁ - g₂|`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 18 [PROPOSITIONAL] (2 ativas; kinds: axiom)
- `mass_gap_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/GeminiValidation13.lean:81
- `mass_gap_monotonic_in_g` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:89
- conclusão: `mass_gap g₂ a < mass_gap g₁ a`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 19 [PROPOSITIONAL] (2 ativas; kinds: axiom)
- `mass_gap_A_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:80
- `mass_gap_A_tendsto` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:90
- conclusão: `Filter.Tendsto (fun a : ℝ => mass_gap_A g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Delta0 g))`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 20 [PROPOSITIONAL] (2 ativas; kinds: axiom)
- `mass_gap_B_tendsto_continuum` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:90
- `mass_gap_B_tendsto` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:99
- conclusão: `Filter.Tendsto (fun a : ℝ => mass_gap_B g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Delta0 g))`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 21 [PROPOSITIONAL] (2 ativas; kinds: axiom)
- `scheme_diff_order_a` (axiom) — Phase2/RGFlow_Work/GeminiValidation14.lean:101
- `scheme_diff_O_a` (axiom) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:119
- conclusão: `ℝ, 0 < C ∧ ∀ᶠ a in nhdsWithin (0 : ℝ) (Set.Ioi 0), |mass_gap_A g a - mass_gap_B g a| ≤ C * a`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 22 [PROPOSITIONAL] (2 ativas; kinds: theorem)
- `gemini_scheme_agreement_trivial` (theorem) — Phase2/RGFlow_Work/GeminiValidation14.lean:111
- `rg_invariance` (theorem) — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:190
- conclusão: `Delta0 g = Delta0 g`
- Mesmo enunciado provado múltiplas vezes. Canônica: `rg_invariance` @ Phase2/RGFlow_Work/Theorem14_RGInvariance.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 23 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `limit_unique_aux` (axiom) — Phase2/RGFlow_Work/Theorem10_ContinuumLimitExistence.lean:60
- `continuum_limit_unique` (theorem) — Phase2/RGFlow_Work/Theorem10_ContinuumLimitExistence.lean:75
- conclusão: `L1 = L2`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 24 [PROPOSITIONAL] (2 ativas; kinds: theorem)
- `continuum_mass_gap_positive` (theorem) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:98
- `mass_gap_strictly_positive_strong` (theorem) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:167
- conclusão: `(0 : ℝ) < Delta0 g`
- Mesmo enunciado provado múltiplas vezes. Canônica: `continuum_mass_gap_positive` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 25 [PROPOSITIONAL] (2 ativas; kinds: theorem)
- `continuum_mass_gap_ne_zero` (theorem) — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:107
- `mass_gap_never_vanishes` (theorem) — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:183
- conclusão: `Delta0 g ≠ 0`
- Mesmo enunciado provado múltiplas vezes. Canônica: `continuum_mass_gap_ne_zero` @ Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 26 [PROPOSITIONAL] (2 ativas; kinds: lemma)
- `mass_gap_diff_tendsto` (lemma) — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:97
- `gap_diff_tendsto` (lemma) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:144
- conclusão: `Filter.Tendsto (fun a : ℝ => mass_gap g₁ a - mass_gap g₂ a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Delta0 g₁ `
- Mesmo enunciado provado múltiplas vezes. Canônica: `mass_gap_diff_tendsto` @ Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean. Ação: CONSOLIDATE→alias (PR pequeno).

## Grupo 27 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `continuum_gap_quantitative_separation` (axiom) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:113
- `continuum_gap_quantitative_bound` (theorem) — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:217
- conclusão: `0.2 * (g₂ - g₁) ≤ Delta0 g₁ - Delta0 g₂`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 28 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `coupling_decrease_from_ref` (axiom) — Phase2/RGFlow_Work/Theorem2_Monotonicity.lean:85
- `coupling_decreases_from_reference` (theorem) — Phase2/RGFlow_Work/Theorem2_Monotonicity.lean:92
- conclusão: `running_coupling μ μ₀ g₀ a < g₀`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 29 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `coupling_stays_bounded_aux` (axiom) — Phase2/RGFlow_Work/Theorem3_BoundPreservation.lean:84
- `no_landau_pole` (theorem) — Phase2/RGFlow_Work/Theorem3_BoundPreservation.lean:102
- conclusão: `running_coupling μ μ₀ g₀ a ≤ g0`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 30 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `continuity_from_lipschitz` (axiom) — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:89
- `mass_gap_continuous` (theorem) — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:99
- conclusão: `|mass_gap g1 a - mass_gap g2 a| < lipschitz_L * eps`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 31 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `gap_bounded_aux` (axiom) — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:111
- `gap_bounded_across_region` (theorem) — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:115
- conclusão: `|mass_gap 0.5 a - mass_gap 1.18 a| ≤ lipschitz_L * 0.68`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 32 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `no_plateaus_aux` (axiom) — Phase2/RGFlow_Work/Theorem7_QuantitativeMonotonicity.lean:144
- `no_plateaus` (theorem) — Phase2/RGFlow_Work/Theorem7_QuantitativeMonotonicity.lean:153
- conclusão: `mass_gap g1 a > mass_gap g2 a`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 33 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `expansion_form` (axiom) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:31
- `mass_gap_asymptotic_in_a` (theorem) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:44
- conclusão: `ℝ, mass_gap g a = Δ0 g + c2 g * (a * a) + R ∧ |R| ≤ K_remainder * (a * a * a * a)`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 34 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `c2_negative_axiom` (axiom) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:65
- `c2_is_negative` (theorem) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:68
- conclusão: `c2 g < 0`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 35 [PROPOSITIONAL] (2 ativas; kinds: axiom,theorem)
- `Delta0_positive_axiom` (axiom) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:74
- `continuum_gap_positive` (theorem) — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:77
- conclusão: `Δ0 g > 0`
- **DUPLICATA DE PRESSUPOSTO**: o mesmo enunciado assumido em múltiplos lugares. Ação: CONSOLIDATE_ASSUMPTION — um único axiom canônico (política nunca-Gemini), demais viram referência. PRIORIDADE ALTA: pressupostos duplicados inflam a base axiomática aparente.

## Grupo 36 [DATA] (2 ativas; kinds: def)
- `shift` (def) — Phase3/LatticeGauge/Basic.lean:31
- `shiftBack` (def) — Phase3/LatticeGauge/WilsonLoop.lean:17
- conclusão: `Site N`
- Objetos com mesma assinatura, corpos distintos/ausentes → NOT_DUPLICATE (ex.: shift vs shiftBack).

## Resumo: 36 grupos; 19 grupos de PRESSUPOSTOS duplicados (axioma×axioma ou axioma×teorema) — o achado mais relevante da V3.