# AUDIT_ZERO_SUMMARY.md — v2 (regenerado da main pós-pedras 15-16 e passo 1)

**922 declarações:** 283 PARKED, 182 UNKNOWN, 124 ARCHIVE, 114 REFORMULATE, 99 CORE, 93 COROLLARY, 27 DUPLICATE_CANDIDATE

## Reconciliação 52 → 42 (exigência do parecer, item 2)

O inventário v1 detectou 52 órfãos NA ÁRVORE DE ONTEM. Entre o inventário
e o passo 1 entraram na main o bloco 4 e a 16ª pedra, cujos imports novos
(UnitaryChar, HaarUnitary em HolonomyHaar) 'adotaram' arquivos por nome de
folha; o passo 1 recomputou a lista NA HORA da execução (42) em vez de
aplicar a lista velha — comportamento correto. Os 10 preservados:

(lista v1 truncada em 30 no summary — reconciliação completa: comparar coluna 'orphan' dos dois CSVs)

## Duplicatas (NÃO remover — aguardando parecer sobre este v2)
- 8×: mass_gap_numerical_consistency@Phase1/YangMills/EntropicPrinciple_Standalone.lean, mass_gap_numerical_consistency@Phase1/YangMills/EntropicTest.lean, mass_gap_numerical_consistency@Phase1/archive/EntropicPrinciple.lean, mass_gap_numerical_consistency@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean
- 5×: entropy_functional_local@Phase1/YangMills/EntropicTest.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v2_fixed.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v3.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v4.lean
- 5×: zero_pairing_rate_expected@Phase1/YangMills/EntropicTest.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v2.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v3.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v4.lean
- 5×: axiom_holographic_consistency@Phase1/archive/EntropicPrinciple.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple_v3.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple_v4.lean
- 5×: mass_gap_tendsto_continuum@Phase2/RGFlow_Work/GeminiValidation12.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/GeminiValidation13.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- 5×: continuum_mass_gap_lower_bound@Phase2/RGFlow_Work/GeminiValidation15.lean, continuum_mass_gap_lower_bound@Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean, mass_gap_lower_bound_continuum@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean, mass_gap_lower_bound_continuum@Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- 4×: suppresses_gribov_copies_entropic@Phase1/YangMills/EntropicTest.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v3.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v4.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v5_1_.lean
- 4×: lowestEigenvalue@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, spectralZetaFunction_derivative_at_zero@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, fpDeterminant@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, signOfDeterminant@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean
- 3×: mutual_information@Phase1/YangMills/EntropicPrinciple_Standalone.lean, mutual_information@Phase1/YangMills/EntropicTest.lean, mutual_information@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean
- 3×: orientationReversalPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean, conjugationReflectionPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean, hodgeDualPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean
- 3×: l2_metric_riemannian@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, l2_metric_riemannian@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, l2_metric_riemannian@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
- 3×: christoffel_symbols@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, christoffel_symbols@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, christoffel_symbols@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
- 3×: riemann_tensor@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, riemann_tensor@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, riemann_tensor@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
- 3×: thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v3.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v4.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v5_1_.lean
- 3×: axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v3.lean, axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v4.lean, axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v5_1_.lean
- 3×: theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v3.lean, theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v4.lean, theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v5_1_.lean
- 3×: entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v3.lean, entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v4.lean, entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v5_1_.lean
- 3×: continuum_lipschitz_in_g@Phase2/RGFlow_Work/GeminiValidation15.lean, continuum_lipschitz_in_g@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean, continuum_lipschitz_in_g@Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- 3×: continuum_monotonic_in_g@Phase2/RGFlow_Work/GeminiValidation15.lean, continuum_monotonic_in_g@Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean, continuum_monotonic_in_g@Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- 3×: Ioc_mem_nhdsWithin_Ioi_zero@Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean, Ioc_mem_nhdsWithin_Ioi_zero@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean, Ioc_mem_nhdsWithin_Ioi_zero@Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean

Rodada 2 só começa após aprovação deste v2. — Fable