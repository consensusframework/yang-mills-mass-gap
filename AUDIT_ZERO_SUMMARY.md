# AUDIT_ZERO_SUMMARY.md — v2 (regenerado da main pós-pedras 15-16 e passo 1)

**922 declarações:** 283 PARKED, 182 UNKNOWN, 124 ARCHIVE, 114 REFORMULATE, 99 CORE, 93 COROLLARY, 27 DUPLICATE_CANDIDATE

## Reconciliação 52 → 42 (item 2 do parecer — EXATA, por diff de árvores)

52 órfãos (v1) = 42 arquivados no passo 1 + 10 que JÁ ESTAVAM em
Phase1/archive/ (as variantes da dedup de 2026-07-05: EntropicPrinciple
×7, R1_FOR_CLAUDE ×2, R4_ROUND2). O passo 1 exclui '/archive/' por
construção — arquivar o já-arquivado seria ruído. Nenhuma anomalia;
os 10, nominalmente:

- Phase1/archive/EntropicPrinciple.lean
- Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean
- Phase1/archive/EntropicPrinciple_v2.lean
- Phase1/archive/EntropicPrinciple_v2_fixed.lean
- Phase1/archive/EntropicPrinciple_v3.lean
- Phase1/archive/EntropicPrinciple_v4.lean
- Phase1/archive/EntropicPrinciple_v5_1_.lean
- Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean
- Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
- Phase1/archive/R4_BishopGromov_ROUND2.lean

Verificação independente: diff entre a árvore da branch audit-zero (52
recomputados) e archive_peneira/orphans (42 movidos); interseção
movidos∖v1 = ∅.

## Nota de escopo do total v2

v1 contava 1425 declarações incluindo os arquivos hoje em
archive_peneira/ (fora do glob Phase*). Conta viva v2: 922 declarações
na árvore ativa + ~503 nos 42 arquivos arquivados no passo 1. Nada
sumiu; mudou de coluna.

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