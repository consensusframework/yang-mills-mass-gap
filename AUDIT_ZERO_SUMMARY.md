# AUDIT_ZERO_SUMMARY.md — Peneira Zero (rodada 1: inventário, zero remoções)

Proposta: Ju Carvalho. Especificação: Sol (GPT-5.6). Execução: Claude Fable 5.
Análise ESTÁTICA — classificações PRELIMINARES; nada removido. Confirmações
que exigem compilador (uso real, #print axioms, unificação) = rodada 2.

## O placar honesto (formato Sol)

**1425 declarações inventariadas:** 912 PARKED, 183 UNKNOWN, 114 REFORMULATE, 97 CORE, 92 COROLLARY, 27 DUPLICATE_CANDIDATE

- Phase1: 1025 declarações (113 no build)
- Phase2: 295 declarações (295 no build)
- Phase3: 105 declarações (105 no build)
- Axiomas totais: 291 (fortes/circulares: 121)
- Declarações com sorry: 85
- Arquivos órfãos: 52

## Nota estrutural (a lição da 14ª)
SingleLink/PairLink = COROLLARY: corretos e úteis como API, mas
subsumidos por MultiLink. Contagem bruta não os trata como independentes.

## Top 20 candidatos a duplicata (enunciado idêntico)
- 10×: mass_gap_numerical_consistency@Phase1/YangMills/EntropicPrinciple_Integrated.lean, mass_gap_numerical_consistency@Phase1/YangMills/EntropicPrinciple_Standalone.lean, mass_gap_numerical_consistency@Phase1/YangMills/EntropicTest.lean, mass_gap_strong_coupling_consistency@Phase1/YangMills/MassGapStrongCoupling.lean …
  `: abs (predicted_mass_gap - experimental_mass_gap) / experimental_mass_gap < 0.02`
- 6×: axiom_holographic_consistency@Phase1/YangMills/EntropicPrinciple_Integrated.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean, axiom_holographic_consistency@Phase1/archive/EntropicPrinciple_v3.lean …
  `: ∃ (α_predicted α_measured : ℝ), α_predicted = 0.25 ∧ α_measured = 0.26 ∧ abs (α_predicted - α_measured) / α_`
- 5×: entropy_functional_local@Phase1/YangMills/EntropicTest.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v2_fixed.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v3.lean, entropy_functional_local@Phase1/archive/EntropicPrinciple_v4.lean …
  `(ρ_UV ρ_IR : DensityMatrix) (yang_mills_action : ℝ) (lambda_coupling : ℝ) : ℝ`
- 5×: zero_pairing_rate_expected@Phase1/YangMills/EntropicTest.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v2.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v3.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_v4.lean …
  `(M : Manifold) (A : GaugeField M) (_ : ∃ (Δ : ℝ), Δ > 0 ∧ ∃ (L ΔS : ℝ), L > 0 ∧ ΔS > 0 ∧ Δ^2 = (2 * Real.pi / `
- 5×: mass_gap_tendsto_continuum@Phase2/RGFlow_Work/GeminiValidation12.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/GeminiValidation13.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean, mass_gap_tendsto_continuum@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean …
  `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Filter.Tendsto (fun a : ℝ => mass_gap g a) (nhdsWithin (0 : ℝ) (Set.Ioi 0)`
- 5×: continuum_mass_gap_lower_bound@Phase2/RGFlow_Work/GeminiValidation15.lean, continuum_mass_gap_lower_bound@Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean, mass_gap_lower_bound_continuum@Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean, mass_gap_lower_bound_continuum@Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean …
  `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : (0.5 : ℝ) ≤ Delta0 g`
- 4×: axiom_entropic_mass_gap_principle@Phase1/YangMills/EntropicPrinciple_Integrated.lean, axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v3.lean, axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v4.lean, axiom_entropic_mass_gap_principle@Phase1/archive/EntropicPrinciple_v5_1_.lean
  `(M : Manifold) (A : GaugeField M) : ∃ (Δ : ℝ), -- 1. Mass gap is positive Δ > 0 ∧ -- 2. Mass gap follows from `
- 4×: theorem_entropic_implies_geometric@Phase1/YangMills/EntropicPrinciple_Integrated.lean, theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v3.lean, theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v4.lean, theorem_entropic_implies_geometric@Phase1/archive/EntropicPrinciple_v5_1_.lean
  `(M : Manifold) (A : GaugeField M) : (∃ (Δ : ℝ), Δ > 0 ∧ ∃ (L ΔS : ℝ), L > 0 ∧ ΔS > 0 ∧ Δ^2 = (2 * Real.pi / L)`
- 4×: suppresses_gribov_copies_entropic@Phase1/YangMills/EntropicTest.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v3.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v4.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v5_1_.lean
  `(M : Manifold) (_ : GaugeField M) (Δ : ℝ) : Prop`
- 4×: lowestEigenvalue@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, spectralZetaFunction_derivative_at_zero@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, fpDeterminant@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean, signOfDeterminant@Phase1/YangMills/Gap1/BRSTMeasure/M1_FP_Positivity.lean
  `(M_FP : FPOperator M N P) (A : Connection M N P) : ℝ`
- 3×: suppresses_gribov_copies_entropic@Phase1/YangMills/EntropicPrinciple_Integrated.lean, suppresses_gribov_copies@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean, suppresses_gribov_copies_entropic@Phase1/archive/EntropicPrinciple_v2_fixed.lean
  `(M : Manifold) (A : GaugeField M) (Δ : ℝ) : Prop`
- 3×: thermodynamic_sector_locking@Phase1/YangMills/EntropicPrinciple_Integrated.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v2_fixed.lean
  `(M : Manifold) (A : GaugeField M) (k : ℝ) : Prop`
- 3×: zero_pairing_rate_expected@Phase1/YangMills/EntropicPrinciple_Integrated.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple.lean, zero_pairing_rate_expected@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean
  `(M : Manifold) (A : GaugeField M) : axiom_entropic_mass_gap_principle M A → -- Zero pairing rate is consistent`
- 3×: mutual_information@Phase1/YangMills/EntropicPrinciple_Standalone.lean, mutual_information@Phase1/YangMills/EntropicTest.lean, mutual_information@Phase1/archive/EntropicPrinciple_OPUS45_ORIGINAL.lean
  `: DensityMatrix → DensityMatrix → ℝ`
- 3×: orientationReversalPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean, conjugationReflectionPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean, hodgeDualPairing@Phase1/YangMills/Gap2/AtiyahSinger/TopologicalPairing.lean
  `(M : Manifold4D) (N : ℕ) (P : PrincipalBundle M N) : PairingMap M N P where map A`
- 3×: l2_metric_riemannian@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, l2_metric_riemannian@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, l2_metric_riemannian@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
  `: ∀ (A_G : ModuliSpace M N), IsRiemannianMetric (l2_metric A_G) (RegularLocus A_G)`
- 3×: christoffel_symbols@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, christoffel_symbols@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, christoffel_symbols@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
  `(A_G : ModuliSpace M N) : ChristoffelSymbols A_G`
- 3×: riemann_tensor@Phase1/YangMills/Gap4/RicciLowerBound/R1_RicciWellDefined.lean, riemann_tensor@Phase1/archive/R1_ORIGINAL_FOR_CLAUDE.lean, riemann_tensor@Phase1/archive/R1_RicciWellDefined_FOR_CLAUDE.lean
  `(A_G : ModuliSpace M N) : RiemannTensor A_G`
- 3×: thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v3.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v4.lean, thermodynamic_sector_locking@Phase1/archive/EntropicPrinciple_v5_1_.lean
  `(M : Manifold) (_ : GaugeField M) (k : ℝ) : Prop`
- 3×: entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v3.lean, entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v4.lean, entropic_subsumes_geometric@Phase1/archive/EntropicPrinciple_v5_1_.lean
  `(M : Manifold) (A : GaugeField M) (h_entropic : ∃ (Δ : ℝ), Δ > 0 ∧ ∃ (L ΔS : ℝ), L > 0 ∧ ΔS > 0 ∧ Δ^2 = (2 * R`

## Top 20 axiomas mais fortes/circulares
- `mass_gap` (Phase1/YangMills/MassGap.lean:38, refs≈121)
- `mass_gap` (Phase2/RGFlow_Work/Basic.lean:29, refs≈121)
- `mass_gap` (Phase2/RGFlow_Work/GeminiValidation12.lean:62, refs≈121)
- `mass_gap` (Phase2/RGFlow_Work/GeminiValidation13.lean:69, refs≈121)
- `mass_gap` (Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:66, refs≈121)
- `mass_gap` (Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:78, refs≈121)
- `Delta0` (Phase2/RGFlow_Work/GeminiValidation12.lean:65, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/GeminiValidation13.lean:72, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/GeminiValidation14.lean:74, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/GeminiValidation15.lean:57, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:12, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:69, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:81, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:84, refs≈114)
- `Delta0` (Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:72, refs≈114)
- `HasQuartetDecomp` (Phase1/YangMills/Restoration.lean:47, refs≈20)
- `physical_inner` (Phase1/YangMills/Restoration.lean:101, refs≈17)
- `GribovRegion` (Phase1/YangMills/L3_TopologicalPairing.lean:44, refs≈16)
- `von_neumann_entropy` (Phase1/archive/EntropicPrinciple_v2_fixed.lean:21, refs≈15)
- `mass_gap_A` (Phase2/RGFlow_Work/GeminiValidation14.lean:68, refs≈13)

## Arquivos órfãos
- Phase1/YangMills/AXIOM3_Compose.lean
- Phase1/YangMills/AreaLaw.lean
- Phase1/YangMills/Axiom1Prime.lean
- Phase1/YangMills/Axiom2Prime.lean
- Phase1/YangMills/B1_BFSConvergence.lean
- Phase1/YangMills/B2_ClusterDecomposition.lean
- Phase1/YangMills/B3_MassGapStrongCoupling.lean
- Phase1/YangMills/B4_ContinuumLimitStability.lean
- Phase1/YangMills/B5_BRSTBFSConnection.lean
- Phase1/YangMills/BochnerWeitzenbock.lean
- Phase1/YangMills/ContinuumLimit.lean
- Phase1/YangMills/Corollary_Convergence.lean
- Phase1/YangMills/Correspondence.lean
- Phase1/YangMills/CurvatureDecomposition.lean
- Phase1/YangMills/Decomposition.lean
- Phase1/YangMills/EntropicPrinciple_Integrated.lean
- Phase1/YangMills/Equivalence.lean
- Phase1/YangMills/FieldEquations.lean
- Phase1/YangMills/FiniteSizeEffects.lean
- Phase1/YangMills/GapLowerBound.lean
- Phase1/YangMills/GeminiValidation.lean
- Phase1/YangMills/GradientFlowConvergence.lean
- Phase1/YangMills/GribovCancellationThm.lean
- Phase1/YangMills/GribovRegion.lean
- Phase1/YangMills/L3_TopologicalPairing.lean
- Phase1/YangMills/LowerBound.lean
- Phase1/YangMills/M2_BRSTConvergence.lean
- Phase1/YangMills/Main.lean
- Phase1/YangMills/MassGap.lean
- Phase1/YangMills/MassGapStrongCoupling.lean

## Ordem de limpeza proposta (rodada 2: PRs pequenos, CI antes/depois)
1. Órfãos → archive/. 2. Duplicatas → 1 canônica. 3. Fase 2: triviais
viram corolários medidos pelo compilador. 4. Axiomas fortes: hipótese
nomeada, Caixa 2 com referência, ou Caixa 3 com aviso. 5. Fase 1: só
reformular o que a Fase 3 não substituiu. 6. #print axioms nos capstones.