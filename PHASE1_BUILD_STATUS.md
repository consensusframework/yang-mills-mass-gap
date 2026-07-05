# PHASE1_BUILD_STATUS.md

Iteration 2 (July 5, 2026). Lean 4.15 + Mathlib, CI job build-phase1.

- **Iteration 3 (green baseline): 9 / 87 modules compile with full transitive closure.**
- Iteration 2 counted 34 "passing", but many only passed while their broken
  dependencies were also being built; the honest number requires the whole
  dependency cone to compile. The catalogue below therefore mixes two kinds:
  ROOT failures (real semantic errors) and DEP-BLOCKED modules (import a
  failing/lost module). Next iteration should classify each.
- Modules failing: 53 — individual semantic errors (instance synthesis, mistyped applications), each needs case-by-case repair.
- NOTE: many failing files are redundant version variants (EntropicPrinciple v2/v3/v4/v5/ORIGINAL/Integrated...). Recommend picking one canonical version per family and archiving the rest.

## Failing modules

- `YangMills.AXIOM3_Compose`: failed to synthesize; function expected at
- `YangMills.AreaLaw`: application type mismatch; declaration uses 'sorry'
- `YangMills.Axiom1Prime`: function expected at; type mismatch
- `YangMills.Axiom2Prime`: type mismatch
- `YangMills.B1_BFSConvergence`: unexpected identifier; expected command; unexpected token ':'; expected command
- `YangMills.B2_ClusterDecomposition`: unexpected identifier; expected command; unexpected token ':'; expected command
- `YangMills.B3_MassGapStrongCoupling`: unexpected identifier; expected command; unexpected token ':'; expected command
- `YangMills.B4_ContinuumLimitStability`: failed to synthesize; function expected at
- `YangMills.B5_BRSTBFSConnection`: failed to synthesize; function expected at
- `YangMills.BetaFunction`: declaration uses 'sorry'; unknown identifier 'ℝ'
- `YangMills.ContinuumLimit`: unsolved goals
- `YangMills.ConvergenceRegion`: failed to synthesize; unknown identifier 'ℝ'
- `YangMills.Correspondence`: application type mismatch; failed to synthesize
- `YangMills.Decomposition`: failed to synthesize; function expected at
- `YangMills.EntropicPrinciple`: failed to synthesize; function expected at
- `YangMills.EntropicPrinciple_OPUS45_ORIGINAL`: tactic 'introN' failed, insufficient number of binders; type expected, got
- `YangMills.EntropicPrinciple_v2`: failed to synthesize; function expected at
- `YangMills.EntropicPrinciple_v2_fixed`: declaration uses 'sorry'; failed to compile definition, consider marking it as 'n
- `YangMills.Equivalence`: application type mismatch; elaboration function for 'YangMills.A5.BRSTCohomology.«
- `YangMills.FieldEquations`: application type mismatch; don't know how to synthesize implicit argument 'M'
- `YangMills.FiniteSizeEffects`: unsolved goals
- `YangMills.Gap1.BRSTMeasure.M5_BRSTCohomology`: object file '././.lake/build/lib/YangMills/Gap1/BRSTMea
- `YangMills.Gap1.GribovGaugeOrbits`: failed to compile definition, consider marking it as 'n; invalid field 'inGribovRegion', the environment does no
- `YangMills.Gap2.AtiyahSinger.IndexTheorem`: failed to solve universe constraint; failed to synthesize
- `YangMills.Gap2.GribovCancellation`: type mismatch
- `YangMills.Gap3.BFS_Convergence`: type mismatch
- `YangMills.Gap3.LemmaA_Combinatorial`: object file '././.lake/build/lib/YangMills/Gap3/SimpleC
- `YangMills.Gap3.LemmaB_Analytic`: object file '././.lake/build/lib/YangMills/Gap3/SimpleC
- `YangMills.Gap4.RicciLimit`: unexpected token '}'; expected term
- `YangMills.Gap4.RicciLimit.R1_Bochner.LaplacianConnection`: expected token
- `YangMills.Gap4.RicciLimit.R3_Decomposition.RicciTensorFormula`: expected token; failed to prove index is valid, possible solutions:
- `YangMills.Gap4.RicciLowerBound.Prelude`: invalid 'import' command, it must be used in the beginn; unexpected identifier; expected command
- `YangMills.GapLowerBound`: application type mismatch; automatically included section variable(s) unused in th
- `YangMills.GeminiValidation`: unknown module prefix 'RGFlow_Work'
- `YangMills.GradientFlowConvergence`: The namespace 'Flow' is duplicated in the declaration '; declaration uses 'sorry'
- `YangMills.GribovRegion`: The namespace 'GribovRegion' is duplicated in the decla; failed to synthesize
- `YangMills.L3_TopologicalPairing`: 'Orientation' has already been declared; application type mismatch
- `YangMills.LowerBound`: 'apply sInf_le_iff.mpr' tactic does nothing; 'constructor' tactic does nothing
- `YangMills.M2_BRSTConvergence`: invalid 'import' command, it must be used in the beginn; unexpected identifier; expected command
- `YangMills.MassGap`: unknown module prefix 'RGFlow_Work'
- `YangMills.MassGapStrongCoupling`: unsolved goals
- `YangMills.MeasureDecomposition`: failed to compile definition, consider marking it as 'n; tactic 'rfl' failed, expected goal to be a binary relat
- `YangMills.Monotonicity`: The namespace 'Entropy' is duplicated in the declaratio; expected token
- `YangMills.MultiSectorSampling`: function expected at; unused variable `K`
- `YangMills.Positivity`: The namespace 'Hamiltonian' is duplicated in the declar; application type mismatch
- `YangMills.R4_BishopGromov_ROUND2`: function expected at
- `YangMills.R5_CompactnessToStability`: expected token; failed to synthesize
- `YangMills.ReflectionPositivity`: failed to compile definition, consider marking it as 'n; structure ... :=' has been deprecated in favor of 'stru
- `YangMills.Restoration`: application type mismatch; failed to synthesize
- `YangMills.SobolevEmbedding`: failed to synthesize; function expected at
- `YangMills.Stability`: application type mismatch; failed to synthesize
- `YangMills.Topology.GribovPairing`: @gribov_topological_pairing : ∀ {G : Type u_1} (A : Con; don't know how to synthesize implicit argument 'G'
- `YangMills.UniversalityScaling`: unsolved goals