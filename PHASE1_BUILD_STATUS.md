# PHASE1_BUILD_STATUS.md

Incremental build of Phase 1 (Lean 4.15 + Mathlib, CI job build-phase1).

- Modules compiling: 8 (whitelisted in lakefile.toml)
- Modules failing: 46 (catalogued below, excluded from build)
- Modules blocked by LOST files (account suspension): see commit 6873923

## Failing modules and first error classes

### `YangMills.AXIOM3_Compose`
- failed to synthesize
- function expected at
- unexpected identifier; expected command

### `YangMills.AreaLaw`

### `YangMills.Axiom1Prime`
- function expected at
- type mismatch
- unknown identifier 'h_exponential_decay_validation'

### `YangMills.Axiom2Prime`
- type mismatch

### `YangMills.Axiom8Prime`
- unexpected identifier; expected command

### `YangMills.B1_BFSConvergence`
- unexpected identifier; expected command
- unexpected token ':'; expected command
- unexpected token '|'; expected term

### `YangMills.B2_ClusterDecomposition`
- unexpected identifier; expected command
- unexpected token ':'; expected command
- unexpected token '|'; expected term

### `YangMills.B3_MassGapStrongCoupling`
- unexpected identifier; expected command
- unexpected token ':'; expected command
- unexpected token '|'; expected term

### `YangMills.B4_ContinuumLimitStability`
- failed to synthesize
- function expected at
- unexpected identifier; expected command

### `YangMills.B5_BRSTBFSConnection`
- failed to synthesize
- function expected at
- unexpected identifier; expected command

### `YangMills.BetaFunction`
- declaration uses 'sorry'
- unknown identifier 'ℝ'

### `YangMills.ContinuumLimit`
- unsolved goals

### `YangMills.ConvergenceRegion`
- failed to synthesize
- unknown identifier 'ℝ'

### `YangMills.Correspondence`

### `YangMills.Decomposition`

### `YangMills.EntropicPrinciple`
- failed to synthesize
- function expected at
- invalid 'end', insufficient scopes

### `YangMills.EntropicPrinciple_OPUS45_ORIGINAL`
- tactic 'introN' failed, insufficient number of binders
- type expected, got
- unexpected token 'λ'; expected '_' or identifier

### `YangMills.EntropicPrinciple_v2`
- failed to synthesize
- function expected at
- unknown identifier 'Real.pi'

### `YangMills.EntropicPrinciple_v2_fixed`
- declaration uses 'sorry'
- failed to compile definition, consider marking it as 'noncom
- function expected at

### `YangMills.EntropicTest`
- unknown constant 'Real.pi'

### `YangMills.Equivalence`

### `YangMills.FieldEquations`

### `YangMills.FiniteSizeEffects`
- unsolved goals

### `YangMills.Gap1.GribovGaugeOrbits`
- failed to compile definition, consider marking it as 'noncom
- invalid field 'inGribovRegion', the environment does not con

### `YangMills.Gap2.AtiyahSinger.IndexTheorem`
- failed to solve universe constraint
- failed to synthesize
- type mismatch

### `YangMills.Gap2.GribovCancellation`
- type mismatch

### `YangMills.Gap3.BFS_Convergence`
- type mismatch

### `YangMills.Gap4.RicciLimit`
- unexpected token '}'; expected term

### `YangMills.Gap4.RicciLimit.R1_Bochner.LaplacianConnection`
- expected token
- unexpected token '('; expected command

### `YangMills.Gap4.RicciLimit.R3_Decomposition.RicciTensorFormula`

### `YangMills.GapLowerBound`

### `YangMills.GradientFlowConvergence`

### `YangMills.L3_TopologicalPairing`
- expected token
- invalid 'import' command, it must be used in the beginning o

### `YangMills.LowerBound`
- 'apply sInf_le_iff.mpr' tactic does nothing
- 'constructor' tactic does nothing
- 'exact sub_eq_zero.mp (norm_eq_zero.mp this)' tactic does no

### `YangMills.MassGapStrongCoupling`
- unsolved goals

### `YangMills.MeasureDecomposition`

### `YangMills.Monotonicity`

### `YangMills.MultiSectorSampling`
- function expected at
- unused variable `K`
- unused variable `S`

### `YangMills.Positivity`
- The namespace 'Hamiltonian' is duplicated in the declaration
- application type mismatch
- type mismatch

### `YangMills.R4_BishopGromov_ROUND2`
- invalid binder annotation, type is not a class instance

### `YangMills.ReflectionPositivity`
- structure ... :=' has been deprecated in favor of 'structure
- type mismatch
- unexpected token '['; expected ','

### `YangMills.Restoration`

### `YangMills.SobolevEmbedding`

### `YangMills.Stability`

### `YangMills.Topology.GribovPairing`
- @gribov_topological_pairing : ∀ {G : Type u_1} (A : Connecti
- don't know how to synthesize implicit argument 'G'
- don't know how to synthesize implicit argument 'α'

### `YangMills.UniversalityScaling`
- unsolved goals
