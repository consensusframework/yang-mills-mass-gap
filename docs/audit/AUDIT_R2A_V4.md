# AUDIT_R2A_V4.md — categorias por FATO do kernel (issue #3)

Fonte primária: docs/audit/KERNEL_XRAY.json (dependências reais).
Consolidação NÃO executada — este documento é o plano exato exigido.

## 1. AXIOM_AXIOM_DUPLICATE (mesmo pressuposto declarado N vezes)

### `Delta0` — 9 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation12.lean
- Phase2/RGFlow_Work/GeminiValidation13.lean
- Phase2/RGFlow_Work/GeminiValidation14.lean
- Phase2/RGFlow_Work/GeminiValidation15.lean
- Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean
- Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- Phase2/RGFlow_Work/Theorem14_RGInvariance.lean
- Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- dependentes (kernel): 33 → RGFlow.complete_characterization, RGFlow.continuum_complete_picture, RGFlow.continuum_diff_eq_zero, RGFlow.continuum_gap_diff_nonneg, RGFlow.continuum_gap_injective, RGFlow.continuum_gap_positive_and_lipschitz…
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `continuum_lipschitz_in_g` — 3 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation15.lean
- Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- dependentes (kernel): 1 → RGFlow.complete_characterization
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `continuum_mass_gap_lower_bound` — 3 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation15.lean
- Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean
- Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- dependentes (kernel): 0 → 
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `continuum_monotonic_in_g` — 3 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation15.lean
- Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean
- dependentes (kernel): 7 → RGFlow.complete_characterization, RGFlow.extremes_at_endpoints, RGFlow.lower_bound_from_monotonicity, RGFlow.mass_gap_never_vanishes, RGFlow.mass_gap_strictly_positive_strong, RGFlow.universal_physical_bound…
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_A` — 2 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation14.lean
- Phase2/RGFlow_Work/Theorem14_RGInvariance.lean
- dependentes (kernel): 4 → RGFlow.continuum_limit_well_defined, RGFlow.mass_gap_is_physical_observable, RGFlow.rg_invariance_strong, RGFlow.scheme_diff_tendsto_zero
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem14_RGInvariance.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_B` — 2 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation14.lean
- Phase2/RGFlow_Work/Theorem14_RGInvariance.lean
- dependentes (kernel): 3 → RGFlow.mass_gap_is_physical_observable, RGFlow.rg_invariance_strong, RGFlow.scheme_diff_tendsto_zero
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem14_RGInvariance.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_lipschitz_in_g` — 2 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation12.lean
- Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- dependentes (kernel): 4 → RGFlow.continuum_gap_positive_and_lipschitz, RGFlow.continuum_lipschitz_in_g, RGFlow.continuum_mass_gap_continuous_in_g, RGFlow.lipschitz_bound_eventually
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_lower_bound_continuum` — 2 declarações vivas
- Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- dependentes (kernel): 2 → RGFlow.continuum_complete_picture, RGFlow.continuum_gap_positive_and_lipschitz
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_monotonic_in_g` — 2 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation13.lean
- Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- dependentes (kernel): 2 → RGFlow.continuum_gap_diff_nonneg, RGFlow.lattice_gap_diff_eventually_pos
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

### `mass_gap_tendsto_continuum` — 5 declarações vivas
- Phase2/RGFlow_Work/GeminiValidation12.lean
- Phase2/RGFlow_Work/GeminiValidation13.lean
- Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean
- Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean
- Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean
- dependentes (kernel): 10 → RGFlow.continuum_gap_diff_nonneg, RGFlow.continuum_gap_positive_and_lipschitz, RGFlow.continuum_lipschitz_in_g, RGFlow.continuum_mass_gap_continuous_in_g, RGFlow.continuum_mass_gap_lower_bound, RGFlow.continuum_mass_gap_ne_zero…
- **PLANO**: canônica em `Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean`; demais declarações removidas e arquivos passam a `import` o módulo canônico. Módulos afetados = os dos dependentes acima. PR individual, 3 jobs verdes.

## 2. AXIOM_THEOREM_WRAPPER (kernel-confirmados)

- `RGFlow.beta_negativity` ← RGFlow.beta → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.c2_is_negative` ← RGFlow.c2_negative_axiom → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_limit_exists` ← RGFlow.continuum_limit_exists_aux → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_limit_unique` ← RGFlow.limit_unique_aux, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_mass_gap_continuous_in_g` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_lipschitz_in_g, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_mass_gap_lower_bound` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_lower_bound, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_mass_gap_ne_zero` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_lower_bound, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.continuum_mass_gap_positive` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_lower_bound, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.coupling_stays_bounded` ← RGFlow.coupling_stays_bounded_aux → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.gap_bounded_across_region` ← RGFlow.gap_bounded_aux, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.gap_change_full_range` ← RGFlow.gap_change_full_range_aux, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.gap_stable_under_refinement` ← RGFlow.gap_stable_aux, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_abs_diff_tendsto` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_asymptotic_in_a` ← RGFlow.expansion_form, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_continuous` ← RGFlow.continuity_from_lipschitz, RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_diff_tendsto` ← RGFlow.Delta0, RGFlow.mass_gap, RGFlow.mass_gap_tendsto_continuum → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_eventually_ge_bound` ← RGFlow.mass_gap, RGFlow.mass_gap_lower_bound → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_joint_lipschitz_L1` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_jointly_lipschitz` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_lipschitz_continuous` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_lipschitz_in_a` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_monotone_in_g` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_persistence` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_quantitative_monotonicity` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_strictly_positive` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_two_sided_bound` ← RGFlow.mass_gap, RGFlow.two_sided_upper_bound → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.mass_gap_uniform_bound_at_g0` ← RGFlow.mass_gap → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.
- `RGFlow.no_plateaus` ← RGFlow.mass_gap, RGFlow.no_plateaus_aux → **PLANO**: docstring 'WRAPPER of assumption' + mover para seção de aliases; não conta como prova independente em nenhum placar.

## 3-5. THEOREM_THEOREM_ALIAS / PREDICATE_DEFINITIONS / DATA_SAME_SIGNATURE

Sem mudança factual desde a V3 (kernel não altera): grupos proposicionais
theorem×theorem seguem CONSOLIDATE→alias com canônica nunca-Gemini;
BRSTClosed/BRSTExact = PREDICATE_DEFINITIONS (corpos distintos, não dup);
shift/shiftBack etc = DATA_SAME_SIGNATURE (não dup).

## Ordem de execução proposta (pós-parecer)

1. `Delta0` (canônica: Theorem11_ContinuumMassGapLowerBound.lean; 33 dependentes)
2. `mass_gap_tendsto_continuum` (canônica: Theorem11_ContinuumMassGapLowerBound.lean; 10 dependentes)
3. `continuum_monotonic_in_g` (canônica: Theorem13_ContinuumMonotonicityInG.lean; 7 dependentes)
4. `mass_gap_A` (canônica: Theorem14_RGInvariance.lean; 4 dependentes)
5. `mass_gap_lipschitz_in_g` (canônica: Theorem12_ContinuumLipschitzInG.lean; 4 dependentes)
6. `mass_gap_B` (canônica: Theorem14_RGInvariance.lean; 3 dependentes)
7. `mass_gap_lower_bound_continuum` (canônica: Theorem12_ContinuumLipschitzInG.lean; 2 dependentes)
8. `mass_gap_monotonic_in_g` (canônica: Theorem13_ContinuumMonotonicityInG.lean; 2 dependentes)
9. `continuum_lipschitz_in_g` (canônica: Theorem12_ContinuumLipschitzInG.lean; 1 dependentes)
10. `continuum_mass_gap_lower_bound` (canônica: Theorem11_ContinuumMassGapLowerBound.lean; 0 dependentes)
11. Wrappers: rebatizar em lote único (sem impacto de kernel).