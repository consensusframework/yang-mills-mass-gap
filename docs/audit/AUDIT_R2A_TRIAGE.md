# AUDIT_R2A_TRIAGE.md — Rodada 2A: triagem de duplicatas (ZERO remoções)

Spec: Sol. Execução: Fable. Regras: archive/ preserva proveniência e fica
fora da dedup; Phase1 = classificar apenas (sem CI); Phase2 = consolidar
só em PRs pequenos com 3 jobs verdes; Phase3 = corolários/API ficam
(SingleLink/PairLink como wrappers da MultiLink é MELHORIA, não remoção).

Colunas por grupo: ativas | em archive | tipos Lean idênticos? | mesmo
significado? | refs | canônica proposta | ação proposta

## Grupo 1 (3 ativas, 0 em archive)
- `Ioc_mem_nhdsWithin_Ioi_zero` — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:39 (refs≈5, DUPLICATE_CANDIDATE)
- `Ioc_mem_nhdsWithin_Ioi_zero` — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:121 (refs≈5, DUPLICATE_CANDIDATE)
- `Ioc_mem_nhdsWithin_Ioi_zero` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:123 (refs≈5, DUPLICATE_CANDIDATE)
- enunciado extraído: `: Set.Ioc (0 : ℝ) 0.2 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 2 (2 ativas, 6 em archive)
- `mass_gap_numerical_consistency` — Phase1/YangMills/EntropicPrinciple_Standalone.lean:164 (refs≈7, DUPLICATE_CANDIDATE)
- `mass_gap_numerical_consistency` — Phase1/YangMills/EntropicTest.lean:52 (refs≈7, DUPLICATE_CANDIDATE)
- enunciado extraído: `: abs (predicted_mass_gap - experimental_mass_gap) / experimental_mass_gap < 0.02`
- Mesmo significado? Plausível (declarações Phase1 repetidas entre arquivos).
- **Ação proposta: CLASSIFY_ONLY** (Phase1 sem CI; consolidar só quando houver build).

## Grupo 3 (2 ativas, 0 em archive)
- `gemini_scheme_agreement_trivial` — Phase2/RGFlow_Work/GeminiValidation14.lean:111 (refs≈0, DUPLICATE_CANDIDATE)
- `rg_invariance` — Phase2/RGFlow_Work/Theorem14_RGInvariance.lean:190 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Delta0 g = Delta0 g`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 4 (2 ativas, 0 em archive)
- `continuum_mass_gap_positive` — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:98 (refs≈1, DUPLICATE_CANDIDATE)
- `mass_gap_strictly_positive_strong` — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:167 (refs≈2, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : (0 : ℝ) < Delta0 g`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 5 (2 ativas, 0 em archive)
- `continuum_mass_gap_ne_zero` — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:107 (refs≈0, DUPLICATE_CANDIDATE)
- `mass_gap_never_vanishes` — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:183 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : Delta0 g ≠ 0`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 6 (2 ativas, 0 em archive)
- `mass_gap_diff_tendsto` — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:97 (refs≈1, DUPLICATE_CANDIDATE)
- `gap_diff_tendsto` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:144 (refs≈1, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) : Filter.Tendsto (fun a : ℝ =>`
- Canônica proposta: `mass_gap_diff_tendsto` @ Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean (maior nº de referências).
- **Ação proposta: CONSOLIDATE** (PR pequeno, 3 jobs verdes antes/depois).

## Grupo 7 (2 ativas, 0 em archive)
- `shift` — Phase3/LatticeGauge/Basic.lean:31 (refs≈23, DUPLICATE_CANDIDATE)
- `shiftBack` — Phase3/LatticeGauge/WilsonLoop.lean:17 (refs≈13, DUPLICATE_CANDIDATE)
- enunciado extraído: `(x : Site N) (μ : Dir) [NeZero N] : Site N`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 8 (1 ativas, 1 em archive)
- `holographic_scaling_agreement` — Phase1/YangMills/EntropicPrinciple_Standalone.lean:223 (refs≈1, DUPLICATE_CANDIDATE)
- enunciado extraído: `: abs (alpha_predicted - alpha_measured) / alpha_predicted < 0.05`
- Mesmo significado? Plausível (declarações Phase1 repetidas entre arquivos).
- **Ação proposta: CLASSIFY_ONLY** (Phase1 sem CI; consolidar só quando houver build).

## Grupo 9 (1 ativas, 4 em archive)
- `entropy_functional_local` — Phase1/YangMills/EntropicTest.lean:29 (refs≈4, DUPLICATE_CANDIDATE)
- enunciado extraído: `(ρ_UV ρ_IR : DensityMatrix) (yang_mills_action : ℝ) (lambda_coupling : ℝ) : ℝ`
- Mesmo significado? Plausível (declarações Phase1 repetidas entre arquivos).
- **Ação proposta: CLASSIFY_ONLY** (Phase1 sem CI; consolidar só quando houver build).

## Grupo 10 (1 ativas, 3 em archive)
- `suppresses_gribov_copies_entropic` — Phase1/YangMills/EntropicTest.lean:34 (refs≈19, DUPLICATE_CANDIDATE)
- enunciado extraído: `(M : Manifold) (_ : GaugeField M) (Δ : ℝ) : Prop`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 11 (1 ativas, 4 em archive)
- `zero_pairing_rate_expected` — Phase1/YangMills/EntropicTest.lean:41 (refs≈7, DUPLICATE_CANDIDATE)
- enunciado extraído: `(M : Manifold) (A : GaugeField M) (_ : ∃ (Δ : ℝ), Δ > 0 ∧ ∃ (L ΔS : ℝ), L > 0 ∧ ΔS > 0 ∧ Δ^2 = (2 * `
- Mesmo significado? Plausível (declarações Phase1 repetidas entre arquivos).
- **Ação proposta: CLASSIFY_ONLY** (Phase1 sem CI; consolidar só quando houver build).

## Grupo 12 (5 ativas, 0 em archive)
- `continuum_mass_gap_lower_bound` — Phase2/RGFlow_Work/GeminiValidation15.lean:62 (refs≈3, REFORMULATE)
- `continuum_mass_gap_lower_bound` — Phase2/RGFlow_Work/Theorem11_ContinuumMassGapLowerBound.lean:79 (refs≈3, DUPLICATE_CANDIDATE)
- `mass_gap_lower_bound_continuum` — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:207 (refs≈4, REFORMULATE)
- `mass_gap_lower_bound_continuum` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:245 (refs≈4, REFORMULATE)
- `continuum_mass_gap_lower_bound` — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:77 (refs≈3, REFORMULATE)
- enunciado extraído: `(g : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) : (0.5 : ℝ) ≤ Delta0 g`
- Tipos idênticos? Textualmente, mas o fragmento é curto/genérico.
- **Ação proposta: NOT_DUPLICATE** (baixa confiança; requer verificação de unificação no Lean).

## Grupo 13 (3 ativas, 0 em archive)
- `continuum_lipschitz_in_g` — Phase2/RGFlow_Work/GeminiValidation15.lean:67 (refs≈5, REFORMULATE)
- `continuum_lipschitz_in_g` — Phase2/RGFlow_Work/Theorem12_ContinuumLipschitzInG.lean:159 (refs≈5, DUPLICATE_CANDIDATE)
- `continuum_lipschitz_in_g` — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:82 (refs≈5, REFORMULATE)
- enunciado extraído: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) : |Delta0 g₁ - Delta0 g₂| ≤ 2.`
- Canônica proposta: `continuum_lipschitz_in_g` @ Phase2/RGFlow_Work/GeminiValidation15.lean (maior nº de referências).
- **Ação proposta: CONSOLIDATE** (PR pequeno, 3 jobs verdes antes/depois).

## Grupo 14 (3 ativas, 0 em archive)
- `continuum_monotonic_in_g` — Phase2/RGFlow_Work/GeminiValidation15.lean:74 (refs≈9, REFORMULATE)
- `continuum_monotonic_in_g` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:188 (refs≈9, DUPLICATE_CANDIDATE)
- `continuum_monotonic_in_g` — Phase2/RGFlow_Work/Theorem15_UniversalPhysicalBound.lean:89 (refs≈9, REFORMULATE)
- enunciado extraído: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) (h_order : g₁ < g₂) : Delta0 g`
- Canônica proposta: `continuum_monotonic_in_g` @ Phase2/RGFlow_Work/GeminiValidation15.lean (maior nº de referências).
- **Ação proposta: CONSOLIDATE** (PR pequeno, 3 jobs verdes antes/depois).

## Grupo 15 (2 ativas, 0 em archive)
- `continuum_gap_quantitative_separation` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:113 (refs≈3, REFORMULATE)
- `continuum_gap_quantitative_bound` — Phase2/RGFlow_Work/Theorem13_ContinuumMonotonicityInG.lean:217 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g₁ g₂ : ℝ) (hg₁ : 0.5 ≤ g₁ ∧ g₁ ≤ 1.18) (hg₂ : 0.5 ≤ g₂ ∧ g₂ ≤ 1.18) (h_order : g₁ < g₂) : 0.2 * (g`
- **Tipos idênticos? SIM (textual). Mesmo significado? NÃO** — nomes distintos no mesmo arquivo com o MESMO TIPO CURTO (ex.: quatro constantes ': ℝ'): equivalência de tipo detectada pelo script, não duplicação semântica (exatamente o caso apontado no parecer).
- **Ação proposta: NOT_DUPLICATE** (artefato do detector; refinar extração na v3).

## Grupo 16 (2 ativas, 0 em archive)
- `coupling_decrease_from_ref` — Phase2/RGFlow_Work/Theorem2_Monotonicity.lean:85 (refs≈1, UNKNOWN)
- `coupling_decreases_from_reference` — Phase2/RGFlow_Work/Theorem2_Monotonicity.lean:92 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(μ μ₀ g₀ a : ℝ) (h_higher : 0 < μ₀ ∧ μ₀ < μ) (hg : 0 < g₀ ∧ g₀ ≤ g0) (ha : 0 < a ∧ a ≤ a_max) : runn`
- **Tipos idênticos? SIM (textual). Mesmo significado? NÃO** — nomes distintos no mesmo arquivo com o MESMO TIPO CURTO (ex.: quatro constantes ': ℝ'): equivalência de tipo detectada pelo script, não duplicação semântica (exatamente o caso apontado no parecer).
- **Ação proposta: NOT_DUPLICATE** (artefato do detector; refinar extração na v3).

## Grupo 17 (2 ativas, 0 em archive)
- `continuity_from_lipschitz` — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:89 (refs≈1, REFORMULATE)
- `mass_gap_continuous` — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:99 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g1 g2 a eps : ℝ) (hg1 : 0.5 ≤ g1 ∧ g1 ≤ 1.18) (hg2 : 0.5 ≤ g2 ∧ g2 ≤ 1.18) (ha : 0 < a ∧ a ≤ a_max)`
- **Tipos idênticos? SIM (textual). Mesmo significado? NÃO** — nomes distintos no mesmo arquivo com o MESMO TIPO CURTO (ex.: quatro constantes ': ℝ'): equivalência de tipo detectada pelo script, não duplicação semântica (exatamente o caso apontado no parecer).
- **Ação proposta: NOT_DUPLICATE** (artefato do detector; refinar extração na v3).

## Grupo 18 (2 ativas, 0 em archive)
- `gap_bounded_aux` — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:111 (refs≈1, REFORMULATE)
- `gap_bounded_across_region` — Phase2/RGFlow_Work/Theorem5_LipschitzContinuity.lean:115 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(a : ℝ) (ha : 0 < a ∧ a ≤ a_max) : |mass_gap 0.5 a - mass_gap 1.18 a| ≤ lipschitz_L * 0.68`
- **Tipos idênticos? SIM (textual). Mesmo significado? NÃO** — nomes distintos no mesmo arquivo com o MESMO TIPO CURTO (ex.: quatro constantes ': ℝ'): equivalência de tipo detectada pelo script, não duplicação semântica (exatamente o caso apontado no parecer).
- **Ação proposta: NOT_DUPLICATE** (artefato do detector; refinar extração na v3).

## Grupo 19 (2 ativas, 0 em archive)
- `expansion_form` — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:31 (refs≈1, REFORMULATE)
- `mass_gap_asymptotic_in_a` — Phase2/RGFlow_Work/Theorem9_AsymptoticExpansion.lean:44 (refs≈0, DUPLICATE_CANDIDATE)
- enunciado extraído: `(g a : ℝ) (hg : 0.5 ≤ g ∧ g ≤ 1.18) (ha : 0 < a ∧ a ≤ a_max) : ∃ R : ℝ, mass_gap g a = Δ0 g + c2 g *`
- **Tipos idênticos? SIM (textual). Mesmo significado? NÃO** — nomes distintos no mesmo arquivo com o MESMO TIPO CURTO (ex.: quatro constantes ': ℝ'): equivalência de tipo detectada pelo script, não duplicação semântica (exatamente o caso apontado no parecer).
- **Ação proposta: NOT_DUPLICATE** (artefato do detector; refinar extração na v3).

## Resumo
- 19 grupos triados; nenhuma remoção executada.
- Nota estrutural: SingleLink/PairLink (Phase3) NÃO estão nesta lista —
  a proposta em separado é reescrevê-los como wrappers da MultiLink
  (provas delegadas), preservando a API pedagógica. PR próprio, se aprovado.