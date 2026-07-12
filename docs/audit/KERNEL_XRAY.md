# KERNEL_XRAY.md — dependências reais segundo o kernel (Fase 2)

Método: Audit_<Mod>.lean com #print axioms para cada teorema, executado
no CI; saída colhida do log do build. NÃO é heurística: é o kernel.
Instrumentação permanente — o raio-X regenera a cada build.

## Placar do kernel
- Teoremas radiografados: 126
- **Kernel-clean (apenas propext/Classical.choice/Quot.sound): 2**
- Dependentes de axiomas científicos: 124

## Confirmação dos wrappers (pergunta do parecer)

- `c2_is_negative` → RGFlow.c2_negative_axiom (WRAPPER)
- `continuum_limit_unique` → limit_unique_aux + mass_gap (WRAPPER composto)
- `coupling_decreases_from_reference` → coupling_decrease_from_ref (WRAPPER)

Nota adicional do kernel: a tentativa de co-importar todos os módulos
FALHOU porque `mass_gap` está axiomatizado em ≥2 arquivos — confirmação
em nível de import da duplicação de pressupostos apontada na R2A.

## Axiomas científicos por número de teoremas dependentes

- `Classical.choice` ← 124 teorema(s)
- `Quot.sound` ← 124 teorema(s)
- `RGFlow.Delta0` ← 33 teorema(s)
- `RGFlow.mass_gap` ← 33 teorema(s)
- `RGFlow.mass_gap_tendsto_continuum` ← 10 teorema(s)
- `RGFlow.continuum_monotonic_in_g` ← 7 teorema(s)
- `RGFlow.Delta0_at_gmax` ← 5 teorema(s)
- `RGFlow.Delta0_at_gmin` ← 5 teorema(s)
- `RGFlow.continuum_gap_quantitative_separation` ← 5 teorema(s)
- `RGFlow.mass_gap_lipschitz_in_g` ← 4 teorema(s)
- `RGFlow.mass_gap_A` ← 4 teorema(s)
- `RGFlow.mass_gap_lower_bound` ← 4 teorema(s)
- `RGFlow.mass_gap_A_tendsto` ← 3 teorema(s)
- `RGFlow.mass_gap_B` ← 3 teorema(s)
- `RGFlow.mass_gap_lower_bound_continuum` ← 2 teorema(s)
- `RGFlow.mass_gap_monotonic_in_g` ← 2 teorema(s)
- `RGFlow.initial_condition` ← 2 teorema(s)
- `RGFlow.coupling_stays_bounded_aux` ← 2 teorema(s)
- `RGFlow.continuum_lipschitz_in_g` ← 1 teorema(s)
- `RGFlow.mass_gap_B_tendsto` ← 1 teorema(s)
- `RGFlow.beta` ← 1 teorema(s)
- `RGFlow.c2_negative_axiom` ← 1 teorema(s)
- `RGFlow.Delta0_positive_axiom` ← 1 teorema(s)
- `RGFlow.expansion_form` ← 1 teorema(s)
- `RGFlow.coupling_decrease_from_ref` ← 1 teorema(s)
- `RGFlow.gap_bounded_aux` ← 1 teorema(s)
- `RGFlow.continuity_from_lipschitz` ← 1 teorema(s)
- `RGFlow.gap_change_full_range_aux` ← 1 teorema(s)
- `RGFlow.two_sided_upper_bound` ← 1 teorema(s)
- `RGFlow.no_plateaus_aux` ← 1 teorema(s)
- `RGFlow.continuum_limit_exists_aux` ← 1 teorema(s)
- `RGFlow.gap_stable_aux` ← 1 teorema(s)
- `RGFlow.limit_unique_aux` ← 1 teorema(s)

## Teoremas kernel-clean da Fase 2 (lista nominal)

- `RGFlow.bound_from_monotonicity_concept`
- `RGFlow.monotonicity_from_beta_negativity_concept`