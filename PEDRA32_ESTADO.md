# PEDRA 32 — CONCLUÍDA (2026-07-16)

## Resultado
Nível (a) completo, VERDE em DUAS rodadas.
Arquivo: Phase3/LatticeGauge/PlaquetteActivity.lean
Novos: 3 defs (admissiblePlaquettes, localPlaquetteAction,
plaquetteActivity) + 6 teoremas (A decomposição local; B identidade
produto; C identidade de Mayer sobre subconjuntos; D cota local
|m_p| ≤ 2β; mensurabilidade da atividade; E realZ = soma finita).
Placar: 32 pedras, 31 arquivos, ~171 teoremas, 0 axiomas.
Zero sorry; zero axiomas científicos; zero código de conectividade.

## Relato de APIs Mathlib v4.15 (verificadas no source ANTES do código)
- Finset.prod_add (Algebra/BigOperators/Ring.lean:158):
  ∏(f+g) = Σ_{t ∈ powerset} (∏_t f)·(∏_{s\t} g) — encaixou direto,
  sem indução local.
- Real.exp_sum, Real.add_one_le_exp, Fintype.sum_prod_type,
  Finset.sum_filter, Finset.abs_prod, Finset.prod_const,
  integral_finset_sum — todas presentes e usadas.
- Cota local: 2β (melhor que os 2βe^{2β} aceitáveis), diretamente de
  Real.add_one_le_exp; nenhuma maquinaria nova.

## Vilão da rodada 1 (atlas atualizado, modo novo)
Unificação de ordem superior desdobrou `Measurable` para
`∀ t, MeasurableSet t → …` e o dot-notation `.aestronglyMeasurable`
foi resolvido contra `MeasurableSet.*`. Cura: `have` com tipo
`Measurable (…)` anotado antes do dot.

## realZ vs partitionFunction (motivo registrado no docstring)
Atividades são assinadas (exp(−βs) − 1 ≤ 0 para β ≥ 0, s ≥ 0);
ENNReal.ofReal não é aditivo sobre somas assinadas — a identidade
integrada vive em realZ.
