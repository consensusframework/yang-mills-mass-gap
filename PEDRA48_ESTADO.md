# PEDRA 48 — ESTADO FINAL

**De:** Fable. **Arquiteto:** Sol (GPT-5.6). **Coordenação:** Jucelha Carvalho. **Juiz:** GitHub Actions CI (Lean 4 + Mathlib v4.15.0).
**Status: COMPLETA.** Núcleo matemático congelado e auditado no commit `c9dda043da48ec8127250197132522857695f314` (CI run 31886396666, verde). Fechamento documental/higiene aplicado sobre esse núcleo SEM alterar matemática (parecer consolidado do Sol).

## Revisões externas

- **External adversarial mathematical review — Kimi 3 (Moonshot AI): APPROVED.** Primeira pedra do projeto sem correção substantiva. Achado B1 (higiene): import vestigial de KPSmallness em KPCoefficients — removido neste fechamento (fronteira abstrato/concreto agora literal também no grafo de imports). B2: censo do Fable verificado linha a linha no source pinado.
- **External reproducibility and release review — Manus AI 1.6: APPROVED FOR DOCUMENTATION CLOSURE AND MERGE.** Build reproduzido em clone independente; escopo epistêmico conferido; achados documentais (cabeçalhos desatualizados de KPInduction/KPSpecialization/SeriesBridge) — todos corrigidos neste fechamento.

## O que a Pedra 48 provou (tudo no kernel)

- **48A** — ponte ordem→série CONSUMIDA do pin (nada duplicado): `summable_of_sum_range_le` (InfiniteSum/Real.lean:85) e `Real.tsum_le_of_sum_range_le` (:91); sanidades em `SeriesBridge.lean`.
- **48B** — série do MAJORANTE: `summable_kpTreeCoeff`, `tsum_kpTreeCoeff_le_exp` (≤ exp(a γ)), com a ponte `sum_range_kpTreeCoeff_le_exp` (degrau `sum_range_succ` + não-negatividade, visível).
- **48C-α** — `summable_kpUrsellCoeff`, `tsum_kpUrsellCoeff_le_exp` (série dos coeficientes Ursell ABSOLUTOS), com auditoria semântica do `natAbs` registrada no arquivo.
- **48C-β** — `kpSignedUrsellCoeff` (o objeto ASSINADO: φ ∈ ℤ cast a ℝ, atividades z assinadas); a dominação `|Cₙ(z)| ≤ Aₙ(|z|)`; `summable_abs_…`, `summable_…` (assinada), e `tsum_abs_… ≤ exp(a γ₀)` — hierarquia |Cₙ| ≤ Aₙ ≤ Tₙ fechada no nível das séries.
- **48D** — especialização concreta com z LITERALMENTE `polymerWeight` (assinado): `polymer_summable_abs_signedUrsell`, `polymer_summable_signedUrsell`, **CAPSTONE `polymer_tsum_abs_signedUrsell_le_exp_card`**, e o corolário da raiz `polymer_rooted_signedUrsell_bound`.

**Frase científica congelada:** *For 0 ≤ β ≤ 1/40000, the concrete signed **rooted** Ursell series is absolutely convergent, with Σₙ |Cₙ(w_{β,χ}, γ₀)| ≤ exp(card γ₀).*

## Placar e critério de contagem

63 arquivos Phase-3. Declarações: `grep -rEc "^(theorem|protected theorem)"` = 740; incluindo `^lemma` = 741; incluindo `private/nonrec` = 755; contagem independente do Manus (critério próprio) = 744. **Forma adotada nos materiais: "approximately 740 verified theorem/lemma declarations"** (arredondamento aceito pelo revisor de reprodutibilidade). 0 axiomas científicos, 0 sorry.

## O que a Pedra 48 NÃO provou

Nenhuma identificação com log Z; nenhum realZ ≠ 0; nenhuma representação "cluster expansion = log Z"; nenhum limite termodinâmico; nenhum clustering; nenhum gap. **Pedra 49 NÃO autorizada** (mapa do Sol: 49A tirar a raiz → 49B somabilidade não-enraizada → 49C identificação exp/log).

— Fable
