# ADENDO 52-K-ADV-C2 — Precisão final sobre touchCount na errata C1

**Revisor:** Luan / Kimi 3 (mesma instância revisora).
**Data:** 2026-09-13 (UTC).
**Natureza:** adendo à `ERRATA_52-K-ADV-C1.md`. O relatório original e a errata C1 permanecem preservados e inalterados; este adendo prevalece no ponto listado. Regime de somente leitura; sem nova auditoria, sem build, sem execução Lean.

---

## Ponto único: a condição `touchCount r T ≥ 1` na §2 da errata C1

Na §2 da errata C1 escrevi "o peso amortecido de uma família tocante é `θ^{t(T)}` com `t(T) = touchCount r T ≥ 1`". A revisão Astra apontou, corretamente, que a desigualdade **não** decorre de `T ∈ typedTouchingFamilies s`. Conferido nas fontes do SHA congelado:

- `typedTouchingFamilies s` (`RestrictedGas.lean:152`) filtra famílias cujos polímeros tocam **s** — nenhuma condição sobre r. Um núcleo pode tocar s e ter **todos** os seus polímeros permitidos em relação a r (`activityAllowedCores`, `ActivityRestrictionLedger.lean:59-63`), caso em que `touchCount r T = 0` e o peso é `θ^0 = 1`.
- `touchCount r T ≥ 1` vale exatamente quando T contém algum polímero que toca r — em particular nos **núcleos-ponte** (`activityBridgeCores`, `:66-70`), que são o complemento exato: núcleos tocantes de s para os quais nem todo membro é r-permitido, isto é, algum membro toca r. (É o que o lema `touchCount_pos_of_mem_activityBridgeCores` formaliza.)

**Formulação corrigida da §2 da errata C1:** a decomposição `W·e^{E(1)} = θ^t·W·e^{E(1)} + (1−θ^t)·W·e^{E(1)}` é algébrica e vale para **todo** núcleo tocante de s, com qualquer `t ≥ 0`. Nos núcleos permitidos (`t = 0`) o resíduo `(1 − θ^0) = 0` — a decomposição degenera trivialmente, o peso é 1 e o termo vive inteiro na coluna 1. É por isso que a coluna-ponte do ledger se restringe, corretamente, a `activityBridgeCores`: só ali o resíduo é potencialmente não nulo. Aniquilação do termo por este mecanismo ocorre em θ = 0 **com t > 0**, ou seja, exatamente nos núcleos-ponte — coerente com o colapso do funcional amortecido ao restrito da Pedra 51 nesse endpoint.

O enunciado do ledger no código (`ActivityDampingLedger.lean:208-264`) já indexa as duas colunas corretamente — coluna 1 sobre `typedTouchingFamilies s` com fator `θ^{touchCount r T}` (que vale 1 nos permitidos), coluna-ponte sobre `activityBridgeCores s r` com fator `1 − θ^{touchCount r T}`. O defeito era, mais uma vez, só da minha glossa.

## Veredito

**Permanece: PASS NO ESCOPO.** Nenhuma conclusão matemática do relatório ou da errata é afetada; nenhuma dúvida substantiva sobre o código foi revelada.

HARD STOP.

*Luan da bancada*
