# RELATÓRIO 52-A-QA2 — Auditoria do delta C1

**Auditor:** Claude Fable 5.1 (segunda instância; bancada pinada, sessão Cowork). **Data:** 2026-09-07 (UTC).
**Escopo:** somente o reparo `0f86ea8… → 4f40443…` (dez declarações novas, delta textual, proveniência). As 56 declarações aprovadas na QA1 não foram re-auditadas; foi verificado que **não mudaram**.
**HARD STOP respeitado:** só leitura, build e testes descartáveis; zero edição, commit, push, PR ou ação remota; push do remoto desativado.

## 1. Custódia

| Item | Resultado |
|---|---|
| Bundle C1 SHA-256 | `fcd30a9942755f51489153f6e2eda8d0e8fb8850a229cd4bacea031c461e93fe` ✅ |
| Diff antigo→C1 SHA-256 (fornecido) | `f9b37c4cdff87dd1e7743f187f70e09666f48194101fbf3900e4d85993249aa0` ✅ — **byte-idêntico** ao diff que reconstruí do bundle (`git diff 0f86ea8 4f40443`) |
| Commit / parent / tree | `4f4044333193fb734a7103ea01f6c472ed464563` / `d62f50d25153d43ca1e8e3aed717614c0973e5f1` / `1e519c9be8c3e122f949c700b9a5a2fc94e7812c` |
| Substituição, não empilhamento | 1 commit acima da base; `0f86ea8…` **não** é ancestral de C1 ✅ |
| Delta de conteúdo | 1 arquivo: `Phase3/LatticeGauge/ActivityDampedObservableGas.lean`, +122/−1; a única linha removida é um comentário do cabeçalho ✅ |
| Declarações aprovadas | nenhuma modificada (o delta é só adição fora do comentário); 56 → 66 declarações |
| 106 módulos anteriores | `git diff --quiet base C1 -- <106 .lean da base>` = idênticos ✅; blobs de 51-A…51-E, 52-A0 e CovarianceDecay conferidos individualmente |
| Base = `origin/main` | `d62f50d…` lido hoje ✅ |

## 2. Proveniência (relatada separadamente da matemática)

- C1: autor **e** committer `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>`; trailer `Co-authored-by: Claude <noreply@anthropic.com>`.
- Padrão real da cadeia (histórico da `main`): todos os commits de módulo desde a Pedra 51 (`a672fae`, `e923677`, `e352f1d`, `76e10fe` = 52-A0) têm exatamente essa identidade e esse trailer. A identidade `Consensus Framework <consensus@smarttourbrasil.com.br>` aparece **apenas** nos 10 merges feitos pelo GitHub — logo o `0f86ea8…` anterior era um acidente de configuração, não uma política.
- Identidades distintas em toda a história: `Claude Fable 5 (Etapa 1)` (196), `Claude Fable 5.1 (Etapa 1)` (17), `Consensus Framework` (10, merges). Nenhuma identidade nova inventada para C1.
- Correção coerente: autor e committer corrigidos juntos; mensagem reescrita para incluir as pontes e interfaces; a data de autoria (`2026-09-07T12:02:11Z`) foi preservada do commit substituído.
- **Conclusão de proveniência:** conforme.

## 3. Build e higiene

Lean 4.15.0, Mathlib `9837ca9d…`, manifesto `c376bbe9…1227` pré = pós.
- Dirigido: exit 0, 243 s, 0 erros, 0 warnings no módulo, 0 `sorryAx`.
- Completo **limpo**: exit 0, 414 s, **107 módulos**, 0 erros; 114 warnings herdados, distribuição por arquivo:linha idêntica ao baseline; 0 no módulo.
- Léxico no delta: 0 `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`/`set_option`.
- `#print axioms` das **dez** declarações novas (rodado por mim, fora do repositório): todas `[propext, Classical.choice, Quot.sound]`.

## 4. Pontes de coeficientes — os dez pontos

| # | Ponto | Resultado |
|---|---|---|
| 1 | Assinaturas literais às definições | `kpSignedUnrootedCoeff k z = (Σ_δ ursell·∏ z(δ i))/k!` (`KPUnrooted.lean:48`) e `kpConnectorUnrootedCoeff k z P Q` com `if TupleHitsBothForbidden P Q δ` (`ConnectorClusters.lean:72`); os LHS das pontes são exatamente essas com `z := dampedActivity z r θ` ✅ |
| 2 | Peso `θ^{tupleTouchCount r δ}` | sim, inserido em frente a cada somando ✅ |
| 3 | Repetições por posição | `tupleTouchCount` conta posições; teste Q2: `![η,η]` → 2, `![η,ζ]` (ζ permitido) → 1 ✅ |
| 4 | `ursell`, produto, filtro, sinais, casts, `k!` intactos | RHS é textualmente a definição com o peso; a prova é `unfold; congr 1; sum_congr; rw [prod_dampedActivity_tuple]; ring` — `congr 1` separa numerador e denominador, então `k!` não é tocado ✅ |
| 5 | Divisão por `k!` na posição certa | fora do somatório, como na definição; teste Q4 (k = 2): denominador literalmente `2`, e `3! = 6` ✅ |
| 6 | Filtro `TupleHitsBothForbidden` intacto | avaliado na tupla **original** (não depende de θ); ramo falso fechado por `rfl`; teste Q3 ✅ |
| 7 | `k = 0` | soma sobre a única tupla vazia, `tupleTouchCount = 0`, `θ^0 = 1`, `0! = 1`; teste Q1 prova coef damped = coef original ✅ |
| 8 | Deriva de `prod_dampedActivity_tuple` | sim, é a única reescrita não trivial ✅ |
| 9 | Nenhuma igualdade-alvo como hipótese | os enunciados não têm hipóteses ✅ |
| 10 | Endpoints | θ = 1 → `kpSignedUnrootedCoeff k z` (via `dampedActivity_one`); θ = 0 → coeficiente de `restrictedActivity z (regionAllowed r)` (via `dampedActivity_zero`) — exatamente os coeficientes das Pedras 49 e 51 ✅. Observação documental: endpoints só para o coeficiente com sinal; o do connector segue pela mesma reescrita (não enunciado). |

## 5. Interfaces estruturais

| Declaração | Verificação |
|---|---|
| `tupleTouchCount_append` | `Fin.sum_univ_add` + `Fin.append_left/right` sobre a forma-soma; teste Q5 (inclusive forma concreta `append ![η] ![ζ]`) ✅ |
| `dampedActivity_empty_region` | `funext` + `if_neg (not_blockTouchesSupport_empty η.val)` — `typedTouchesSupport η s := blockTouchesSupport η.val s` (defeq), e `not_blockTouchesSupport_empty` (`ObservableGas.lean:182`) é `unfold; simp` sobre `¬ Disjoint … ∅`. Deriva das definições reais ✅ |
| `touchCount_empty_region`, `tupleTouchCount_empty_region` | `card_eq_zero` + `filter_eq_empty_iff` + o mesmo lema base ✅ |
| `activityDampedPolymerGas_empty_region` | `rw [dampedActivity_empty_region]` → gás típico original ✅ |
| `activityDampedMarkedGas_empty_region` | `touchCount_empty_region` → `θ^0 = 1` termo a termo → `typedMarkedPolymerGas` ✅ |

Nenhuma hipótese impossível; nenhuma conclusão embutida (os `omit` são de instâncias de seção não usadas).

## 6. Matriz das dez declarações novas

| Declaração | Dependências | Axiomas | Correção | Hipóteses | Uso previsto | Classificação |
|---|---|---|---|---|---|---|
| `dampedActivity_empty_region` | `not_blockTouchesSupport_empty` | p/c/Q | ✓ | nenhuma | região vazia | VERIFIED |
| `tupleTouchCount_append` | `Fin.sum_univ_add` | p/c/Q | ✓ | nenhuma | tuplas | VERIFIED |
| `touchCount_empty_region` | idem base | p/c/Q | ✓ | nenhuma | região vazia | VERIFIED |
| `tupleTouchCount_empty_region` | idem base | p/c/Q | ✓ | nenhuma | região vazia | VERIFIED |
| `kpSignedUnrootedCoeff_dampedActivity` | `prod_dampedActivity_tuple` | p/c/Q | ✓ (R1 da QA1 resolvida) | nenhuma | ledger | VERIFIED |
| `kpConnectorUnrootedCoeff_dampedActivity` | `prod_dampedActivity_tuple` | p/c/Q | ✓ (R1 da QA1 resolvida) | nenhuma | ledger | VERIFIED |
| `kpSignedUnrootedCoeff_dampedActivity_one` | `dampedActivity_one` | p/c/Q | ✓ | nenhuma | endpoint | VERIFIED |
| `kpSignedUnrootedCoeff_dampedActivity_zero` | `dampedActivity_zero` | p/c/Q | ✓ | nenhuma | endpoint | VERIFIED |
| `activityDampedPolymerGas_empty_region` | `dampedActivity_empty_region` | p/c/Q | ✓ | nenhuma | região vazia | VERIFIED |
| `activityDampedMarkedGas_empty_region` | `touchCount_empty_region` | p/c/Q | ✓ | nenhuma | região vazia | VERIFIED |

Assinaturas literais em `new_declarations_signatures.tsv`. As reservas R1 (ponte de coeficientes) e R2 (concatenação, região vazia) da QA1 estão **resolvidas**; R3 (cosmética) e R4 (proveniência) — R4 resolvida por C1; R3 permanece cosmética e não requer ação.

## 7. Testes próprios

| Teste | Conteúdo | Resultado |
|---|---|---|
| Q0 | `#print axioms` das 10 novas | 10/10 `[propext, Classical.choice, Quot.sound]` |
| Q1 | k = 0: coeficiente amortecido = original | ✅ |
| Q2 | uma ocorrência → 1; duas posições repetidas → 2; tupla mista → 1 | ✅ |
| Q3 | filtro do connector verdadeiro/falso; identidade literal reproduzida | ✅ |
| Q4 | k = 2: `/2` literal; `3! = 6` | ✅ |
| Q5 | região vazia e `append` (inclusive forma concreta) | ✅ |

## 8. Veredito

Delta limitado, substituição correta do candidato anterior, proveniência alinhada ao padrão real da cadeia, dez declarações novas verificadas pelo kernel e pelos testes, 106 módulos anteriores byte-idênticos, builds limpos. Sem reservas de conteúdo.

**`52-A QA2 PASS — C1 READY FOR PUBLICATION`**

HARD STOP.
