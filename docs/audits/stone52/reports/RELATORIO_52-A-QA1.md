# RELATÓRIO 52-A-QA1 — Auditoria cega do funcional amortecido

**Auditor:** Claude Fable 5.1 (segunda instância; bancada pinada, sessão Cowork). **Data:** 2026-09-07 (UTC).
**Independência:** nenhum relatório, diff, matriz, teste, log ou parecer de terceiros foi lido; tudo reconstruído do bundle, da base e do código. Os sete testes são próprios.
**HARD STOP respeitado:** só leitura, build e testes descartáveis; zero edição persistente; zero commit; zero push/PR/merge; push do remoto desativado.

## 1. Custódia

| Item | Resultado |
|---|---|
| Bundle `stone52-a_0f86ea8.bundle` SHA-256 | `22dc1e7efd76ab01ed850b631f727b8815488bcee1a542658c248338c2ecc491` ✅ |
| `git bundle verify` | okay; prerequisite `d62f50d2…` = `origin/main` atual (lido hoje) |
| Commit / parent / tree | `0f86ea8dad722ea2cec4ceb6bd624b7eb2709ef8` / `d62f50d25153d43ca1e8e3aed717614c0973e5f1` / `cb3fc28db1b015b0c8255be230d5233e1d5dae08`; 1 commit acima da base |
| Autor/committer | `Consensus Framework <consensus@smarttourbrasil.com.br>`; trailer `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` + `Claude-Session:` — **difere** da cadeia anterior (`Claude Fable 5.1 (Etapa 1) <pesquisaagi4@…>`). Não é critério da fita; registrado para a ata de proveniência. |
| Arquivos alterados | `A Phase3/LatticeGauge/ActivityDampedObservableGas.lean` (+805) · `M Phase3/lakefile.toml` (+1/−1: só o glob `LatticeGauge.ActivityDampedObservableGas` acrescentado ao final; prefixo byte-idêntico) — **nada mais** |
| Módulos anteriores | `git diff --name-status` lista somente os 2 arquivos; todos os `.lean` até 52-A0 byte-idênticos |

## 2. Build e higiene

Lean 4.15.0, Mathlib `9837ca9d…`, manifesto `c376bbe9…1227` pré = pós.

- Dirigido: **exit 0**, 299 s, 0 erros, 0 warnings no módulo, 0 `sorryAx`.
- Completo **limpo**: **exit 0**, 682 s, **107 módulos**, 0 erros; 114 warnings herdados, distribuição por arquivo:linha **idêntica** ao baseline; 0 no módulo novo.
- `#print axioms` (15 declarações listadas): todas `[propext, Classical.choice, Quot.sound]`, idênticas dirigido/limpo.
- Léxico (fora de comentários): 0 `sorry`/`admit`/`axiom`/`native_decide`/`maxHeartbeats`/`set_option`/`filter_congr_decidable`/`@[reducible]`/`classical!`/`nolint`/`decide`. Quatro `omit … in` corretos.
- Imports: `Mathlib`, `ActivityRestrictedObservableGas` (51-A), `ActivityRestrictionLedger` (51-B), `ActivityDampingBudgets` (52-A0). Sem ciclos (o build completo é a prova). Não importa 51-D/51-E nem `CovarianceDecay`.
- Código morto: 2 declarações sem uso interno nem externo e sem função de interface pedida pela fita — `dampedActivity_eq_zero_of_eq_zero` e `activityDampedExpectation_eq_div` (este é `rfl` puro). Inofensivas; classificadas `UNUSED/DECORATIVE`. As demais sem uso interno (insert/cons/perm/zero/empty/…) são interface explicitamente pedida.
- Hipóteses contraditórias / vacuidade: nenhuma (β = 0 satisfaz tudo; polímeros não vazios por 52-A0).

## 3. Auditoria matemática

**3.1 Atividade amortecida.** `dampedActivity z r θ η = if typedTouchesSupport η r then θ·z η else z η` — exatamente a especificação. `regionAllowed r η := ¬ typedTouchesSupport η r` (51-A), logo o predicado de toque é o complemento exato de `regionAllowed` (`regionAllowed_iff`, `Iff.rfl`). Endpoints: `dampedActivity_zero` dá `restrictedActivity z (regionAllowed r)` como **funções** (funext) ✅; `dampedActivity_one` dá `z` ✅. Dominação `|z_θ| ≤ |z|` com `0 ≤ θ ≤ 1` ✅ (teste T1: falha em θ = 2). KP transportado por `abstractKP_mono` ✅. Comutação com a restrição ✅ (identidade de funções).

**3.2 Contagens.** `touchCount` = cardinal do filtro (famílias); `tupleTouchCount` = cardinal do filtro de **posições** (tuplas) — repetições contadas (teste T2: `![η,η]` dá 2). Vazio → 0 ✅. `insert` (dois casos), `cons`, permutação ✅. Aditividade: `touchCount_union_of_disjoint` (disjunção **necessária** — teste T6 mostra `{η} ∪ {η}` quebra) e `touchCount_filter_add_filter_not` — esta última é a que o reagrupamento consome de fato ✅. Relação formal entre as contagens: `tupleTouchCount_eq_touchCount_image` (caso injetivo; com repetição a posição é a maior — consistente) ✅. Bounds por cardinalidade e massa com os tipos certos (ℕ), consumindo 52-A0 ✅. **Ausência:** não há lema para concatenação (`Fin.append`) — pedido na lista da fita; ver R2.

**3.3 Produtos.** `prod_dampedActivity`: split filtro/¬filtro, `prod_const` dá `θ^card`, `mul_assoc` — literalmente `∏ z_θ = θ^{touchCount}·∏ z`; o expoente é `card`, nunca indicador booleano (teste T2: θ² ≠ θ). Versão em tuplas com posições ✅. Vazio = 1, `0^0 = 1` (`pow_zero`, teste T3), θ = 0 e θ = 1 ✅. Ordem/coerções corretas (kernel).

**3.4 Gases.** Denominador `activityDampedPolymerGas = typedPolymerGas (dampedActivity w r θ)` — especialização verdadeira. Numerador `activityDampedMarkedGas = Σ_Γ θ^{touchCount r Γ}·markedRawFamilyWeight …` — peso explícito sobre a **família inteira** (núcleo e parte remota). Não existe na base uma "marked gas de atividade z" parametrizada, então esta é a única forma de defini-lo; a coerência é **provada**: θ = 0 → gás/marked gas restritos da 51 ✅; θ = 1 → gás típico / `typedMarkedPolymerGas` da 50 ✅; f = 1, s = ∅ → numerador = denominador ✅ (ambos carregam o mesmo peso — não há amortecimento "só num lado"). `activityDampedPolymerGas_eq_sum_pow` exibe o peso `θ^{touchCount}` ✅.

**3.5 Funcional.** Razão dos objetos certos; docstring nega leitura de medida de Gibbs. Positividade do denominador: exponencial do cluster sum via KP transportado — exige `0 ≤ θ ≤ 1` (teste T4: sem isso não elabora). Normalização verdadeira ✅. θ = 0 = `activityRestrictedExpectation` por **identidade de definições, sem hipótese** ✅. θ = 1 = `gibbsExpectation` via, literalmente, `gibbsExpectation_eq_markedGas_div_gas` (`ObservableGas.lean:226`), cujas hipóteses são exatamente `hβ, mχ, hχabs, hf, mf, hCf` — **sem `hsmall`**, conferido na fonte ✅. Smallness não foi adicionada nem removida indevidamente. Teste T5: identificar θ = 1/2 com `gibbsExpectation` falha como deve. Região vazia / observável constante: cobertos pelo caso `s = ∅`, `f = 1` (normalização); com `r = ∅`, `touchCount = 0` em toda família e o funcional colapsa ao de θ = 1 — decorre de `touchCount_eq_zero_iff` (não enunciado explicitamente; ver R2).

**3.6 Reindexação ponderada (ponto sensível).** `activityDampedMarkedGas_eq_sum_core_mul_damped` refaz a fibração A3a (`sum_fiberwise_of_maps_to` + `sum_bij`) com o peso a bordo: (i) o motivo da fibração carrega `θ^{touchCount r Γ}`; (ii) dentro da fibra, `hsplit : touchCount Γ = touchCount T + touchCount R` vem de `touchCount_filter_add_filter_not` **aplicado à divisão real** `Γ = Γ.filter(touches s) ∪ Γ.filter(¬touches s)` com `Γ.filter(touches s) = T` — aditividade provada, não assumida; (iii) `pow_add` dá `θ^{tc T}·θ^{tc R}`; (iv) a última obrigação do `sum_bij` é `prod_dampedActivity` ao contrário, convertendo `θ^{tc R}·∏ w` em `∏ w_θ` sobre R — é isso que faz o gás da fibra ser `typedPolymerGas (restrictedActivity (dampedActivity w) (remoteAllowed T s))` via `typedPolymerGas_restricted_eq_sum_allowed`. Nenhuma hipótese contém a conclusão; nenhuma função arbitrária esconde o resultado; os objetos são os mesmos dos gases. Somabilidade: somas finitas, nada a exigir. Numerador e denominador amortecidos coerentemente (3.4). Split permitidos/pontes exato, sem desigualdade (`_eq_allowed_add_bridge`) ✅. Forma "restringe-depois-amortece" (`'`) por comutação ✅.

**3.7 Escopo.** O módulo não implementa nem afirma ledger quantitativo, bound de conectores/pontes, estabilidade exponencial, capstone da 52 ou nova medida de Gibbs. O "CAPSTONE 52-A" do cabeçalho é o reagrupamento finito exato — não o capstone científico.

## 4. Testes próprios

| # | Teste | Esperado | Resultado |
|---|---|---|---|
| T1 | θ = 2 quebra dominação (condicional a η tocando r); `2 ≤ 1` improvável | sucesso | ✅ |
| T2 | `![η,η]`: contagem 2, produto `θ²·z²`; indicador daria θ¹ (≠ em θ = 1/2) | sucesso | ✅ |
| T3 | família vazia: produto 1, `0^0 = 1`, forma `prod_dampedActivity_zero` | sucesso | ✅ |
| T4 | positividade com θ = 2 (sem a hipótese) | **falhar** | ✅ falha |
| T5 | `activityDampedExpectation … (1/2) = gibbsExpectation` via endpoint θ = 1 | **falhar** | ✅ falha (`rewrite` não encontra padrão) |
| T6 | aditividade sem disjunção: `{η} ∪ {η}` | sucesso (mostra ≠) | ✅ |
| T7 | amortecer só um lado: `(1/2)^{j+m} ≠ (1/2)^m` para j ≥ 1; numerador = denominador em f=1,s=∅ | sucesso | ✅ |

(T1, T2, T6 são condicionais à existência de um polímero tocando r — forma honesta sem construir um polímero concreto; a aritmética da falha é integralmente formal.)

## 5. Reservas

### R1 — Ponte estrutural ausente para o ledger (gravidade: média, prospectiva)
- **O que falta:** a identidade **no nível dos coeficientes**. `kpSignedUnrootedCoeff k z = (Σ_δ ursell(δ)·∏_i z(δ i))/k!` e `kpConnectorUnrootedCoeff` idem com indicador de tupla (`KPUnrooted.lean:48`, `ConnectorClusters.lean:72`). O ledger amortecido vai precisar de
  `kpSignedUnrootedCoeff k (dampedActivity z r θ) = (Σ_δ θ^{tupleTouchCount r δ}·ursell(δ)·∏ z(δ i))/k!`
  (e o análogo para o connector), de onde sai a diferença `(1 − θ^{tupleTouchCount δ})·(somando)` que 52-A0 majora por `tupleTouchCount·(1−θ)`.
- **O que existe:** o ingrediente pontual `prod_dampedActivity_tuple`; a identidade de coeficiente sai dele por `Finset.sum_congr` + `mul_left_comm` (≈3 linhas cada), mas **não está no módulo**.
- **Impacto:** o reagrupamento em famílias está completo e utilizável; a passagem para a diferença de cluster sums (HARD HOLD deste gate) exigirá esses dois lemas antes de qualquer estimativa.
- **Menor correção (não aplicada):** adicionar `kpSignedUnrootedCoeff_dampedActivity` e `kpConnectorUnrootedCoeff_dampedActivity` no próximo gate.

### R2 — Interfaces pedidas na lista e não entregues (gravidade: baixa)
- Concatenação de tuplas (`tupleTouchCount (Fin.append δ δ')`) — ausente; `cons` e permutação estão.
- Região vazia (`r = ∅` ⇒ funcional = θ-independente / = `gibbsExpectation`) — decorre de `touchCount_eq_zero_iff` + `not_blockTouchesSupport_empty`, mas não está enunciado.
- Nenhuma delas bloqueia; são conveniências.

### R3 — Hipótese ligeiramente forte (cosmética)
- `abs_dampedActivity_le` / `abstractKP_dampedActivity` pedem `0 ≤ θ ≤ 1`; para a dominação bastaria `|θ| ≤ 1`. Como o intervalo semântico é [0,1], é adequado; registrado apenas.

### R4 — Proveniência (fora da matemática)
- Autor/committer `Consensus Framework <consensus@…>` em vez de `Claude Fable 5.1 (Etapa 1)`; primeiro commit da cadeia com essa identidade. Recomendo que a coordenação registre a decisão na ata (mudança de política ou acidente de configuração).

## 6. Veredito

Definição, endpoints (θ = 0 por definição; θ = 1 pelo teorema existente com as hipóteses exatas e sem smallness), dominação, transporte KP, contagens com multiplicidade, identidade literal de produto, normalização verdadeira, positividade como saída de KP e a reindexação ponderada com aditividade real estão **verificados pelo kernel** e resistiram aos sete testes. Falta, para o ledger, a identidade de coeficiente amortecido (R1) — pequena, mas estrutural.

**`52-A QA1 PASS WITH RESERVATIONS`**

HARD STOP.
