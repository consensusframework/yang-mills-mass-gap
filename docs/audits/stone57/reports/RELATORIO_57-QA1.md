# RELATÓRIO 57-QA1 — Auditoria independente da Pedra 57 (composição finita da estimativa localizada da Pedra 56 para uma família de regiões)

**Auditor:** Claude Fable 5.1 (instância auditora, bancada Lean própria; distinta da instância construtora da 57-L).
**Data:** 2026-10-09 (UTC). **Fita:** FITA 57-QA1 (Can/Ju). **Modo:** somente leitura sobre o candidato; zero edições, zero commit científico/push/PR/merge/tag/Release/Zenodo; nenhum defeito corrigido; Pedra 58 não iniciada. Ref temporária local `refs/bundles/qa57` apenas para a reconstrução.

## 0. Identidade e exposição prévia

Declaro exposição prévia: auditei as fitas 52-A0…52-E, 53, 54, 55 e 56 (com a errata C1) deste programa; a arquitetura (Can/Astra) está na fita; li `RELATORIO_57-L.md` (SHA `f77e0ee2…` conforme a fita; 15.791 B) antes da execução, só para identificar o alvo. **Esta auditoria não é cega.** Separação de instâncias ≠ diversidade de família de modelos ≠ revisão por especialista humano. Testes, matrizes e logs do construtor ficaram fechados até `PRELIMINARY_CONCLUSIONS_first_pass.md` (no pacote); depois foram abertos, comparados e reexecutados (§7). Oleans do construtor não foram usados. A bancada anterior foi perdida com o container; esta auditoria reconstruiu a bancada do zero (§2).

## 1. Alvo e custódia

| item | observado | fita |
|---|---|---|
| base | `95091fdd07398a7b42901829ad61e4e2c26d5aaa` = `origin/main` = tag `zenodo-v56` (fetch de 2026-10-09); root `8b723878…`, Phase3 `f387f26d…` | ✅ |
| candidato | `c936d4617f3e6f35ea1431c2fa9496b235940f5a`, parent único = base; root `47e84319…`, Phase3 `cc1bfb26…` | ✅ |
| blobs | módulo `818048c4…` (`Phase3/LatticeGauge/ActivityProfileDampingMultiRegion.lean`, 527 linhas, 28.102 B, SHA `9a66665a…`, modo 100644); lakefile `11de6e17…` (antes `ae8438d4…`, modo 100644) | ✅ |
| diff | exatamente 2 caminhos, A +527 e M +1/−1 (só o glob novo), total +528/−1; `git diff base..cand` byte-idêntico a `stone57_vs_base.diff` (`5ed714dd…`) | ✅ |
| preservação | 117 módulos anteriores, manifesto (`c376bbe9…`), pins, workflows, docs, auditorias, licenças idênticos à base | ✅ |
| ZIP | `934a898d…d9d2` (359.578 B); 20 entradas, 0 diretórios, caminhos seguros, sem duplicatas, CRC OK; `SHA256SUMS_57-L.txt` 19/19 sem auto-inclusão; avulsos (módulo, bundle `2d02b78a…`, diff, matrizes `8c28f460…`/`78c65139…`) com bytes e hashes = fita | ✅ |
| bundle | `git bundle verify` OK; requer a base; `refs/heads/stone57` = candidato | ✅ |

Proveniência: autor/committer `Claude <noreply@anthropic.com>`, cabeçalho `gpgsig` SSH presente (não verificável nesta bancada), trailers `Co-Authored-By: Claude Fable 5.1` / `Claude-Session` — precedente 53–56; registrado, não é autenticação independente de autoria.

## 2. Bancada e método

Container novo: elan 4.2.4; toolchain `leanprover/lean4:v4.15.0` (Lean 4.15.0, 11651562caae; Lake 5.0.0-1165156); clone próprio com push desabilitado (`DISABLED_NO_REMOTE_WRITE`); worktree destacada no candidato. Dependências: **cache comunitário do Mathlib** (`lake exe cache get`, 5.826 arquivos, 12:53–12:55Z), origem registrada; 9/9 revisões do checkout = manifesto versionado (mathlib `9837ca9d…`, batteries, aesop, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli); sem `lake update`; manifesto `c376bbe9…` idêntico antes das dependências, antes e depois do build. Nenhum artefato de build do projeto existia (`.lake/build` ausente, registrado em `prebuild_artifacts.txt`). Sequência: custódia → leitura integral das 527 linhas e das interfaces consumidas da 56 → `lake build` integral desacoplado (`setsid nohup`) → testes próprios Q0–Q8x (`lake env lean` a partir de `Phase3/`) → comparação de blocos de warnings → certidões → higiene e contagens → conclusões preliminares → material do construtor → este relatório.

## 3. Execução

- **Rebuild integral** (único, sem tentativas parciais): início 2026-10-09T12:55:31Z, fim 13:08:45Z, exit 0 (794 s); **118 `LatticeGauge` Built / 0 Replayed**; dependências 0 Built / 0 Replayed (oleans do cache já presentes; nenhum diagnóstico de dependências emitido — isso não afirma ausência de avisos numa recompilação das dependências); 0 erros; 0 sorryAx; 118 `.olean`, 0 anteriores ao início; árvore limpa após o build. Log `build_full_clean.log` (SHA `5bd23aab…`).
- **Certidões** (parser com listas multilinha, prefixo `info:` e apóstrofo): **291 = 269 + 22, 291/291 exatamente `[propext, Classical.choice, Quot.sound]`**, 74 multilinha, 291 nomes únicos (inclui `activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`); as 3 definições têm `#print axioms` no módulo e aparecem no rebuild. Q0 (próprio): 22/22.
- **Warnings** (blocos integrais multilinha; normalização só do prefixo `./`; projeto/dependências/testes separados): baseline = `docs/audits/stone56/packages/QA1_56_evidence.zip` do commit da base (SHA `53399f1a…` ✅; manifesto 45/45 sem auto-inclusão, caminhos `./` resolvidos) → `build_full_clean.log` (SHA `38ca3d81…` ✅, meu log da 56-QA1, que validou os 117 módulos preservados). Candidato: **114 blocos de projeto, multiconjunto idêntico ao baseline**, cabeçalhos idênticos, 113 pares arquivo:linha, **0 no módulo novo**; dependências 0 = 0. Testes descartáveis da QA1: **34 avisos** (Q1 28 — binders não usados nos dois `example` de comparação de tipos; Q4 4; Q6 2; demais 0), separados dos 114 herdados.

| tabela de avisos | projeto (herdados) | módulo novo | dependências | testes QA1 |
|---|---:|---:|---:|---:|
| meu rebuild / testes | 114 (= baseline) | 0 | 0 emitidos | 34 |

- **Higiene** (código, fora de docstrings/comentários): 0 sorry/admit/axiom/native_decide/unsafe/opaque/set_option/maxHeartbeats/partial/decide/Disjoint/DependsOnlyOn; "admitted" na docstring l. 370 é a palavra inglesa; `card R` só no cabeçalho (negado). Imports: `Mathlib`, `LatticeGauge.ActivityProfileDampingLocality`. Consumidos da 56: `abs_profileExpectation_sub_profileExpectation_le_two_terms_localized` (dependência intencional, 1 uso, l. 285), `profileExpectation_eq_of_touchFactor_eq` (2 usos); `nonneg_of_abs_le_of_config` (52-E); capstone 56 (`…_le_local_exp_decay_localized`) não usada. Linters ativos.
- **Contagens** (método publicado do README, nove alternativas com espaço, sobre objetos Git): módulos 117 → 118; linhas Lean 37.994 → 38.521; linhas de declaração **1.780 → 1.802** (+22 = 19 `theorem` + 1 `def` + 2 `noncomputable def`; não é número de teoremas); `#print axioms` 269 → 291.

## 4. Matemática (rederivação própria, §4 da fita)

1. **Substituição de coordenadas.** `moved owner k η := ∃ i, owner η = some i ∧ i.val < k`; `p_k η := if moved then a′ η else a η`. `p_0 = a` (nenhum `i < 0`); `p_k ∈ [0,1]` por seleção; `touchFactor R p_k η = if moved then b′ η else b η` por `split_ifs <;> rfl` (R fixo). Conferido à mão; Q3a/b, Q4a/a′ exibem os valores por estágio.
2. **Hipóteses locais no passo i.** Fora de `r i`: `moved_i ⇒ moved_{i+1}` (monotonia); `¬moved_i ∧ moved_{i+1} ⇒ owner η = some i` (`Fin.ext` + `omega`) ⇒ `η` toca `r i` por `howner_touch` — contradição; senão ambos `b`. Em `r i`: três casos — ambos movidos (diferença 0 ≤ δ i por `hδ0`), troca exatamente em i (`howner_bound`), nenhum (0). Um polímero que toca várias regiões muda só no passo do dono: Q3c com δ 1 = 1/10 < 1/2 = |Δ| em η₁ (toca r 0 e r 1, dono 0), obrigação do passo 1 paga por 0. `hδ0` entra só nos casos de diferença nula; `howner_touch` só em `step_same`; `howner_bound` só na troca.
3. **Extremo.** `moved_m ⟺ owner = some i` (`i.isLt`); `none ⇒ howner_none`. Igualdade dos fatores efetivos ⇒ `F_R(p_m) = F_R(a′)` por `profileExpectation_eq_of_touchFactor_eq` (56). Rederivado em Q4c; Q4b mostra `p_m η ≠ a′ η` com fatores iguais para η que evita R (igualdade bruta seria falsa).
4. **Composição.** Q5_two_steps: perfil intermediário PRÓPRIO, `hsame`/`hδ` próprios nos dois passos, dois usos da estimativa de dois termos da 56, igualdade do extremo, `abs_sub_le` — sem as capstones, sem `abs_profileExpectation_sub_le_of_owner`, sem `step_same`/`step_bound`/`stepProfile`; certidão exata. Telescopagem geral reprovada por indução (Q5_telescope), `Finset.sum_range` e a reorganização `Cf·(E₆+E₄)·Σ = Σ custos` conferidas.
5. **Dono por `hcover`.** `coverOwner η := if h : b η ≠ b′ η then some (Classical.choose (hcover η h)) else none`; as três obrigações por `of_not_not` e `Classical.choose_spec`, sem fortalecer a cobertura; as capstones públicas recebem `hcover` e nenhum `owner`; nenhuma otimalidade exigida.
6. **Constante final.** `0 ≤ Cf` derivado (l. 429, `nonneg_of_abs_le_of_config`), `B ≥ 0` (`budget_nonneg`), `e^{4D/113} ≤ e^{6D/113}` por `nlinarith` com `D ≥ 0` (D = 0 dá igualdade; Cf = 0 dá cota 0 — Q6b/c″); sinais corretos (`mul_le_mul_of_nonneg_right _ hB`, `…_left _ hCf0`); nenhum custo fora de `B`.

Ausências conferidas nos tipos elaborados (Q0 `#check`): sem `owner` nas finais, sem `m > 0`, disjunção, `r i ⊆ R`, separação s/R, fundo unitário, `δ i ≤ 1`, `DependsOnlyOn`, sinal; nada dividido; `m` só por `B`. Contexto completo: grupo, `MeasurableSpace`, `MeasurableMul₂`, `MeasurableInv`, medida σ-finita de probabilidade, `Measurable χ`, `Measurable f`, `|χ| ≤ 1`, `|f| ≤ Cf`; a interface `m = 0` omite as quatro instâncias de medida. Dependência intencional da estimativa de dois termos da 56 aceita conforme a fita; a especialização `m = 1` é teste de compatibilidade (Q1), não prova da 56.

## 5. Testes próprios (prefixo Q)

Q0–Q7 exit 0; Q8x exit 1 exatamente na obrigação `howner_none` (goal `False`) ao compor com `owner ≡ none` e fatores que mudam — falha de aplicação/obrigação, não teorema negativo. Cobertura: Q1 uma região (aplicação efetiva com LHS, derivação própria com m = 1 reduzindo `Fin 1` no RHS, tipos defeq nas duas direções com a capstone 56); Q2 família vazia e δ ≡ 0 (perfis brutos diferentes fora de R; capstone com B = 0); Q3 sobreposição e amplitudes distintas; Q4 fundo 1/2, valores ignorados, extremo por fatores efetivos, fator zero; Q5 fechamento próprio; Q6 δ = 7 com Cf geral, Cf = 0 separado, comparação escalar exata B₂ = 1/2 + e^{−2}/2 < 1 = B₁ e melhora estrita da cota completa só com Cf > 0 (sem geometria); Q7 família duplicada custa o dobro, dono não minimiza B. Geometria assumida por hipóteses (sem rede concreta). Deslizes meus (attempt logs preservados; candidato intocado): contraposição sem `not_not`, `s` implícito com m = 0, `Real.exp_lt_one` inexistente, `if` sob lambda não dividido por `split_ifs`. Matriz: `57_QA1_TEST_MATRIX.tsv`.

## 6. Documentação

Cabeçalho, docstrings e relatório do construtor coerentes com os tipos elaborados: hipóteses efetivas, cobertura por polímeros (não por links), sobreposição permitida, "lado direito" na interface de uma região, limites (sem ganho universal, sem novo expoente, volume finito). Relatório 57-L: contagens (§7), certidões 291 e 12 (T57L), 118/0, 114 = 114, replay das dependências (0 Built / 1.332 Replayed) corretamente descritos; E1–E5 refletidas no fonte e nos testes. §9 (revisão editorial das notas v56, `SHA256SUMS.8.txt`) é registro fechado; não reaberto. Nenhuma imprecisão documental encontrada.

## 7. Comparação com o material do construtor (segunda passagem)

- `clean_build.log` (SHA `9739bd60…` ✅): 118 Built / 0 Replayed; dependências 0 Built / 1.332 Replayed com 4.599 avisos reapresentados (replay, não compilação); 114 avisos de projeto com **blocos integrais idênticos** ao baseline e ao meu log; 291 certidões exatas, 74 multilinha; manifesto antes = depois; início 21:57:29Z, 1.051 s. `clean_build_attempt1_killed.log` (101 Built, interrompido) preservado como tentativa, não usado como evidência. `buildL.log` (`f0582773…` ✅): dirigido, 1 Built / 73 Replayed. `T57L_run2.log` (`93480ac2…` ✅): exit 0, 12 certidões (W1, W1′, W2a, W2b, W3, W4, W5a, W5b, W6, W6′, W7, W9 — nomes com apóstrofo lidos), 0 avisos. `W8x…log`: exit 1, goal `⊢ 1 = 1/2`.
- Testes W (do construtor; **não** são evidência de autoria da QA1): reexecutados na minha bancada — `T57L_api_tests.lean` exit 0, 12 certidões, 0 avisos; `W8x` exit 1, mesmo goal. Conferido no fonte: W1/W1′ exercitam o enunciado completo por `exact` (não só RHS); W3 assume apenas h₁₀, h₁₁, h₂₁ (nada sobre η₂ e r 0); W4 não deduz localização de `none`; W5b separa δ = 7 com Cf geral de Cf = 0 ⇒ 0; W6 escalar e W6′ estrita sob Cf > 0, E > 0; W7 sem ganho universal; W9 recompõe dois passos pela estimativa de dois termos da 56 com `step_same`/`step_bound`/`stepProfile_mem` e `abs_sub_le`, 0 ocorrências das capstones novas e de `…_sub_le_of_owner` (minha Q5 vai além: perfil intermediário e hipóteses de passo próprios); W8x é falha de obrigação, não teorema negativo.
- Matrizes do construtor: 22 itens, nomes completos e linhas coincidem com a minha matriz; certidões "directed build; clean rebuild" corretas (as 3 definições têm `#print axioms` no módulo); matriz de testes com apóstrofos preservados. Nenhuma divergência entre as minhas conclusões preliminares e o material do construtor.

## 8. Limitações

Não é auditoria cega (§0). Assinatura SSH não verificada independentemente. Dependências pelo cache comunitário do Mathlib (revisões conferidas), não recompiladas da fonte. Geometria dos testes assumida por hipóteses. Composição derivada da 56 (uso intencional). Certificação restrita ao escopo formal enunciado: estabilidade em volume finito, regime `0 ≤ β ≤ 1/40000`, para uma família finita de regiões; sem ganho universal, sem novo expoente, sem constante ótima, sem família infinita, limites termodinâmico/contínuo, nova medida de Gibbs ou mass gap.

## 9. Vereditos

| eixo | veredito |
|---|---|
| Custódia | **PASS** |
| Execução | **PASS** |
| Matemática | **PASS** |
| Documentação | **PASS** |
| **Global** | **PASS NO ESCOPO** (sem observações de mérito) |

Preservação confirmada: candidato `c936d461` e base `95091fdd` intactos; `origin/main` = `zenodo-v56` = base; tags `zenodo-v53…v56` e branches preservadas; nenhuma escrita remota; worktree limpa. A construção local da 57 não é integração na main nem publicação. Nenhuma publicação. Pedra 58 não iniciada. **HARD STOP.**

## 10. Pacote

`QA1_57_evidence.zip` com `SHA256SUMS_57-QA1.txt` (sem auto-inclusão): este relatório, as duas matrizes, `PRELIMINARY_CONCLUSIONS_first_pass.md`, `environment.txt`, `deps_cache_get.log` + instantes, `prebuild_artifacts.txt`, `build_full_clean.log` + `.result` + instantes, manifestos pré/pós, `compare_warning_blocks.py`, `warnings_block_comparison.txt`, `tests/` (fontes Q, logs finais e attempts), `builder_tests_rerun/`. Caminhos arquivados na raiz do ZIP (o diretório `out/` da bancada é a raiz). O SHA do ZIP vai na mensagem de entrega, não aqui.
