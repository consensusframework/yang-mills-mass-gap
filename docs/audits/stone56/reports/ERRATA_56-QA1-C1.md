# ERRATA 56-QA1-C1 — Precisões do registro da auditoria 56-QA1

**Emitente:** a mesma instância auditora que emitiu `RELATORIO_56-QA1.md` (Claude Fable 5.1, bancada Lean própria).
**Data:** 2026-09-24 (UTC). **Fita:** FITA 56-QA1-C1 (coordenação). **Modo:** leitura dos materiais já disponíveis e recontagem por scripts; **nenhum novo build Lean**; nenhuma edição no candidato, no relatório, nas matrizes, nos testes, nos logs ou no ZIP originais; sem commit, push, PR, merge, tag, Release, Zenodo ou Pedra 57.

## 1. Alvo e originais (referências históricas, preservadas byte a byte)

Base `445cc76b02550291e6524bb1bf631aac4cc86c61`; candidato `a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1`.

| Original | SHA-256 (reconferido nesta errata) |
| --- | --- |
| `QA1_56_evidence.zip` | `53399f1a3c4a3887cb6c88daeba209ed48739918c9b7b1a5822d8758c27f483d` |
| `RELATORIO_56-QA1.md` | `2481ab1eaab57481d73868cdc79a6dd6e5506bebddc5b5b9c1c43797ab6e2599` |
| `56_QA1_DECLARATION_MATRIX.tsv` | `5419a12027a78d4a5a45f669fd80f871bcad0e8447e76262031bf510bba3827e` |
| `56_QA1_TEST_MATRIX.tsv` | `3d9ad36ba31825b6e6d53b7b06e56208af9c9d1bd754412c89ec0482efaa94d9` |
| `STONE56L_evidence.zip` (construtor) | `7049021dddb54b19962d8986f6274c8d78fd0cdb6464545ede58d336014e38e6` |

O pacote QA1 tem 48 entradas = 46 arquivos (45 no manifesto + o próprio `SHA256SUMS_56-QA1.txt`, sem auto-inclusão) + 2 diretórios; 45/45 conferidos. Confirmado.

## 2. Contagem de linhas de declaração — corrige o relatório §3 (e §7, PRELIMINARY_CONCLUSIONS "Contagens")

**Passagem original:** "linhas de declaração 1.745 (`^(theorem|lemma|def|noncomputable def) `) ou 1.790 (incluindo instance/structure/abbrev/inductive/class) — a referência 1.780 do construtor (1.756 + 24) depende do padrão de grep".

**Valor confirmado pelo método publicado** (README da base, l. 45: linhas iniciadas por `theorem`, `lemma`, `def`, `abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` ou `class` seguidas de um espaço literal), aplicado aos objetos Git:

```bash
git grep -c -E '^(theorem|lemma|def|abbrev|structure|noncomputable def|instance|inductive|class) ' <commit> -- 'Phase3/LatticeGauge/*.lean' | awk -F: '{n += $NF} END {print n}'
```

| Medida | Base `445cc76b` | Candidato `a2fcf8e9` |
| --- | ---: | ---: |
| Módulos Lean | 116 | 117 |
| Linhas de declaração (método publicado) | **1.756** | **1.780** |
| Padrão reduzido de quatro tipos | 1.721 | 1.745 |
| Comandos `#print axioms` | 247 | 269 |

**Origem do 1.790 do relatório** (conferida no meu próprio comando, registrado na sessão): o padrão que usei foi `^(theorem|lemma|def|noncomputable def|instance|structure|abbrev|noncomputable abbrev|noncomputable instance|inductive|class) ` sobre `cat LatticeGauge/*.lean` na worktree — **onze** alternativas, não nove; as duas extras (`noncomputable abbrev`, `noncomputable instance`) casam 10 linhas no candidato, e 1.780 + 10 = 1.790. Não é o método publicado.

**Registro retificado:** 1.780 é a contagem reproduzida pelo método documentado; incremento de 24 linhas = 22 `theorem` + 2 `noncomputable def` do módulo novo. Métrica textual; não é inventário das declarações elaboradas nem contagem global de teoremas. A frase "não material" do relatório permanece correta quanto ao mérito, mas a caracterização "depende do padrão de grep" fica substituída por: o método publicado é único e reproduz 1.780; o meu 1.790 veio de um padrão mais largo do que o publicado.

## 3. Cache das dependências no rebuild do construtor — corrige o relatório §7

**Passagem original:** "o log do construtor contém adicionalmente 4.599 warnings de Mathlib por ter compilado as dependências da fonte".

**Conferido em `STONE56L_evidence.zip` → `logs/clean_build.log`** (SHA-256 `3e08223c89893e3eb5955dafe0ffcda85258fc33f6817e54817288812c4b57a0`, reconferido): projeto 117 `Built` / 0 `Replayed`; **dependências 0 `Built` / 1.332 `Replayed`**; avisos 114 do projeto e 4.599 das dependências **reapresentados** (replayed) no log.

**Registro retificado:** naquele rebuild as dependências foram **reaproveitadas do cache** (replay), não compiladas; os 4.599 avisos são a reapresentação de diagnósticos armazenados. A origem histórica desse cache (o `environment.txt` do construtor menciona compilação anterior da fonte na bancada dele) é afirmação do construtor sobre um evento anterior, sem evidência própria neste log, e não é atribuída a ele por esta auditoria. O meu log limpo (`build_full_clean.log`, 117 `Built` / 0 `Replayed`, nenhum diagnóstico de dependências emitido) continua descrito corretamente; a ausência de diagnósticos de dependências no meu log **não** afirma ausência de avisos numa recompilação das dependências.

## 4. Avisos nos testes descartáveis da QA1 — corrige o relatório §5 (e PRELIMINARY_CONCLUSIONS "Testes")

**Passagem original:** "W0–W7: exit 0 (36 itens positivos; W1 com 1 warning de variável não usada num teste meu)".

**Recontagem (só os logs finais dos testes W; excluídos `attempt1/2`, os V reexecutados e os logs de build):**

| Log | Avisos |
| --- | ---: |
| `tests/w1_background_cancellation.log` | 2 |
| `tests/w3_two_regions.log` | 6 |
| `tests/w4_empty_region_translation.log` | 26 |
| `tests/w7_localization.log` | 4 |
| demais logs finais W (w0, w2, w5, w6, w7x) | 0 |
| **Total** | **38** |

Natureza: variáveis não usadas (26 em W4, todas nos dois `example` de comparação de assinaturas, cujos binders do tipo não são usados no termo; mais `r`, `R` em W1), `'beta_reduce' tactic does nothing` (8, em W3/W7) e `tac1 <;> tac2` onde `(tac1; tac2)` bastaria (2). Todos em arquivos descartáveis meus, fora da árvore; os testes positivos terminam `exit=0`; W7x termina com a falha esperada. Os testes **não** foram editados para remover avisos: a evidência executada fica preservada.

**Registro retificado:** três contagens distintas e separadas — **38** avisos nos testes descartáveis da QA1; **114** avisos herdados no build do projeto (blocos idênticos ao baseline 55); **0** avisos no módulo científico novo.

## 5. Fontes dos certificados e referências das matrizes — corrige o relatório §§3 e 7 e a legenda da matriz

**Passagens originais:** §7 "certidões 24/24 iguais"; legenda da coluna 9 da matriz "certificate (#print axioms, own W0 + directed + clean)".

**Conferido (parser com listas multilinha, prefixo `info:` e apóstrofo no nome):** `build_full_clean.log` da QA1 — 269 saídas padrão = 247 anteriores + 22 teoremas novos; **nenhuma saída para as duas definições**; `tests/w0_print_axioms.log` — 24 saídas padrão = 22 teoremas + 2 definições (`kpLocalizedDiffCoeff`, `localizedConnectorDiff`); build limpo do construtor — 269 saídas padrão; matriz do construtor, itens 7 e 12 — `— (definition)`.

**Registro retificado:** na comparação com o construtor há (i) correspondência das 24 declarações (nomes e linhas), (ii) igualdade dos **22** certificados de teoremas (build limpo de ambas as bancadas e W0), e (iii) **2 verificações adicionais da QA1**, exclusivas de W0, para as definições — que o construtor, corretamente, não lista como certificadas. A coluna 9 da matriz deve ser lida assim: para os itens 7 e 12 a fonte é **somente W0**; para os 22 teoremas, W0 + build dirigido + build limpo.

**Referências numéricas internas da matriz (coluna 10 "auditor tests" e coluna 7), corrigidas pelos nomes completos:**

| Item | Original | Correto |
| --- | --- | --- |
| 5 `abs_tupleProfileWeight_sub_le_k_localized` | `via (9)` | usada em `abs_kpLocalizedDiffCoeff_le` (item 10) |
| 6 `abs_profileWeight_sub_le_card_localized` | `via (17)` | usada em `abs_sum_localizedBridgeColumn_le` (item 19) |
| 10 `abs_kpLocalizedDiffCoeff_le` | `via (12)` | dominação usada em `abs_localizedConnectorDiff_le_eroded` (item 14) |
| 17 `abs_sum_localizedConnectorColumn_le` | `0 ≤ Cf as hypothesis (derived in (18))` | `hCf0` é hipótese nos itens 17, 18 e 19; a derivação `nonneg_of_abs_le_of_config hCf` ocorre em `abs_profileExpectation_sub_profileExpectation_le_two_terms_localized` (item 20, l. 818) e em `…_le_local_exp_decay_localized` (item 21, l. 854) |

As demais referências numéricas da matriz (coluna 8 "dependencies", p.ex. "(3), touchCount_le_card"; "(15), (14)"; "(16), (17), (19)"; "(20)"; "(21) with R := r, (11)") foram reconferidas contra as provas e estão corretas.

**Precisão de caminho:** no ZIP QA1 o log limpo está na **raiz** como `build_full_clean.log` (SHA-256 `38ca3d817f3f9a0d6f2c54cea6fe8fa6a3b8a6eba2af5874f529cac8d3e1a611`, reconferido), porque o ZIP foi gerado a partir do diretório `out/` da bancada; o prefixo `out/` no relatório §3 descreve a bancada original, não o caminho arquivado. O mesmo vale para as demais entradas (`tests/`, `builder_tests_rerun/` estão na raiz do ZIP).

## 6. Prevalência

Nos pontos dos §§2–5 acima, **esta errata C1 prevalece** sobre `RELATORIO_56-QA1.md`, `56_QA1_DECLARATION_MATRIX.tsv`, `56_QA1_TEST_MATRIX.tsv` e `PRELIMINARY_CONCLUSIONS_first_pass.md` quando lidos em conjunto; os originais permanecem inalterados como referência histórica e não foram regenerados.

## 7. Impacto avaliado por eixo

| Eixo | Conferência | Impacto |
| --- | --- | --- |
| Custódia | Hashes dos cinco originais e dos dois logs citados reconferidos; candidato `a2fcf8e9`, base `445cc76b`, `origin/main` = `zenodo-v55`, worktree limpa; nenhuma escrita | **Nenhum.** Veredito PASS mantido |
| Execução | Meu build limpo: 117/0, 0 erros, 269/269 certificados exatos, 114 blocos de avisos idênticos ao baseline, 0 no módulo novo — inalterado. Correções: descrição do replay das dependências no log do construtor; 38 avisos nos meus testes descartáveis (não no candidato); fonte dos 2 certificados das definições (W0) | **Nenhum sobre o candidato.** Veredito PASS mantido |
| Matemática | Nenhum ponto da fita C1 toca código, hipóteses, enunciados ou provas; as 22 provas e as duas definições permanecem as auditadas e certificadas; as referências corrigidas da matriz apontam para usos que já estavam conferidos nas provas | **Nenhum.** Veredito PASS mantido |
| Documentação | Correções são **do relato da QA1** (contagem 1.780 pelo método publicado; replay vs compilação; 38 avisos de testes; legenda/fontes de certificados; quatro referências numéricas; caminho no ZIP). Nenhuma imprecisão no candidato científico ou nos seus docstrings foi identificada | **Nenhum sobre o candidato.** Veredito PASS mantido |

**Veredito científico:** permanece **PASS NO ESCOPO** — porque nenhuma das correções altera o objeto auditado (os objetos Git do candidato são os mesmos, com os mesmos hashes), nenhuma altera os resultados de compilação, certificação ou comparação de avisos do projeto, e nenhuma altera as rederivações matemáticas; todas são precisões do próprio registro da auditoria, resolvidas com as evidências já existentes e sem novo build. A conferência não revelou divergência nova de código, hipóteses, execução ou custódia; portanto não há retorno à coordenação por esse motivo.

## 8. Confirmação de integridade

Nenhum original (relatório, matrizes, testes, logs, `PRELIMINARY_CONCLUSIONS_first_pass.md`, `QA1_56_evidence.zip`) e nenhum código científico foi alterado: hashes da §1 reconferidos após a produção desta errata; `git status` da worktree do candidato limpo; `a2fcf8e9` e `445cc76b` intactos; push desabilitado. Esta errata é um arquivo adicional, fora da árvore, e não integra nem regenera o pacote original. Bytes e SHA-256 desta errata vão na mensagem de entrega, não aqui.

Sem publicação. Pedra 57 não iniciada. **HARD STOP.**
