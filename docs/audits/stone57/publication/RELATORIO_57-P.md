# RELATÓRIO — FITA 57-P (integração científica da Pedra 57)

Publicador: Claude Fable 5.1 (Claude Code, instância construtora/publicadora). Repositório: `consensusframework/yang-mills-mass-gap`. Data: 2026-10-09 (UTC). Executado: verificações em leitura, push normal de `stone57` no SHA fixo, PR não-draft, análise integral dos logs da CI do PR e da `main`, merge normal com head travado. Não executado (não autorizado): novo commit, amend, rebase, squash, force-push, bypass, alteração de regras, tag `zenodo-v57`, Release, pacote, DOI, Zenodo, consolidação documental, Pedra 58. Nenhum rebuild local nesta fita. Nenhuma consulta ao Zenodo.

## 1. Materiais recebidos e verificação própria

| Arquivo | Bytes | SHA-256 (calculado aqui) | Fita |
|---|---:|---|---|
| `QA1_57_evidence.zip` | 60.267 | `e495b4760e9e174a1da37c5583c0cd12fc1f0c8431548826f073a209b0b790ea` | ✅ |
| `RELATORIO_57-QA1.md` | 15.238 | `59664df41f9e2b7cfa9058b99ea912c8c5ba27e4ecf733b6da71b729dbcb45ed` | ✅ |
| `57_QA1_DECLARATION_MATRIX.tsv` (no ZIP) | 6.284 | `8b3d08afadc43ea8aa3039ad3bdeee81f5b745188c2d574bf7468642a3915b66` | ✅ |
| `57_QA1_TEST_MATRIX.tsv` (no ZIP) | 7.906 | `caf32cfc5ab94544e6644d8e3c3998f1b0c7cbc123f20968f28a1b17d8ab88eb` | ✅ |
| `build_full_clean.log` (raiz do ZIP) | — | `5bd23aab5d2ab848c915557dfa6a6487b9beb4326e7edef73a053b9aca9a386f` | ✅ |

ZIP: 48 entradas = 46 arquivos + 2 diretórios (`tests/`, `builder_tests_rerun/`), caminhos seguros, CRC OK; `SHA256SUMS_57-QA1.txt` **45/45 OK**, sem auto-inclusão; relatório avulso byte-idêntico ao exemplar interno; `environment.txt` identifica o candidato exato `c936d461…` e a base `95091fdd…`. Log da QA1: 118 `Built LatticeGauge`, 0 `Replayed`, "Build completed successfully". Parecer lido: **PASS NO ESCOPO** (custódia, execução, matemática, documentação PASS), referido ao candidato exato; instância Fable 5.1 distinta da construtora, exposição prévia declarada, não cega. Originais preservados fora da árvore (não incorporados nesta etapa). Materiais da 57-L (relatório `f77e0ee2…`, ZIP `934a898d…`, bundle `2d02b78a…`, fonte `9a66665a…`, diff `5ed714dd…`) já entregues; não recalculados aqui além do fonte via blob.

## 2. Etapa Zero (antes de qualquer escrita remota)

- Árvore limpa; branch local `stone57` = `c936d4617f3e6f35ea1431c2fa9496b235940f5a`; parent único `95091fdd07398a7b42901829ad61e4e2c26d5aaa`; root tree `47e843190b38159fcc408340313bda77de0f46e7`; Phase3 tree `cc1bfb261610266372745473fb54ad86f1077fae`; blobs `818048c4b849658c3e3dbcbdeca6a2b45b5b0dc4` (módulo, 100644) e `11de6e17d9e7bf208d16ce322a757a39e1f97683` (lakefile, 100644; anterior `ae8438d45594a5fd9ee27c7a3fa3dc0c5f974bff`); diff exatamente 2 arquivos, +527/0 e +1/−1 (= +528/−1); `git diff --check` limpo; 0 linhas fora dos dois caminhos; `gpgsig` presente; identidade `Claude <noreply@anthropic.com>`; trailers presentes. Candidato não alterado.
- Remoto (fetch): `origin/main` = `95091fdd…` = `zenodo-v56`; nenhuma `stone57` remota; 0 PRs abertos; tags `zenodo-v52` `f4015c5c…`, `v53` `571b83aa…`, `v54` `9358faa2…`, `v55` `445cc76b…`, `v56` `95091fdd…`; `stone56` `a2fcf8e9…`, `stone56-doc` `c4915084…`.
- Ruleset 22341147 "Protect main — PR + Phase 3 CI": ativo em `~DEFAULT_BRANCH`; deletion, non_fast_forward, pull_request (0 aprovações, resolução de threads requerida, só `merge`), required_status_checks estrito `build-phase3`; sem bypass. Não alterado.
- Toolchain Lean 4.15.0, Lake 5.0.0-1165156; manifesto `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`; nove revisões da bancada = manifesto (Mathlib `9837ca9d…`).

## 3. Publicação

| Passo | Resultado |
|---|---|
| Push | `stone57` → `c936d461…` (push normal, novo ref); `origin/main` inalterada |
| PR | **#39** https://github.com/consensusframework/yang-mills-mass-gap/pull/39 — não-draft, base `main`@`95091fdd…`, head `c936d461…`, 1 commit, 2 arquivos, +528/−1; título `Stone 57: finite multi-region composition of localized profile stability`; corpo com enunciado, `hcover`, hipóteses, ausências, rota, interfaces, limites, contagens (118 / 38.521 / 1.802 / 291; +19 teoremas +3 definições), evidências do construtor e da QA1 com atribuição Q/W e os 34 avisos dos testes da QA1 separados, precisões **D1–D3** e distinção de Q4d (qualificações da coordenação, não errata da QA1), materiais não incorporados, revisão adversarial futura |
| CI do PR | run **505**, id 37955736915, attempt 1, job 113905659491: **success** (15:58:58Z → 16:08:55Z); todos os 11 passos success. Checkout efetivo `refs/remotes/pull/39/merge` = `3214768` ("Merge c936d461… into 95091fdd…"), merge provisório do GitHub, distinto do candidato e do merge definitivo. Log integral (155.341 caracteres, 1.379 linhas; `run505.raw` `f55df8d8…`, `run505.log` `308cd9bf…`) analisado por script (100%): manifesto `c376bbe9…1227` registrado e `OK` após a resolução e após o build; 9 dependências nas revisões do manifesto, sem `lake update`; "Build completed successfully"; **118 `LatticeGauge` Built / 0 Replayed** (dependências 9 Built / 0 Replayed no runner — cache do CI, não recompilação das dependências na bancada QA1); 0 erros; **114 avisos, todos de `LatticeGauge/`, 0 no módulo novo, 0 de dependências**; blocos integrais de avisos como multiconjunto **idênticos** ao `build_full_clean.log` da QA1 (114 = 114; 0 só no candidato, 0 só no baseline; normalização simétrica só de prefixos/timestamps; script `compare_warnings.py` calibrado também contra o run 504); **294 saídas de axiomas = 291 do build + 3 do workflow**, todas `[propext, Classical.choice, Quot.sound]`; 292 nomes únicos (duas das três saídas do workflow repetem nomes já certificados em arquivo); parser remonta listas multilinha até o colchete e aceita apóstrofo (`activityRestrictedMarkedGas_eq_sum_core_mul_restricted'`); **22 certidões do módulo novo** (19 teoremas + 3 definições); passo Kernel certificates OK; nenhum `sorryAx` |
| Pré-merge | `main` = `95091fdd…`, `stone57` = `c936d461…`, PR `mergeable = true`, `mergeable_state = clean`, único check `build-phase3` success no head; #39 único PR aberto; ruleset inalterado; tags intocadas; nenhuma tag `zenodo-v57` |
| Merge | merge normal, `expectedHeadSha = c936d4617f3e6f35ea1431c2fa9496b235940f5a`; commit **`b66c255c83bba02dc8d53158279296bbf7ea005c`** ("Merge pull request #39 from consensusframework/stone57", 2026-10-09T16:10:00Z), parents **na ordem** `95091fdd…` + `c936d461…`; root tree `47e84319…` = candidato; Phase3 tree `cc1bfb26…`; diff candidato → merge vazio; diff base → merge = exatamente os 2 caminhos (+527, +1/−1); sem squash/rebase/bypass/exclusão de branch |
| CI da main | run **506**, id 37957117948, attempt 1, job 113910337460: **success** (16:10:05Z → 16:21:41Z); checkout efetivo `refs/remotes/origin/main` = `b66c255c…` (lido no log); log integral (155.521 caracteres, 1.378 linhas; `run506.raw` `e9edef74…`, `run506.log` `50b56bf0…`) analisado por script (100%): manifesto OK após resolução e após build; 9 dependências; 118 Built / 0 Replayed (dependências 9/0); 0 erros; 114 avisos (todos `LatticeGauge/`, 0 no módulo, 0 de dependências), multiconjunto idêntico ao baseline da QA1; 294 saídas (291 + 3), todas padrão, 292 nomes únicos, 22 do módulo; multiconjunto de certidões idêntico ao do run 505; nenhum `sorryAx` |
| Preservação | `stone57` = `c936d461…` preservada; `stone56` `a2fcf8e9…`, `stone56-doc` `c4915084…` e demais branches intactas; tags `zenodo-v52…v56` intocadas (16 refs de tag, sem `zenodo-v57`); `origin/main` = `b66c255c…`; árvore local limpa, branch local `stone57` no candidato |

## 4. Registros da seção 5 da fita (a transportar para a consolidação)

- QA1: PASS NO ESCOPO; rebuild 118/0, 0 erros, 291 certidões padrão, 114 blocos idênticos ao baseline da 56, 0 no módulo; dependências do cache comunitário Mathlib (0 Built / 0 Replayed, 0 diagnósticos — não afirma ausência de avisos numa recompilação); manifestos pré-dependências/pré-build/pós-build iguais; Q0–Q7 passaram, Q8x falhou na obrigação `howner_none` (meta `False`); Q5 rederivou a composição com perfis próprios; 22 certidões do módulo em Q0 + 2 próprias em Q5, não somadas às 291; **34 avisos** dos testes descartáveis da QA1 (Q1 28, Q4 4, Q6 2), separados dos 114; W1–W9/W8x são do construtor e foram reexecutados pela QA1 (reexecução não transfere autoria); testes geométricos parametrizados por hipóteses.
- Precisões da coordenação (D1 Q3c genérico, sem instância numérica de diferença global 1/2; D2 `owner ≡ none` satisfaz `howner_none` sse todos os fatores efetivos concordam, sem obrigar `none`; D3 seleção por casos, não bicondicional; Q4d valor bruto zero sem geometria assumida): registradas no PR #39 e aqui; não são errata da QA1 nem novo veredito; sem mudança no módulo; originais preservados.

## 5. Fontes de verificação

Verificado aqui: hashes e integridade dos materiais; candidato, push, PR, merge; logs dos jobs 113905659491 e 113910337460 (API MCP), parseados integralmente por script e comparados ao baseline da QA1 e ao run 504; refs, tags, ruleset, PRs e runs pela API pública (leitura). Recebido (não reexecutado): rebuild e testes da QA1; rebuild e testes do construtor (57-L). Logs conservados em `scratchpad/stone57/ci/` (run505/506 raw e log) e nos pacotes `STONE57L_evidence.zip` / `QA1_57_evidence.zip`.

## 6. Ocorrências e limitações

- Os vigias em segundo plano da sessão expiram aos 600 s; os runs foram reconsultados pela API e nenhum foi reexecutado. Nenhuma falha de infraestrutura ou Lean.
- Assinatura SSH do commit: presente, não autenticada independentemente.
- Zenodo não consultado. Nada incorporado à árvore além do candidato auditado.

**Integração concluída e verificada**: Pedra 57 em `main` no merge `b66c255c83bba02dc8d53158279296bbf7ea005c`, CI da `main` verde e conferida. HARD STOP. Próximas etapas (fitas próprias): revisão adversarial adicional, consolidação documental, tag/Release/depósito.
