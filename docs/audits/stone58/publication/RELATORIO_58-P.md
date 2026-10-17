# RELATÓRIO 58-P — Integração científica do candidato auditado da Pedra 58

Executor: Claude Fable 5.1 (Claude Code, sessão remota; identidade conforme a configuração da sessão). Fita: FITA 58-P (coordenação Ju; revisão Can / GPT Astra, 15/10/2026). Repositório: `consensusframework/yang-mills-mass-gap`. Relatório externo à árvore; bytes e SHA-256 na mensagem de entrega. Hashes calculados nesta sessão.

## 0. Resultado

- **Integração concluída.** `stone58` publicada no SHA auditado `d942edd3986ac8cb13a8d5958bf1e11461434794`; PR **#42** (não-draft) aberta, CI verde no run 511, merge normal com `expectedHeadSha` travado → **`69706b9a13a23b0f132418f2390d4030e1fcc78b`** em `main`; CI da `main` verde no run 512 com log inspecionado por script. `origin/main` = `69706b9a…`.
- Nenhuma tag, Release, DOI, pacote de depósito, escrita no Zenodo, consolidação documental, alteração de materiais de auditoria ou Pedra 59. **HARD STOP.**

## 1. Custódia dos materiais recebidos

| Arquivo | Bytes | SHA-256 | Fita |
|---|---:|---|---|
| `QA1_58_evidence.zip` | 57.595 | `b23ce8ed4b8838fea877bfdb00d127892788c5ee657360280481e73916b067c9` | ✅ |
| `RELATORIO_58-QA1.md` | 15.441 | `de495f379fe1a38193ba2d4c01a9f1f489e6c79471eeb5ec6175a936e3a0f308` | ✅ |
| `58_QA1_DECLARATION_MATRIX.tsv` (interno) | 8.147 | `6f9202ac794c2667f6422752d66284d39bc3737b0becb8af313fdcc19cfc618d` | ✅ |
| `58_QA1_TEST_MATRIX.tsv` (interno) | 7.022 | `9f12217dacee69414eb5ab97e04e3d67aa215e9216a787a5039097f8f61f9475` | ✅ |
| `build_full_clean.log` (raiz do ZIP, baseline primário) | 105.147 | `71a6faa01a4b5a469a1f63778836ca11a9f294fb3fc80a5151129bb81a0a5d80` | ✅ |

ZIP: CRC sem erros; 39 entradas = 37 arquivos + 2 diretórios; sem duplicatas, symlinks ou caminhos inseguros; `SHA256SUMS_58-QA1.txt` 36/36 OK, sem auto-inclusão, cobertura exata (36 arquivos listados = 36 arquivos além do manifesto). Relatório interno byte-idêntico ao avulso. O parecer lido integralmente: **PASS NO ESCOPO** (custódia, execução, matemática, documentação) referido ao SHA `d942edd3986ac8cb13a8d5958bf1e11461434794`, parent único `18c6ff08…`. Os recebidos foram conservados fora da árvore rastreada. Materiais da construção já na bancada reconferidos pelos hashes da fita §1 (relatório `b55079dc…`, ZIP `7af10568…`, bundle `cc2acd27…`, fonte `fcef59de…`, diff `364a43cb…`): iguais.

## 2. Etapa Zero (antes de qualquer escrita remota)

| Item | Observado |
|---|---|
| Local | branch `stone58` em `d942edd3…`, árvore limpa; commit intacto (parent `18c6ff08…`; root tree `674507a44812160be7cc7bf319359f66f5dca4a2`; Phase3 tree `58a60e8be11d00cfa94f36a9adbc81b5dbe3e32b`; blobs módulo `9d0274fd…`, lakefile `9ad914d0…` ← `11de6e17…`, ambos 100644); autor/committer `Claude <noreply@anthropic.com>`, cabeçalho `gpgsig` SSH presente (fato de custódia; nenhuma autenticação independente da assinatura foi realizada) |
| Diff vs base | 2 arquivos, +661/−1 (módulo +660/−0; lakefile +1/−1 só o glob); `git diff --check` limpo; 118 módulos e demais caminhos byte-idênticos; manifesto `c376bbe9…1227` no candidato; sem `lake update` |
| Remoto (fetch) | `origin/main` = tag simples `zenodo-v57` = `18c6ff08…`; 0 refs `stone58*`; 0 PRs abertas; tags `zenodo-v52…v57` presentes |
| Ruleset 22341147 | "Protect main — PR + Phase 3 CI", active, `~DEFAULT_BRANCH`; regras `deletion`, `non_fast_forward`, `pull_request` (threads resolvidos; só merge normal), `required_status_checks` estrito com `build-phase3`; `bypass_actors = []`, `current_user_can_bypass = never`. Reconfirmado idêntico no pré-merge |

Nada foi descartado, sobreposto, rebaseado ou reaplicado.

## 3. Publicação e PR

- `git push -u origin stone58` (sem force): `[new branch] stone58 -> stone58`; remoto em `d942edd3…`.
- PR **#42** (id 4879859556), não-draft, `stone58` → `main`, 1 commit, 2 arquivos, +661/−1; título `Stone 58: finite-volume stability under additive multiregion cover`; URL https://github.com/consensusframework/yang-mills-mass-gap/pull/42. O corpo registra enunciado, hipótese aditiva, conclusões, rota, recuperações, alcance, a QA1 (PASS NO ESCOPO; hashes do §1; 119/0, 317 saídas, 32 verificações próprias, 114 avisos herdados, 0 no módulo; dependências reaproveitadas; 61 avisos dos testes da QA1 separados) e as precisões D1–D3, alcance de T2/Q2 e C58-Q6, atribuídas à coordenação/revisão e não como errata da QA1.

## 4. CI da PR — run 511

| Item | Valor |
|---|---|
| Run / job | run **511**, id **38807381633**, attempt 1, `pull_request`, head `d942edd3…`, success, 21:07:05Z → 21:16:59Z; job **116671625661** `build-phase3`, https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/38807381633/job/116671625661 |
| Checkout efetivo | **merge provisório `e8eb54d9b3ab397f6290ffa3f31d5000f963f9ab`** ("Merge d942edd3… into 18c6ff08…"; `git checkout --force refs/remotes/pull/42/merge`; `git log -1` = `e8eb54d9…`) — **não** o head auditado; relação: merge de teste do head sobre a base |
| Manifesto / revisões | `c376bbe9…1227` registrado; `lake-manifest.json: OK` após a resolução e após o build; 9/9 revisões iguais ao manifesto; sem `lake update` |
| Build | **119 `Built LatticeGauge` / 0 `Replayed LatticeGauge`**, 0 erros, `Build completed successfully`; fora de `LatticeGauge`: 9 `Built` = ferramenta de cache do Mathlib (`Cache.IO`, `Cache.Hashing`, `Cache.Requests`, `Cache.Main`, 4 objetos C, `cache`), 0 Replayed; demais artefatos do cache |
| Avisos | 114 blocos de projeto, **multiconjunto igual ao baseline QA1-58** (`build_full_clean.log` `71a6faa0…`), cabeçalhos iguais, 113 pares arquivo:linha; **0 no módulo `ActivityProfileDampingAdditiveCover`**; dependências 0 = 0; comparação pelo script da QA1 após remover só o timestamp do CI (`warnings_block_comparison_run511.txt`) |
| Certidões | **320 saídas = 317 do build + 3 do passo do workflow; 318 nomes distintos** (`abs_gibbsCovariance_le_local_exp_decay` e `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay` com multiplicidade 2; `logPartition_eq_tsum_unrooted` só no workflow); 26 do módulo novo; todas `[propext, Classical.choice, Quot.sound]`; 87 listas multilinha recompostas; nome com apóstrofo tratado; "no sorryAx"; 0 `sorryAx` fora do script |
| Hashes | `run511.raw` `7efe1b597f63e4ec701d5efa3451b53a6e0ae3f8971783b7e3585e757ead7742`; `run511.log` `a5b63b126bb9532a791cd02fc95e3992366df4951d8a15364455df7c49793307` (1.408 linhas) |

## 5. Pré-merge e merge

Reconfirmado após o run 511: `origin/main` = `18c6ff08…`; head da PR = `d942edd3…`; não-draft; `mergeable = true`, `mergeable_state = clean`; check `build-phase3` success no head (check-run 116671625661); 0 comentários/threads; ruleset inalterado; diff restrito aos dois caminhos.

Merge normal via API com `expectedHeadSha = d942edd3986ac8cb13a8d5958bf1e11461434794`, `merge_method = merge`: **`69706b9a13a23b0f132418f2390d4030e1fcc78b`**, merged_at 2026-10-15T21:18:10Z. Sem squash, rebase, amend, force, push direto ou bypass.

Após fetch:
1. Dois parents na ordem **`18c6ff08…` (base) + `d942edd3…` (candidato)** ✔
2. Root tree `674507a44812160be7cc7bf319359f66f5dca4a2` = do candidato ✔
3. Phase3 tree `58a60e8be11d00cfa94f36a9adbc81b5dbe3e32b` = do candidato ✔
4. Diff candidato→merge vazio; base→merge = 2 arquivos, +661/−1, só os esperados ✔
5. `.github`, licenças, `docs`, README, `lean-toolchain`, `lake-manifest.json`, `formalization.yaml`, `VERIFICATION_STATUS.md`, `RELEASE_NOTES_PEDRA51.md` idênticos à base; 209 arquivos ✔
6. `stone58` preservada (remota em `d942edd3…`, não apagada); branches anteriores e tags `zenodo-v52…v57` (12 tags `zenodo-*` locais, 15 refs de tag remotas) preservadas ✔

## 6. CI da main — run 512

| Item | Valor |
|---|---|
| Run / job | run **512**, id **38808823637**, attempt 1, `push`, head `69706b9a…`, success, 21:18:13Z → 21:26:43Z; job **116676549072** `build-phase3`, https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/38808823637/job/116676549072 |
| Checkout efetivo | `git fetch … +69706b9a…:refs/remotes/origin/main`; `git log -1` = **`69706b9a13a23b0f132418f2390d4030e1fcc78b`** (o próprio merge) |
| Manifesto / revisões | `c376bbe9…1227`; OK após resolução e após build; 9/9 |
| Build | 119 / 0; 0 erros; 9 alvos de cache Built; `Build completed successfully` |
| Avisos | 114 = baseline QA1-58 (multiconjunto igual), 0 no módulo novo, dependências 0 = 0 (`warnings_block_comparison_run512.txt`) |
| Certidões | 320 / 318 nomes, mesmas multiplicidades, todas padrão, 87 multilinha, sem sorryAx; **mapa de certidões idêntico ao do run 511** |
| Hashes | `run512.raw` `970b3a2708019cb6a20c41eb7495fb74addcf7c1d855c0e2af7faa3584cfcce6`; `run512.log` `e29f7679c03c84805b562e3fd94162976b233aca554669ead2fc29aab27da762` (1.384 linhas) |

Contagens (método textual publicado; conferidas no candidato = merge, mesma root tree): módulos 118 → **119**; linhas 38.521 → **39.181**; linhas de declaração 1.802 → **1.834** (não são teoremas); `#print axioms` nos fontes 291 → **317**. Acréscimo: **28 teoremas e 4 definições** num módulo de 660 linhas. As 320 saídas do CI não são 320 comandos nos fontes nem 320 declarações novas; as 32 certidões de Q0 e as 3 de Q5 (testes da QA1) não entram nessa conta. Nenhum rebuild local adicional foi feito nesta fita (não exigido; a reprodução independente é a QA1).

## 7. Precisões de relato (registro; originais intactos)

Atribuição: D1–D3 e o alcance de T2/Q2 vêm da QA1 (§6 do seu relatório) e foram aceitos pela coordenação; C58-Q6 é precisão da coordenação. Nenhuma é errata da QA1; nenhuma altera o candidato, os pacotes ou o veredito.

- **D1** (sobre o `RELATORIO_58-AL.md`, do executor): o `rfl` de T6 enuncia igualdade de dois termos de prova da mesma proposição por irrelevância de provas — não identidade sintática dos corpos. A frase "igualdade de proposições, não de termos de prova" no §2 daquele relatório está invertida; o comentário no fonte do teste já estava correto. Aceito.
- **D2** (idem): "3 definições" no §2 é lapso; são 4 (`move`, `regionCost`, `prefixCost`, `additiveProfile`); 26 = 22 + 4. Aceito.
- **D3** (idem): `L/compare_warning_blocks.py` e `L/warnings_block_comparison.txt` do pacote do executor imprimem o rótulo do módulo 57; a comparação dos 114 blocos é correta; o zero no módulo 58 foi contado separadamente (no relatório AL e, nesta fita, pelo analisador do CI com o nome correto). Aceito.
- **Alcance de T2/Q2**: T2 prova a obrigação aditiva na coordenada-testemunha, a impossibilidade do pagador único e os três estágios; não prova `∀ η, hadd η` para os perfis do seu enunciado — isso está em Q2 da QA1 (testemunho global + aplicação da capstone). Contatos e geometria são hipóteses; nenhuma rede concreta foi construída. Aceito.
- **C58-Q6** (coordenação): `tests/q6_recoveries.lean` da QA1 rederiva `hcover ⇒ hadd`, a recuperação compacta da 57 e a da 56, com comparações de tipos das formas compactas; não contém rederivação separada da recuperação de duas parcelas da 57 (que existe no módulo e está entre as 32 declarações verificadas em Q0; Q5 rederiva a estimativa aditiva de duas parcelas). A descrever com esses alcances na consolidação.

## 8. Ocorrências e limitações

- Nenhuma falha de CI, nenhuma reexecução, nenhum conflito.
- Distinção: leitura de evidência (parecer e pacote QA1, materiais do executor), execução local (apenas conferências Git e scripts sobre logs; nenhum Lean executado nesta fita) e execução no CI (runs 511 e 512, logs integrais capturados via API e analisados por script; nenhuma conclusão tirada do ícone).
- Comparação de avisos com baseline em formato `lake` puro exigiu remover o prefixo de timestamp das linhas do CI; nenhuma outra normalização além do `./` do script da QA1.
- Observadores de CI encerrados (loops de polling terminaram com os runs); nenhuma inscrição de PR ativa.

## 9. Estado final

`origin/main` = **`69706b9a13a23b0f132418f2390d4030e1fcc78b`** (merge, CI verde, log conferido); PR #42 fechada/merged; `origin/stone58` = `d942edd3…`; tag `zenodo-v57` = `18c6ff08…`; tags históricas intactas; árvore local limpa em `stone58`; nenhum token exposto ou solicitado.

**HARD STOP** — integração da Pedra 58 concluída com CI verde da `main` conferido. Nada de tag/Release/DOI/Zenodo/consolidação/Pedra 59 nesta fita.
