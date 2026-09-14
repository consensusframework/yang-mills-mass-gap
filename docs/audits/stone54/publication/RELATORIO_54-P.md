# RELATÓRIO — FITA 54-P (publicação do candidato auditado da Pedra 54)

Publicador: Claude Fable 5.1 (Claude Code, instância construtora/publicadora). Repositório: `consensusframework/yang-mills-mass-gap`. Data: 2026-09-14 (UTC). Sem tag, Release, Zenodo, edição documental ou Pedra 55.

## Etapa Zero (tudo conforme antes do push)
- Sem instruções locais no repositório; autenticação `consensusframework` (credenciais não expostas).
- Recebidos = fita: `QA1_54_evidence.zip` SHA-256 `6698ff0c…15ba`; manifesto interno `SHA256SUMS_54-QA1.txt` 29/29 OK, sem auto-inclusão; sem caminhos absolutos/travessia/links; `RELATORIO_54-QA1.md` avulso (`333b9ee9…`) byte-idêntico ao exemplar do ZIP; parecer: PASS com observação documental, nenhum defeito matemático; log limpo da QA: exit 0, 550 s, 114 Built / 0 Replayed.
- Candidato `410bde8146e8f14b698a03387da395a79f81f9eb`: parent único = base `571b83aa…`; root tree `eaffdb13…`; Phase3 tree `7d8373f6…`; blobs `e2ff9e0e…` (módulo, 523 linhas, 13 declarações) e `ffd0edff…` (lakefile, um glob); diff A + M, +524/−1; 113 módulos anteriores e arquivos protegidos byte-idênticos à base. ZIP do construtor `fa5c9b86…9601` e bundle `185b7834…4987` = fita.
- Remoto: `origin/main` = `571b83aa…` (base); nenhuma branch `stone54` nem PR prévios; ruleset 22341147 ativo (deletion, non_fast_forward, pull_request com merge only, `build-phase3` strict, sem bypass); `zenodo-v53` → `571b83aa…` e `zenodo-v52` intocadas.

## Publicação
| Passo | Resultado |
|---|---|
| Push | `stone54` → `410bde81…` (push normal, novo ref) |
| PR | #30 https://github.com/consensusframework/yang-mills-mass-gap/pull/30 — não-draft, base `main`@`571b83aa…`, head `410bde81…`, 1 commit, 2 arquivos, +524/−1; refinamento exp(8D_s/113) → exp(6D_s/113) com hipóteses, intervalo e taxa mantidos; D1/D2/I1 e proveniência aceita registradas no corpo |
| CI do PR | run 487, id 34875314038, job 104080933983: success (17:31:56Z → 17:42:14Z). Checkout efetivo `refs/pull/30/merge` = `9a9c9eb` ("Merge 410bde81… into 571b83aa…"), merge provisório distinto do candidato. Build completed successfully; 114 `LatticeGauge` Built (inclui `[5951/5952] ActivityDampingLipschitzRefined`), 0 Replayed; 0 erros; 114 warnings herdados, 0 no módulo novo; 13 certificados novos = `[propext, Classical.choice, Quot.sound]`; passo Kernel certificates OK, "no sorryAx" |
| Merge | `mergeable_state = clean`; merge normal com `expectedHeadSha = 410bde81…`; merge commit `9c0f6fdecee5c8628a2434d032e421edc78bb722`, parents `571b83aa…` + `410bde81…`; root tree `eaffdb13…` e Phase3 tree `7d8373f6…` = candidato (`git diff 410bde81 origin/main` vazio); sem squash/rebase/amend/cherry-pick/force-push/bypass |
| CI da main | run 488, id 34876420216, job 104084633795: success (17:42:58Z → 17:53:24Z); checkout efetivo `9c0f6fde…`; Build completed successfully; 114 Built, 0 Replayed; 0 erros; 114/0 warnings; 13 certificados padrão; no sorryAx |
| Preservação | `stone54` = `410bde81…`, `stone53` = `abad1667…`, `stone53-doc` = `6963227f…`, tags `zenodo-v52`/`zenodo-v53` intocadas; `origin/main` = `9c0f6fde…` |

## Registros para a consolidação documental
- **D1** (aceita, candidato intacto): docstring de `refined_constant_le_published_constant` diz "agree exactly when D_s = 0" e omite o caso Cf = 0; o teorema enuncia `≤` corretamente; igualdade das constantes completas também em Cf = 0; melhora estrita exige Cf > 0 e D_s > 0. Correção editorial na consolidação.
- **D2**: o teste estrito do construtor compara só as exponenciais; a QA1 cobre o prefator completo — coberturas distintas.
- **I1**: `import LatticeGauge.CovarianceDecay` evitável mas legítimo; não modificado.
- Proveniência do commit aceita conforme registrada (precedente da 53); identidade e assinatura não refeitas.

## Ocorrências
Nenhuma. Logs de job obtidos via API MCP (download direto bloqueado pela política de egresso) e analisados integralmente; análises em `ci/`.
