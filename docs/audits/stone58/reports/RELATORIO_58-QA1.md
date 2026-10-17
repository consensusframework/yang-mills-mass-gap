# RELATÓRIO 58-QA1 — Auditoria independente da Pedra 58 (cobertura aditiva das mudanças efetivas por várias regiões)

**Auditor:** Claude Fable 5.1 (sessão Cowork; modelo configurado `claude-fable-5-1`, identidade informada pela configuração da sessão, não inferida), instância QA1 distinta da construtora.
**Data:** 2026-10-15 (UTC). **Fita:** FITA 58-QA1 (Can/Astra, coordenação Ju). **Modo:** somente leitura sobre o candidato; zero edições, zero commit de correção/push/PR/merge/CI remoto/tag/Release/Zenodo; Pedra 59 não iniciada. Ref temporária local `refs/bundles/qa58` apenas para a reconstrução.

## 0. Exposição e ordem de trabalho

Auditei as fitas 52-A0…57 deste programa (com a errata 56-C1); a arquitetura (Can/Astra) está na fita; li `RELATORIO_58-AL.md` (SHA `b55079dc…`, conforme a fita) e a fita antes da execução, para identificar alvo, escopo e custódia. **A revisão não é cega.** Ordem seguida: custódia → reconstrução → leitura integral das 660 linhas e das interfaces consumidas (56/57/52-E) → testes próprios Q0–Q8x → `PRELIMINARY_CONCLUSIONS_first_pass.md` (no pacote) → abertura de testes, logs, matrizes e scripts do construtor → comparação e reexecução. Desvio registrado: nenhum (do ZIP, antes da segunda passagem, só foram usados bundle, manifesto, fonte, diff e a listagem de caminhos/hashes). Oleans do construtor não usados. A fita chegou duas vezes na conversa (conteúdo idêntico); uma única execução.

## 1. Alvo e custódia

| item | observado | fita |
|---|---|---|
| remoto (fetch 2026-10-15) | `origin/main` = tag `zenodo-v57` = base `18c6ff08…`; 0 refs remotas `stone58*`; tags `zenodo-v53…v57` | ✅ |
| base | root `0f48b8e6…`, Phase3 `cc1bfb26…`, parents `c09fa063…`/`4239e749…` | ✅ |
| candidato | `d942edd3986ac8cb13a8d5958bf1e11461434794`, parent único = base; root `674507a4…`; Phase3 `58a60e8b…`; reconstruído pelo bundle (`git bundle verify` OK) | ✅ |
| blobs | módulo `9d0274fd…` (`Phase3/LatticeGauge/ActivityProfileDampingAdditiveCover.lean`, 660 linhas, 36.253 B, SHA `fcef59de…`, 100644); lakefile `9ad914d0…` ← `11de6e17…` (100644) | ✅ |
| diff | 2 arquivos: A +660, M +1/−1 (só o glob novo), total +661/−1; `git diff --check` limpo; conteúdo = `git/diff_vs_base.patch` (ids abreviados não alteram o conteúdo); 118 módulos e todos os demais caminhos idênticos à base; manifesto `c376bbe9…` | ✅ |
| ZIP | `7af10568…6a83` (660.006 B); 38 entradas = 33 arquivos + 5 diretórios; sem links, duplicatas, caminhos inseguros; CRC OK; `SHA256SUMS_58L.txt` 32/32 sem auto-inclusão; avulsos internos (bundle `cc2acd27…` 10.278 B, módulo, diff `364a43cb…` 45.791 B, testes `d4c63909…` 17.815 B) = fita | ✅ |

Proveniência: autor/committer `Claude <noreply@anthropic.com>`, cabeçalho `gpgsig` SSH presente (fato de custódia; não verificado nesta bancada), trailers `Co-Authored-By: Claude Fable 5.1` / `Claude-Session` — precedente 53–57.

## 2. Bancada e reprodução

Bancada da 57-QA1 (container sobreviveu): elan 4.2.4, toolchain `leanprover/lean4:v4.15.0` (Lean 4.15.0, 11651562caae; Lake 5.0.0-1165156); clone próprio com push desabilitado; worktree destacada no candidato. Dependências: o cache `.lake/packages` materializado na 57-QA1 pelo cache comunitário do Mathlib, movido para esta worktree; **9/9 revisões do checkout = manifesto** conferidas antes do build; sem `lake update`; manifesto `c376bbe9…` idêntico antes e depois; nada recompilado. Artefatos do projeto removidos antes (`prebuild_artifacts.txt`: NONE).

- **Build integral único** (`lake build`, `setsid nohup`): 16:36:52Z → 17:04:30Z, exit 0 (1.658 s); **119 `LatticeGauge` Built, 119 nomes únicos, 0 Replayed**; dependências 0 Built / 0 Replayed (cache; nenhum diagnóstico emitido — o que não afirma ausência de avisos numa recompilação); 0 erros; 0 sorryAx; 119 `.olean`, 0 anteriores ao início; `git diff --exit-code` limpo. Log `build_full_clean.log` (SHA `71a6faa0…`). Nenhuma tentativa interrompida.
- **Certidões** (listas recompostas até o colchete final; `info:`, multilinha e apóstrofo tratados): **317 = 291 + 26, 317/317 exatamente `[propext, Classical.choice, Quot.sound]`, 86 multilinha, 317 nomes únicos**; 26 do módulo novo (22 teoremas + 4 definições com comando). **QA1 adicional (Q0): 32/32** — as 26 acima mais os 6 auxiliares sem comando (`regionCost_nonneg`, `regionCost_of_not_touch`, `regionCost_of_touch`, `prefixCost_zero`, `prefixCost_nonneg`, `touchFactor_additiveProfile`), todos com a lista padrão; reportados em separado e não atribuídos ao build do construtor.
- **Warnings**: baseline na base exata — pasta `docs/audits/stone57/` (manifesto externo `SHA256SUMS.txt` 12/12 OK) → `packages/QA1_57_evidence.zip` (SHA `e495b476…` ✅; interno 45/45 sem auto-inclusão) → `build_full_clean.log` (SHA `5bd23aab…` ✅, meu log da 57-QA1). Blocos integrais multilinha como multiconjuntos, normalização só do prefixo `./` dos dois lados: **114 = 114, iguais**, 113 pares arquivo:linha; **0 no módulo `ActivityProfileDampingAdditiveCover`** (contagem própria com o nome correto do módulo — D3); dependências 0 = 0.

| avisos | projeto (herdados) | módulo 58 | dependências | testes QA1 |
|---|---:|---:|---:|---:|
| meu build / meus testes | 114 (= baseline) | 0 | 0 emitidos | 61 |

- **Higiene** (código, fora de docstrings): 0 sorry/admit/axiom/native_decide/unsafe/opaque/set_option/maxHeartbeats/partial/decide/@[simp]/Disjoint/DependsOnlyOn/owner; "admitted" só na docstring (l. 441, inglês); nenhuma divisão por orçamento, capacidade ou diferença. Imports: `Mathlib`, `LatticeGauge.ActivityProfileDampingMultiRegion`.
- **Contagens** (método publicado, nove alternativas com espaço, objetos Git): módulos 118 → 119; linhas 38.521 → 39.181; linhas de declaração **1.802 → 1.834** (+32 = 28 `theorem` + 4 `noncomputable def`; não é número de teoremas); `#print axioms` 291 → 317.

## 3. Enunciado e dependências reais

Tipos elaborados (Q0 `#check`): contexto `{N} [NeZero N] [Fintype (Site N)]`, `G` grupo com `MeasurableSpace`, `MeasurableMul₂`, `MeasurableInv`, `μm` σ-finita de probabilidade, `0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ g| ≤ 1`, `Measurable f`, `|f U| ≤ Cf`, perfis em [0,1], `Fin m` com `hδ0`, `hsep`, e `hadd` exatamente como na fita; conclusões `Cf·(e^{6D/113}+e^{4D/113})·B` e `(2Cf)·e^{6D/113}·B`. Ausentes: `m > 0`, disjunção, `r i ⊆ R`, separação s/R, fundo unitário, `δ i ≤ 1`, sinal, `DependsOnlyOn`, owner/decomposição do usuário; `0 ≤ Cf` derivado (l. 495); nenhum fator de `m`/volume fora de `B`; nenhuma divisão. As duas interfaces `m = 0`/`δ ≡ 0` omitem as quatro instâncias de medida e aceitam perfis reais arbitrários.

Dependências reais (código): 56 — `abs_profileExpectation_sub_profileExpectation_le_two_terms_localized` (1 uso, na cadeia), `profileExpectation_eq_of_touchFactor_eq` (3); 57 — `ActivityProfileMultiRegion.abs_telescope` (1), `budget_nonneg` (1); 52-E — `nonneg_of_abs_le_of_config` (1). **A capstone da 57 e a sua forma de dois termos têm 0 usos em código** (uma menção em docstring, como recuperadas); `coverOwner`/`stepProfile` não usados: não há conversão do caso aditivo em dono único (Q7). Importar a 57 ≠ usar a sua capstone.

## 4. Matemática (rederivação própria)

1. **Movimento truncado** (Q1): início, permanência para `t ≥ 0`, saturação sob `|x−y| ≤ t`, incremento `≤ u` para `u ≥ 0` e **`t` real arbitrário** (prova própria: `min y ·`/`max y ·` monótonos e 1-Lipschitz via `min_add_add_right`/`max_add_add_right`; instância com `t = −1`); instâncias numéricas nos dois sentidos, negativos, igualdade, capacidades 0/insuficiente/exata/excedente; monotonia do caminho escalar provada à parte, sem nada sobre `F_R`.
2. **Prefixos** (Q3): `C_0 = 0`, `C_(i+1) = C_i + c_i` (rota própria por tricotomia e `Finset.sum_ite_eq'`), `C_m = Σ c_i`; passo exatamente nulo fora de `r i` mesmo tocando outras regiões; regiões repetidas acumulam (`C_2 = δ₀+δ₁`); fundo 1/2 preservado por `move_self` — distinto de "nenhum fator muda" (Σ = 0 ⇒ fatores iguais).
3. **Perfis intermediários e extremos** (Q4): `p_0 = a` (própria), limites, `hsame`/`hδ` por passo, extremo por saturação sob `hadd` (rederivado) — igualdade de fatores efetivos, não bruta (η fora de R com 3/10 ≠ 9/10); R = ∅, m = 0 (reais fora de [0,1]), budgets nulos, perfis efetivamente iguais.
4. **Fechamento próprio** (Q5): rederivados a telescopagem (indução), a montagem da cadeia (estimativa de dois termos da 56 em cada passo + igualdade do extremo pela 56), a reorganização/fatoração de `B`, `0 ≤ Cf` (do majorante em `fun _ => 1`) e a redução à forma compacta — sem as duas capstones e sem `…_le_of_chain`; reusados intencionalmente `additiveProfile`, `additiveProfile_zero/mem`, `step_same`, `step_bound`, `touchFactor_additiveProfile_last`. Certidões próprias exatas.
5. **Recuperações** (Q6): `hcover ⇒ hadd` próprio (diferença zero incluída); 57 (duas formas) e 56 (`m = 1`, `Fin 1` reduzido no **lado direito**) rederivadas; tipos definicionalmente iguais nas duas direções com os teoremas publicados; budgets zero por aplicação efetiva (`≤ 0`). Classificação: `rfl` entre a capstone recuperada e a publicada = igualdade de dois **termos de prova** da mesma proposição por irrelevância de provas (definicional; nada diz sobre os corpos); `3D(2/113) = 6D/113` = reescrita algébrica (`ring`).
6. **Compartilhamento e alcance** (Q2): estágios 1/4 → 1/2 → 3/4 e inverso com budgets 1/4, 1/4; **testemunho global**: `a ≡ 1/4`, `a′ = 3/4` em η₀ (toca R, r 0, r 1 por hipótese) e 1/4 nos demais: `hadd` vale para **todo** η, nenhum índice paga 1/2 sozinho (cobertura 57 falsa no testemunho), capstone aplicada aos perfis. Geometria assumida; nenhum ganho numérico universal inferido (B é o mesmo; E2).
7. **Q8x**: obrigação `1/2 ≤ 1/4 + 0` provada **falsa** e aplicação da capstone com `![1/4, 0]` falhando exatamente nessa obrigação (goal `False`, exit 1, único erro) — hipótese impossível, não insuficiência de tática; não é falsidade da conclusão sobre `F_R`.

Leitura das docstrings: E1–E6 coerentes com os tipos e com a rota; "`s` é chamado suporte de `f` só onde a hipótese existe" (E4) e "sem monotonicidade de `F_R`" (E6) conferidos.

## 5. Testes próprios (Q)

Q0–Q6 exit 0; Q8x exit 1 na obrigação `hadd`; Q7 por grep/leitura (sem arquivo Lean). 61 avisos nos meus testes (Q6 54 — binders não usados nos `example` de comparação de tipos; Q2 3; Q1 2; Q3 2), separados dos 114 herdados e dos 0 do módulo. Deslizes meus (attempts preservados; candidato intocado): bullets `·` após `split_ifs;` numa linha, variáveis de seção não incluídas em `theorem`, `simp [h]` alterando o goal antes de `exact`, nomes `this` sombreados. Matriz: `58_QA1_TEST_MATRIX.tsv`.

## 6. Segunda passagem — material do construtor

- Logs: `L/build_full_clean.log` (SHA `67c3e429…` ✅): 119 Built únicos / 0 Replayed; dependências 0 Built / **1.332 Replayed** (reaproveitamento; os 4.599 avisos são reapresentação dos da compilação prévia das dependências pela fonte em `env/deps_build.log`, 5.826 Built — preparação separada, não o rebuild); 114 blocos de projeto idênticos ao baseline e ao meu log; 317 certidões exatas, 86 multilinha, 26 do módulo; manifesto pré registrado. `env/build_base.log` (115 Built, interrompido) + `env/build_base_resume.log` (3 Built) = aquecimento da base, separado do rebuild do candidato, que é único e completo. `L/build_module.log`: dirigido (1 Built / 74 Replayed).
- Testes **T1–T8x (do construtor)**: `T58L_api_tests.lean` reexecutado na minha bancada — exit 0, 0 erros, 0 avisos; contém 15 `#check` e **0** certidões (conforme a fita); `T58L_T8x` e `A/T58A_T8x` reexecutados — exit 1, goal `⊢ False`. Reexecutar não os torna testes da QA1.
- Pontos da fita §7, conferidos (observações sobre o **relato** do construtor; nenhum afeta o candidato):
  - **D1**: o `rfl` de T6 enuncia igualdade entre duas constantes de teorema; é igualdade de termos de prova da mesma proposição por irrelevância de provas (o comentário no fonte do teste já diz isso corretamente); a frase do relatório "igualdade de proposições, não de termos de prova" está invertida, e a matriz "not same proof term" precisa da qualificação "sintaticamente" — a igualdade formal enunciada vale. Confirmado por Q6f.
  - **D2**: "3 definições" no §2 do relatório contra quatro listadas; o correto é 4 (26 = 22 + 4). Não altera o fonte.
  - **D3**: `L/compare_warning_blocks.py` e `L/warnings_block_comparison.txt` imprimem o rótulo "…MultiRegion" (módulo 57); a comparação dos 114 blocos é correta; a contagem zero no módulo 58 foi refeita por mim com o nome correto.
  - **Alcance de T2**: prova a obrigação aditiva em η₀, a impossibilidade do índice individual e os três estágios; não prova `∀ η, hadd η` para os perfis do seu enunciado. Registrado; o testemunho global está em Q2b1. Não é defeito das capstones.
- Matrizes do construtor: 32 declarações com nomes/linhas iguais à minha matriz; `L/certs_module.tsv` lista 19 auxiliares (os 7 públicos estão no TSV completo, 317 linhas).

## 7. Limitações

Revisão não cega (§0). Assinatura SSH não verificada independentemente. Dependências do cache comunitário (revisões conferidas), não recompiladas. Geometria dos testes assumida por hipóteses. Composição derivada da 56 (uso intencional). Certificação restrita ao escopo formal: estabilidade em volume finito, regime `0 ≤ β ≤ 1/40000`, família finita de regiões sob cobertura aditiva; o ganho é na hipótese de cobertura (mesma constante, taxa e regime da 57); sem soma/ordem ótima, melhora universal, prioridade bibliográfica, limite termodinâmico/contínuo, nova medida de Gibbs ou mass gap.

## 8. Vereditos

| eixo | veredito |
|---|---|
| Custódia | **PASS** |
| Execução | **PASS** |
| Matemática | **PASS** |
| Documentação | **PASS** — módulo e docstrings sem imprecisão; observações D1–D3 e alcance de T2 referem-se ao relato/testes do construtor, não ao candidato |
| **Global** | **PASS NO ESCOPO** |

Reconfirmado ao terminar: candidato `d942edd3…` e base `18c6ff08…` intactos; `origin/main` = `zenodo-v57` = base; 0 refs remotas `stone58*`; caminhos protegidos (118 módulos, manifesto, toolchain, workflows, docs, licenças) idênticos à base; manifesto `c376bbe9…` pré = pós; worktree limpa; push desabilitado; nenhuma escrita remota. Nenhum commit de correção, PR, merge, CI remoto, tag, Release ou Zenodo. Pedra 59 não iniciada. **HARD STOP.**

## 9. Pacote

`QA1_58_evidence.zip` com `SHA256SUMS_58-QA1.txt` (sem auto-inclusão): este relatório (cópia idêntica à avulsa), as duas matrizes, `PRELIMINARY_CONCLUSIONS_first_pass.md`, `environment.txt`, `prebuild_artifacts.txt`, `build_full_clean.log` + `.result` + instantes, manifestos pré/pós, `compare_warning_blocks.py` (rótulo 58), `warnings_block_comparison.txt`, `tests/` (fontes Q, logs finais e attempts, falha esperada), `builder_tests_rerun/`. Caminhos arquivados na raiz do ZIP. O SHA do ZIP vai na mensagem de entrega, não aqui.
