# RELATÓRIO 59-QA1 — Auditoria independente da Pedra 59 (orçamento ótimo para uma família fixa de regiões)

**Auditor:** Claude Fable 5.1 (sessão Cowork; modelo configurado `claude-fable-5-1`, identidade conforme a configuração da sessão), instância QA1 distinta da construtora.
**Data:** 2026-10-18 (UTC). **Fita:** FITA 59-QA1 (Can/Astra; coordenação Ju). **Modo:** somente leitura sobre o candidato; zero edições, zero commit de correção/push/PR/merge/tag/Release/Zenodo; Pedra 60 não iniciada; hooks de parada não ampliam a autorização. Ref temporária local `refs/bundles/qa59` apenas para a reconstrução.

## 0. Exposição e ordem

Auditei as fitas 52-A0…58 (com errata 56-C1). A fita e `RELATORIO_59-AL.md` (SHA `a62a05dc…`, 19.959 B, conforme a fita) chegaram na mesma mensagem; antes da execução li do relatório só o necessário a alvo, escopo e custódia. **A revisão não é cega.** Ordem: custódia → reconstrução pelo bundle → leitura integral das 646 linhas e das interfaces consumidas (58: duas estimativas; 56: igualdade por fatores efetivos; 52-E: `nonneg_of_abs_le_of_config`; 55: `touchFactor`/`profileExpectation`) → build integral → testes próprios Q0–Q8x → `PRELIMINARY_CONCLUSIONS_first_pass.md` → segunda passagem (A/, L/, tests/, tools/, env/ e leitura integral do relatório). Desvio registrado: nenhum. Oleans do construtor não usados.

## 1. Alvo e custódia

| item | observado | fita |
|---|---|---|
| remoto (fetch 2026-10-18) | `origin/main` = `zenodo-v58` = base `52cc0915…`; 0 refs remotas `stone59*`; tags preservadas | ✅ |
| base | root `2160cbbd…`, Phase3 `58a60e8b…` | ✅ |
| candidato | `dcd6e6b18a909914dd789667d9830bff106bc762`, parent único = base; root `1b4729f3…`, Phase3 `c3157cb9…`, LatticeGauge `7b2da342…`; `git bundle verify` OK; `refs/heads/stone59` do bundle = candidato (não recriado) | ✅ |
| blobs | módulo `292602dd…` (`Phase3/LatticeGauge/ActivityProfileDampingOptimalCover.lean`, 646 linhas, 36.696 B, SHA `61dde0c9…`, 100644); lakefile `cd461108…` (100644) | ✅ |
| diff | 2 caminhos: A +646, M +1/−1 (só o glob novo), total +647/−1; `git diff --check` limpo; conteúdo = `git/diff_vs_base.patch` (ids abreviados); 119 módulos e demais caminhos (pins, manifesto `c376bbe9…`, workflows, auditorias, docs, licenças) idênticos à base | ✅ |
| ZIP | `b355625a…c823` (298.025 B); 38 entradas = 32 arquivos + 6 diretórios; sem links/duplicatas/traversal; CRC OK; `SHA256SUMS_59L.txt` 31/31 sem auto-inclusão (32.º = o manifesto); avulsos internos (módulo, testes `38058a2e…`, diff `8cf349ae…`, bundle `7295ab50…`, matrizes `d36377c5…`/`fae80d86…`) com bytes e hashes = fita | ✅ |

Proveniência: `Claude <noreply@anthropic.com>` (autor e committer), cabeçalho `gpgsig` SSH presente (fato de custódia; não é autenticação independente), trailers `Co-Authored-By: Claude Fable 5.1` / `Claude-Session`.

## 2. Ambiente e reprodução

Bancada da 57/58-QA1 (container sobreviveu): elan 4.2.4, `leanprover/lean4:v4.15.0` (Lean 4.15.0 `11651562caae`, Lake 5.0.0-1165156); clone próprio com push desabilitado; worktree destacada no candidato. Dependências: cache `.lake/packages` materializado na 57-QA1 pelo cache comunitário do Mathlib (reuso, não compilação nesta execução); **9/9 revisões = manifesto** conferidas antes do build; sem `lake update`; manifesto `c376bbe9…` pré = pós. Artefatos do projeto removidos antes (`prebuild_artifacts.txt`: NONE); pureza: 120 `.olean`, 0 anteriores ao instante de início.

- **Build integral único** (`lake build`, `setsid nohup`, sem interrupção): 13:31:47Z → 13:52:03Z, exit 0 (1.216 s); **120 `LatticeGauge` Built, 120 únicos, 0 Replayed**; dependências 0 Built / 0 Replayed (nada reconstruído); 0 erros; 0 sorryAx; `git diff --exit-code` limpo. Log SHA `42817399…`.
- **Certidões** (listas recompostas até o colchete final; `info:`, multilinha, apóstrofo): **361 comandos = 361 saídas = 361 nomes únicos** (sem deduplicar antes de contar), 104 multilinha, **conjunto efetivo de cada uma das 361 = `[propext, Classical.choice, Quot.sound]`** (nenhum subconjunto, nenhuma ausência); 44 do módulo novo. Q0 (próprio): 44/44 com o mesmo conjunto; certidões dos meus testes (Q2 ×4, Q3 ×1, Q6 ×1) reportadas à parte, todas padrão.
- **Warnings**: baseline na base exata — pasta `docs/audits/stone58/` (manifesto externo 9/9 OK) → `packages/QA1_58_evidence.zip` (`b23ce8ed…` ✅; interno 36/36 sem auto-inclusão) → `build_full_clean.log` (`71a6faa0…` ✅). Blocos integrais multilinha como multiconjuntos, mesma normalização de prefixo dos dois lados: **114 = 114 iguais**, 113 pares arquivo:linha, **0 no módulo `ActivityProfileDampingOptimalCover`** (contagem própria com o rótulo correto); dependências 0 = 0.

| avisos | projeto (herdados) | módulo 59 | dependências | testes QA1 |
|---|---:|---:|---:|---:|
| meu build / meus testes | 114 (= baseline) | 0 | 0 emitidos | 62 |

- **Higiene** (código, fora de docstrings): 0 sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial/decide/@[simp]/`Fintype (Polymer`/Disjoint/DependsOnlyOn; `Classical.choose` ×4 (`optimalBudget` e specs). Imports: `Mathlib`, `LatticeGauge.ActivityProfileDampingAdditiveCover`.
- **Contagens** (método publicado, nove alternativas com espaço, objetos Git, comando `git grep -c -E '^(theorem|lemma|def|abbrev|structure|noncomputable def|instance|inductive|class) ' <commit> -- 'Phase3/LatticeGauge/*.lean'`): módulos 119 → 120; linhas 39.181 → 39.827; linhas de declaração **1.834 → 1.878** (+44 = 36 `theorem` + 4 `noncomputable def` + 4 `def`; não é número de teoremas); `#print axioms` 317 → 361 (comandos em arquivo, não inventário global de axiomas). Nomes e linhas da matriz do construtor conferidos contra o fonte (identidade por nome completo).

## 3. Enunciado, contexto e dependências

Tipos elaborados (Q0 `#check`): `Admissible`, `Reaches`, `budget` exatamente como na fita; `exists_optimal` (existência, anterior à escolha) → `optimalBudget` (`Classical.choose`) → `minCost` = `B*`, ambos exigindo no tipo os limites dos perfis e `Reaches` (não aceitam instância inviável). Capstones com o contexto da 58: `{N} [NeZero N] [Fintype (Site N)]`, `G` grupo com as instâncias mensuráveis, `μm` σ-finita de probabilidade, `0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ| ≤ 1`, `Measurable f`, `|f| ≤ Cf`, perfis em [0,1], `hsep ∀ i`; `0 ≤ Cf` derivado (l. 511, 527 via `nonneg_of_abs_le_of_config`) — não é hipótese pública. Ausentes: `m > 0`, disjunção, `r i ⊆ R`, separação s/R, fundo unitário, `DependsOnlyOn`, minimizador/unicidade/capacidade positiva/sinal fornecidos pelo usuário. A fase de otimização (§§1–6 do módulo) não envolve β, integração nem separação. `δ* ≤ 1` é conclusão sobre o minimizador escolhido; a minimalidade é sobre **todos** os admissíveis (sem cota superior).

Dependências reais em código: 58 — `…_le_additive_cover_two_terms` e `…_le_additive_cover` (1 uso cada; dependência pretendida — as recuperações não são reconstrução independente da 58); 56 — `profileExpectation_eq_of_touchFactor_eq` (2); 52-E — `nonneg_of_abs_le_of_config` (2); Mathlib — `isCompact_Icc`, `IsCompact.inter_right`, `isClosed_iInter`, `isClosed_le`, `continuous_finset_sum`, `continuous_apply`, `IsCompact.exists_isMinOn`, `isMinOn_iff`, `Finset.single_le_sum`, `Finset.sum_eq_zero_iff_of_nonneg`; capstones da 57 não usadas. `omit [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]` só nas duas comparações de RHS (l. 495, 515); `omit` das quatro instâncias de medida só nas duas identidades finais (l. 577, 589); as duas recuperações mantêm as instâncias.

## 4. Matemática (rederivação própria)

1. **Viabilidade e truncamento** (Q1): `Reaches ↔ ∃ admissível` rederivado das definições — a soma é só sobre os contatos (orçamento unitário cobre pois `d ≤ 1`; recíproca: sem contato a soma é 0). Truncamento preserva a cobertura por polímero: se algum contato paga ≥ 1 o termo truncado vale 1 e cobre sozinho (`d ≤ 1`); se nenhum paga 1, todos os termos tocados ficam iguais. **Necessidade de `d ≤ 1`** exibida: perfil fora de [0,1] (`a′ = 2`) em polímero que toca R e r 0 — `δ = 2` cobre, `clip = 1` não (admissibilidade escalar num polímero, não global). Custo não aumenta pelos pesos positivos; orçamentos 7, 0, 1, 1/4.
2. **Mínimo atingido** (Q2): fechado da cobertura como `⋂` indexada por **todos** os polímeros (nenhum `Fintype (Polymer N)`), compacidade da caixa ∩ cobertura, não-vazio sob alcance, continuidade do custo; existência na caixa (`exists_isMinOn`) e promoção a mínimo sobre **todos** os admissíveis pelo truncamento — sem chamar `exists_optimal`; `m = 0` conferido; custo ilimitado no conjunto irrestrito (que não é declarado compacto). Auxiliares reusados listados na matriz.
3. **Valor e degenerados** (Q3): custos iguais de dois minimizadores; `B* = 0 ↔` fatores efetivos iguais (pesos > 0, soma finita não negativa, via as interfaces `optimalBudget_admissible`, `minCost_le_budget`, `minCost_nonneg`); `m = 0` e `R = ∅` com perfis brutos distintos ⇒ custo 0 e `F_R` iguais por aplicação efetiva; domínio de `minCost` ([0,1] + alcance) separado das identidades algébricas (reais arbitrários); `rfl` entre termos de prova = irrelevância, não identidade sintática.
4. **Testemunho global e melhora estrita** (Q4; contatos por hipótese): `a ≡ 1/4`, `a′ = 3/4` em η₀; `n = (0,4)`: admissibilidade para **todos** os polímeros de (1/4,1/4) e (0,1/2); `δ₀ + δ₁ ≥ 1/2` para qualquer admissível; cota inferior e **`B* = (1/2)e^{−2}`** (pela interface `minCost_eq_budget_of_isMin` com o minimizador (0,1/2)); `B* < 1/4 + e^{−2}/4`; RHS compactos completos estritos com `Cf > 0`, iguais a 0 com `Cf = 0`. Estrita só contra esse orçamento; `B*` é cota, não o erro real.
5. **Não unicidade** (Q5): `n = (0,0)`: (1/2,0) e (0,1/2) admissíveis, distintos, ambos minimizadores globais (cota inferior 1/2), `minCost = 1/2` por qualquer deles.
6. **Fechamento e recuperações** (Q6): minimizador de `exists_optimal`, 58 aplicada diretamente, as duas formas e as comparações com qualquer admissível por minimalidade e sinais — sem as capstones novas, sem as comparações, sem os wrappers; aplicações explícitas das **duas** recuperações com `δ ≡ 7`; tipos definicionalmente iguais nas duas direções com as capstones da 58.
7. **Inviabilidade** (Q8x): `¬∃ admissível` e `¬Reaches` provados; a aplicação sem alcance (m = 1) falha num único goal `typedTouchesSupport η₀ (r₁ 0)` (negado por `hno 0`) — hipótese impossível, não insuficiência de tática; não é refutação da desigualdade para `F_R`.

Leitura das docstrings/cabeçalho: coerentes com os tipos (família e escalas fixas; sem algoritmo; vetor não único; cota, não o erro; sem melhora estrita universal; sem limites termodinâmico/contínuo/mass gap).

## 5. Testes próprios

Q0–Q6 exit 0; Q8x exit 1 na obrigação de alcance; Q7 por `#check`/grep. 62 avisos nos meus testes (Q6 52 — binders não usados nos `example` de tipos; Q4 6; Q5 4), separados dos 114 herdados e dos 0 do módulo. Deslizes meus (attempts preservados, candidato intocado): bullets após `split_ifs;` em linha única, `hz` não desdobrado para a soma, casts `−(4:ℕ)/2` não normalizados. Matriz: `59_QA1_TEST_MATRIX.tsv`.

## 6. Segunda passagem — material do construtor e observações da §9

- Logs: `L/build_full_clean.log` (SHA `64ccf21c…`): 120 Built únicos / 0 Replayed; dependências 0 Built / **1.332 Replayed** com 4.599 avisos reapresentados (replay; não comprova a origem histórica do cache); 114 blocos de projeto idênticos ao baseline e ao meu log; 361 saídas, 104 multilinha, todas padrão, 44 do módulo; manifesto pré registrado; `env/environment.txt` coerente (bancada da 58-AL). `L/build_module.log`: dirigido (1 Built / 75 Replayed). Fase A (`A/attempt1–4`, T59A, T8x) lida: cadeia A promovida sem alteração (nomes e linhas da matriz do construtor = fonte).
- Testes **T1–T8x (do construtor)**: reexecutados na minha bancada — `T59L_api_tests.lean` exit 0, 0 erros, 0 avisos, 13 `#check`, **0** certidões (conforme a fita); `T59L_T8x` exit 1, goal `⊢ False` (47:58). Reexecutar não os torna testes da QA1.
- Observações da §9 (sobre o **relato/matrizes/scripts** do construtor; nenhuma afeta o candidato):
  1. Pacote: 38 entradas = 32 arquivos + 6 diretórios, manifesto 31/31 — conferido; "0 arquivos da base alterados" (§0 do relatório) é impreciso: `Phase3/lakefile.toml` é preexistente e foi alterado (só o glob); os 119 módulos e demais caminhos estão intactos.
  2. "Nenhuma hipótese de positividade (`t ≥ 0`)" (§1): não há parâmetro `t` nesta otimização; a não negatividade está em `Admissible`, nos perfis e em `β ≥ 0`, `Cf ≥ 0` derivado. §2.2 atribui o `omit` das três instâncias mensuráveis a quatro teoremas; o fonte usa-o só nas duas comparações de RHS; as recuperações mantêm as instâncias; as duas identidades finais têm outro `omit` — confirmado.
  3. `L/tests_matrix.tsv` usa `L/T59L_api_tests.lean` e `L/T59L_T8x_EXPECT_FAIL.lean`; caminhos reais no ZIP: `tests/…` (caminho de bancada ≠ caminho de entrega).
  4. `w_admissible` usa a condição conjunta `1/2 ≤ δ 0 + δ 1` (+ não negatividade), `w_lower` enuncia `1/2 ≤ δ 0 + δ 1`, o passo ponderado está em `w_minCost` — confirmado; T7 usa a forma **compacta** da 58 e `mul_le_mul_of_nonneg_left … hmin`, sem chamar `optimal_two_terms_le_additive_two_terms` (ao contrário da descrição em §2.3/matriz); T6 aplica `δ ≡ 7` só na forma compacta; os `rfl` são entre termos de prova, anotados corretamente no código. Minha Q6 aplica explicitamente as duas formas com `δ ≡ 7`.
  5. O baseline autenticado é o log da QA1-58 (não um log de CI, como diz o §2.5); os 4.599 avisos são replay; a abreviação "`c376bbe9…c227`" no quadro do §0 é erro textual — o hash completo no §5 e nos artefatos termina em `…1227` e é o manifesto da base.

Nenhuma dessas observações converte-se em defeito do teorema; nenhuma omissão de teste foi apagada por relato de PASS — as verificações obrigatórias estão cobertas por evidência própria (Q1–Q8x).

## 7. Limitações

Revisão não cega. Assinatura SSH não verificada independentemente. Dependências do cache (revisões conferidas), não recompiladas. Geometria dos testes por hipótese (sem rede concreta). Resultado restrito ao escopo formal: orçamento ótimo para `r`, `n` **fixos**, família finita, volume finito, regime `0 ≤ β ≤ 1/40000`; existência clássica sem algoritmo; vetor não único; `B*` é cota (não o desvio real); sem melhora estrita universal, constante ótima universal, escolha de regiões/escalas, dualidade, família infinita, limite termodinâmico/contínuo, nova medida de Gibbs ou mass gap.

## 8. Vereditos

| eixo | veredito |
|---|---|
| Custódia | **PASS** |
| Execução | **PASS** |
| Matemática | **PASS** |
| Documentação | **PASS** — módulo e docstrings sem imprecisão; as observações 1–5 da §6 referem-se ao relato/matrizes/scripts do construtor |
| **Global** | **PASS NO ESCOPO** |

Reconfirmado ao terminar: candidato `dcd6e6b1…` e base `52cc0915…` intactos; diff, pins, manifesto `c376bbe9…` (pré = pós), caminhos protegidos e originais do construtor byte-idênticos; `origin/main` = `zenodo-v58` = base; 0 refs remotas `stone59*`; worktree limpa; push desabilitado; nenhuma escrita remota. Nenhum commit de correção, PR, merge, tag, Release ou Zenodo. Pedra 60 não iniciada. **HARD STOP.** (Gemini e Kimi recebem fitas próprias; este parecer não lhes é antecipado por mim.)

## 9. Pacote

`QA1_59_evidence.zip` com `SHA256SUMS_59-QA1.txt` (sem auto-inclusão): este relatório (cópia idêntica à avulsa), as duas matrizes, `PRELIMINARY_CONCLUSIONS_first_pass.md`, `environment.txt`, `prebuild_artifacts.txt`, `build_full_clean.log` + `.result` + instantes, manifestos pré/pós, `compare_warning_blocks.py` (rótulo 59), `warnings_block_comparison.txt`, `tests/` (fontes Q, logs finais e attempts, falha esperada), `builder_tests_rerun/`. O SHA do ZIP vai na mensagem de entrega, não aqui.
