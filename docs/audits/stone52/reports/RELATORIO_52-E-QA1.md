# RELATÓRIO — FITA 52-E-QA1 (auditoria independente do capstone da Pedra 52)

Auditor: Claude Fable 5.1 (instância QA; não é a instância construtora). Bench próprio em `/home/claude/qa52e/wt` (worktree destacado no candidato; cache Mathlib pinado reaproveitado, `.lake/packages` intocado), Lean 4.15.0 (11651562caae), Lake 5.0.0, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, `lake-manifest.json` SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227` (pré = pós). Data: 2026-09-12 (UTC).

**Declaração de exposição prévia (exigida pela fita).** Esta instância auditou os gates 52-A0, 52-A, 52-A-C1, 52-B, 52-C e 52-D e escreveu a nota preparatória de 52-C (v1/v2). Conheço a arquitetura, o ledger 52-B e as cotas 52-D. Esta auditoria **não é cega**. O que é independente aqui: a reconstrução em checkout isolado, a leitura das definições/assinaturas/provas reais, os testes próprios e o parecer, todos formados **antes** de abrir relatório, matrizes, testes e logs do construtor de 52-E (abertura registrada em §9; `PRELIMINARY_CONCLUSIONS_first_pass.md` foi gravado antes dela). O veredito do construtor não foi usado como evidência.

Regime: somente leitura; zero edições no candidato; zero commit/amend/push/PR/merge/tag/release/Zenodo; testes descartáveis fora da árvore.

## 0. Veredito

**PASS. Certifico o capstone da Pedra 52 no escopo formal efetivamente enunciado:** para `N`, `G` grupo com `[MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`, `μm` medida `[SigmaFinite] [IsProbabilityMeasure]`, `0 ≤ β ≤ 1/40000`, `χ` mensurável com `|χ| ≤ 1`, `f : Config N G → ℝ` com `DependsOnlyOn f s`, `Measurable f`, `∀ U, |f U| ≤ Cf`, `WalkBarrierSeparated s r n`, `0 ≤ θ ≤ 1`:

`|gibbsExpectation μm β χ f − activityDampedExpectation μm β χ f s r θ| ≤ (1 − θ)·(2·Cf)·exp(8·D_s/113)·exp(−n/2)`, `D_s = card (supportLinkFinset s)`,

derivado do ledger exato 52-B e das duas cotas de coluna 52-D, passando pela forma de dois termos `(1−θ)·Cf·e^{−n/2}·(e^{8D_s/113} + e^{4D_s/113})`, com `0 ≤ Cf` derivado (não assumido), sem divisão por `(1−θ)`, sem `Disjoint`, sem fator de volume, sem (7/8,3), sem 8/(3e). 7/7 declarações em `[propext, Classical.choice, Quot.sound]`, 0 sorryAx, build limpo verde (111 módulos), warnings herdados idênticos ao baseline. Nenhum defeito matemático. Duas divergências documentais e uma nota de interface (§7). **Isto não equivale a certificar a solução do problema de Yang–Mills no contínuo**: o teorema é uma estimativa de estabilidade em relação a Gibbs numa rede finita, na separação por caminhadas `n`, para uma classe de observáveis locais; não afirma monotonicidade do desvio, controle entre θ e θ′, limite termodinâmico, contínuo ou mass gap (§4-H).

## 1. Custódia e identificadores

| item | valor | verificação |
|---|---|---|
| tarball | `STONE52-E-L_evidence.tgz` SHA-256 `392e41583a18dd7c03a2fc13c6efc65dc6779f2157be19e7882cbf2f5f8c5879` | ✅ = fita; 30 entradas sob `e_out/`, caminhos limpos |
| bundle | `stone52-e_8b638c9.bundle` SHA-256 `bd80e6e92ef9c3694d1ad91e6ef0814598ee4bc4e8421ecebd97e08d5d4fed7e` | ✅ = fita; o bundle enviado à parte é byte-idêntico ao do tarball; `git bundle verify` OK com a base presente; pré-requisito = base |
| manifesto do construtor | `SHA256SUMS_52-E-L.txt` (enviado à parte = o do tarball) | 24 entradas, sem auto-inclusão, 24/24 OK |
| `origin/main` observada | `2a391941847e7e1eb0ccfc690462beb62c74f818` (fetch somente leitura em 2026-09-12) | = base obrigatória; merge do PR #24; tree `226e85ba…` e `Phase3/` `37ea02e6…` = os do candidato 52-D auditado (`6168e23`); blob 52-D `38e61d23…` presente. Não houve avanço remoto além da base |
| candidato | `8b638c94a7db54eb8b5780f962e0e79d522db6ad` | exatamente 1 commit sobre a base (`rev-list --count` = 1); parent = base |
| tree / Phase3 | `343a69ded589e607f3ad2863047ef049a8763c4f` / `bf2fae8c9ae70e4e710b4b2d9d0c56fff1af8997` | ✅ = fita |
| blob do módulo | `6b8514fd88fc6e54788c532de273e4a23a24d73c`, 216 linhas, 7 declarações | ✅ = fita; cópia `e_out/ActivityDampingStability.lean` byte-idêntica |
| blob do lakefile | `20c93a3ab626859ba6048084cf46d52560b68f61` | ✅ = fita; 1 glob acrescentado ao final (110 → 111) |
| diff | A `Phase3/LatticeGauge/ActivityDampingStability.lean` (+216), M `Phase3/lakefile.toml` (+1/−1); 2 arquivos, **+217/−1** | ✅ |
| módulos anteriores | 110 blobs de `LatticeGauge/` byte-idênticos (1 único caminho alterado: o novo) | ✅ |
| protegidos | workflow, README, docs, LICENSE, `lean-toolchain`, `lake-manifest.json`, `formalization.yaml`, Phase1, Phase2 | 0 alterações |
| proveniência | autor e committer `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>`; trailer `Co-authored-by: Claude <noreply@anthropic.com>` | padrão da cadeia |
| imports | `Mathlib`, `LatticeGauge.ActivityDampingColumnBounds` | módulo folha; nada o importa; sem ciclo |

## 2. Build

**Dirigido** (`lake build LatticeGauge.ActivityDampingStability`): exit 0, 219 s, 0 erros, 0 warnings no módulo, 0 sorryAx, 7 certidões.

**Limpo completo** (`rm -rf .lake/build && lake build` — apenas os artefatos de build do projeto; o cache de dependências `.lake/packages` foi preservado; início `2026-09-12T19:21:49Z`): exit 0, 477 s, **111 módulos "Built", 0 "Replayed"**, 0 erros, **114 warnings = 113 pares arquivo:linha com as mesmas multiplicidades do baseline** (diff vazio contra o baseline reconstruído na QA 52-D; a cadeia 52-B → 52-C → 52-D → 52-E tem baseline invariante), **0 warnings no módulo novo** (separados dos testes: meus testes também compilaram sem warnings), 0 sorryAx. Pureza: 111 `.olean` de `LatticeGauge`, todos com mtime posterior ao início; 0 anteriores. Manifesto pré = pós. Logs: `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`.

## 3. Axiomas, higiene, dependências

- Meu `#print axioms` das 7 declarações (S0): 7/7 `[propext, Classical.choice, Quot.sound]` (exatamente esse conjunto; nenhuma abaixo dele, o que é esperado sob `open scoped Classical`), 0 sorryAx, nenhum axioma novo.
- Léxico (`hygiene.txt`): em código, 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial`, 0 divisão por `(1−θ)`, 0 `⁻¹`; `Disjoint`, "volume", "monotonicity", "thermodynamic", "continuum", "mass gap" ocorrem só no cabeçalho (l. 31–38), negando-os.
- Dependências efetivamente consumidas (mapa identificador → módulo definidor, 17 identificadores locais): 52-D `ledger_columns_are_the_estimated_sums` (que é o termo de prova do ledger 52-B), `abs_sum_dampingConnectorColumn_le`, `abs_sum_dampingBridgeColumn_le`; 52-B `gibbsExpectation_sub_activityDampedExpectation_one`, `…_empty_region`; 52-A `activityDampedExpectation_zero`; Basic `trivialConfig`. **`abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay` (capstone 51, `ActivityRestrictionStability.lean:61`) aparece apenas em docstrings (l. 24, 154) e não é alcançável a partir dos imports do candidato** — o capstone 51 não substitui a derivação (exigência D da fita, satisfeita) e a comparação é documental. Nenhuma hipótese contém a conclusão; nenhuma circularidade.

## 4. Pontos obrigatórios (§3 da fita), verificados pelas definições e por testes próprios

**A. Expressões e composição** (S1). LHS usa as definições publicadas: `gibbsExpectation μm β χ f = (∫ f·gibbsWeight ∂configMeasure)/realZ` e `activityDampedExpectation = activityDampedMarkedGas/activityDampedPolymerGas`, ambas por `rfl`. Rederivei a estimativa de dois termos **sem** os teoremas 52-E: `gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger` (52-B, orientação `gibbs − damped`; coluna 1 sobre `typedTouchingFamilies s` com peso `θ^{touchCount r T}`; coluna 2 sobre `activityBridgeCores s r` com peso `1 − θ^{touchCount r T}`; nenhuma coluna omitida/alterada) + `abs_add` + `abs_sum_dampingConnectorColumn_le` e `abs_sum_dampingBridgeColumn_le` (52-D) com os **mesmos** `μm β χ f s r n θ`, `hCf0` fornecido por `le_trans (abs_nonneg _) (hCf (fun _ => 1))`; `ring` fecha. É exatamente a prova do módulo (l. 84–93), que usa a versão 52-D do ledger (`ledger_columns_are_the_estimated_sums`), idêntica ao teorema 52-B por construção (verificado na QA 52-D, R1b).

**B. Constantes e sinais** (S2). `4·D·(2/113) = 8·D/113` e `2·D·(2/113) = 4·D/113` (`ring`); fator comum `(1−θ)·Cf·e^{−n/2}` com `≥ 0` de `θ ≤ 1` (`sub_nonneg`), `0 ≤ Cf` (derivado) e `exp > 0`; `D_s ≥ 0` por `Nat.cast_nonneg`; passagem `K·(e^{8D/113} + e^{4D/113}) ≤ 2K·e^{8D/113}` re-provada com exatamente essas hipóteses; verificação de direção: com o expoente menor a passagem seria falsa (`e^2 + e^1 ≤ 2e^1` refutado). Capstone rederivado por mim a partir da forma de dois termos. RHS retipado: produto de `(1−θ)`, `2·Cf`, `e^{8D_s/113}`, `e^{−n/2}` — sem perda oculta de constante (o único passo com perda é o explícito `e^{4D/113} ≤ e^{8D/113}`, que a forma de dois termos preserva), sem fator de volume, sem `Disjoint`, sem divisão por `(1−θ)`.

**C. Majorante Cf** (S3). `trivialConfig N G` existe na base (`Basic.lean:44`, `fun _ => 1`; `rfl` verificado); `nonneg_of_abs_le_of_config hCf = le_trans (abs_nonneg _) (hCf (trivialConfig N G))`; `Nonempty (Config N G)`. O capstone **não** carrega `hCf0` (retipado sem essa hipótese em escopo). `omit` correto: o lema usa só `[Group G]`.

**D. Dependências científicas.** As duas cotas 52-D são aplicadas com as assinaturas conferidas (KP, `mf`, `hCf0`, `hCf`, `hsep`, `0≤θ≤1`); os orçamentos (1/2,3) e (7/8,1) entram já provados dentro delas; nada de (7/8,3) nem 8/(3e) é reintroduzido (o 8/(3e) permanece interno ao 52-A0, absorvido). O capstone 51 não participa da derivação (§3).

**E. Endpoint θ = 0** (S4). Capstone em θ = 0 + `activityDampedExpectation_zero` ⇒ `|gibbs − activityRestrictedExpectation| ≤ 2·Cf·e^{8D_s/113}·e^{−n/2}`; o capstone 51 (`ActivityRestrictionStability.lean:61–80`, importado explicitamente no meu teste) tem **a mesma conclusão, a mesma constante e a mesma taxa**, com as mesmas hipóteses **mais** `hCf0 : 0 ≤ Cf` explícito; derivação mútua nas duas direções (52-E@0 ⇒ 51 e 51 ⇒ 52-E@0 com `hCf0` derivado).

**F. Endpoint θ = 1** (S5), dois testes distintos: (i) aplicação **efetiva** do capstone em θ = 1 com todas as hipóteses (`hsmall`, `hsep`) ⇒ `|gibbs − damped 1| ≤ 0` ⇒ `gibbs − damped 1 = 0`; (ii) identidade exata pela representação existente, instanciada **sem** `hsmall`, `hsep`, `n` (hipóteses mais fracas: `hβ mχ hχabs hf mf hCf`). `capstone_bound_one` é só álgebra do RHS (retipado); sozinho não testa o capstone — o teste (i) testa.

**G. Região vazia** (S6). Identidade para **todo** θ (instanciada em θ = 5 e θ = −2; o teorema não impõe `0 ≤ θ ≤ 1`). Compatibilidade: `WalkBarrierSeparated s ∅ n` vale para todo `n` (prova própria: `plaquetteTouchesRegion q ∅` é falso), logo o capstone em r = ∅ dá `|0| ≤ (1−θ)·2Cf·e^{8D/113}·e^{−n/2}`, coerente e trivialmente implicado pela identidade (derivei o bound só da identidade, para `θ ≤ 1`). **Não existe declaração específica** para "o bound em r = ∅": só a identidade (`…_empty_region_eq_zero`) e a consequência imediata. O cabeçalho (l. 27) diz "the bound at r = ∅ is also stated" — divergência **documental** (D1), não defeito.

**H. Alcance** (S7). As declarações provam estabilidade em relação a Gibbs: cota de `|gibbs − damped(θ)|` para um θ. Não afirmam monotonicidade do desvio real, nem controle entre θ e θ′ (ilustração abstrata em S7b), nem limite termodinâmico, contínuo ou mass gap; o cabeçalho do módulo (l. 29–38) diz o mesmo. Especialização interior θ = 1/2: `≤ Cf·e^{8D_s/113}·e^{−n/2}`.

## 5. Matriz das 7 declarações

`52-E_QA1_DECLARATION_MATRIX.tsv`: 7 linhas, 7 PASS, com hipóteses explícitas efetivamente exigidas, contexto de typeclasses usado, dependências reais e teste(s) que cobre(m) cada uma.

## 6. Testes próprios

`52-E_QA1_TEST_MATRIX.tsv`: 11 arquivos — 9 positivos (exit 0, 0 warnings), 2 EXPECT_FAIL: S8x (θ = 2: argumento inválido, `⊢ False` de `2 ≤ 1`) e S8y (sem `hf`: placeholder não sintetizável) — ambos **falhas de aplicação**, registradas explicitamente como não-prova de indispensabilidade (a fita lembra: `hCf0` é derivável de `hCf`, e o próprio módulo o deriva). Falsidade demonstrada por contraexemplo: a redução com o expoente menor (S2e). Deslizes meus: S4 tentativa 1 falhou por import ausente (o que **revelou** que o capstone 51 não é alcançável do candidato — achado útil), S7b precisou de quatro tentativas de tática em aritmética de `abs` numa ilustração abstrata; logs `attempt1` preservados; nenhuma falha reclassificada como problema do candidato.

## 7. Classificação de achados

- **Defeito matemático do candidato:** nenhum.
- **Limitação de interface:** (I1) o capstone 51 (`ActivityRestrictionStability`) mantém `hCf0` explícito enquanto 52-E o deriva — assimetria herdada, inócua; quem quiser a igualdade literal de assinaturas usa `nonneg_of_abs_le_of_config`. (I2) retirada: uma primeira leitura minha sugeriu contexto de medida supérfluo em `capstone_bound_one`; o `#check` elaborado (S9) mostra que ela carrega apenas `{N} [NeZero N] [Fintype (Site N)]` — nada a observar.
- **Divergências documentais:** (D1) cabeçalho l. 27 "the bound at r = ∅ is also stated" — não há declaração; só identidade + consequência imediata (§4-G). (D2) cabeçalho l. 23–24 e docstring l. 151–155 apresentam a recuperação do capstone 51 como comparação; correto, mas vale registrar que **não é dependência formal** (não importado). (D3) relatório do construtor: "7 positivos" vs matriz com 6 IDs (E-POS-4 contém dois `example`s) — contagem consistente, rótulo ambíguo.
- **Obrigação futura:** nenhuma no escopo da Pedra 52 formal; fora dele (não reivindicado): tudo o que o cabeçalho põe em HARD HOLD.

## 8. Conclusões preliminares vs finais

`PRELIMINARY_CONCLUSIONS_first_pass.md` (gravado antes de abrir o material do construtor) já registrava PASS com as mesmas leituras A–H, D1 e a não-alcançabilidade do capstone 51. A segunda passagem não alterou o parecer.

## 9. Segunda passagem — comparação com o material do construtor (`e_out/`, aberto após §8)

Concordâncias verificadas (não copiadas): identificadores de custódia (commit, parent, trees — a tree da base `226e85ba…` é de fato a do merge `2a39194`, igual à de `6168e23` —, blobs do módulo e do lakefile, +217/−1, proveniência); build limpo do construtor 557 s / 111 Built / 0 Replayed / 0 erros / 114 warnings; seus 113 pares arquivo:linha **iguais** aos meus; 7 certidões; `print_axioms_all_111.log` com 137 certidões e 0 sorryAx; `52-E_DECLARATION_INDEX.tsv` com assinaturas completas conferidas contra o módulo; `52-E_MODULE_DEPENDENCY_MAP.tsv` marca corretamente o capstone 51 como "docstring-only" (coincide com meu achado); `52-E_ENDPOINT_MATRIX.tsv` consistente com o código (registra θ = 1 via identidade e via RHS = 0; r = ∅ só como identidade — coerente com D1); `52-E_TEST_MATRIX.tsv` classifica E-NEG-1/3/4 como falhas de aplicação **sem** inferir indispensabilidade (conforme a fita) e E-NEG-2 como falha de tática + contraexemplo ao passo de redução; os 4 negativos falham pelo motivo declarado; `pos_e.lean` compila (0 warnings) e importa `ActivityRestrictionStability` para a comparação — mesma necessidade que meu S4 encontrou. Divergências: apenas D1 (afirmação do cabeçalho) e D3 (rótulo de contagem).

## 10. Pacote e HARD STOP

`/home/claude/qa52e/out` (manifesto `SHA256SUMS_52-E-QA1.txt`, sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (11 `.lean` + logs + 2 `attempt1`), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`. Nenhum bloqueio de execução ocorreu.

HARD STOP após esta entrega: nenhuma edição no candidato, nenhum commit, nenhum push/PR/merge, nenhuma publicação de auditoria, nenhuma alteração em Zenodo, nenhum gate iniciado.
