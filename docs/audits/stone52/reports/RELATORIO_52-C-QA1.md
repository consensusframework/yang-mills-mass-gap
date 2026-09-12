# RELATÓRIO — FITA 52-C-QA1 (auditoria independente do conector amortecido)

Auditor: Claude Fable 5.1 (instância QA, segunda instância; não é a instância construtora). Bench próprio em `/home/claude/qa52c/wt` (worktree destacado no candidato), Lean 4.15.0 (commit 11651562caae), Lake 5.0.0, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, `lake-manifest.json` resolvido SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227` (pré = pós build). Data: 2026-09-11 (UTC).

Regime: somente leitura. Zero edições no candidato; zero commit/amend/push/PR/merge/tag/release; testes descartáveis fora da árvore (`/home/claude/qa52c/out/tests`, compilados com `lake env lean`). Nenhum item do construtor além do bundle foi lido antes do registro de `PRELIMINARY_CONCLUSIONS_first_pass.md` (primeira passagem); a comparação documental veio depois (segunda passagem, §9).

## 0. Veredito

**PASS.** O candidato `6502ca9f51754d7e084106e8fa1022ca0fa2427a` entrega o que a fita 52-C pede — coeficiente do conector amortecido, inclusão–exclusão por coeficiente, dominação, somabilidade, identidade de série com orientação `E_T(θ) − E_T(1) = C_{T,r}(θ)`, fatoração da coluna do ledger 52-B, endpoints, cota erodida com subtração natural truncada e sem 8/(3e), controle exponencial com `0 ≤ d ≤ 1` — com 19/19 declarações certificadas em `[propext, Classical.choice, Quot.sound]`, 0 sorry, build limpo verde, 0 warnings no módulo, 114 warnings herdados idênticos ao baseline, e nenhuma hipótese que contenha a conclusão. Nenhum defeito do candidato foi encontrado; há três observações documentais sobre o pacote do construtor (§9), nenhuma sobre o código. Este parecer **não** certifica somas de coluna, orçamentos, capstone nem a constante final da Pedra 52 (fora do escopo de 52-C, conforme o próprio HARD HOLD do módulo).

## 1. Custódia e identificadores

| item | valor | verificação |
|---|---|---|
| tarball recebido | `STONE52-C-L_evidence.tgz` SHA-256 `c61a3db135a8b2d5dd7236a93526adbb2cd191cf1bca2de4db584be1fd6a2ba2` | 28 entradas sob `c_out/`, caminhos limpos |
| bundle | `stone52-c_6502ca9.bundle` SHA-256 `ac26949e224591065c7eab27353e6323d384025825b17cf1711565ba2b7c9056` | `git bundle verify` OK; = entrada do manifesto do construtor |
| base declarada | `eb3051fdd4a888eaf7bf29ebf33f597f0e81ddb5` | = `origin/main` observada por fetch somente leitura; tree `61c6eeac…`, `Phase3/` `805d0b93…` (= base auditada em 52-B) |
| candidato | `6502ca9f51754d7e084106e8fa1022ca0fa2427a` | exatamente 1 commit sobre a base; parent = base |
| tree / Phase3 | `359ac9221292210c70f3ab2cea1b1414bc92bc0b` / `194fac1c4637710fc34895808365771f63c7f821` | ✅ |
| blob do módulo | `5b372d5b5a459dbafd87d5aa27657fdb6a6e7e86` (568 linhas) | ✅; cópia `c_out/ActivityDampingConnector.lean` byte-idêntica |
| blob do lakefile | `b9f532c0c10ed4d096aad26f0f93bb411139973b` | 1 glob acrescentado ao final (108 → 109) |
| diff | A `Phase3/LatticeGauge/ActivityDampingConnector.lean` (+568), M `Phase3/lakefile.toml` (+1/−1); 2 arquivos, +569/−1 | ✅ |
| módulos anteriores | 108 blobs byte-idênticos à base; 52-B `ActivityDampingLedger.lean` = `1bf0dc4a…` (blob auditado em 52-B-QA1) | ✅ |
| arquivos protegidos | workflow, README, docs, LICENSE, `lean-toolchain`, `lake-manifest.json`, Phase1, Phase2 | 0 alterações |
| proveniência | autor e committer `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>`; trailer `Co-authored-by: Claude <noreply@anthropic.com>` | padrão da cadeia 51/52 |
| mensagem | `feat: formalize the damped connector for Stone 52`; corpo não reivindica somas de coluna, orçamentos nem capstone | conforme |

Validade sobre a base pinada = prontidão de publicação (base = main). O manifesto do construtor `SHA256SUMS_52-C-L.txt` tem 24 entradas, sem auto-inclusão, 24/24 OK.

## 2. Build

**Dirigido** (`lake build LatticeGauge.ActivityDampingConnector`, cache Mathlib pinado): exit 0, 295 s, 0 erros, 0 warnings no módulo, 0 sorryAx; log `build_directed.log`.

**Limpo completo** (`rm -rf .lake/build && lake build`, início registrado `2026-09-11T15:29:49Z`): exit 0, 748 s, **109 módulos "Built", 0 "Replayed"**, 0 erros, **114 warnings herdados = 113 pares arquivo:linha com as mesmas multiplicidades do baseline reconstruído na QA 52-B** (diff vazio; `warnings_file_line_QA1.txt`), 0 warnings no módulo novo, 0 sorryAx, 0 `info` no módulo além das 13 certidões. Prova de pureza: 109 `.olean` de `LatticeGauge`, todos com mtime posterior ao início; 0 anteriores. Manifesto pré = pós.

(Uma primeira tentativa de lançar a reconstrução em background abortou em 0 s por `lake: command not found` — PATH do elan ausente no subshell; sem efeito no resultado, apenas registrado por honestidade de log.)

## 3. Axiomas, higiene, dependências

- `#print axioms` do módulo (13 linhas): todas `[propext, Classical.choice, Quot.sound]`.
- **Meu** `#print axioms` das **19** declarações (Q0), incluindo as 6 que o construtor não imprime (as 2 definições, o `iff`, e os 3 lemas de coeficiente de endpoint): 19/19 `[propext, Classical.choice, Quot.sound]`, 0 sorryAx, nenhuma "não depende de axiomas" (esperado: todas usam `Classical`).
- Léxico (`hygiene.txt`): 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial` em código; as ocorrências de "axioms", "sorry", "8/(3e)", "mass gap", "thermodynamic", "continuum" estão só em docstrings e **negam** essas coisas (HARD HOLD do cabeçalho).
- Imports: `Mathlib`, `LatticeGauge.ActivityDampingLedger` (52-B), `LatticeGauge.ActivityRestrictionColumnBounds` (51-D). Módulo folha; nada o importa; sem ciclo.
- Mapa identificador → módulo definidor (43 identificadores locais resolvidos, `hygiene.txt`): 51-D entra apenas por três lemas auxiliares — `walkBarrierSeparated_barrierRegions_sub_familyMass` (erosão), `abs_exp_sub_one_le_decay_exp`, `exp_neg_nat_sub_half_le`; 52-A0 por `summable_nat_mul_kpAbsConnector_polymerWeight` e `tsum_nat_mul_kpAbsConnector_polymerWeight_le_local_P`; 52-A/C1 por `dampedActivity`, `tupleTouchCount*`, `abstractKP_dampedActivity`, `prod_dampedActivity_tuple`, `one_sub_dampedPow_*`; 51-B/C por `activityRestrictionConnector`, `regionAllowed_eq_remoteAllowed_empty`, `kpConnectorUnrootedCoeff`, `TupleHitsBothForbidden`, `connectorClusterSum`. **Nenhum** uso de 51-E, `CovarianceDecay`, somas de coluna, orçamentos ou capstone. Nenhuma hipótese de nenhum teorema contém a identidade ou a cota que ele conclui.

## 4. Matemática — os nove pontos da fita (verificados pelas definições, com testes próprios)

1. **Coeficiente literal** (Q1). `kpDampedConnectorUnrootedCoeff k z P r θ` é, por `rfl`, `(Σ_δ if TupleHitsBothForbidden P (regionAllowed r) δ then (1 − θ^{tupleTouchCount r δ})·((ursell : ℤ) : ℝ)·∏ z(δ i) else 0)/k!` — filtro, peso, Ursell, produto das atividades **originais** `z` (não `dampedActivity`), casts e `k!` exatamente como em 49/50/51-C. Contagem por posição com repetições (Q4c: `![η,η]` conta 2 ou 0, nunca 1).

2. **Orientação** (Q2). A identidade de série é `E_T(θ) − E_T(1) = C_{T,r}(θ)` com `E_T(θ) := dampedActivityCoreExponent` (restrito − pleno, definição 52-B) e `E_T(1) = fullActivityCoreExponent` — a mesma orientação de 51-C (`region − full = connector`). Consistência por duas rotas em θ = 0: (51-C `regionActivityCoreExponent_sub_full_eq_activityRestrictionConnector` + `dampedActivityCoreExponent_zero` + `activityDampingConnector_zero`) e (teorema de série 52-C em θ = 0) dão o mesmo valor. Em θ = 1: a série dá `E_T(1) − E_T(1) = C(1)`, logo `C(1) = 0`, coerente com `activityDampingConnector_one`. Refutação abstrata: a orientação invertida forçaria `C = −C`.

3. **Inserção do filtro** (Q3, leitura das linhas 114–149). Só a implicação `TupleAllowed (regionAllowed r) δ → tc = 0 → 1 − θ^0 = 0` é usada (caso "P proibido, Q permitido": `hc : tc = 0`, `pow_zero`); a recíproca "peso 0 ⇒ tc = 0" **não** aparece — e é falsa em θ = 1 (contraexemplo t = 1, Q3b), verdadeira só para 0 ≤ θ < 1 (Q3c). O teorema de inclusão–exclusão não tem hipótese em θ (Q3d) e em θ = 1 colapsa a 0 coerentemente (Q3e).

4. **Dominação** (Q4). `|c_k| ≤ (1−θ)·k·A_k` com `A_k = kpAbsConnectorUnrootedCoeff k |z| P (regionAllowed r)`, para 0 ≤ θ ≤ 1. Ingredientes re-provados: `0 ≤ 1−θ^t ≤ t(1−θ) ≤ k(1−θ)` (t ≤ k por `tupleTouchCount_le`); `k!` nos dois lados (θ = 0 reduz a `|c_k^{51}| ≤ k·A_k`); fora de [0,1] o peso muda de sinal (θ = 2, t = 1 dá −1), logo a hipótese é necessária e sua ausência falha por aplicação (Q4x, `⊢ False` vindo de `2 ≤ 1`).

5. **Somabilidade vs identidade** (Q5). Distintas e corretamente separadas: a identidade de série (`tsum_sub`/`tsum_add` sobre quatro séries somáveis por KP + transporte 52-A) **não** exige separação — instanciada com `r` arbitrário e θ = 1/2; a somabilidade **absoluta** do conector exige `WalkBarrierSeparated (barrierRegion T s) (barrierRegion ∅ r) q` e vem só do majorante 52-A0 (nada sobre o conector é assumido). As quatro somabilidades KP foram rederivadas sem o módulo (Q5c). θ = 2 falha por hipótese (Q5x).

6. **Endpoints** (Q6). k = 0 → 0 para todo θ (tupla vazia é P-permitida; o peso nem é avaliado). `0^0 = 1` é tratado explicitamente e irrelevante: tuplas de contagem 0 estão fora do filtro (Q1b). r = ∅ → 0 (coeficiente e série; coerente com `dampedActivityCoreExponent_empty_region` via a identidade, Q6c'). θ = 1 → 0. θ = 0 → `activityRestrictionConnector` (51-C), **sem** hipótese KP (β = −7 aceito, Q6e).

7. **Cota erodida** (Q7). `|C_{T,r}(θ)| ≤ (1−θ)·exp(−((n − familyTotalCard T : ℕ))/2)·(card(barrierLinkFinset T s)·2/113)` sob `T ∈ typedTouchingFamilies s`, `WalkBarrierSeparated s r n`, 0 ≤ θ ≤ 1. Subtração **truncada em ℕ antes do cast** (m_T > n ⇒ expoente 0 ⇒ cota `(1−θ)·q′`, sem explosão, Q7b); a erosão vem de 51-D com `T' = ∅` de massa 0 (rederivado, Q7b'); o primeiro momento 52-A0 usado conclui `exp(−q/2)·q′` **sem** 8/(3e) (retipado, Q7c); em θ = 0 reduz-se a uma cota para o conector 51-C (Q7d).

8. **Controle exponencial** (Q8). `|1 − e^{C}| ≤ d·e^{2q′}`, `d = (1−θ)·exp(−((n−m_T:ℕ))/2)`. `0 ≤ d ≤ 1` re-provado para **todo** n, m (padrão 51-D: `Nat.cast_nonneg` do natural truncado + `mul_le_one₀`); contraexemplo abstrato mostra que **sem** truncação (subtração real) `d ≤ 1` falharia (Q8a'); hipóteses de `abs_exp_sub_one_le_decay_exp` retipadas (`B = 2q′` exatamente, Q8b); especialização m_T > n: `|1−e^C| ≤ (1−θ)e^{2q′}` (Q8c); forma recomprada `e^{−n/2}e^{m_T/2}` rederivada (Q8d).

9. **Fatoração vs coluna 52-B** (Q9). `e^{E_T(1)} − e^{E_T(θ)} = e^{E_T(1)}(1 − e^{C})`, aplicada ao termo da coluna 1 do ledger 52-B: `θ^t·W·(e^{E1} − e^{Eθ}) = θ^t·W·e^{E1}·(1 − e^{C})`; cota termo-a-termo montada só com peças 52-C: `≤ θ^t·|W|·e^{E1}·(1−θ)·e^{−((n−m_T:ℕ))/2}·e^{2q′}` (Q9b). Isto **não** é soma de coluna nem capstone; é a verificação de que a interface encaixa. O ledger 52-B foi retipado literalmente (Q9c). A reserva R2 (lema geral `|e^a − e^b|`) fica dispensada para 52-C, como previsto na nota preparatória v2.

## 5. Matriz das 19 declarações

`52-C_QA1_DECLARATION_MATRIX.tsv` — 19 linhas: 19 PASS; hipóteses efetivamente exigidas registradas declaração a declaração; uma nota de interface na linha 7 (§7).

## 6. Testes próprios

`52-C_QA1_TEST_MATRIX.tsv` — 12 arquivos: 10 positivos (exit 0), 2 EXPECT_FAIL (exit 1, ambos `⊢ False` derivado de `2 ≤ 1`: **falhas de aplicação**, não refutações). Contraexemplos abstratos provados: recíproca do filtro em θ = 1 (Q3b); peso negativo em θ = 2 (Q4e); orientação invertida (Q2e); `d ≤ 1` sem truncação (Q8a'). Dois deslizes táticos meus (Q8: `linarith` após `norm_num` já ter fechado; Q9: associatividade) foram corrigidos; os logs `attempt1` ficam no pacote. Nenhuma falha tática foi reclassificada como problema do candidato.

## 7. Classificação de achados

- **Problema do candidato:** nenhum.
- **Limitação de interface (herdada, não defeito):** `summable_kpDampedConnectorUnrootedCoeff` exige a separação das **regiões de barreira** (`barrierRegion T s`, `barrierRegion ∅ r`, forma 52-A0), enquanto as cotas exigem `WalkBarrierSeparated s r n` + `T ∈ typedTouchingFamilies s` e derivam a primeira via 51-D. Duas formas de hipótese coexistem; quem consumir a somabilidade sozinha precisa fazer a mesma passagem (ou usar `(abs_…_le_eroded)` que já a embute). Sem impacto em 52-C.
- **Obrigação futura (fora de 52-C):** somas das duas colunas, orçamentos (1/2,3) e (7/8,1), capstone e constante da Pedra 52; para o construtor de 52-D, a cota termo-a-termo de Q9b mostra a forma que a coluna 1 assume.
- **Observações documentais:** §9.

## 8. Conclusões preliminares vs finais

`PRELIMINARY_CONCLUSIONS_first_pass.md` (registrado antes de abrir qualquer material do construtor) já apontava PASS com as mesmas reservas. A segunda passagem não alterou nada do parecer técnico.

## 9. Segunda passagem — comparação com o material do construtor (`c_out/`)

Concordâncias (verificadas, não copiadas): identificadores de custódia (commit, parent, trees, blobs, +569/−1, proveniência) — todos iguais aos meus; build limpo do construtor 580 s / 109 módulos / 0 erros / 114 warnings; sua lista de 113 pares arquivo:linha é **igual** à minha (a dele sem multiplicidades; a minha registra o par duplo `HolonomyHaar:198`); 13 certidões iguais; `print_axioms_all_109.log` sem sorryAx; os 4 testes negativos falham pelo motivo declarado (type mismatch; `unsolved goals` com `θ^(n+1) = 1` possível; placeholder `h1`; positivity em ℝ) e o positivo compila; a matriz de endpoints e a de testes são consistentes com o código. O relatório não reivindica nada além do gate.

Observações documentais (nenhuma toca o código):
- **D1.** `52-C_DECLARATION_INDEX.tsv`, coluna `hypotheses`, nas três cotas (linhas 401/487/521) lista só "KP (hβ,mχ,hχabs,hsmall)"; as declarações exigem também `hT`, `hsep` e `0 ≤ θ ≤ 1` (a `52-C_ENDPOINT_MATRIX.tsv` do próprio construtor os lista corretamente). Inconsistência entre duas tabelas do pacote.
- **D2.** `52-C_MODULE_DEPENDENCY_MAP.tsv` lista `dampedActivityCoreExponent_zero` e `regionActivityCoreExponent` como consumidos; o módulo não referencia nenhum dos dois (grep vazio). Superdeclaração inócua.
- **D3.** `postests/pos_c.log` tem 2 warnings de variável não usada (`hj`, `h1`) nos testes do construtor — não no módulo; o relatório diz "8 positivos (EXIT 0)", o que é verdade.

## 10. Pacote e HARD STOP

Conteúdo de `/home/claude/qa52c/out` (manifesto `SHA256SUMS_52-C-QA1.txt` sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (12 `.lean` + logs + 2 `attempt1`), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`.

Após este parecer: HARD STOP. Nenhuma correção dos itens D1–D3 foi feita (são do pacote do construtor, não do candidato); nenhum próximo gate iniciado; nenhuma escrita remota.
