# RELATÓRIO — FITA 52-D-QA1 (auditoria independente das duas colunas)

Auditor: Claude Fable 5.1 (instância QA, segunda instância; não é a construtora). Bench próprio em `/home/claude/qa52d/wt` (worktree destacado no candidato), Lean 4.15.0 (11651562caae), Lake 5.0.0, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, `lake-manifest.json` SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227` (pré = pós). Data: 2026-09-11 (UTC).

Regime: somente leitura; zero edições no candidato; zero commit/amend/push/PR/merge/tag/release; testes descartáveis fora da árvore (`out/tests`, `lake env lean`). O parecer foi formado pelo código e pelas dependências (registro em `PRELIMINARY_CONCLUSIONS_first_pass.md`) ANTES de abrir relatório, matrizes, testes e logs do construtor (§9).

## 0. Veredito

**PASS.** O candidato `6168e2336495a968e4c74005b61d7e33e5f1cb76` estima separadamente as duas colunas exatas do ledger 52-B, com o fator `(1 − θ)` preservado e sem divisão por ele: coluna 1 (todos os núcleos tocantes) `≤ (1−θ)·Cf·e^{−n/2}·e^{8D_s/113}` via fatoração 52-C + normalização + controle exponencial recomprado + orçamento (1/2, 3), κ = 3; coluna 2 (as pontes do ledger) `≤ (1−θ)·Cf·e^{−n/2}·e^{4D_s/113}` via `1−θ^t ≤ card T·(1−θ)`, primeiro momento de pontes 52-A0 (onde `n ≤ m_T` paga `e^{−n/2}`) e orçamento (7/8, 1). Somas de módulos e módulos de somas; endpoints θ = 1, θ = 0, r = ∅ corretos; 15/15 declarações em `[propext, Classical.choice, Quot.sound]`; build limpo verde, 0 warnings no módulo, 114 herdados idênticos ao baseline. Nenhum defeito. Duas observações documentais e uma observação de interface (§7, §9). Este parecer **não** certifica o capstone nem a combinação das colunas (52-E), que aqui não foram implementados.

## 1. Custódia e identificadores

| item | valor | verificação |
|---|---|---|
| tarball | `STONE52-D-L_evidence.tgz` SHA-256 `ffa1389bd7fe5cb526c5bc73000742daa7178bb2087de63f00e0f14ae8a28612` | ✅ = fita; 30 entradas sob `d_out/`, caminhos limpos |
| bundle | `stone52-d_6168e23.bundle` SHA-256 `cd06af10871ff2b2e9ed5fb002de4f493a8dac620f9dfd7fdd6f8da6c0cdea8c` | ✅ = fita; `git bundle verify` OK; pré-requisito = base |
| base | `2708eb9f33fe1cfc3a439c3f0a97217ce13ebd2d` | = `origin/main` observada por fetch somente leitura (merge do PR #23); tree `359ac922…` e `Phase3/` `194fac1c…` = os do candidato 52-C auditado (`6502ca9`); blob 52-C `5b372d5b…` presente |
| candidato | `6168e2336495a968e4c74005b61d7e33e5f1cb76` | exatamente 1 commit sobre a base (`rev-list --count` = 1); parent = base |
| tree / Phase3 | `226e85bad5da2822cd72798d650a4197715f2273` / `37ea02e6a47a2a35e8c668889ea1ea3455cd9e04` | ✅ = fita |
| blob do módulo | `38e61d23700538651874fe788dda3d9160236abf`, 484 linhas, 15 declarações | ✅ = fita; cópia `d_out/ActivityDampingColumnBounds.lean` byte-idêntica |
| blob do lakefile | `8d901f3784ca9b5d3219bdcfc05644ccd929c64f` | 1 glob acrescentado ao final (109 → 110) |
| diff | A `Phase3/LatticeGauge/ActivityDampingColumnBounds.lean` (+484), M `Phase3/lakefile.toml` (+1/−1); 2 arquivos, +485/−1 | ✅ |
| módulos anteriores | 109 blobs byte-idênticos (só 1 caminho alterado em `LatticeGauge/`, o novo) | ✅ |
| protegidos | workflow, README, docs, LICENSE, `lean-toolchain`, `lake-manifest.json`, `formalization.yaml`, `VERIFICATION_STATUS`, Phase1, Phase2 | 0 alterações |
| proveniência | autor e committer `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>`; trailer `Co-authored-by: Claude <noreply@anthropic.com>` | padrão da cadeia |
| mensagem | `feat: bound the two columns of the damping ledger for Stone 52`; declara explicitamente "no combination of the two columns; no (7/8, 3); no 8/(3e); the Stone 52 capstone is not claimed" | conforme |

Manifesto do construtor `SHA256SUMS_52-D-L.txt`: 24 entradas, sem auto-inclusão, 24/24 OK.

## 2. Build

**Dirigido** (`lake build LatticeGauge.ActivityDampingColumnBounds`): exit 0, 312 s, 0 erros, 0 warnings no módulo, 0 sorryAx.

**Limpo completo** (`rm -rf .lake/build && lake build`, início `2026-09-11T20:22:00Z`): exit 0, 786 s, **110 módulos "Built", 0 "Replayed"**, 0 erros, **114 warnings = 113 pares arquivo:linha com as mesmas multiplicidades do baseline** (diff vazio contra o baseline reconstruído na QA 52-C, que por sua vez era idêntico ao de 52-B), 0 warnings no módulo, 0 sorryAx. Pureza: 110 `.olean` de `LatticeGauge`, todos posteriores ao início; 0 anteriores. Manifesto pré = pós. (Nota de leitura de log: um `grep ColumnBounds.lean` casa também `ActivityRestrictionColumnBounds.lean` de 51-D; as 14 certidões do candidato foram separadas por nome.)

## 3. Axiomas, higiene, dependências

- Certidões no módulo: 14 linhas, todas `[propext, Classical.choice, Quot.sound]`. **Meu** `#print axioms` das **15** declarações (R0), incluindo `sevenEighthsBudgetTerm_nonneg` (ausente da lista interna): 15/15 limpas, 0 sorryAx.
- Léxico (`hygiene.txt`): 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial`; 0 divisão por `(1 − θ)`; `Disjoint`, "volume", `8/(3e)`, `(7/8, 3)` aparecem apenas no cabeçalho, que os **nega** (HARD HOLD); o único outro hit de "card r" é `touchCount_le_card r T` (nome de lema, falso positivo do grep). Nenhum limite de tamanho de r; peso sempre `θ^{touchCount}` com `touchCount` = card de filtro (R1d), nunca indicador booleano.
- Import único: `LatticeGauge.ActivityDampingConnector` (52-C). Módulo folha; sem ciclo.
- Mapa identificador → módulo (48 identificadores locais, `hygiene.txt`): 52-C (`exp_full_sub_exp_damped_eq_activityDampingConnector`, `abs_one_sub_exp_activityDampingConnector_le_decay`), 51-D (`typedMarkedCoreWeight_mul_exp_full_eq_normalizedMarkedCoreTerm`, `sum_halfTilt_three_le`), 50/51-D `CovarianceNormalizedColumns` (`abs_normalizedMarkedCoreTerm_le`, `halfTiltCoreBudgetTerm(_eq)`), 52-A0 (`nat_card_mul_abs_normalizedMarkedCoreTerm_le_budgetTerm`, `sum_sevenEighthsTilt_one_le`, `dampedPow_*`, `one_sub_dampedPow_*`), 52-A (`touchCount*`, `pow_touchCount_eq_one_of_mem_activityAllowedCores`, `touchCount_pos_of_mem_activityBridgeCores`), 51-B/C (`activityAllowedCores`, `activityBridgeCores`, `sum_touchingFamilies_eq_activityAllowed_add_bridge`), 52-B (ledger e endpoints do expoente). `activityBridgeCore_familyTotalCard_ge` é citado só em docstring (consumido indiretamente dentro do lema 52-A0). **Nenhum** uso de 51-E, `CovarianceDecay`, capstone. Nenhuma hipótese contém a conclusão; sem circularidade.

## 4. Matemática — os nove pontos da fita (verificados pelas definições e por testes próprios)

1. **Ligação literal ao ledger 52-B** (R1). A coluna 1 estimada é indexada por `typedTouchingFamilies s` (TODOS os núcleos tocantes) e a coluna 2 por `activityBridgeCores s r` (a família de pontes do ledger). Do teorema 52-B `gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger` derivei diretamente `gibbs − damped − col2 = col1` com a expressão **exata** que o módulo estima (R1a). `ledger_columns_are_the_estimated_sums` é o próprio termo de prova de 52-B (R1b). Nenhuma família menor substitui a coluna real.

2. **Coluna 1** (R2; leitura das linhas 67–145). Fatoração 52-C com a orientação do ledger `e^{E1} − e^{Eθ} = e^{E1}(1 − e^{C})`; normalização `W_T·e^{E_T(1)} = N_f(s,T)` (51-D) e `|N| ≤ Cf·e^{b_T·2/113}·ΠM`; `0 ≤ θ^t ≤ 1` dominado por 1 (nunca dividido); controle 52-C na forma recomprada `|1−e^C| ≤ (1−θ)e^{−n/2}e^{m_T/2 + 2b_T·2/113}`. Contabilidade: `e^{b·2/113}·e^{m/2+2b·2/113} = e^{m/2+3b·2/113}` = `halfTiltCoreBudgetTerm β 3 s T` (por `halfTiltCoreBudgetTerm_eq`) ⇒ custo exponencial total **κ = 3**, tilt de massa **λ = 1/2**. Orçamento (1/2, 3) admissível (`1/2 + 3·8/113 = 161/226 ≤ 1`, R2e) e é o consumido (`sum_halfTilt_three_le`).

3. **Alvo coluna 1** (R3). `Σ_T |θ^t W (e^{E1} − e^{Eθ})| ≤ (1−θ)·Cf·e^{−n/2}·e^{8D_s/113}` (retipado com `4·D·2/113 = 8D/113`); `|Σ| ≤ Σ|·|` rederivado por `Finset.abs_sum_le_sum_abs`; com o ledger: `|gibbs − damped − col2| ≤` mesma cota (coluna 2 deixada intacta — não é o capstone).

4. **Coluna 2** (R4; linhas 219–272). `0 ≤ 1−θ^t ≤ t(1−θ) ≤ card T·(1−θ)` re-provado com `one_sub_dampedPow_le_nat_mul_one_sub` + `touchCount_le_card`. Dependência efetivamente usada: `nat_card_mul_abs_normalizedMarkedCoreTerm_le_budgetTerm` (52-A0), retipada: exige `T ∈ activityBridgeCores s r` e `WalkBarrierSeparated s r n`. Li a sua prova: **dentro** dela a geometria de ponte `n ≤ m_T` (`activityBridgeCore_familyTotalCard_ge`) paga `e^{−n/2}` com `e^{m_T/2}` (metade da massa) e `card T ≤ m_T ≤ e^{3m_T/8}` (via `(8/(3e))·e^{3m/8}` absorvido por `8/(3e) ≤ 1` — o 8/(3e) fica **interno** a 52-A0 e não aparece na conclusão nem no candidato) custa os 3/8 restantes ⇒ tilt 7/8 (R4c: `1/2 + 3/8 = 7/8`). A massa não é paga duas vezes (uma só recompra `e^{m/2}`); o fator de contagem `card T` vem de `t ≤ card T` e é consumido pelo primeiro momento — não se perde.

5. **Extensão pontes → tocantes** (R5). `activityBridgeCores s r ⊆ typedTouchingFamilies s` (`filter_subset`); majorante `e^{b_T·2/113}·Π massTilt(7/8)` ≥ 0 (prova própria); `Finset.sum_le_sum_of_subset_of_nonneg`. Orçamento **exclusivamente** (7/8, 1): admissível (`7/8 + 8/113 = 855/904 ≤ 1`); (7/8, 3) é **inadmissível** (`7/8 + 24/113 > 1`, provado em R5c), logo não pode ter sido usado; `coreLocalBudget` retipado com `lam + κ·(8/113) ≤ 1` como única condição.

6. **Alvo coluna 2** (R6). `Σ_ponte |(1−θ^t) W e^{E1}| ≤ (1−θ)·Cf·e^{−n/2}·e^{4D_s/113}` (retipado com `2·D·2/113 = 4D/113`); `|Σ|` rederivado; com o ledger: `|gibbs − damped − col1| ≤` mesma cota (coluna 1 intacta).

7. **Hipóteses** (R7, R9). Estimativas: KP (`0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ| ≤ 1`), `Measurable f`, `0 ≤ Cf`, `∀U, |f U| ≤ Cf`, `WalkBarrierSeparated s r n`, `0 ≤ θ ≤ 1`, e nos termos a pertinência (`typedTouchingFamilies` para a coluna 1; `activityBridgeCores` para a 2). **Não** exigem `DependsOnlyOn f s` (instanciadas com `f` arbitrário, R7a/b). O ledger exige `hf : DependsOnlyOn f s` e **não** exige `hCf0` nem `hsep` (R7c). Sem `Disjoint s r`, sem limite de r, sem fator de volume nas assinaturas. R7x (θ = 2) registrado como **falha de aplicação**, não como prova de indispensabilidade. R9: `hCf0` é **derivável** de `hCf` (Config N G é habitado; `0 ≤ |f U| ≤ Cf`) — logo é convenção de interface (uniforme com 51-D), não necessidade matemática.

8. **Endpoints** (R8). θ = 1: ambos os termos 0 termo a termo e as somas 0 (derivado), sem divisão por `1−θ`; as cotas continuam aplicáveis em θ = 1 com RHS `0·…` (R8a'). θ = 0: `0^0 = 1` nos núcleos permitidos (`touchCount = 0`) e `0^t = 0` nas pontes (`touchCount > 0`, `touchCount_pos_of_mem_activityBridgeCores`); a coluna 1 reduz-se **à coluna permitida da Pedra 51** (`Σ_allowed W(e^{E1} − e^{E_region})`) e a coluna 2 à coluna ponte da 51; consistência **literal** com o ledger θ = 0 de 52-B (`gibbsExpectation_sub_activityRestrictedExpectation_eq_damping_ledger_zero`, R8c); a cota 52-D em θ = 0 dá para a coluna permitida da 51 a **mesma constante** de 51-D `e^{−n/2}·Cf·e^{4D·2/113}` (R8d). r = ∅: ambos os termos 0, somas 0, e `activityBridgeCores s ∅ = ∅` (prova própria, R8e').

9. **Ausências** (§3): `Disjoint s r`, fator de volume, limite de tamanho de r, indicador booleano, 8/(3e), (7/8, 3) — nenhum no código; os nomes só aparecem no cabeçalho como HARD HOLD.

## 5. Matriz das 15 declarações

`52-D_QA1_DECLARATION_MATRIX.tsv`: 15 linhas, 15 PASS, hipóteses efetivamente exigidas por declaração, teste(s) próprio(s) que a cobre(m).

## 6. Testes próprios

`52-D_QA1_TEST_MATRIX.tsv`: 11 arquivos — 10 positivos (exit 0, sem output), 1 EXPECT_FAIL (R7x, exit 1, `⊢ False` de `2 ≤ 1`; falha de aplicação). Contraexemplo/impossibilidade provada: (7/8, 3) inadmissível (R5c). Nenhum deslize tático nesta rodada; nenhuma falha reclassificada como problema do candidato.

## 7. Classificação de achados

- **Defeito do candidato:** nenhum.
- **Limitação de interface:** (I1) `hCf0 : 0 ≤ Cf` é redundante (derivável de `hCf`, R9); mantida por uniformidade com as assinaturas de 51-D/`CovarianceNormalizedColumns`. Inócua; um consumidor futuro pode fornecê-la com `le_trans (abs_nonneg _) (hCf _)`.
- **Obrigação futura (52-E):** combinação `|gibbs − damped| ≤ (1−θ)·Cf·e^{−n/2}·(e^{8D_s/113} + e^{4D_s/113})` via `ledger_columns_are_the_estimated_sums` + `abs_add` + as duas cotas de módulo-da-soma; e a constante da Pedra 52. Não implementado aqui, por instrução.
- **Observações documentais:** D1 — a lista interna de `#print axioms` tem 14 entradas; `sevenEighthsBudgetTerm_nonneg` não está nela (coberta por R0). D2 — em `52-D_TEST_MATRIX.tsv` do construtor, D-NEG-1 (`hCf0`) e D-NEG-4 (`h1`) recebem a classe "application failure (hypothesis genuinely required)": a primeira metade está certa; o parêntese é uma inferência que a fita proíbe extrair de uma falha de aplicação — e, no caso de `hCf0`, é factualmente inexata (R9).

## 8. Conclusões preliminares vs finais

`PRELIMINARY_CONCLUSIONS_first_pass.md` (registrado antes de abrir o material do construtor) já concluía PASS com a mesma leitura matemática. A segunda passagem acrescentou apenas R9 e as observações D1–D2/I1; nada alterou o parecer técnico.

## 9. Segunda passagem — comparação com o material do construtor (`d_out/`)

Concordâncias verificadas: identificadores de custódia (commit, parent, trees — a tree da base `359ac922…` é de fato a do merge `2708eb9`, igual à de `6502ca9` —, blobs, +485/−1, proveniência); build limpo do construtor 592 s / 110 Built / 0 Replayed / 0 erros / 114 warnings; os 113 pares arquivo:linha dele são **iguais** aos meus; 14 certidões; `print_axioms_all_110.log` (130 certidões, 0 sorryAx); `52-D_DECLARATION_INDEX.tsv` tem 15 linhas com assinaturas completas e axiomas por declaração (inclui `sevenEighthsBudgetTerm_nonneg`) — conferido contra as assinaturas do módulo; `52-D_MODULE_DEPENDENCY_MAP.tsv` marca corretamente `activityBridgeCore_familyTotalCard_ge` como "docstring-only" e coincide com meu mapa; `52-D_ENDPOINT_MATRIX.tsv` consistente com o código; 6 testes positivos compilam (0 warnings) e os 4 negativos falham pelo motivo declarado. O relatório do construtor não reivindica capstone nem combinação. Discordâncias: só D2 acima (redação da classificação), sem impacto no código.

## 10. Pacote e HARD STOP

`/home/claude/qa52d/out` (manifesto `SHA256SUMS_52-D-QA1.txt`, sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (11 `.lean` + logs), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`.

HARD STOP após este parecer: nenhuma alteração no candidato, nenhum commit, nenhuma escrita remota, capstone/combinação não implementados, próximo gate não iniciado.
