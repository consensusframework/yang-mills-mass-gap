# RELATÓRIO — FITA 55-QA1 (reprodução independente e auditoria final da Pedra 55)

Auditor: Claude Fable 5.1 (instância QA com Lean executável, distinta da construtora). Coordenação: Ju. Arquitetura e revisão: GPT Astra. Bancada própria em `/home/claude/qa55/wt` (worktree destacado no candidato; dependências materializadas pelo manifesto **versionado** `Phase3/lake-manifest.json`, 9/9 revisões conferidas contra `.lake/packages`, sem `lake update`; `.lake/build` do Phase3 apagado antes da reconstrução — **nenhum olean do construtor usado**). Data: 2026-09-17 (UTC).

**Exposição prévia (§1 da fita).** Auditei 52-A0…52-E, 53 e 54; a arquitetura da 55 está na fita (Astra); li o `RELATORIO_55-L.md` do construtor para identificar o alvo. **Não é auditoria cega.** Após a verificação de integridade do pacote, `logs/` e `tests/` do construtor ficaram fechados até a conclusão da reconstrução, dos testes próprios e das conclusões preliminares (`PRELIMINARY_CONCLUSIONS_first_pass.md`); comparação em §9.

Regime: candidato intacto; sem commit científico, push, PR, merge, tag, Release ou Zenodo; Pedra 56 não iniciada.

## 0. Veredito

**PASS NO ESCOPO, com observações documentais.** Commit reconstruído: `0c50b6d5e23915f13d6f36d560a58ba6f24ae97b` (root `e69c0fe9…`, Phase3 `20ffea86…`). Reproduzido e verificado, para `F(a) = profileExpectation μm β χ f s r a` (funcional polimérico normalizado da atividade regional `z_a(γ) = a(γ)·z(γ)` se γ toca r, `z(γ)` caso contrário), perfis `a, a′` com `∀γ, 0 ≤ a γ ≤ 1`, `0 ≤ δ` e `|a γ − a′ γ| ≤ δ` nos polímeros tocantes:

`|F(a) − F(a′)| ≤ δ·Cf·e^{−n/2}·[e^{6D_s/113} + e^{4D_s/113}] ≤ δ·(2Cf)·e^{6D_s/113}·e^{−n/2}`,

sob `0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ| ≤ 1`, `Measurable f`, `∀U, |f U| ≤ Cf`, `WalkBarrierSeparated s r n`, no contexto `[NeZero N] [Fintype (Site N)] [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm]` (conferido por `#check`). O capstone deriva `0 ≤ Cf`, **não** exige `DependsOnlyOn f s`, **não** exige `δ ≤ 1`, preserva o fator δ sem divisão, e mantém constante, taxa e regime da 54. Correção matemática: sem defeito. Execução: 116 módulos do zero, 0 replayed, 0 erros, 114 warnings herdados com texto idêntico ao baseline, 0 nos módulos novos, 68/68 certidões padrão, 0 sorryAx. Custódia: conforme. Documentação: cinco precisões registradas (§7), nenhuma matemática. O objeto é um funcional polimérico normalizado; nenhuma interpretação de perfil por link, condição de contorno ou nova medida de Gibbs é atribuída.

## 1. Custódia (conforme)

| item | valor | verificação |
|---|---|---|
| ZIP | `STONE55L_evidence.zip` SHA-256 `6867a61bdd879a4f2a348026e7c9a492fbc0a136ba449121484624047f1e4348` | ✅ = fita; 29 arquivos + 5 diretórios sob `deliver/`; caminhos limpos (sem `/` inicial nem `..`) |
| manifesto interno | `SHA256SUMS_55-L.txt` (SHA `d1f0ae6d…ea15` = relatório) | 28 entradas, sem auto-inclusão, **28/28 OK** |
| bundle | `stone55_0c50b6d5.bundle` SHA-256 `12c9870a561e1a9ec86a17bd6cd4a8c53f80d246d9934a5b779e9bd2491852d7` | ✅ = fita; o enviado à parte é byte-idêntico ao do ZIP; `git bundle verify` OK com a base presente; pré-requisito = base |
| relatório | `RELATORIO_55-L.md` SHA-256 `718773e4c17ed17f11a9a9482043cced33699c505b1d0249767686e73150a9c5` | ✅ = fita |
| `origin/main` observada | `bd2f6c1b0ad600b0282b4776859bb917466152ea` (fetch somente leitura, 2026-09-17) | = base (merge do PR #32 `stone54-maintenance`: versiona `lake-manifest.json` = blob `79049caf…`, SHA-256 `c376bbe9…1227`; CI resolvida por ele; docs 54). Entre o candidato 54 (`410bde8`) e a base **0 módulos de `LatticeGauge/` mudaram** |
| candidato | `0c50b6d5e23915f13d6f36d560a58ba6f24ae97b` | 1 commit sobre a base; parent único = base |
| trees | root `e69c0fe94d18b83f0664fdc42642358ef4f8e867`; Phase3 `20ffea86201c8a35d62479b2c0038f8c3e592de5` (base `2f3a5117…`, root base `f3822ea8…`) | ✅ = fita |
| blobs | A `dc85622b…` (923 linhas; 8 `noncomputable def`, 43 `theorem`, 43 `#print axioms`); B `6f12d160…` (999 linhas; 2 defs, 25 teoremas, 25 certidões); lakefile `e8852d40…` | ✅ = fita; fontes avulsas do ZIP byte-idênticas aos blobs |
| diff | A A M; +1923/−1; 2 globs ao final (114 → 116) | ✅ |
| preservação | 114 módulos anteriores byte-idênticos; pins (`lean-toolchain`, `lakefile` require), manifesto, `.github`, `docs/`, auditorias, README, `VERIFICATION_STATUS`, `formalization.yaml`, licenças, Phase1/2: 0 alterações | ✅ |
| proveniência | `Claude <noreply@anthropic.com>` (autor e committer), assinatura SSH, trailers `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` e `Claude-Session:` | = precedente aceito (53/54); registrado |
| imports | A ← `Mathlib`, `ActivityDampingLipschitzRefined`; B ← `Mathlib`, A | B é folha; sem ciclo |

## 2. Reconstrução (execução)

Bancada: `leanprover/lean4:v4.15.0` (Lean 11651562caae), Lake 5.0.0-1165156; manifesto versionado SHA-256 `c376bbe9…1227` **antes = depois**; 9/9 pacotes nas revisões do manifesto (mathlib `9837ca9d…`, plausible `2c57364e…`, LeanSearchClient `003ff459…`, importGraph `9a0b533c…`, proofwidgets `2b000e02…`, aesop `2689851f…`, Qq `f0c584bc…`, batteries `e8dc5fc1…`, Cli `0c8ea32a…`); `lake update` **não** executado (`environment.txt`, `manifest_pre/post_build.sha256`).

**Dirigido** (`lake build LatticeGauge.ActivityProfileDampingStability`): exit 0, 343 s, 0 erros, 0 warnings nos módulos novos, 68 certidões, 0 sorryAx.

**Limpo** (`rm -rf .lake/build && lake build`, início `2026-09-17T18:26:28Z`): exit 0, 644 s, **116 módulos "Built", 0 "Replayed"** (nem de `LatticeGauge`, nem de dependências), 0 erros, **114 warnings, todos de `LatticeGauge/`, 0 de dependências, 0 nos módulos novos**, 0 sorryAx, 247 certidões (179 + 68). Comparação de warnings com a base **em texto integral** (`arquivo:linha:coluna: warning: mensagem`; normalização explícita: a regex de extração `LatticeGauge/[^:]+\.lean:...` descarta o prefixo `./././` em ambos os lados): diff vazio contra o baseline da QA 54. Pureza: 116 `.olean`, 0 anteriores ao início.

## 3. Axiomas, higiene, dependências

- Meu `#print axioms` dos **68 teoremas** (W0; lista = os 68 nomes `theorem` dos dois módulos, cobertura conferida): 68/68 exatamente `[propext, Classical.choice, Quot.sound]`; 0 sorryAx; nenhum axioma novo. `#check` do capstone e da forma de dois termos: hipóteses como em §0; **sem `DependsOnlyOn`, sem `δ ≤ 1`**.
- Léxico (`hygiene.txt`): em código, 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial`, 0 divisão por δ, 0 `⁻¹`; `Disjoint`, "volume", "per-link", "boundary", "monotonicity", "differentiability", "mass gap" só nos cabeçalhos, negados.
- Dependências reais (mapa de 104 identificadores, `hygiene.txt`): de 54 apenas os helpers `abs_exp_sub_exp_le_exp_mul_abs_sub`, `le_exp_self` (e, via 54, `sum_halfTilt_two_le`); de 52-E `nonneg_of_abs_le_of_config`; de 53-A a rota genérica da barreira (`tsum_restricted_sub_full`, `tsum_abs_kpForbiddenUnrootedCoeff_le`, `kpForbiddenRootEnvelope_mono/_le_barrierLinkCount`); de 52-A0 os primeiros momentos e `nat_le_exp_three_eighths`; de 52-A/C `dampedActivity_one/_zero`, `kpDampedConnectorUnrootedCoeff(_one)`, `activityDampingConnector`, `activityDampedExpectation_one/_zero`, gases; de 51-D erosão, `halfTiltCoreBudgetTerm_eq`, `exp_neg_nat_sub_half_le`; de 50 `typedPolymerGas_eq_exp_tsum_of_KP`, `typedPolymerGas_ratio_eq_exp_sub`, `typedPolymerGas_restricted_eq_sum_allowed`, `markedRawFamilyWeight_rawFamily`, `abstractKP_mono`. **O capstone 54 (`…_le_local_exp_decay_refined`) aparece só em docstring (B l. 902) e não é usado na prova geral**; `abs_activityDampingConnector_sub_le_eroded` só como "mirror" (B l. 284). Importar a 54 não implica usar seu capstone — conferido.

## 4. Escopo matemático e pontos centrais (§§4–5 da fita), lidos integralmente e verificados

**Pesos e representação.** Dominação `|z_a| ≤ |z|` para `0 ≤ a ≤ 1` (A l. 135–144); transporte KP por `abstractKP_mono` (l. 148–153); gás `= exp(Σ' coeficientes)` por `typedPolymerGas_eq_exp_tsum_of_KP` e positividade como consequência (l. 510–529); razão pela identidade publicada `typedPolymerGas_ratio_eq_exp_sub`, sem cancelamento de denominador (l. 533–548); fibração do numerador (l. 610–765) com o split de produto `A_Γ = A_T·A_R` (`Finset.prod_filter_mul_prod_filter_not`) e a bijeção fibra ↔ famílias remotas permitidas, fechando com `∏ z_a = A·∏ z` (`prod_profileDampedActivity`). Identidades literais de peso para famílias e tuplas (repetições por posição: W1b — `![η,η]` tem peso `a η²` e contagem 2). Telescópica `|∏x − ∏y| ≤ Σ|x−y|` em [0,1] por indução em Finset, chave `xP − yQ = x(P−Q) + (x−y)Q` (l. 239–273); testada com produto vazio, fator zero e prova própria a dois fatores; falha fora de [0,1] (W1e/e′).

**Ledger.** Rederivado por mim a partir de `profileExpectation_eq_sum_core_mul_exp` aplicado aos dois lados, **sem** `profileExpectation_sub_eq_two_column_ledger` (W2a): `F(a) − F(a′) = Σ_tocantes A′_T W_T (e^{E(a)} − e^{E(a′)}) + Σ_pontes (A_T − A′_T) W_T e^{E(a)}`, sinal MAIS nas pontes, orientação `a → a′`, correção nula nos núcleos permitidos (`A_T = A′_T = 1`, `profileWeight_eq_one_of_mem_activityAllowedCores`).

**Controle analítico.** `E_T(a) − E_T(cheio) = C(a)` (B l. 228–261; quatro séries somáveis por KP transportado; inclusão–exclusão por coeficiente com filtro inserido só pela implicação `TupleAllowed (regionAllowed r) → tc = 0 → A_δ = 1`, sem recíproca, sem hipótese em a); consistência com 52-C no perfil constante (W3a′). Diferença de conectores `|c_k(a) − c_k(a′)| ≤ δ·k·A_k` pela contagem de posições (l. 128–164); somabilidade pelo primeiro momento 52-A0 com a dominação a um perfil contra o unitário (δ = 1; l. 168–223); erosão `n − familyTotalCard T` truncada em ℕ antes do cast (l. 295, 379), m_T > n ⇒ `δ·q_T` (W3e); barreira do expoente κ = 1 (A l. 553–588, rota 53-A.3); controle bilateral da 54 com κ = 2 (B l. 389–456) — rederivado (W3b); orçamentos (1/2,2) e (7/8,1), (7/8,2) inadmissível (provado, W3c); sem 8/(3e) (interno a 52-A0).

**Fechamento.** Rederivado pelas colunas até dois termos e capstone **sem** os dois teoremas finais (W3d): ledger + `abs_add` + `abs_sum_profileConnectorColumn_le` + `abs_sum_profileBridgeColumn_le` ⇒ `δ·Cf·e^{−n/2}(e^{6D/113} + e^{4D/113})` ⇒ `δ·2Cf·e^{6D/113}·e^{−n/2}` com `e^{4D/113} ≤ e^{6D/113}`, `K ≥ 0`, `Cf ≥ 0` derivado.

## 5. Testes próprios (§6 da fita)

`55_QA1_TEST_MATRIX.tsv`: W0–W4 positivos (exit 0, 0 warnings), W5x falha esperada. Cobertura pedida: perfis não constantes, famílias e tuplas com repetição (W1a–c); aplicação efetiva do capstone com δ = 0 ⇒ `F(a) = F(a)` (W4a); perfis coincidentes nos tocantes e diferentes fora ⇒ `F(a) = F(a′)` — pelo capstone com δ = 0 **e**, independentemente, pela igualdade literal das atividades (W4b/b′); δ = 7 (W4c); recuperação escalar da 54 por especialização própria + 54 retipado (W4d); perfil zero → funcional restrito, sem `hf` (W4e); perfil unitário → Gibbs, com `hf` entrando só por `profileExpectation_one` (W4f); região vazia para perfis reais **não constantes e fora de [0,1]** (`card + 3` vs `−5`) pela identidade publicada, sem extrapolar o capstone (W4g); erosão com m_T > n (W3e); fechamento independente pelas colunas (W3d). W5x (perfil com valor 2): falha de aplicação — não falsidade nem indispensabilidade. Sem `rfl` entre provas. Deslize meu: W4f (goal não β-reduzido), corrigido; `attempt1` preservado.

## 6. Matriz das declarações

`55_QA1_DECLARATION_MATRIX.tsv`: 78 linhas (68 teoremas + 10 definições), módulo, tipo, linha, certificado próprio, teste/leitura que cobre cada uma; 78 PASS.

## 7. Achados classificados

- **Matemática:** nenhum defeito.
- **Execução:** conforme (§2); nenhum bloqueio.
- **Custódia:** conforme (§1).
- **Documentação (registrar para consolidação; candidato não editado):**
  - D1 — `profile_bound_self` (B l. 893) simplifica apenas o RHS com δ = 0; a aplicação efetiva do capstone com δ = 0 está comprovada por W4a/W4b (e pelo V3 do construtor, l. 21).
  - D2 — "KP as OUTPUT" (A l. 37 e docstring de `profilePolymerGas_pos`, l. 522): o critério KP é **estabelecido** (`abstractKP_of_beta_le_one_div_40000`) e **transportado** (`abstractKP_profileDampedActivity`) e é ele que alimenta a representação exponencial; a positividade do gás é consequência dessa representação. A frase deve ser lida assim; não afeta a prova.
  - D3 — o cabeçalho A (l. 45–46: "constant-profile specializations (definitional identities)") mistura casos: `profileDampedActivity_const`, `profilePolymerGas_const`, `profileCoreExponent_const` são `rfl`; `profileWeight_const`, `tupleProfileWeight_const`, `profileMarkedGas_const`, `profileExpectation_const` são teoremas por reescrita. A tabela do relatório do construtor já distingue corretamente.
  - D4 — o teste V3 do construtor (l. 60) registra `rfl` entre `…_of_profile` e `…_refined` como irrelevância de provas, não como igualdade de derivações — correto e assim anotado no próprio teste.
  - D5 — perfil zero recupera o funcional restrito da 51 sem hipótese (`profileExpectation_zero`); a comparação com Gibbs exige `DependsOnlyOn` (`profileExpectation_one`, `abs_profileExpectation_sub_gibbsExpectation_le`) — conferido (W4e/f).
- **Interface:** I1 — `import CovarianceDecay` herdado de 54 para o wrapper `sum_halfTilt_two_le` (já observado na QA 54); nada novo.

## 8. Preliminar vs final

`PRELIMINARY_CONCLUSIONS_first_pass.md` já concluía PASS NO ESCOPO com D1–D5 e I1. A segunda passagem confirmou D4 no teste V3 e acrescentou as concordâncias de §9.

## 9. Segunda passagem — logs e testes do construtor (abertos após §8)

`stone55_commit.txt`/`stone55_diffstat.txt` = objetos Git e meu diff. `logs/lake_build_clean.log` (17:14:00Z → 17:27:27Z, exit 0): 116 `LatticeGauge` Built, 0 Replayed de `LatticeGauge` (os 1332 "Replayed" e 4599 warnings restantes são da Mathlib compilada da fonte na bancada dele — distinguidos por filtro), 0 erros, 114 warnings de `LatticeGauge` com **texto idêntico** aos meus, 0 nos módulos novos, 0 sorryAx, 247 certidões; `manifest_before.sha256` = c376bbe9…; a lista `warnings_candidate_clean.txt` do construtor coincide com a sua `warnings_base_run490.txt` após remoção do prefixo. `buildA.log`/`buildB.log`: 0 erros, 0 warnings nos módulos novos, 43/68 certidões. `tests/results.txt`: V1–V4 exit 0; logs com 0 erros e 0 warnings; V3 contém a aplicação efetiva com δ = 0 (l. 21) e o `rfl` documentado (l. 60). `55_DECLARATION_MATRIX.tsv`: 78 linhas (10 definições, 68 teoremas) — conferida contra minha matriz gerada das fontes. Divergências: nenhuma além das precisões documentais já registradas.

## 10. Pacote e HARD STOP

`/home/claude/qa55/out` (manifesto `SHA256SUMS_55-QA1.txt`, sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (6 `.lean` + logs + 1 `attempt1`), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`.

HARD STOP: candidato intacto (worktree limpo — o manifesto agora é versionado); nenhum commit científico, push, PR, merge, tag, Release ou Zenodo; Pedra 56 não iniciada.
