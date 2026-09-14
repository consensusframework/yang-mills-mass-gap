# RELATÓRIO — FITA 53-QA1 (reprodução independente final da Pedra 53)

Auditor: Claude Fable 5.1 (instância QA com Lean; distinta da construtora/publicadora). Bancada própria em `/home/claude/qa53/wt` (worktree destacado no candidato; dependências pinadas já verificadas nas auditorias anteriores, `.lake/packages` reaproveitado; **nenhum olean Phase3 do construtor foi usado** — `.lake/build` apagado antes da reconstrução). Data: 2026-09-13 (UTC).

**Exposição prévia (exigida pela fita).** Auditei 52-A0, 52-A, 52-A-C1, 52-B, 52-C, 52-D e 52-E; a arquitetura da Pedra 53 está na fita e no `RELATORIO_53-L.md` anexo, lido antes da reconstrução. **Esta auditoria não é cega.** O que é independente: a reconstrução, a leitura das definições/assinaturas/provas reais, os testes próprios e o parecer, registrados em `PRELIMINARY_CONCLUSIONS_first_pass.md` **antes** de abrir logs e testes do construtor (abertura em §9).

Regime: somente leitura; zero edições no candidato; zero commit/push/PR/merge/tag/Release/Zenodo.

## 0. Parecer

**PASS NO ESCOPO.** Commit efetivamente reconstruído: `abad16674ab9b713c7ef9d0344c8f5cc02b09739` (root tree `0e156fc6…`, Phase3 `99758dfc…`). Reproduzida e verificada a estimativa

`|F(θ) − F(θ′)| ≤ |θ−θ′|·Cf·e^{−n/2}·[e^{8D_s/113} + e^{4D_s/113}] ≤ |θ−θ′|·(2Cf)·e^{8D_s/113}·e^{−n/2}`, `θ, θ′ ∈ [0,1]`, `F(θ) = activityDampedExpectation μm β χ f s r θ`, `D_s = card (supportLinkFinset s)`,

sob `0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ| ≤ 1`, `Measurable f`, `∀U, |f U| ≤ Cf`, `WalkBarrierSeparated s r n` — **sem `DependsOnlyOn f s`** (confirmado por `#check` do enunciado elaborado); `0 ≤ Cf` derivado; fator `|θ−θ′|` preservado, nada dividido por ele. 29/29 declarações em exatamente `[propext, Classical.choice, Quot.sound]`, 0 sorryAx, 113 módulos reconstruídos do zero, warnings herdados idênticos ao baseline, 0 nos módulos novos. Nenhum defeito matemático. Uma observação de **custódia** (proveniência fora do padrão da cadeia, §7) e precisões documentais. `F` foi tratado como o funcional com parâmetro `s`, sem pressupor que `s` seja suporte de `f`; a única identificação que exige `hf` é a de θ′ = 1 com Gibbs.

## 1. Custódia

| item | valor | verificação |
|---|---|---|
| ZIP | `stone53-L_candidate_abad166.zip` SHA-256 `e0ffb98c3f849cc410e48a829e7ec8c44cbb16e14e03a5f5848d245da230d3fe` | ✅ = fita; 29 arquivos sob `deliver/`, caminhos limpos |
| bundle interno | `stone53_abad166.bundle` SHA-256 `3f89198ccdf77deb9c9361d7a9b9713693f0163fa6f3ab2c2a2f4b98a956a369` | ✅ = fita; `git bundle verify` OK com a base presente; pré-requisito = base |
| manifesto do construtor | `SHA256SUMS_53-L.txt` | 25 entradas, sem auto-inclusão, 25/25 OK; fontes avulsas = blobs commitados (byte a byte); `SHA256_SOURCES.txt` = meus SHA das fontes no worktree |
| `origin/main` observada | `f4015c5c8e7376a924c3ec3ab3dc7c00097e6085` (fetch somente leitura, 2026-09-13) | = base obrigatória (merge do PR #27, docs); `Phase3/` da base `bf2fae8c…` = tree Phase3 do candidato 52-E auditado; blob 52-E `6b8514fd…` presente |
| candidato | `abad16674ab9b713c7ef9d0344c8f5cc02b09739` | exatamente 1 commit sobre a base; parent = base |
| trees | root `0e156fc6c53b5c6c27d71f1e3c589ea63be45f4a`; Phase3 `99758dfc339edf0e412133ca7f5826ecab45b56d` | ✅ = fita |
| blobs | Infrastructure `f5fc008c…` (555 linhas, 11 decl.); Lipschitz `34d88d7b…` (649 linhas, 18 decl.); lakefile `11f54d7d…` | ✅ = relatório do construtor |
| diff | A + A + M `Phase3/lakefile.toml` (2 globs ao final: 111 → 113); **+1205/−1** | ✅ |
| módulos anteriores / protegidos | 111 módulos byte-idênticos; workflow, docs, README, LICENSE, `lean-toolchain`, `lake-manifest.json`, `formalization.yaml`, Phase1/2: 0 alterações | ✅ |
| **proveniência** | autor e committer `Claude <noreply@anthropic.com>`, assinatura SSH, trailers `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` e `Claude-Session: …` | **FORA do padrão da cadeia 51/52** (`Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>` + `Co-authored-by: Claude <noreply@anthropic.com>`). Declarado pelo construtor (§6 do relatório dele). Não é defeito matemático; ver §7 |
| imports | Infrastructure ← `ActivityDampingColumnBounds`; Lipschitz ← Infrastructure + `ActivityDampingStability` | Lipschitz é folha; sem ciclo |

## 2. Reconstrução (bancada própria)

Toolchain `leanprover/lean4:v4.15.0` (Lean 11651562caae), Lake 5.0.0-1165156, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, `lake-manifest.json` SHA-256 `c376bbe9…1227` (pré = pós; não commitado, como em toda a cadeia). Comandos e durações em `environment.txt`, `build_directed.result`, `build_full_clean.result`.

**Dirigido** (`lake build LatticeGauge.ActivityDampingLipschitz`): exit 0, 280 s, 0 erros, 0 warnings nos módulos novos, 29 certidões, 0 sorryAx.

**Limpo completo** (`rm -rf .lake/build && lake build`, início `2026-09-13T22:19:07Z`): exit 0, 523 s, **113 módulos "Built", 0 "Replayed"** (sem reutilização de oleans Phase3), 0 erros, **114 warnings = 113 pares arquivo:linha com as mesmas multiplicidades do baseline** (diff vazio contra o baseline da QA 52-E, invariante desde 52-B), **0 warnings nos módulos novos** (meus testes: 0 warnings também), 0 sorryAx. Pureza: 113 `.olean` de `LatticeGauge`, todos posteriores ao início; 0 anteriores.

## 3. Axiomas e higiene

- Meu `#print axioms` das 29 declarações (U0): 29/29 exatamente `[propext, Classical.choice, Quot.sound]`; 0 sorryAx; nenhum axioma novo. `#check` do capstone: hipóteses `hβ mχ hχabs hsmall mf hCf hsep h0 h1 h0' h1'` — **sem `DependsOnlyOn`**.
- Léxico (`hygiene.txt`): em código, 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial`; 0 divisão por `(1−θ)` ou `|θ−θ′|`, 0 `⁻¹`. `Disjoint`, "volume", "monotonicity", "derivative", "mass gap", "(7/8, 2)", "8/(3e)" ocorrem só em docstrings que os negam ou explicam (o 8/(3e) fica interno ao lema 52-A0 `nat_le_exp_three_eighths`, absorvido por `≤ 1`; não aparece em nenhum enunciado).
- Dependências efetivamente consumidas (mapa de 79 identificadores, `hygiene.txt`): 52-B (`activityDampedExpectation_eq_sum_core_mul_exp`), 52-C (`summable_kpDampedConnectorUnrootedCoeff`, `dampedActivityCoreExponent_sub_full_eq_activityDampingConnector`, `kpDampedConnectorUnrootedCoeff`), 52-A0 (`summable_nat_mul_kpAbsConnector_polymerWeight`, `tsum_…_le_local_P`, `nat_le_exp_three_eighths`, `familyCard_le_familyTotalCard`, `sum_sevenEighthsTilt_one_le`), 52-A (`abstractKP_dampedActivity`, `abs_dampedActivity_le`, `touchCount*`, `activityDampedExpectation_one/_zero`, gases em r=∅), 52-D (`sevenEighthsBudgetTerm_nonneg`), 52-E (**apenas** `nonneg_of_abs_le_of_config`), 51-D (`walkBarrierSeparated_barrierRegions_sub_familyMass`, `abs_exp_sub_one_le_decay_exp`, `exp_neg_nat_sub_half_le`, `sum_halfTilt_three_le`, `halfTiltCoreBudgetTerm_eq`), 50 (`tsum_restricted_sub_full`, `summable_abs_kpForbiddenUnrootedCoeff`, `tsum_abs_kpForbiddenUnrootedCoeff_le`, `kpForbiddenRootEnvelope_le_barrierLinkCount`, `abs_typedMarkedCoreWeight_le_mayerCoreMajorant`, `prod_family_massTiltActivity`), 51-B/C (`activityAllowedCores/BridgeCores`, `sum_touchingFamilies_eq_activityAllowed_add_bridge`, `activityBridgeCore_familyTotalCard_ge`, `regionAllowed_eq_remoteAllowed_empty`). **O capstone 52 (`abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay`) aparece só em docstring (Lipschitz l. 511) e não é consumido pela prova principal** — a importação de `ActivityDampingStability` serve ao lema de não-negatividade de Cf, como a fita pede distinguir. `abs_kpDampedConnectorUnrootedCoeff_le`, `abs_activityDampingConnector_le_eroded`, `nat_card_mul_abs_normalizedMarkedCoreTerm_le_bridge` são citados só como "mirror" em docstrings.

## 4. Leitura integral e verificação (item 3 da fita)

- **Ledger direto, sinal MAIS nas pontes** (U1, rederivado por mim da representação 52-B `F(θ) = Σ_touching θ^t W e^{E(θ)}` aplicada aos dois lados): `F(θ) − F(θ′) = Σ_touching θ′^t W (e^{E(θ)} − e^{E(θ′)}) + Σ_bridge (θ^t − θ′^t) W e^{E(θ)}`; nos permitidos ambos os pesos são 1, por isso a correção fica suportada nas pontes. Sem `hf`, `mf`, `hCf`.
- **Bound direto do expoente amortecido, κ = 1** (Infrastructure l. 117–156): `|E_T(θ)| ≤ b_T·2/113` pela cadeia genérica da Pedra 50 (`S_P − S = −Σ' forbidden`, majorante de uma barreira, monotonia do envelope sob `|z_θ| ≤ |z|`, localização 2/113) transportada pelo KP amortecido 52-A; em θ = 1 devolve a cota do expoente pleno (U2a). É o ingrediente que mantém a coluna 2 em (7/8,1): a rota `N_f·e^{C}` custaria κ = 2 e (7/8,2) é inadmissível (`7/8 + 16/113 > 1`, provado em U2h).
- **Diferença de coeficientes, somabilidade, diferença de tsums** (l. 210–360): peso `θ′^{tc} − θ^{tc}`, `|θ^j − θ′^j| ≤ j|θ−θ′|` (re-provado por indução, U2b; falha fora de [0,1], U2b′), `tc ≤ k`; ambas as séries somáveis por 52-C (`Summable.of_norm`), `tsum_sub`, `norm_tsum_le_tsum_norm`, `tsum_le_tsum`, primeiro momento 52-A0. Em θ′ = 1 reduz-se exatamente a 52-C (U2c/U2d).
- **Erosão com subtração natural truncada** (l. 277–282, 359): `n − (m_T + 0)` em ℕ; `d = |θ−θ′|·e^{−((n−m_T:ℕ))/2} ≤ 1` (precisa de `|θ−θ′| ≤ 1`, l. 433–437; re-provado em U2f); m_T > n ⇒ fator 1.
- **Controle exponencial κ = 3** (l. 392–468): `e^{E(θ)} − e^{E(θ′)} = e^{E(θ′)}(e^{Δ} − 1)`, `Δ = C_θ − C_θ′` (U2e); `|e^Δ − 1| ≤ d·e^{2q′}`; `e^{E(θ′)} ≤ e^{q′}` ⇒ `e^{3q′}`; recompra `e^{−(n−m)/2} ≤ e^{−n/2}e^{m/2}`. U2f confere a contabilidade.
- **Coluna 1, orçamento (1/2,3)** (Lipschitz l. 151–269): `0 ≤ θ′^t ≤ 1`, `|W_T| ≤ Cf·ΠM` (sem exponencial), controle κ = 3 ⇒ `halfTiltCoreBudgetTerm β 3`; `sum_halfTilt_three_le` ⇒ `e^{4D·2/113} = e^{8D/113}`.
- **Coluna 2, orçamento (7/8,1)** (l. 276–404): `|θ^t − θ′^t| ≤ card T·|θ−θ′|`; primeiro momento amortecido κ = 1 (l. 478–541: `n ≤ m_T` paga `e^{−n/2}` com `e^{m/2}`, `card T ≤ m_T ≤ e^{3m/8}`, tilt 1/2 + 3/8 = 7/8, sem dupla cobrança); inclusão ponte ⊂ tocantes com somandos ≥ 0 (`sevenEighthsBudgetTerm_nonneg`); `sum_sevenEighthsTilt_one_le` ⇒ `e^{2D·2/113} = e^{4D/113}`.
- **Fator `|θ−θ′|` preservado** em todas as cotas; `Cf ≥ 0` derivado nas duas declarações finais (l. 426, 459) via `nonneg_of_abs_le_of_config` (52-E, `trivialConfig`).
- **Fechamento** (U3a, rederivado sem os dois teoremas finais): ledger + `abs_add` + os dois `|Σ|` ⇒ forma de dois termos ⇒ capstone (`e^{4D/113} ≤ e^{8D/113}` com `D ≥ 0`, fator comum `|θ−θ′|·Cf·e^{−n/2} ≥ 0`); casts `4D·2/113 = 8D/113`, `2D·2/113 = 4D/113`.
- **Hipóteses e constantes efetivamente elaboradas**: `#check` (U0) e as instanciações simbólicas (U3b) confirmam o conjunto acima e a ausência de `DependsOnlyOn`; typeclasses: `[NeZero N] [Fintype (Site N)] [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm]`.

## 5. Testes próprios (item 5 da fita)

`53_QA1_TEST_MATRIX.tsv`: U0–U4 positivos (exit 0, 0 warnings), U5x/U5y falhas esperadas. Cobertura: dois parâmetros simbólicos sem `DependsOnlyOn` (U3b); θ = θ′ pela **aplicação efetiva** do capstone (U4a; `lipschitz_bound_self` registrado como álgebra do RHS, U4a′); θ′ = 1 e identificação com Gibbs (U4b, derivação própria, `hf` entra aqui; igualdade de **tipo** entre o capstone 52 e a re-derivação 53, U4b′ — nada sobre igualdade de provas); θ′ = 0 e funcional restrito (U4c, sem `hf`); região vazia com θ = −7, θ′ = 42 (U4d, e derivação própria U4d′); forma de dois termos (U3b); recombinação do ledger com as cotas das colunas sem invocar os dois teoremas finais (U3a); ingredientes (U2). Classificação rigorosa: U5x (θ = 2) e U5y (sem `hf`) são **falhas de aplicação** (argumento inválido / ausente) — não provam indispensabilidade nem falsidade fora de [0,1]; falsidades demonstradas por contraexemplo: `|θ^j − θ′^j| ≤ j|θ−θ′|` fora de [0,1] (U2b′), orçamento (7/8,2) (U2h). Deslizes meus resolvidos autonomamente: U1 (rota `simp` sem progresso → rota explícita) e U2b′ (meu primeiro contraexemplo θ = 2, j = 2 era falso — `4 ≤ 4` vale — substituído por θ = 3); logs `attempt1` preservados. Nenhuma falha reclassificada como problema do candidato.

## 6. Matriz das 29 declarações

`53_QA1_DECLARATION_MATRIX.tsv`: 29 linhas, 29 PASS, com hipóteses explícitas efetivamente exigidas, dependências reais (por nome e Pedra) e teste que cobre cada uma.

## 7. Achados classificados

- **Defeito matemático:** nenhum.
- **Custódia / publicação (não matemático):** C1 — a proveniência do commit (`Claude <noreply@anthropic.com>`, assinatura SSH, trailers `Co-Authored-By: Claude Fable 5.1` + `Claude-Session`) difere do padrão adotado em toda a cadeia 51/52 (`Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>` + `Co-authored-by: Claude <noreply@anthropic.com>`), padrão que Sol exigiu em 51-A-C4. O construtor declara isso. Decisão cabe a Ju/Sol antes da publicação: aceitar como está (o objeto auditado é este commit) ou pedir ao publicador um commit com a identidade da cadeia (o que muda o hash e exigiria nova conferência de custódia — a matemática e os blobs não mudam).
- **Limitação de interface:** I1 — o capstone 52 e a re-derivação 53 (`…_le_of_lipschitz`) têm o mesmo enunciado; coexistem sem conflito. I2 — `activityDampedExpectation_one` (52-A) é a única porta para Gibbs e exige `hf`; qualquer consumidor que queira Gibbs precisa fornecê-la.
- **Precisões documentais:** D1 — o relatório do construtor diz "8 exemplos positivos"; o arquivo tem 9 `example`s (conferido). D2 — `lipschitz_bound_self` simplifica apenas o RHS; o teste efetivo de θ = θ′ é a aplicação do capstone (feita em U4a e, no construtor, em T5). D3 — a igualdade `rfl` entre a prova via 52-E e via 53 (teste T5 do construtor) é irrelevância de provas de um mesmo enunciado; não certifica igualdade de percursos. D4 — o construtor compilou Mathlib da fonte; a reprodução aqui usou a Mathlib pinada já verificada (mesmo commit e manifesto), como a fita permite.

## 8. Preliminar vs final

`PRELIMINARY_CONCLUSIONS_first_pass.md` (gravado antes de abrir logs/testes do construtor) já concluía PASS NO ESCOPO com C1, D1–D3. A segunda passagem acrescentou apenas D4 e as concordâncias de §9.

## 9. Segunda passagem — logs e testes do construtor (`deliver/`, abertos após §8)

Concordâncias verificadas: `stone53_commit.txt` (commit, parent, tree, autor/committer, mensagem) = objetos Git; `lake_build_clean.log` do construtor: 113 `LatticeGauge` Built, 0 Replayed de `LatticeGauge` (os 1332 "Replayed" e 4599 warnings do log dele são da Mathlib compilada da fonte — separados por filtro), 0 erros, 114 warnings de `LatticeGauge` com **os mesmos 113 pares** que os meus, 0 nos módulos novos, 0 sorryAx; `AXIOMS_53-L.txt`: 29 entradas, todas padrão; `test_positive.log`: 9 exemplos, 0 erros, 0 warnings; `test_negative.log`: falha em `⊢ False` de `2 ≤ 1`, como declarado. `RELATORIO_53-L.md` no ZIP = o enviado à parte. Divergências: só D1 (contagem).

## 10. Pacote e HARD STOP

`/home/claude/qa53/out` (manifesto `SHA256SUMS_53-QA1.txt`, sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (7 `.lean` + logs + 2 `attempt1`), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`. Nenhum bloqueio de execução.

HARD STOP: candidato intacto (worktree só com o `lake-manifest.json` gerado, não rastreado); nenhum push, PR, merge, tag, Release ou Zenodo; nenhum gate iniciado. Após PASS, o candidato segue intacto ao Code publicador — com a decisão sobre C1 a cargo de Ju/Sol.
