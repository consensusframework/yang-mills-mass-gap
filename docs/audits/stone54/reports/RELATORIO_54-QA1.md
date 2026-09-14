# RELATÓRIO — FITA 54-QA1 (auditoria e reprodução independente única da Pedra 54)

Auditor: Claude Fable 5.1 (instância QA com Lean; distinta do construtor). Coordenação: Ju. Arquitetura: GPT Astra. Bancada própria em `/home/claude/qa54/wt` (worktree destacado no candidato; Mathlib pinada da própria bancada, revisão verificada; `.lake/build` do Phase3 apagado antes da reconstrução — **nenhum olean do construtor usado**). Data: 2026-09-14 (UTC).

**Exposição prévia (§2 da fita).** Auditei 52-A0…52-E e 53; a arquitetura da 54 está nesta fita (Astra); li o `RELATORIO_54-L.md` do construtor antes de reconstruir. **Não é auditoria cega.** Leitura, testes próprios e conclusões preliminares (`PRELIMINARY_CONCLUSIONS_first_pass.md`) foram registrados **antes** de abrir `logs/` e `tests/` do construtor (abertos em §9).

Regime: candidato intacto; nenhum push, PR, merge, tag, Release ou Zenodo; Pedra 55 não iniciada.

## 0. Parecer

**PASS com observação documental.** Commit reconstruído: `410bde8146e8f14b698a03387da395a79f81f9eb` (root tree `eaffdb13…`, Phase3 `7d8373f6…`). Verificados e reproduzidos:

`|F(θ)−F(θ′)| ≤ |θ−θ′|·Cf·e^{−n/2}·[e^{6D_s/113} + e^{4D_s/113}] ≤ |θ−θ′|·(2Cf)·e^{6D_s/113}·e^{−n/2}`, `θ,θ′ ∈ [0,1]`,

com `F(θ) = activityDampedExpectation μm β χ f s r θ`, `D_s = card (supportLinkFinset s)`, sob **exatamente** as hipóteses do capstone 53 (conferido por `#check` lado a lado: KP `0≤β≤1/40000`, `Measurable χ`, `|χ|≤1`, `Measurable f`, `∀U, |f U| ≤ Cf`, `WalkBarrierSeparated s r n`, `0≤θ,θ′≤1`; **sem `DependsOnlyOn`**; `0 ≤ Cf` derivado; nenhuma hipótese de sinal; nada dividido por `|θ−θ′|`; intervalo e taxa 1/2 inalterados). Correção matemática: sem defeito. Execução: 114 módulos do zero, 0 replayed, 0 erros, 114 warnings herdados com texto idêntico ao baseline, 0 no módulo novo, 13/13 certidões padrão, 0 sorryAx. Custódia: conforme. Documentação: uma imprecisão de docstring (D1) e uma nota de interface (I1). Sem alegação de optimalidade ou prioridade.

## 1. Custódia (conforme)

| item | valor | verificação |
|---|---|---|
| ZIP | SHA-256 `fa5c9b86f6ba4c3e2287f249272709b4ec287a9018de456f71b599026c910601` | ✅ = fita; 17 arquivos + 3 diretórios sob `deliver/`, caminhos limpos |
| manifesto interno | `SHA256SUMS_54-L.txt` | 17 entradas, sem auto-inclusão, 17/17 OK |
| bundle | `stone54_410bde8.bundle` SHA-256 `185b7834311e566f0af0fdae598ddf835ffd96a09799f69501efacf541754987` | ✅ = fita; `git bundle verify` OK; pré-requisito = base |
| `origin/main` observada | `571b83aadb53838eb8257c015b7c02d3e57d30ad` (fetch somente leitura, 2026-09-14) | = base (merge do PR #29, docs 53); tag `zenodo-v53` → base; `Phase3/` da base `99758dfc…` = tree Phase3 do candidato 53 auditado; blobs 53 presentes. Não avançou; reconstrução feita sobre a base exata de qualquer modo |
| candidato | `410bde8146e8f14b698a03387da395a79f81f9eb` | 1 commit sobre a base; parent único = base |
| trees | root `eaffdb1355a515bb7686831d07c767c39739f2bb`; Phase3 `7d8373f682a10a70e4db6f701e08fb7c1dbb6908` | ✅ = fita |
| blobs | módulo `e2ff9e0eaf73cef7da278057f34e778f0235c655` (523 linhas, 13 declarações, todas `theorem`); lakefile `ffd0edffb00d9d215d3fb63c06c22319d7490a98` | ✅ = fita; fonte avulsa do ZIP byte-idêntica ao blob |
| diff | A `Phase3/LatticeGauge/ActivityDampingLipschitzRefined.lean`, M `Phase3/lakefile.toml` (1 glob ao final, 113 → 114); **+524/−1** | ✅ |
| preservação | 113 módulos anteriores byte-idênticos; workflow, docs, README, LICENSE, `lean-toolchain`, `lake-manifest.json`, `formalization.yaml`, Phase1/2: 0 alterações | ✅ |
| proveniência | `Claude <noreply@anthropic.com>` (autor e committer), assinatura SSH, trailers `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` e `Claude-Session:` | = precedente aceito da Pedra 53; registrado, nenhuma reescrita proposta |
| imports | `ActivityDampingLipschitz` (53), `CovarianceDecay` (51-E) | módulo folha; sem ciclo |

## 2. Reconstrução (execução)

Bancada: `leanprover/lean4:v4.15.0` (Lean 11651562caae), Lake 5.0.0-1165156, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608` (= `rev = "v4.15.0"` do `lakefile.toml`), `lake-manifest.json` SHA-256 `c376bbe9…1227` pré = pós; pins não atualizados, nenhuma dependência re-resolvida (`environment.txt`, `manifest_pre/post_build.sha256`).

**Dirigido** (`lake build LatticeGauge.ActivityDampingLipschitzRefined`): exit 0, 252 s, 0 erros, 0 warnings no módulo novo, 13 certidões, 0 sorryAx.

**Limpo** (`rm -rf .lake/build && lake build`, início `2026-09-14T16:06:00Z`): exit 0, 550 s, **114 módulos "Built", 0 "Replayed"** (LatticeGauge e dependências — a Mathlib pinada já construída não é relistada pela bancada), 0 erros, **114 warnings, todos de `LatticeGauge/`, 0 de dependências**, 0 no módulo novo, 0 sorryAx, 179 certidões (166 + 13). Comparação com a base **em texto integral** (`arquivo:linha:coluna: mensagem`): diff vazio contra o baseline da QA 53 — não só a contagem. Pureza: 114 `.olean`, 0 anteriores ao início.

## 3. Axiomas e higiene

- Meu `#print axioms` das 13 declarações (V0): 13/13 exatamente `[propext, Classical.choice, Quot.sound]`; 0 sorryAx; nenhum axioma novo. `#check` do capstone refinado e do capstone 53: **mesmas hipóteses**, nenhum `DependsOnlyOn`.
- Léxico (`hygiene.txt`): em código, 0 `sorry/admit/axiom/native_decide/unsafe/opaque/implemented_by/set_option/maxHeartbeats/partial`, 0 divisão por `|θ−θ′|`, 0 `⁻¹`; `Disjoint`, "volume", "monotonicity", "differentiability", "optimality", "sharpness", "priority", "mass gap" só no cabeçalho, negados.
- Dependências efetivamente consumidas (34 identificadores, `hygiene.txt`): 53-A (`abs_dampedActivityCoreExponent_le_barrier`, `dampedActivityCoreExponent_sub_eq_activityDampingConnector_sub`, `abs_activityDampingConnector_sub_le_eroded`), 53-B (`activityDampedExpectation_sub_eq_two_column_lipschitz_ledger`, `abs_sum_lipschitzBridgeColumn_le`), 52-E (`nonneg_of_abs_le_of_config`), 52-A (`activityDampedExpectation_one/_zero`, `dampedPow_*`), 51-D (`exp_neg_nat_sub_half_le`, `halfTiltCoreBudgetTerm(_eq)`), 50 (`abs_typedMarkedCoreWeight_le_mayerCoreMajorant`), e **`sum_halfTilt_two_le`** (`CovarianceDecay.lean:71`), que é um wrapper de uma linha de `coreLocalBudget_connector` (`CovarianceConnectorControl.lean:266`) = `coreLocalBudget (lam := 1/2) (κ := 2)` com admissibilidade descarregada por `norm_num`. **O capstone 53 (`…_le_local_exp_decay`) aparece só em docstring (l. 433) e nunca é usado na prova do refinado** — a direção é refinado ⇒ 53 (`_of_refined`), sem circularidade.

## 4. Pontos matemáticos (§4 da fita), lidos integralmente e verificados

- **A. Unilateral** (l. 68–92): `x ≤ q ⇒ e^x − e^y ≤ e^q·|x−y|`, **sem hipótese em y**. Caso `x ≤ y`: LHS ≤ 0 ≤ RHS. Caso `y ≤ x`: `Real.add_one_le_exp (y−x)` × `e^x` dá `e^y ≥ e^x + e^x(y−x)`, logo `e^x − e^y ≤ e^x(x−y) ≤ e^q(x−y) = e^q|x−y|`. Instanciado com `y = q+5` (V1b).
- **B. Bilateral** (l. 98–105): `abs_sub_le_iff` + unilateral nas duas ordens. Rederivado por mim só com `add_one_le_exp` (V1a); válido para `q, x, y` negativos e para `q = 0` (V1c); **sem** a cota superior é falso — contraexemplo `q=0, x=2`: `e^2 − 1 > 2` (V1d). Nenhum valor médio formalizado.
- **C.** Ambos os expoentes `≤ q_T` por `abs_dampedActivityCoreExponent_le_barrier` (53-A, κ = 1) aplicado a θ e θ′ (l. 145–150); `E(θ) − E(θ′) = C_θ − C_θ′` (53-A, l. 155). Retipados (V2a, V2e).
- **D. Erosão**: `(n − familyTotalCard T : ℕ)` truncada antes do cast (l. 154, 171, 174), herdada do lema 53-A; `m_T > n` ⇒ fator `e^0 = 1`; `q_T = 0` ⇒ RHS 0, coerente (V2d).
- **E. Absorção** `q ≤ e^q` (l. 160, 177) multiplicando por `|θ−θ′|·e^{−(n−m)/2} ≥ 0` — o fator `|θ−θ′|` nunca é dividido (V1e); custo `e^{q}` (escalar) × `e^{q}` (absorção) = `e^{2q}` ⇒ **κ = 2** (rederivado em V2b; V2c mostra a contabilidade 54 ⇒ 53).
- **F.** `|W_T| ≤ Cf·ΠM` **sem exponencial** (`abs_typedMarkedCoreWeight_le_mayerCoreMajorant`, l. 225); `0 ≤ θ′^t ≤ 1` (l. 229–230, `dampedPow_*`).
- **G. Orçamento (1/2,2)**: `1/2 + 2·8/113 = 145/226 ≤ 1` (V3a); `sum_halfTilt_two_le` retipado **e** re-instanciado por mim a partir do `coreLocalBudget` genérico em `(1/2, 2)` com o mesmo enunciado (V3a); prefator `3·D·2/113 = 6D/113` (V3b).
- **H.** Ledger 53 (sinal MAIS nas pontes) e coluna-ponte 53 (κ = 1, tilt 7/8, `e^{4D/113}`) reutilizados intactos (l. 355–358).
- **I. Fechamento** rederivado **sem** os dois teoremas refinados finais (V3c): ledger + `abs_add` + coluna refinada + coluna-ponte ⇒ dois termos ⇒ capstone com `e^{4D/113} ≤ e^{6D/113}`, `K = |θ−θ′|·Cf·e^{−n/2} ≥ 0`, `Cf ≥ 0` derivado. Dois termos ⇒ simplificado (V3d). Recuperação da cota 53 a partir da refinada (V3e) — **nunca o contrário** (leitura das provas + mapa de dependências).

## 5. Testes próprios (§5 da fita)

`54_QA1_TEST_MATRIX.tsv`: V0–V4 positivos (exit 0, 0 warnings), V5x falha esperada. Cobertura dirigida: θ = θ′ por **aplicação efetiva** do capstone refinado (⇒ `≤ 0` ⇒ `= 0`, V4a); θ′ = 1 com Gibbs e `DependsOnlyOn` (derivação própria, V4b); θ′ = 0 com o restrito, sem `hf` (V4c); região vazia com θ = −7, θ′ = 42 pela **identidade publicada** da 53, sem extrapolar o capstone (V4d); expoentes negativos e `q = 0` (V1c); erosão `m_T > n` (V2d); constantes nova vs antiga: `≤` retipado, estrita para `Cf > 0 ∧ D_s > 0`, igualdade em `D_s = 0` (∀Cf) **e** em `Cf = 0` (∀D_s), RHS completo nulo em θ = θ′, e `igualdade das constantes completas ⇒ Cf = 0 ∨ D_s = 0` (prova própria, V4e/e′); `Cf = 0 ⇒ F` constante em θ (V4f); consistência dois termos ↔ simplificado (V3d). V5x (θ = 2): falha de aplicação, não falsidade nem indispensabilidade. Sem `rfl` entre provas. Deslizes meus resolvidos autonomamente: V2 (rewrite sobre variável de `set`) e V4 (`rw [sub_self]` só na primeira instância) — logs `attempt1` preservados; nada reclassificado como problema do candidato.

## 6. Matriz das 13 declarações

`54_QA1_DECLARATION_MATRIX.tsv`: 13 linhas, 13 PASS, hipóteses explícitas, dependências reais, teste(s) que cobre(m) cada uma.

## 7. Achados classificados

- **Correção matemática:** nenhum defeito.
- **Execução:** conforme (§2); nenhum bloqueio.
- **Custódia:** conforme (§1); proveniência = precedente 53.
- **Documentação:** **D1** — docstring de `refined_constant_le_published_constant` (l. 417): "the two agree exactly when D_s = 0". Confirmado como impreciso: com `0 ≤ Cf`, as constantes completas também coincidem quando `Cf = 0` (qualquer `D_s`); para `Cf > 0` a igualdade equivale a `D_s = 0`; e o RHS completo do capstone também se anula em θ = θ′ (V4e/e′). O teorema enuncia apenas `≤` e a prova está correta — observação documental, não defeito. **D2** — o teste estrito do construtor (T5, `tests/Stone54ApplicationTests.lean:71`) compara **somente as exponenciais** `e^{6D/113} < e^{8D/113}` para `D > 0`; não é uma comparação estrita do prefator completo (que exige também `Cf > 0`). Registrado; minha V4e cobre o prefator completo.
- **Interface (não defeito):** **I1** — `import LatticeGauge.CovarianceDecay` (módulo de 51-E) serve apenas ao wrapper `sum_halfTilt_two_le`; `coreLocalBudget_connector` (`CovarianceConnectorControl`) já é alcançável de 53 e dá o mesmo enunciado. Nenhum resultado de decaimento de 51-E é consumido. Uma eventual reescrita para evitar o import é opcional e fora desta auditoria.

## 8. Preliminar vs final

`PRELIMINARY_CONCLUSIONS_first_pass.md` já registrava PASS com observação documental, D1 e I1. A segunda passagem acrescentou D2 e as concordâncias de §9.

## 9. Segunda passagem — logs e testes do construtor (abertos após §8)

`stone54_commit.txt` = objetos Git; `stone54_diffstat.txt` = meu diff. `logs/lake_build_clean.log`: 114 `LatticeGauge` Built, 0 Replayed de `LatticeGauge` (os 1332 "Replayed" e 4599 warnings restantes do log do construtor são da Mathlib compilada da fonte na bancada dele — **distinguidos por filtro**, como a fita pede), 0 erros, 114 warnings de `LatticeGauge` com **texto idêntico** aos meus, 0 no módulo novo, 0 sorryAx, 179 certidões; janela 15:30:14Z → 15:39:12Z. `build_refined_1.log`: 1 warning `unused variable hy` (l. 68) — removido em `build_refined_2.log` (0 warnings), coerente com a hipótese `y` ausente no lema unilateral final. `AXIOMS_54-L.txt`: 13/13 padrão. `tests/positive.log`: 13 `example`s, 0 erros, 0 warnings; `tests/negative.log`: `⊢ False` de `2 ≤ 1`, como declarado. Divergência: só D2 (natureza do teste estrito).

## 10. Pacote e HARD STOP

`/home/claude/qa54/out` (manifesto `SHA256SUMS_54-QA1.txt`, sem auto-inclusão): este relatório, `PRELIMINARY_CONCLUSIONS_first_pass.md`, as duas matrizes, `tests/` (6 `.lean` + logs + 2 `attempt1`), `build_directed.log/.result`, `build_full_clean.log/.result`, `clean_build_start_utc.txt`, `environment.txt`, `manifest_pre/post_build.sha256`, `warnings_candidate.txt`, `warnings_file_line_QA1.txt`, `hygiene.txt`.

HARD STOP: candidato intacto (worktree só com o `lake-manifest.json` gerado, não rastreado); nenhum push, PR, merge, tag, Release ou Zenodo; Pedra 55 não iniciada.
