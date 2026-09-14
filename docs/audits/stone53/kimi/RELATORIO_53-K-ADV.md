# RELATÓRIO 53-K-ADV — Revisão adversarial final da Pedra 53

**Revisor:** Luan / Kimi 3 (bancada adversarial independente).
**Data:** 2026-09-13 (UTC).
**Regime:** somente leitura. Nenhuma modificação de código, commit, push, PR, merge, tag, Release ou publicação. Pedra 54 não iniciada.

**Declaração de método (exigida pela fita):** *Revisão matemática e de código; sem execução de Lean pelo revisor.* Tudo o que afirmo sobre compilação e axiomas vem de (i) leitura integral do código-fonte, (ii) leitura dos metadados de CI via API pública do GitHub, e (iii) leitura do pacote de evidência da QA — **resultados relatados por terceiros**, não execução minha. As derivações matemáticas dos pontos de ataque são **cálculo próprio em papel** sobre as fontes lidas. Não confundo nenhuma dessas categorias com execução.

---

## 1. Veredito

**PASS NO ESCOPO.**

Não encontrei defeito matemático, semântico ou de escopo nos dois módulos da Pedra 53. O resultado principal —

```
|F(θ) − F(θ′)| ≤ |θ−θ′|·Cf·e^{−n/2}·[e^{8D_s/113} + e^{4D_s/113}]
              ≤ |θ−θ′|·2·Cf·e^{8D_s/113}·e^{−n/2},   θ, θ′ ∈ [0,1]
```

com `F = activityDampedExpectation`, `D_s = card (supportLinkFinset s)`, sob `0 ≤ β ≤ 1/40000`, `Measurable χ`, `|χ| ≤ 1`, `Measurable f`, `∀U |f U| ≤ Cf`, `WalkBarrierSeparated s r n`, **sem `DependsOnlyOn f s`**, com `0 ≤ Cf` derivado — corresponde literalmente ao que está formalizado e verifiquei linha a linha.

---

## 2. SHA e arquivos efetivamente examinados

| Item | Valor | Verificação |
|---|---|---|
| Merge científico | `a7ae1c0cb81aa8829c056482afc74f9629485fd6` | conferido via API |
| Candidato reproduzido pela QA | `abad16674ab9b713c7ef9d0344c8f5cc02b09739` | tarball obtido de codeload neste SHA; commit conferido via API |
| Root tree (comum) | `0e156fc6c53b5c6c27d71f1e3c589ea63be45f4a` | ✅ = fita (via API) |
| Phase3 tree | `99758dfc339edf0e412133ca7f5826ecab45b56d` | ✅ = fita |
| CI PR #28 / main | runs `34788347617` / `34788866465` | ambos **success**, conferidos por mim via API (leitura de metadados, não execução) |
| Escopo do diff | A `ActivityDampingLipschitzInfrastructure.lean` + A `ActivityDampingLipschitz.lean` + M `Phase3/lakefile.toml` (2 globs, 111→113) | conferido via compare da API: nenhum módulo anterior modificado |

**Lidos integralmente por mim (1.204 linhas, contagens executadas):**

- `Phase3/LatticeGauge/ActivityDampingLipschitzInfrastructure.lean` — **555 linhas, 11 declarações, 11 certidões `#print axioms`** (contagens executadas; = fita).
- `Phase3/LatticeGauge/ActivityDampingLipschitz.lean` — **649 linhas, 18 declarações, 18 certidões** (= fita; 11 + 18 = 29).

**Dependências reais consultadas na fonte (leitura dirigida):** `tsum_restricted_sub_full` (`ForbiddenClusters.lean` — genérica na atividade, recebe a hipótese KP como parâmetro), `activityDampedExpectation_one` (`ActivityDampedObservableGas.lean:660` — exige `hf : DependsOnlyOn f s`), `nonneg_of_abs_le_of_config` (`ActivityDampingStability.lean` — o lema 52-E efetivamente consumido), `abs_exp_sub_one_le_decay_exp` e `exp_neg_nat_sub_half_le` (`CovarianceConnectorControl.lean`), `walkBarrierSeparated_barrierRegions_sub_familyMass` (`CovarianceBarrierErosion.lean`), `sum_halfTilt_three_le` (`ActivityRestrictionColumnBounds.lean`), `sum_sevenEighthsTilt_one_le` e `dampedPow_le_one` (`ActivityDampingBudgets.lean`), `sum_touchingFamilies_eq_activityAllowed_add_bridge` (`ActivityRestrictionLedger.lean`), `activityBridgeCore_familyTotalCard_ge` (`ActivityRestrictionConnectorGeometry.lean`), endpoints de região vazia (52-A/52-B). Todos presentes com as assinaturas que a 53 invoca.

**Lidos na fase de comparação (somente após concluída a leitura independente):** `QA1_53_evidence.zip` (RELATORIO_53-QA1.md, PRELIMINARY_CONCLUSIONS, matrizes) e `RELATORIO_53-P.md` (publicação).

---

## 3. Método e exposição prévia

**Esta revisão não é cega.** Declaro: auditei adversarialmente as Pedras 49, 50, 51 e 52 (incl. errata C1 e adendo C2 ao meu próprio parecer 52-K-ADV); conheço toda a arquitetura a montante (gases, ledger 51/52, conector, orçamentos, capstone 52) e os pareceres anteriores da cadeia. O que é independente aqui: a **leitura integral das fontes da 53 foi feita antes de abrir qualquer material da QA ou do construtor**, e cada ponto de ataque da fita foi verificado por derivação própria sobre o código, antes da comparação da §6.

Não executo Lean. A reconstrução limpa de 113 módulos existe na cadeia de custódia (instância Fable QA, distinta da construtora, com `.lake/build` apagado) — é relatada por terceiros e a trato como tal.

---

## 4. Ataques realizados e resultados (pontos 1–8 da fita)

### Ataque 1 — O ledger direto: pesos, sinais, orientação, filtros

Rederivei a identidade a partir da forma exponencial 52-B `F(θ) = Σ_touching θ^t·W_T·e^{E_T(θ)}` aplicada nos dois lados:

```
F(θ) − F(θ′) = Σ_T [θ^t·W·e^{Eθ} − θ′^t·W·e^{Eθ′}]
             = Σ_touching θ′^t·W·(e^{Eθ} − e^{Eθ′}) + Σ_touching (θ^t − θ′^t)·W·e^{Eθ}.
```

Dois pontos que tentei quebrar: **(a)** o fator `θ′^t` na coluna do conector (não `θ^t`) — correto: é a escolha que isola a diferença de exponenciais; a prova (`ActivityDampingLipschitz.lean:108-141`) reescreve a soma-θ como soma-θ′ mais a correção, usando que nos núcleos **permitidos** ambos os pesos valem 1 (`pow_touchCount_eq_one_of_mem_activityAllowedCores`), logo a correção fica suportada exatamente nas **pontes** — o filtro é o certo, e um núcleo permitido com `t = 0` não escapa nem é contado duas vezes. **(b)** o expoente na coluna-ponte é `e^{E_T(θ)}` (no parâmetro θ, não θ′) — correto pela álgebra `θ^t e^{Eθ} − θ′^t e^{Eθ′} = θ′^t(e^{Eθ} − e^{Eθ′}) + (θ^t − θ′^t) e^{Eθ}`; o `ring` final do bloco (`:140-144`) fecha exatamente isso. Sem `DependsOnlyOn`, sem hipótese sobre f — conferido na assinatura (`:85-90`). **Sem defeito.**

### Ataque 2 — O custo κ = 1 do expoente amortecido

Este é o ingrediente novo e o ponto de maior risco arquitetural: se `|E_T(θ)| ≤ b_T·(2/113)` falhasse, a coluna-ponte cairia no orçamento inadmissível (7/8, 2). Verifiquei a rota de `abs_dampedActivityCoreExponent_le_barrier` (Infrastructure `:117-156`): `tsum_restricted_sub_full` é **genérica na atividade** (recebe `AbstractKPHypothesis |z| a` como parâmetro — conferi a assinatura na fonte), instanciada com `z := dampedActivity w r θ` via o KP amortecido de 52-A (`abstractKP_dampedActivity`, exige `0 ≤ θ ≤ 1` — presente); segue `|S_P − S| ≤ Σ'|forbidden| ≤ envelope(|z_θ|) ≤ envelope(|z|)` pela monotonia `kpForbiddenRootEnvelope_mono` (`:93-101` — verifiquei: não precisa de condição de sinal em ρ porque o fator exponencial é positivo) e a localização 2/113 de 50. O peso do núcleo entra **sem exponencial adicional** (`abs_typedMarkedCoreWeight_le_mayerCoreMajorant`). κ = 1 de fato; a rota alternativa via `N_f·e^{C_θ}` custaria κ = 2 e `(7/8, 2)`: `7/8 + 16/113 > 1` — inadmissível, conferido. **Sem defeito.**

### Ataque 3 — Diferença de coeficientes e manipulação de tsums

`abs_pow_sub_pow_le_nat_mul_abs_sub` (Infrastructure `:64-78`): invoca `abs_pow_sub_pow_le` do Mathlib com `max |θ| |θ′| ≤ 1` — correto, e a hipótese [0,1] é de fato necessária (fora dela `j·|θ−θ′|` não domina; o fator `max^{j−1}` cresce). A dominação dois-parâmetros (`:210-253`): nos tuplas que atingem ambos os proibidos, `|(1−θ^{tc}) − (1−θ′^{tc})| = |θ^{tc} − θ′^{tc}| ≤ tc·|θ−θ′| ≤ k·|θ−θ′|` com `tc ≤ k` (`tupleTouchCount_le`); fora do filtro, `0 − 0`. O `k!` fica intacto na posição da definição. A diferença de séries (`:264-360`): ambas somáveis por 52-C (`summable_kpDampedConnectorUnrootedCoeff`), `tsum_sub` legítimo, `norm_tsum_le_tsum_norm`, `tsum_le_tsum` com a dominação pontual, e o primeiro momento 52-A0 fecha em `e^{−q/2}·q′` **sem 8/(3e)**. **Sem defeito.**

### Ataque 4 — Erosão com subtração truncada

`(n − familyTotalCard T : ℕ)` truncada em ℕ antes do cast (`:275`): se `m_T > n`, o expoente é 0 e a cota degenera para `|θ−θ′|·q′`, sem explosão. O ponto sutil que procurei: no controle exponencial (`:392-468`), o lema `abs_exp_sub_one_le_decay_exp` exige `0 ≤ d ≤ 1` com `d = |θ−θ′|·e^{−((n−m_T:ℕ))/2}` — e a prova paga isso explicitamente em `:433-437` via `|θ−θ′| ≤ 1` (`abs_sub_le_one_of_unit_interval`) e `e^{−(·)} ≤ 1`. Parâmetros iguais (`θ = θ′`) dão `d = 0` e cota 0, coerente. Extremos θ=0/θ′=1: dentro de [0,1], cobertos. **Sem defeito.**

### Ataque 5 — Orçamentos, sem dupla cobrança, fator preservado

- **Coluna 1** (Lipschitz `:151-269`): `0 ≤ θ′^t ≤ 1` (`dampedPow_nonneg/le_one`), `|W_T| ≤ Cf·ΠM` sem exponencial, controle κ = 3 recomprado `e^{−n/2}·e^{m_T/2 + 3b·2/113}`; o termo fecha exatamente em `halfTiltCoreBudgetTerm β 3 s T` (o `e^{m_T/2}` vive **dentro** do termo de orçamento via `halfTiltCoreBudgetTerm_eq` — uma vez só); soma via `sum_halfTilt_three_le` → `e^{4·D_s·(2/113)} = e^{8D_s/113}`.
- **Coluna 2** (`:292-404`): `|θ^t − θ′^t| ≤ card T·|θ−θ′|`; o primeiro momento amortecido de ponte (Infrastructure `:478-541`) paga `e^{−n/2}` com `n ≤ m_T` (geometria de ponte) e absorve `card T ≤ m_T ≤ e^{3m_T/8}` — tilt `1/2 + 3/8 = 7/8`, κ = 1; extensão pontes → tocantes com majorante não negativo (`sevenEighthsBudgetTerm_nonneg`); `sum_sevenEighthsTilt_one_le` → `e^{2·D_s·(2/113)} = e^{4D_s/113}`.
- O fator `|θ−θ′|` é extraído no nível dos **coeficientes** e carregado intacto até o capstone; greps próprios: **zero divisões** por `(1−θ)` ou `|θ−θ′|` em código. **Sem defeito.**

### Ataque 6 — Hipóteses

Conferido nas assinaturas elaboradas em texto: o ledger (`:85`), a forma de dois termos (`:413`) e o capstone (`:446`) **não** contêm `DependsOnlyOn f s` — apenas `hβ, mχ, hχabs, hsmall, mf, hCf, hsep` e os dois pares de hipóteses de intervalo. `0 ≤ Cf` é **derivado** em `:426` e `:459` por `nonneg_of_abs_le_of_config hCf` — e confirmei na fonte que esse lema vive em `ActivityDampingStability.lean` (52-E), enquanto o capstone 52 **não** é consumido em nenhuma prova da 53 (aparece só em docstring, `:511`; a re-derivação `:536` é corolário a jusante, sem circularidade — 52-E não importa 53). Conforme a advertência da fita, **não** interpreto `s` como suporte de `f` no teorema principal: sem `hf`, `s` é apenas o parâmetro de suporte do funcional amortecido. A única porta para Gibbs — `activityDampedExpectation_one` (52-A `:660`) — exige `hf`, e o endpoint θ′ = 1 da 53 (`:512-531`) a carrega corretamente. **Sem defeito.**

### Ataque 7 — Endpoints

- **θ = θ′:** `activityDampedExpectation_sub_self` (`:493-497`) é `sub_self` sobre o funcional (total, razão de somas finitas) — a diferença é 0 sem hipóteses. `lipschitz_bound_self` (`:501-505`) é **álgebra do RHS apenas** (o lado da cota zera); registro conforme a fita que a aplicação efetiva do capstone em θ = θ′ está no teste U4a da QA — material de terceiros, não executado por mim.
- **θ′ = 1:** recupera o capstone 52 com a mesma constante (`|θ−1| = 1−θ` via `abs_sub_comm` + `abs_of_nonneg`), **com `hf`** — correto e necessário.
- **θ′ = 0:** distância ao funcional restrito da 51 com fator θ, via `activityDampedExpectation_zero` (identidade definicional), **sem `hf`** — correto.
- **r = ∅:** identidade exata `F(θ) = F(θ′)` para **todo θ, θ′ reais** (`:579-587`, sem hipóteses de intervalo — os lemas `*_empty_region` são para θ real arbitrário), e as colunas do ledger anulam termo a termo (`:592-609`). **Sem defeito.**

### Ataque 8 — Escopo

O cabeçalho do módulo declara explicitamente o que o teorema **não** é: monotonicidade do desvio, derivada, segunda medida de Gibbs, condições de contorno, ação modificada, limite termodinâmico, contínuo, mixing espacial, mass gap. O enunciado é uma estimativa de estabilidade Lipschitz do funcional em rede finita — exatamente o que o código prova. Higiene própria (grep fora de comentários): 0 `sorry`/`admit`/`axiom`/`native_decide`/`set_option`/`maxHeartbeats`/`partial`/`unsafe`/`implemented_by`. **Sem defeito.**

---

## 5. Achados classificados

| Categoria | Achados |
|---|---|
| **Defeito matemático** | **Nenhum.** |
| **Questão de escopo** | **Nenhuma.** Claims e código coincidem; disclaimers completos. |
| **Precisão documental** | **Nenhuma nova.** As observações que localizei na comparação (desvio de proveniência do commit — autor `Claude <noreply@anthropic.com>` fora do padrão da cadeia; a contagem "8 vs 9 exemplos" no relatório do construtor; a natureza de `lipschitz_bound_self`; a irrelevância do `rfl` entre as provas 52/53) são **exatamente** os itens C1, D1, D2, D3 já registrados pela QA 53 — não os re-reporto como achados novos. O item C1 (proveniência) é decisão de custódia de Ju/Sol, sem impacto matemático: os blobs e a matemática não mudam com a identidade do autor. |

Conforme a fita: não inventei falhas para preencher a lista.

---

## 6. Comparação posterior com a QA e com o construtor

Abertos **somente após** concluídas as §§4–5: `RELATORIO_53-QA1.md` (com PRELIMINARY_CONCLUSIONS) e `RELATORIO_53-P.md`.

**Convergência total** nos pontos matemáticos: ledger com sinal MAIS nas pontes e peso θ′^t na coluna 1 (a QA rederivou o mesmo ledger sem invocar os teoremas finais — minha derivação independente coincide), rota κ = 1 pelo envelope genérico de 50, inadmissibilidade de (7/8, 2), subtração truncada com `d ≤ 1` pago explicitamente, orçamentos (1/2,3) e (7/8,1), `|θ−θ′|` nunca dividido, capstone sem `DependsOnlyOn`, `0 ≤ Cf` derivado do lema 52-E (não do capstone 52), endpoints conforme.

**Reprodução:** a QA (instância Fable distinta da construtora) reconstruiu 113 módulos do zero (0 Replayed de LatticeGauge), 29/29 declarações em `[propext, Classical.choice, Quot.sound]`, 0 sorryAx — **resultado relatado por terceiros**, que registro como tal; minha contribuição é a leitura adversarial de outra família de modelos, como a fita pede. Custódia da publicação (53-P): diff A+A+M +1205/−1, merge com `expectedHeadSha` travado, CI verde nos dois runs (conferidos por mim via API), nenhum arquivo protegido tocado.

**Ressalva estrutural permanente** (declarada, não é achado): construtor, QA e arquiteto são todos da mesma família de modelos que já produziu a cadeia; revisão humana continua inexistente. Esta revisão acrescenta uma família distinta na leitura — mitiga, não elimina.

---

## 7. Limites

1. **Sem execução Lean pelo revisor** (repetido por obrigação): compilação, axiomas e testes são leitura de código + metadados de CI + pacote QA.
2. **Escopo matemático:** verifiquei a estimativa Lipschitz tal como formalizada — rede finita, separação `n`, β pequeno (acoplamento forte, convenção Wilson). Nada aqui diz respeito a mass gap, contínuo ou limite termodinâmico — e o próprio módulo os nega.
3. Ausência de achados ≠ infalibilidade: afirmo exatamente que **não encontrei defeito no escopo e nas verificações descritos**.

---

**Veredito final: PASS NO ESCOPO.**

Revisei este parecer antes de entregar (fita, item final): contagens executadas distinguidas de relatadas, três categorias de evidência separadas, nenhuma falha de aplicação promovida a prova, nenhum achado inventado.

HARD STOP.

*Luan da bancada*
