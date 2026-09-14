# RELATÓRIO 54-K-ADV — Revisão adversarial independente da Pedra 54

**Revisor:** Luan / Kimi 3 (Moonshot AI) — família de modelos distinta de construtor (Claude Fable 5.1), QA (Claude Fable 5.1) e arquiteto (GPT Astra).
**Data:** 2026-09-14 (UTC).
**Regime:** somente leitura. Nenhuma escrita no GitHub ou Zenodo, nenhuma alteração de prova, Pedra 55 não iniciada.

**Declaração de método (item 4 da fita):** *revisão por leitura e análise matemática, sem execução Lean.* Não compilei, elaborei ou executei teste algum. Distingo ao longo do texto: (i) fatos conferidos diretamente na fonte ou na API pública do GitHub; (ii) argumentos rederivados por mim em papel sobre o código lido; (iii) execução Lean própria — **nenhuma**; (iv) resultados de execução relatados pela QA1 ou pelo publicador — atribuídos como tal, nunca apresentados como reprodução minha.

---

## 1. Veredito

**PASS NO ESCOPO.**

Não encontrei defeito matemático, hipótese oculta, circularidade, erro de constante ou exagero documental novo na Pedra 54. O resultado —

```
|F(θ) − F(θ′)| ≤ |θ−θ′|·Cf·e^{−n/2}·[e^{6D_s/113} + e^{4D_s/113}]
              ≤ |θ−θ′|·(2Cf)·e^{6D_s/113}·e^{−n/2},   θ, θ′ ∈ [0,1]
```

com hipóteses, intervalo e taxa `1/2` exatamente os do capstone 53 — corresponde literalmente ao formalizado. Os pontos D1/D2/I1 já documentados são confirmados com a classificação dada (§6); não os apresento como descobertas. Ausência de achados novos não é prova de optimalidade nem avanço sobre o problema do Milênio: é uma melhoria de constante numa estimativa de estabilidade em rede finita.

---

## 2. SHA exato revisado e custódia (conferido por mim na fonte/API)

| Item | Valor | Verificação |
|---|---|---|
| Candidato | `410bde8146e8f14b698a03387da395a79f81f9eb` | tarball de codeload neste SHA; commit conferido via API |
| Merge revisado | `9c0f6fdecee5c8628a2434d032e421edc78bb722` | CI da main conferido neste SHA via API |
| Base | `571b83aadb53838eb8257c015b7c02d3e57d30ad` | parent único do candidato, conferido via API |
| Root tree | `eaffdb1355a515bb7686831d07c767c39739f2bb` | ✅ = fita (API) |
| Phase3 tree | `7d8373f682a10a70e4db6f701e08fb7c1dbb6908` | ✅ = fita |
| Blob do módulo | `e2ff9e0eaf73cef7da278057f34e778f0235c655` | ✅ recomputado por mim (SHA-1 git do arquivo baixado) |
| Diff | A `ActivityDampingLipschitzRefined.lean` (+523) + M `Phase3/lakefile.toml` (+1/−1); 1 commit sobre a base; **+524/−1** | ✅ conferido via compare da API: nenhum dos 113 módulos anteriores tocado |
| CI PR #30 / main | runs `34875314038` / `34876420216` | ambos **success**, conferidos por mim via API (metadados; logs analisados pelo publicador, não por mim) |
| Contagens | 523 linhas, 13 declarações (todas `theorem`), 13 certidões `#print axioms` | ✅ executadas por mim |

**Fontes lidas:** o módulo novo **integralmente** (523 linhas) no SHA fixado; dependências dirigidas na fonte: `sum_halfTilt_two_le` (`CovarianceDecay.lean:71-77`), `coreLocalBudget_connector` (`CovarianceConnectorControl.lean:266-277`), `coreLocalBudget` (`CovarianceCoreLocalBudget.lean:328-…`), e — já lidas integralmente nas minhas auditorias anteriores — as famílias 50/51/52/53 consumidas. Material de terceiros lido **somente após** a análise independente: `RELATORIO_54-QA1.md` (+ PRELIMINARY_CONCLUSIONS, matrizes) e `RELATORIO_54-P.md`. Nenhuma limitação de acesso a registrar.

**Exposição prévia (item 6):** auditei adversarialmente as Pedras 49–53 (pareceres 51, 52-K-ADV + errata C1 + adendo C2, 53-K-ADV + errata C1); conheço a arquitetura inteira da cadeia e os pareceres anteriores. **Esta revisão não é cega** — família de modelo diferente não significa auditoria cega, e não a descrevo como tal. O que é independente: a leitura do módulo e todas as contas da §4 foram feitas antes de abrir QA1 e 54-P.

---

## 3. Modelo e método efetivamente utilizado

Leitura integral do código; cálculo próprio em papel de cada item A–F da fita (incluindo tentativas de refutação: casos de ordem, expoentes negativos, q = 0, m_T > n, Cf = 0, D_s = 0, θ = θ′); greps de higiene próprios; API do GitHub para custódia. Nenhuma execução Lean.

---

## 4. Análise dos itens A–F (derivações próprias)

### A — Passo escalar (`:68-105`)

Verifiquei as duas provas linha a linha:

- **Unilateral** (`exp_sub_exp_le_exp_mul_abs_sub`, `:68-92`): hipótese só `x ≤ q`. Caso `x ≤ y`: `e^x − e^y ≤ 0 ≤ e^q·|x−y|` ✓. Caso `y ≤ x`: de `1 + (y−x) ≤ e^{y−x}` (`Real.add_one_le_exp`), multiplicando por `e^x > 0`: `e^y ≥ e^x + e^x·(y−x)`, logo `e^x − e^y ≤ e^x·(x−y) ≤ e^q·(x−y) = e^q·|x−y|` ✓. Orientação correta nos dois casos; válido com expoentes negativos e `q = 0` (nenhuma hipótese de sinal em x, y — a prova usa só positividade de exp); a ausência de cota superior tornaria o lema falso (`q=0, x=2, y=0`: `e²−1 > 2`) — e ela está presente. **Não é derivação por TVM**: usa exclusivamente `Real.add_one_le_exp`, como a fita exige distinguir. ✓
- **Bilateral** (`:98-105`): `abs_sub_le_iff` + unilateral nas duas ordens — por isso precisa de `x ≤ q` **e** `y ≤ q`; a distinção unilateral/bilateral está correta e é a razão das duas hipóteses. ✓
- `le_exp_self` (`:108-110`): `q ≤ e^q` de `q + 1 ≤ e^q`, todo q real. ✓

**Sem defeito.**

### B — Controle κ = 2 (`:130-200`)

Reconstituí a contabilidade completa:

1. Ambos os expoentes `≤ q_T = b_T·(2/113)` — via `|E_T(·)| ≤ q_T` da 53-A aplicada a θ e a θ′ (`:145-150`); **nenhuma hipótese de sinal** sobre atividades ou expoentes (o bound é sobre o valor absoluto).
2. Valor médio escalar: `|e^{Eθ} − e^{Eθ′}| ≤ e^{q_T}·|E_T(θ) − E_T(θ′)|` — **um** exponencial.
3. Diferença de expoentes = diferença de conectores (53-A), erodida: `|Δ| ≤ |θ−θ′|·e^{−((n−m_T:ℕ))/2}·q_T` — orientação e normalização conferidas (o `rw` em `:155` reescreve para a forma do lema 53-A, aplicado depois).
4. Absorção `q_T ≤ e^{q_T}` (`:160,177`) multiplicando por `|θ−θ′|·e^{−(·)} ≥ 0` — **segundo** exponencial. Total: `e^{2q_T}` ⇒ **κ = 2** ✓.
5. Recompra da erosão `e^{−((n−m_T:ℕ))/2} ≤ e^{−n/2}·e^{m_T/2}` (`exp_neg_nat_sub_half_le`, 51-D) ✓.

`|θ−θ′|` preservado integralmente (grep próprio: zero divisões por `|θ−θ′|` ou por `q`; zero `⁻¹` em código). Nenhum custo exponencial omitido: a economia real em relação à 53 é que a rota antiga pagava `e^{E(θ′)} ≤ e^{q}` **mais** `d·e^{2q}` (3q); a nova paga `e^q` (valor médio) + `e^q` (absorção de q) = 2q. **Sem defeito.**

### C — Erosão e orçamento (`:143-200`, `:270-308`)

- A subtração `(n − familyTotalCard T : ℕ)` é **natural truncada antes do cast** — herdada do lema erodido 53-A que a 54 instancia; em `m_T > n` o expoente é 0 e a cota degenera para `|θ−θ′|·q_T·e^{q_T}` sem explosão. ✓
- Re-instanciei em papel o orçamento genérico: `coreLocalBudget (lam := 1/2) (κ := 2)` exige `1/2 + 2·(8/113) = 1/2 + 16/113 = 113/226 + 32/226 = 145/226 ≤ 1` ✓ (descarregado por `norm_num` em `coreLocalBudget_connector`, `CovarianceConnectorControl.lean:274`).
- **Cadeia real lida, não só o nome do wrapper:** `sum_halfTilt_two_le` (`CovarianceDecay.lean:71-77`) é `coreLocalBudget_connector` (`CovarianceConnectorControl.lean:266-277`), que instancia `coreLocalBudget` (`CovarianceCoreLocalBudget.lean:328`) em `(1/2, 2)` e conclui `Σ ≤ e^{(κ+1)·D_s·(2/113)} = e^{3·D_s·(2/113)}`. O termo somado bate com `halfTiltCoreBudgetTerm β 2 s T` via `halfTiltCoreBudgetTerm_eq` (51-D) — o mesmo padrão dos wrappers (1/2,3) → `e^{4·D_s·(2/113)}` e (7/8,1) → `e^{2·D_s·(2/113)}` que verifiquei nas auditorias 52/53. Logo `3·D_s·(2/113) = 6D_s/113` ✓.
- Nenhum fator absorvido foi reinserido: o `e^{m_T/2}` vive dentro do termo de orçamento via `halfTiltCoreBudgetTerm_eq`, uma única vez (`:255-263`). **Sem defeito.**

### D — Ledger e fechamento (`:339-460`)

- O ledger de dois parâmetros é **reutilizado da 53** (`:357`: `activityDampedExpectation_sub_eq_two_column_lipschitz_ledger`) — pesos, expoentes, suporte das colunas e sinal MAIS nas pontes são os que auditei na 53-K-ADV; a coluna-ponte da 53 (`abs_sum_lipschitzBridgeColumn_le`, κ = 1, tilt 7/8, `e^{4D_s/113}`) entra intacta (`:355`).
- **Rederivação própria do fechamento, sem os dois teoremas finais da 54:** ledger ⇒ `|F(θ)−F(θ′)| ≤ |coluna 1| + |coluna 2|` (`abs_add`) ⇒ `|θ−θ′|·Cf·e^{−n/2}·(e^{3·D_s·(2/113)} + e^{2·D_s·(2/113)})` (duas cotas) ⇒ capstone por `e^{2·D_s·(2/113)} ≤ e^{3·D_s·(2/113)}` (D_s ≥ 0, `:388-393`) com prefator `K = |θ−θ′|·Cf·e^{−n/2} ≥ 0` usando `0 ≤ Cf` derivado (`:383`). Fecha. ✓
- **Direção lógica:** refinado ⇒ bound da 53 (`_of_refined`, `:435-460`: capstone refinado + `refined_constant_le_published_constant` + multiplicação por `|θ−θ′| ≥ 0`). O capstone publicado da 53 **não** é usado em nenhuma prova da 54 (aparece só em docstring, `:433`); a 54 importa a 53, a 53 não importa a 54 — **sem circularidade**, e o módulo publicado da 53 está byte-intacto (diff conferido). ✓

**Sem defeito.**

### E — Hipóteses e endpoints

Conferido nas assinaturas em texto: capstone refinado (`:370-377`) e dois termos (`:339-346`) com exatamente `hβ, mχ, hχabs, hsmall, mf, hCf, hsep` e os intervalos — **sem `DependsOnlyOn`**, com `0 ≤ Cf` derivado (`:352,383`) via o lema 52-E. Endpoints: **θ′ = 1** (`:467-486`) identifica com Gibbs via `activityDampedExpectation_one` — exige e carrega `hf : DependsOnlyOn f s` ✓ (e produz o enunciado da 52 com o prefator menor, honestamente descrito); **θ′ = 0** (`:490-507`) com o funcional restrito e fator θ, sem `hf` ✓; **região vazia**: identidade da 53 reutilizada — vale para parâmetros reais arbitrários, inclusive fora de [0,1], e a 54 corretamente **não** reivindica o capstone fora do intervalo; **θ = θ′**: o capstone aplicado dá `|F(θ)−F(θ)| ≤ 0` — o RHS zera porque nada foi dividido por `|θ−θ′|`; **Cf = 0**: `|f| ≤ 0` ⇒ f ≡ 0, ambos os lados 0, coerente; **D_s = 0**: `e^0 = 1`, as duas constantes coincidem. Falha de aplicação em θ = 2 (relatada pela QA como V5x) é falha de aplicação — não prova falsidade fora do intervalo nem indispensabilidade, e eu a registro nesses termos. **Sem defeito.**

### F — Comparação das constantes (`:415-460`)

O teorema `refined_constant_le_published_constant` enuncia **somente** `2Cf·e^{6D_s/113}·e^{−n/2} ≤ 2Cf·e^{8D_s/113}·e^{−n/2}` sob `0 ≤ Cf` — distinção correta entre (1) exponenciais, (2) constantes completas, (3) RHS completos, (4) desvio efetivo: **nada no módulo afirma que o desvio efetivo `|F(θ)−F(θ′)|` diminuiu**; só a cota melhorou. O cabeçalho (`:41-42`) declara explicitamente "no optimality, sharpness or bibliographic priority". **Sem defeito.**

---

## 5. Higiene (greps próprios, fora de comentários)

0 `sorry`, 0 `admit`, 0 declaração `axiom`, 0 `native_decide`, 0 `set_option`, 0 `maxHeartbeats`, 0 `partial`, 0 `unsafe`, 0 `implemented_by`, 0 `⁻¹`, 0 divisão por `|θ−θ′|` ou `(1−θ)`. "mass gap", "continuum", "monotonicity", "optimality", "Disjoint", "volume" só no cabeçalho, negados. Escopo declarado: estabilidade em rede finita — sem limite termodinâmico, contínuo, mass gap, monotonicidade ou diferenciabilidade. Pequeno β = acoplamento forte (convenção Wilson), como em toda a cadeia.

---

## 6. Achados

**Novos:** nenhum — em nenhuma das cinco categorias (defeito matemático, hipótese oculta, circularidade, erro de constante, exagero documental).

**Já conhecidos (fita, "Observações já conhecidas") — confirmo a classificação, com verificação própria:**

- **D1 (imprecisão documental, não defeito):** confirmado — a docstring de `refined_constant_le_published_constant` (`:417`) diz "agree exactly when D_s = 0" e omite `Cf = 0`: com `0 ≤ Cf`, a igualdade das constantes completas ocorre também quando `Cf = 0` (qualquer D_s); para `Cf > 0` a igualdade equivale a `D_s = 0`; melhora estrita exige `Cf > 0 ∧ D_s > 0`; e o RHS completo se anula também em θ = θ′. O **teorema** enuncia `≤` e está correto — só a glossa é imprecisa. Aceito com o candidato intacto; consolidação documental.
- **D2 (cobertura de teste, não defeito):** confirmado pela leitura da QA — o teste estrito do construtor compara só as exponenciais; a QA cobre o prefator completo. Sem impacto no código.
- **I1 (interface, não defeito):** confirmado — `import LatticeGauge.CovarianceDecay` serve apenas ao wrapper `sum_halfTilt_two_le` (`CovarianceDecay.lean:71`); `coreLocalBudget_connector` daria o mesmo enunciado sem o import. Legítimo; nenhum resultado de decaimento de 51-E é consumido.
- **Proveniência:** precedente da 53, já aceito; não reabro — nenhuma evidência nova de divergência de custódia (blobs, trees e diff conferidos por mim, §2).

---

## 7. Comparação posterior com QA1 e publicador

Abertos só após as §§4–6. **Convergência total** com a QA1: mesma leitura do passo escalar (incl. a nota de que o lema unilateral dispensa hipótese em y — a QA notou até o warning de variável não usada na primeira versão do construtor, removido depois), mesma contabilidade κ = 2, mesma cadeia de orçamento até `coreLocalBudget`, mesma direção refinado ⇒ 53, mesmos D1/D2/I1. A QA rederivou o fechamento sem os teoremas finais (V3c) — como eu, em papel — e executou o que eu não executo: 114 módulos do zero, 0 replayed, 13/13 certidões `[propext, Classical.choice, Quot.sound]`, 0 sorryAx, warnings com texto integral idêntico ao baseline (**execução relatada por terceiros**, registrada como tal). Publicação (54-P): custódia conforme, merge com `expectedHeadSha` travado, CI verde nos dois runs (conferidos por mim via API), D1/D2/I1 registrados no corpo do PR para consolidação.

**Ressalva estrutural (formulação corrente):** construtor e QA são instâncias distintas de Claude Fable 5.1; arquitetura é GPT Astra; esta revisão é Kimi — três famílias na cadeia. Coordenação humana documentada (fitas, aceites, publicação); **revisão matemática humana especializada do conteúdo das provas não está documentada nesta etapa.**

---

## 8. Limites

1. Sem execução Lean pelo revisor (declarado no cabeçalho e aqui repetido): compilação, axiomas e testes são leitura de código + API + pacote QA.
2. Escopo: estimativa de estabilidade Lipschitz em rede finita com constante melhorada; nada sobre mass gap, contínuo, termodinâmico, monotonicidade ou diferenciabilidade — e o módulo os nega corretamente.
3. Não reivindico optimalidade, prioridade ou exclusividade da rota; a origem da proposta (seção E.3 do relatório de antecedentes da 53, modelo pesquisador não nomeado) está registrada no cabeçalho do módulo sem identidade inventada — conforme a fita.
4. Ausência de achados ≠ infalibilidade: afirmo exatamente que **não encontrei defeito no escopo e nas verificações descritos**.

---

**Veredito final: PASS NO ESCOPO.**

HARD STOP.

*Luan da bancada*
