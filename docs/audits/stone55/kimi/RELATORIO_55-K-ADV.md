# RELATÓRIO 55-K-ADV — Auditoria adversarial independente da Pedra 55

**Auditor:** Luan (Kimi 3), bancada adversarial independente.
**Data:** 2026-09-19.
**Coordenação:** Ju. Arquitetura e revisão: GPT Astra. Construção: Fable. Reprodução Lean: QA1 (instância Claude Fable 5.1, distinta da construtora).
**Natureza da revisão:** **revisão por leitura e análise matemática, sem execução Lean.** Toda execução Lean citada neste parecer (reconstrução limpa de 116 módulos, testes V1–V4, certidões de axiomas) é atribuída à QA1, conforme a fita; não a apresento como minha. Não apresento CI nem logs alheios como reprodução própria.

---

## 1. Objeto e custódia efetivamente verificados

| item | valor | verificação própria |
|---|---|---|
| repositório | `consensusframework/yang-mills-mass-gap` | localizado por busca na API do GitHub |
| candidato | `0c50b6d5e23915f13d6f36d560a58ba6f24ae97b` | commit, parent único e árvores conferidos via API do GitHub |
| base | `bd2f6c1b0ad600b0282b4776859bb917466152ea` | = parent do candidato |
| merge (PR #33) | `d6ce3d7232f08b5f975dfa8c6f43ec5031937e10` | parents = base + candidato, conferidos via API |
| árvore raiz | `e69c0fe94d18b83f0664fdc42642358ef4f8e867` | conferida |
| árvore Phase3 | `20ffea86201c8a35d62479b2c0038f8c3e592de5` | conferida |
| CI | runs 35262236671 e 35263497257, ambos `success` | conferidos via API |
| módulos novos | `ActivityProfileDamping.lean` (923 linhas; blob `dc85622b…`), `ActivityProfileDampingStability.lean` (999 linhas; blob `6f12d160…`) | baixados por codeload no SHA fixado; **byte-idênticos** aos dois arquivos enviados por upload; hashes de blob git recalculados por mim |
| preservação | 114 módulos anteriores intactos; lakefile ganha 2 globs (114 → 116) | conferido no tarball |
| contagens | 10 `def` + 68 `theorem`; 43 + 25 = 68 `#print axioms` | contados por mim nas fontes |

Fonte de leitura: tarball codeload no candidato fixado, re-baixado nesta sessão (o /tmp é volátil); comparação byte a byte com os uploads da fita.

## 2. Método, exposição e limitações

- Leitura integral e independente dos dois módulos (923 + 999 linhas) **antes** de abrir qualquer material de QA ou do construtor. Os pacotes `QA1_55_evidence.zip` e `STONE55L_evidence.zip` foram abertos somente após concluída a minha análise, para comparação.
- Rederivação própria, no papel, dos pontos algébricos críticos (§3).
- **Limitações:** não executei Lean; não verifiquei a compilação por conta própria; minha verificação da custódia usa a API pública do GitHub e hashes recalculados; não audito a Mathlib nem as pedras anteriores além das interfaces usadas (estas já auditadas nas fitas 49–54).
- Exposição prévia declarada: auditei as Pedras 49–54 nesta bancada; a arquitetura da 55 consta da fita. Não é auditoria cega, é auditoria adversarial informada.

## 3. Análise dos pontos prioritários da fita (ataques 3.1–3.4 e §4)

### 3.1 Pesos, telescópica e contagens (módulo A)
- `touchFactor r a η = if typedTouchesSupport η r then a η else 1`: valores de `a` fora do suporte de r nunca são lidos — nenhuma hipótese lateral é necessária. Conferido.
- Identidades de perfil constante: `profileDampedActivity_const` é **rfl** (o perfil constante É o amortecimento escalar da 52, definicionalmente); as demais (`profileWeight_const`, `tupleProfileWeight_const`, `profileExpectation_const`) são reescritas. Conferido caso a caso.
- Telescópica `abs_prod_sub_prod_le_sum_abs_sub`: indução em Finset com a identidade `x·P − y·Q = x·(P−Q) + (x−y)·Q`; produto vazio fechado por `simp`; fatores em [0,1] usados para descartar o produto caudal. Rederivado; falharia fora de [0,1], e por isso as hipóteses `0 ≤ a ≤ 1` são essenciais e estão presentes em toda a cadeia.
- Cotas de diferença de pesos: `|A_Γ − A′_Γ| ≤ touchCount·δ` (famílias) e `|A_δ − A′_δ| ≤ tupleTouchCount·δ ≤ k·δ` (tuplas, **repetições contadas por posição** — `![η,η]` conta 2). Variantes `_le_card` exigem `hδ0 : 0 ≤ δ`, presente em todos os usos. Ataque de multiplicidade: **resiste**.

### 3.2 Conector, inclusão–exclusão e séries (módulo B, §55-B.1–B.4)
- Coeficiente `kpProfileConnectorUnrootedCoeff`: peso `1 − A_δ` nas tuplas que batem nas duas barreiras, Ursell e ∏z originais, /k! fora da soma. No perfil constante reduz ao coeficiente da 52; no perfil unitário é 0 (peso 1−1). Conferido.
- **Inclusão–exclusão** (`kpProfileConnector_inclusion_exclusion`): refiz a árvore de casos. (i) Tupla P-permitida: restrição não altera nada, os quatro termos cancelam e o indicador do conector é 0 — fecha por `ring`. (ii) P-proibida e regionalmente permitida: `tupleTouchCount = 0` ⇒ `A_δ = 1`, os termos com restrição zeram e `∏z_a = ∏z` — fecha. (iii) Proibida nas duas: sobra `∏z·(1 − A_δ)`, exatamente o lado direito. O filtro regional entra **só pela implicação** `TupleAllowed (regionAllowed r) → tc = 0 → A_δ = 1`, sem recíproca — orientação correta, sem hipótese sobre `a`.
- Identidades de séries: `E_T(a) − E_T(cheio) = C(a)` com as quatro séries de aglomerados somáveis (KP transportado por `abstractKP_mono`); orientação idêntica à 51-C/52-C; `E_T(a) − E_T(a′) = C(a) − C(a′)` por `linarith` sobre duas instâncias. Conferido.
- Dominação `|c_k(a) − c_k(a′)| ≤ δ·k·A_k(|z|)`: divisão por k! ≥ 0, termwise com a contagem de posições; caso k = 0 trivial (ambos os lados 0). Somabilidade pela dominação contra o perfil unitário (δ = 1) e o primeiro momento 52-A0.
- **Erosão:** `|C(a) − C(a′)| ≤ δ·e^{−((n − m_T : ℕ))/2}·q_T` com subtração **truncada em ℕ** antes do cast (sem 8/(3e)); a separação das regiões-barreira em `n − m_T` vem de `walkBarrierSeparated_barrierRegions_sub_familyMass` com a família vazia em r. Quando m_T > n o exponencial truncado é 1 e a cota é `δ·q_T` — comportamento correto, sem falso decaimento.

### 3.3 Constante, κ = 2 e as duas colunas (módulo B, §55-B.5–B.8)
- Controle bilateral da exponencial herdado da 54: `|e^x − e^y| ≤ e^q·|x−y|` com **ambos** `E_T(a), E_T(a′) ≤ q_T = b_T·(2/113)` (55-A); depois `q_T ≤ e^{q_T}` absorvido, entregando κ = 2: `|e^{E_T(a)} − e^{E_T(a′)}| ≤ δ·e^{−n/2}·e^{m_T/2 + 2·b_T·(2/113)}`. Rederivado; **nenhuma hipótese δ ≤ 1 em ponto algum** (verifiquei: só `hδ0 : 0 ≤ δ` em toda a cadeia). O teste mental δ = 7 da fita: o enunciado permanece válido, apenas frouxo — correto.
- **Coluna conector** (orçamento (1/2, 2)): `0 ≤ A′_T ≤ 1`, `|W_T| ≤ Cf·∏M` (majorante de Mayer, sem exponencial), controle κ = 2; soma sobre famílias tocantes fecha em `sum_halfTilt_two_le` = `coreLocalBudget (1/2) (κ:=2)` (admissibilidade `145/226 ≤ 1` auditada na 54) ⇒ prefator `e^{3·D_s·(2/113)} = e^{6D_s/113}`.
- **Coluna ponte** (κ = 1, tilt 7/8, orçamento (7/8, 1)): `|A_T − A′_T| ≤ card T·δ`; o primeiro momento `card T·|W_T·e^{E_T(a)}|` é pago por `card T ≤ m_T ≤ e^{3m_T/8}`, pela geometria de ponte `n ≤ m_T` (pagamento `1 ≤ e^{−n/2}·e^{m_T/2}`) e pela fusão `e^{m_T/2}·e^{3m_T/8} = e^{7m_T/8}` absorvida em `massTilt(7/8)`. Soma estendida de pontes a tocantes (termos não-negativos) e fechada por `sum_sevenEighthsTilt_one_le` ⇒ prefator `e^{2·D_s·(2/113)} = e^{4D_s/113}`.
- **Fechamento:** ledger de dois perfis da 55-A (peso A′ na coluna conector, `(A−A′)·e^{E_T(a)}` na ponte, sinal **MAIS**, suporte nos núcleos-ponte porque nos permitidos `A_T = A′_T = 1`) + desigualdade triangular + as duas colunas ⇒ forma de dois termos `δ·Cf·e^{−n/2}·(e^{6D_s/113} + e^{4D_s/113})`; capstone por `e^{4D_s/113} ≤ e^{6D_s/113}` (D_s ≥ 0) ⇒ `δ·(2Cf)·e^{6D_s/113}·e^{−n/2}`. `0 ≤ Cf` é derivado de `|f| ≤ Cf`; **sem `DependsOnlyOn`**; **nada é dividido por δ**. Exatamente o alvo da fita.
- **Recuperação da 54:** `…_of_profile` aplica o capstone novo a `a ≡ θ, a′ ≡ θ′, δ = |θ−θ′|` e reescreve via `profileExpectation_const`. A direção é 55 ⇒ 54: o módulo da 54 está intocado e o capstone da 54 aparece na 55 **apenas em docstring** (B, l. 902) — confirmei que nenhuma prova da 55 o referencia. **Sem circularidade.**

### 3.4 Endpoints (§4 da fita)
- **δ = 0:** a forma de dois termos dá cota 0 diretamente (nada dividido por δ); `profile_bound_self` é só a simplificação do RHS — registro documental já existente (D1), confirmado, não é defeito.
- **δ > 1 (δ = 7):** válido e frouxo, como acima.
- **Perfil constante:** recupera a estimativa da 54 como aplicação (§3.3).
- **Perfil zero:** `abs_profileExpectation_sub_activityRestrictedExpectation_le` — comparação com o funcional restrito da 51, **sem** `DependsOnlyOn`, via `profileExpectation_zero` (também sem hipóteses); a hipótese `a ≤ δ` nos tocantes é usada como `|a − 0| = a ≤ δ`. Conferido.
- **Perfil unitário:** `abs_profileExpectation_sub_gibbsExpectation_le` — **com** `DependsOnlyOn f s`, via `profileExpectation_one`; `1 − a ≤ δ` convertido a `|a − 1| ≤ δ` por `abs_sub_comm` + `abs_of_nonneg` (usa `a ≤ 1`). A assimetria documentada (zero sem hipótese, unitário com DependsOnlyOn) é real e necessária: só o lado unitário precisa identificar o funcional com Gibbs. Conferido.
- **Região vazia:** identidade para **todos** os perfis reais (módulo A) — fora de [0,1] inclusive, pois nenhum fator é lido. Conferido.

### Dependências cruzadas
Verifiquei a existência e a localização dos 13 lemas críticos consumidos: `abs_exp_sub_exp_le_exp_mul_abs_sub` (54), `sum_halfTilt_two_le` (CovarianceDecay), `sum_sevenEighthsTilt_one_le` e `nat_le_exp_three_eighths` (orçamentos), `exp_neg_nat_sub_half_le` (CovarianceConnectorControl), `activityBridgeCore_familyTotalCard_ge` (geometria, pré-52), `tupleAllowed_regionAllowed_iff_tupleTouchCount_eq_zero` (52), e os internos da 55-A — todos em módulos anteriores ou no próprio par da 55. **Nenhum ciclo.**

## 4. Comparação com as evidências (abertas após a minha análise)

- **QA1** (`RELATORIO_55-QA1.md`): PASS NO ESCOPO com observações documentais; reconstrução limpa atribuída à QA1 (116 módulos, 0 replayed, 0 erros, 114 warnings herdados com texto idêntico ao baseline, 0 nos módulos novos, 68/68 certidões padrão `[propext, Classical.choice, Quot.sound]`, 0 sorryAx); ledger rederivado pela QA1 por rota independente; testes V1–V4 exit 0. Concordância plena com a minha leitura, inclusive nos pontos que ataquei de forma independente (inclusão–exclusão sem recíproca, κ = 2 sem δ ≤ 1, erosão truncada, sinal do ledger).
- **Construtor** (`STONE55L_evidence.zip`): logs e testes consistentes com o relatado pela QA1 na segunda passagem; matriz de declarações (78 linhas = 10 defs + 68 teoremas) bate com as fontes.
- Os registros documentais **D1–D5** e a observação de interface **I1** (import de `CovarianceDecay` herdado da 54) já constam da fita e do relatório da QA1. Confirme cada um contra as fontes e **não os apresento como descobertas novas**; nenhum é defeito matemático.

## 5. Achados

**Matemáticos:** nenhum defeito encontrado.

**Documentais:** nenhum além dos já registrados (D1–D5), que confirmo como precisões de redação sem efeito sobre as provas.

**Melhorias opcionais:** nenhuma nova. (I1 permanece como observação herdada e legítima.)

## 6. Veredito

**PASS NO ESCOPO.**

A Pedra 55 entrega, para perfis `a, a′` em [0,1] e `0 ≤ δ` majorando `|a − a′|` nos polímeros que tocam r:

`|F(a) − F(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6D_s/113} + e^{4D_s/113}) ≤ δ·(2Cf)·e^{6D_s/113}·e^{−n/2}`,

com a constante, a taxa e o regime da 54, δ no lugar de |θ − θ′|, sem `DependsOnlyOn`, sem δ ≤ 1, sem divisão por δ, e com a 54 recuperada como aplicação sem circularidade. Custódia conforme; escopo declarado respeitado (nenhuma reivindicação de otimalidade, exclusividade ou ineditismo; nenhuma interpretação por link, condição de contorno ou limite termodinâmico atribuída).

Não alterei arquivos do repositório, não publiquei nada e **não iniciei a Pedra 56**.

— Luan da bancada

**HARD STOP.**
