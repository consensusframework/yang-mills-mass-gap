# RELATÓRIO 52-A0-QA1 — Auditoria cega independente

**Auditor:** Claude Fable 5.1 (segunda instância; bancada pinada em sessão Cowork). **Data:** 2026-09-06 (UTC).
**Independência:** nenhum relatório do construtor, relatório adversarial, log, índice ou matriz de terceiros foi lido. O único item do `SHA256SUMS_52A0L.txt` usado foi o hash do bundle, já fornecido pela própria fita. Todos os testes negativos são próprios.
**HARD STOP respeitado:** somente leitura, build e testes descartáveis; zero alteração persistente; zero commit; zero push/PR/merge; push do remoto desativado (`DISABLED_NO_REMOTE_WRITE`).

## 1. Custódia (itens 1–2)

| Item | Resultado |
|---|---|
| Bundle `stone52-a0_76e10fe.bundle` SHA-256 | `06dc20e067842e5869ac7df9f667dee30a2cc2111d79cac9e8e4fc5abaaf9818` ✅ = esperado |
| `git bundle verify` | okay; prerequisite `5a63f572…` (= `origin/main` atual, lido hoje) |
| Commit candidato | `76e10feb40a064e5813828fc1feae7c0949d3ec6` ✅ |
| Parent | `5a63f5727997602e5b84ac2cec25a663816c18ce` ✅ (1 commit acima da base) |
| Tree | `f7fac46c6f799c7761b383245010bb760c6ff5c2` |
| Autor/committer | `Claude Fable 5.1 (Etapa 1) <pesquisaagi4@gmail.com>` |
| Arquivos alterados | `A Phase3/LatticeGauge/ActivityDampingBudgets.lean` (+690) · `M Phase3/lakefile.toml` (+1/−1) — **nada mais** |

## 2. Ambiente e build (itens 3, 11, 12)

Lean 4.15.0 (`11651562caae`), Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`, manifesto resolvido `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227` (pré = pós).

- Build dirigido `lake build LatticeGauge.ActivityDampingBudgets`: **exit 0**, 226 s, 0 erros, 0 warnings no módulo, 0 `sorryAx`.
- Build completo **limpo** da Phase 3 (`.lake/build` apagado, cache Mathlib mantido): **exit 0**, 392 s, **106 módulos**, 0 erros.
- Warnings: total **114**, distribuição por arquivo:linha **idêntica** ao baseline (build limpo da 51-B); **0** atribuíveis a `ActivityDampingBudgets.lean`.
- `#print axioms` das 11 declarações listadas no módulo: todas `[propext, Classical.choice, Quot.sound]`, idênticas entre build dirigido e limpo, zero `sorryAx`.

## 3. Higiene (item 4, parte lexical)

Fora de comentários: 0 `sorry`, 0 `admit`, 0 declaração `axiom`, 0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`, 0 `filter_congr_decidable`, 0 `@[reducible]`, 0 `classical!`, 0 `nolint`, 0 `decide`. Quatro `omit … in` (instâncias de seção não usadas — correto, sem efeito nas provas).

## 4. Itens 10 e 14

- **Lakefile:** o diff é exatamente o acréscimo de `"LatticeGauge.ActivityDampingBudgets"` ao final de `globs`; prefixo byte-idêntico; nenhuma outra linha tocada. Necessário (sem o glob o módulo não entra no alvo `LatticeGauge`); não altera outros alvos.
- **Byte-identidade:** `git diff --name-status base..candidato` lista somente os 2 arquivos acima; Phase1, Phase2, docs, README e workflow: 0 alterações. Todos os `.lean` até a Pedra 51 permanecem byte-idênticos.

## 5. Auditoria matemática (itens 4–9, 13)

Todas as 35 declarações foram lidas; cada lema consumido foi conferido contra a assinatura na fonte pinada (`coreLocalBudget`, `kpAbsConnector_le_exp_neg_mul_tilt`, `summable_kpAbsConnectorUnrootedCoeff`, `tsum_kpAbsConnector_le`, `kpForbiddenRootEnvelope_le_barrierLinkCount`, `abs_normalizedMarkedCoreTerm_le_of_abs_le`, `prod_family_massTiltActivity`, `kpAbsSummand_massTilt`, `incompatible_kp_sum_geometric_bound`, `kpQ_le_one_div_5000`, `kpR_le_512_div_625`, `sum_indicator_eq_sum_incompatible`, defs `kpForbiddenRootEnvelope`, `massTiltActivity`, `tupleTotalCard`, `familyTotalCard`, `kpActivityWeight`, `AbstractKPHypothesis`, `allPlaquettePolymers`, `IsPlaquettePolymer`). Matriz completa em `52-A0_QA1_DECLARATION_MATRIX.tsv`.

Pontos obrigatórios (item 6):

- **`1 − θ^j ≤ j(1−θ)`**: enunciado e prova corretos (indução, kernel). Endpoints `j=0` (=0), `θ=0` com `0<j` (=1; a hipótese `0<j` é necessária: `j=0` dá 0), `θ=1` (=0): corretos.
- **Cardinalidade × ocorrências × massa**: `nat_le_tupleTotalCard` conta posições (com repetição) em ambos os lados — é o objeto certo para tuplas; `familyCard_le_familyTotalCard` para famílias (Finset de polímeros distintos). Ambos consomem `polymer_card_pos`.
- **Não-vacuidade dos polímeros**: `polymer_card_pos` extrai `Nonempty` como primeiro conjunto de `IsPlaquettePolymer` (`PolymerGeometry.lean:54`), via `allPlaquettePolymers = powerset.filter IsPlaquettePolymer`. Verificado textualmente; não vacuoso.
- **Absorção por `8/(3e)`**: `x ≤ (1/(eδ))e^{δx}` para todo real x (de `y+1 ≤ e^y`), especializado em δ=3/8. Margem: `0.98 < 8/(3e) ≤ 1` (teste QA3) — apertado, correto. δ=1/4 seria falso (x=4), demonstrado no teste QA3.
- **`8/(3e) ≤ 1`**: prova formal via `e ≥ 8/3` de `Real.sum_le_exp_of_nonneg` com 4 termos (1+1+1/2+1/6 = 8/3). Correta.
- **KP com tilt 7/8**: `abstractKP_massTilt_sevenEighths_polymerWeight` é espelho exato do caso 1/2 (`kp_sum_le_half_card`), com penalidade `card/8` e o escalar `64q/(1−r) ≤ 8/113 ≤ 1/8`. Aritmética: com `q ≤ 1/5000`, `1−r ≥ 113/625`, o bound é **exato** (`64/5000 ÷ 113/625 = 8/113`, teste QA4) — zero folga, mas correto.
- **Recombinação do envelope**: `kpForbiddenRootEnvelope_massTilt_complement` é uma identidade genuinamente λ-livre (`e^{λ·card}·e^{(1−λ)card} = e^{card}`); a localização 2/113 é consumida sem recontagem.
- **Orçamento `(7/8,1)`**: `7/8 + 1·8/113 = 855/904 ≤ 1` ✅ (`norm_num`). **Preservação de `(1/2,3)`**: `161/226 ≤ 1` ✅ — o módulo não a reprova, apenas a cita (`sum_halfTilt_three_le` vive em `ActivityRestrictionColumnBounds`, não importado aqui). **`(7/8,3)`**: `983/904 > 1`; o teste QA2 confirma que `norm_num` **falha** nessa condição e que a negação é provável. Nenhum uso de `(7/8,3)` no módulo.
- **Item 7 (fator de contagem pago de verdade)**: sim, em desigualdades compostas com o fator no lado esquerdo: `k·A_k(ρ) ≤ (8/3e)·e^{−q/2}·A_k(ρ tilt 7/8)` e `card T·|N_f(s,T)| ≤ Cf·e^{−n/2}·e^{b_T}·Π massTilt(7/8)`. Não há nome ou comentário fazendo o trabalho da desigualdade.
- **Item 8 (quantificadores/objetos para reuso)**: o primeiro momento do connector é enunciado para `ρ = |polymerWeight|`, `P = remoteAllowed T s`, `Q = remoteAllowed T' s'`, separação `q` entre `barrierRegion`s — instancia-se com `T' = ∅`, `s' = r`, `q = n − m_T` via `walkBarrierSeparated_barrierRegions_sub_familyMass` (mesma rota da 51-D), e a ponte `|kpConnectorUnrootedCoeff| ≤ kpAbsConnectorUnrootedCoeff |z|` existe (`KPAbsoluteUnrooted.lean:72`). O primeiro momento da ponte já está no vocabulário da Pedra 51 (`activityBridgeCores s r`, `WalkBarrierSeparated s r n`) e na forma de somando do orçamento κ=1. Reutilizáveis.
- **Item 9 (circularidade)**: imports = Pedra 50 (A10/A12/A14/A17/A18) + `ActivityRestrictionConnectorGeometry` (51-C). Não importa `CovarianceDecay`, `ActivityRestrictionColumnBounds`, `ActivityRestrictionStability` nem módulo algum da Pedra 52. Sem circularidade.
- **Sem dupla cobrança**: o tilt 7/8 é aplicado às atividades **dentro** do connector (paga contagem k e separação); a erosão `e^{m_T/2}` da separação `n − m_T` será paga pelo tilt 1/2 sobre o **núcleo** no orçamento `(1/2,3)` — objetos distintos.
- **Hipóteses contraditórias/vacuidade**: `hβ, hsmall` satisfeitas por β=0; `WalkBarrierSeparated` é a mesma hipótese da Pedra 50/51. Nenhuma conclusão vacuamente verdadeira encontrada.

## 6. Testes próprios (item 13) — `negtests/`

| Teste | Esperado | Resultado |
|---|---|---|
| QA1 Bernoulli: provar `1−θ^j ≤ j(1−θ)` só com `0 ≤ θ` via `one_add_mul_le_pow`; contraexemplo `θ=−3,j=3` sem hipótese | sucesso / sucesso | ✅ exit 0 |
| QA2 `(7/8)+3·(8/113) ≤ 1` por `norm_num` | **falhar** | ✅ exit 1 (unsolved goals) |
| QA2b `(7/8,1)`, `(1/2,3)` cabem; `¬((7/8,3))` | sucesso | ✅ exit 0 |
| QA3 absorção com δ=1/4 é falsa (x=4, `exp_one_lt_d9`); `0.98 < 8/(3e)` | sucesso | ✅ exit 0 |
| QA4 `64·(1/5000)/(113/625) = 8/113` exato; `8/113 < 1/8` | sucesso | ✅ exit 0 |

## 7. Possíveis problemas encontrados

### R1 — Hipótese desnecessariamente forte (gravidade: cosmética)
- **Declaração:** `one_sub_dampedPow_le_nat_mul_one_sub`, linhas 72–86.
- **Demonstração:** teste QA1 prova o mesmo enunciado com `0 ≤ θ` apenas (Bernoulli, `one_add_mul_le_pow`). `θ ≤ 1` é supérflua (é usada só para `hle`; outra rota dispensa).
- **Impacto no capstone:** nenhum — o uso é com θ ∈ [0,1].
- **Menor correção (não aplicada):** opcionalmente remover `h1` e provar via `one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ θ − 1) j`. Não requer mudança.

### R2 — Lacuna de infraestrutura para a constante anunciada (gravidade: média, prospectiva — fora do escopo declarado do gate, mas decisiva para "EXACT TARGET")
- **Onde:** não é defeito de nenhuma declaração deste módulo; é uma peça **ausente** que a coluna permitida da Pedra 52 vai exigir.
- **Análise:** o termo permitido é `N_f(s,T)·(e^{C} − e^{C_θ})`. Com o primeiro momento deste gate, `|C − C_θ| ≤ (1−θ)·(8/3e)·e^{−(n−m_T)/2}·q'` com `q' = b_T·(2/113)` (d := `(1−θ)(8/3e)e^{−(n−m_T)/2} ≤ 1`).
  - **Rota de valor médio** `|e^a − e^b| ≤ |a−b|·e^{max(|a|,|b|)}`: custo `d·q'·e^{q'} ≤ d·e^{2q'}`; com a normalização `e^{q'}` dá κ = 3 → orçamento `(1/2,3)` → `exp(4·D_s·2/113) = e^{8D_s/113}` — **exatamente** a constante-alvo `(1−θ)·2Cf·e^{8D_s/113}·e^{−n/2}`.
  - **Rota ingênua** com o que existe (`e^{C}·(e^{C_θ−C} − 1)` + `abs_exp_sub_one_le_decay_exp`): custo extra `e^{|C|} ≤ e^{q'}` → κ = 4 → `(1/2,4)`: `1/2 + 32/113 = 145/226 ≤ 1` (ainda cabe no orçamento), mas o prefator vira `e^{10D_s/113}`, **não** o anunciado.
- **Demonstração:** grep na base: existem `abs_exp_sub_one_le_abs_mul_exp_abs` e `abs_exp_sub_one_le_decay_exp` (Pedra 50, `CovarianceConnectorControl.lean:43,78`); **não existe** lema para `|e^a − e^b|` no projeto, e não encontrei um pronto no Mathlib pinado.
- **Impacto:** a meta exata continua **alcançável** (a rota de valor médio é elementar: WLOG `b ≤ a`, `e^a − e^b = e^b(e^{a−b} − 1) ≤ (a−b)e^a`), mas **não** com o que existe hoje sem esse lema; quem construir o capstone precisa saber disso antes de escolher a rota.
- **Menor correção (não implementada):** em gate futuro, um lema ≈10 linhas `abs_exp_sub_exp_le_abs_sub_mul_exp_max (a b : ℝ) : |exp a − exp b| ≤ |a − b| · exp (max |a| |b|)` derivado de `abs_exp_sub_one_le_abs_mul_exp_abs` por divisão em casos.

Nenhum outro problema: nenhum lema decorativo (os endpoints A foram pedidos pela fita; todo o resto é consumido dentro do módulo ou é a interface declarada), nenhuma hipótese impossível, nenhuma conclusão vazia, nenhum fator escondido.

## 8. Veredito

A infraestrutura do gate 52-A0 é matematicamente correta, verificada pelo kernel com certidões limpas, higiênica, não circular, sem tocar nenhum arquivo científico anterior, e paga o fator de contagem por massa em desigualdades compostas explícitas. As duas reservas são: (R1) uma hipótese supérflua inofensiva; (R2) a constante exata anunciada para o capstone depende de um lema de valor médio para diferenças de exponenciais que ainda não existe na base — elementar, mas necessário para que a rota κ = 3 (e não κ = 4) seja a executada.

**`QA1 PASS WITH RESERVATIONS`**

HARD STOP.
