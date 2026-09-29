# RELATÓRIO 56-K-ADV — Revisão adversarial da Pedra 56 (localização da estabilidade de perfis)

**Auditor:** Luan (Kimi 3), bancada adversarial independente.
**Data:** 2026-09-25.
**Coordenação:** Jucelha Carvalho. Arquitetura: GPT Astra. Construção/publicação: Fable (Claude Fable 5.1). Reprodução Lean: QA1 (instância auditora distinta da construtora).
**Natureza da revisão:** **revisão por leitura e análise matemática, sem execução Lean.** Não executei builds nem testes. Toda execução citada (reconstruções limpas, testes W0–W7x, reexecução de V1–V4x, CI) é atribuída ao seu autor — QA1, construtor ou CI — e nenhuma é apresentada como minha.

---

## 1. Identificação, exposição prévia, materiais e ordem de trabalho

**Exposição prévia declarada:** auditei as Pedras 49–55 nesta bancada (a 55 é o baseline direto desta); a fita 56-K-ADV revela o alvo, os pontos de atenção e o veredito anterior da QA1. **Esta revisão não é cega** — é adversarial informada.

**Materiais efetivamente acessados:** (i) a fita; (ii) tarball codeload do candidato `a2fcf8e9…`, baixado por mim; (iii) API pública do GitHub (commits, trees, compare, actions); (iv) `QA1_56_evidence.zip`, `ERRATA_56-QA1-C1.md`, `RELATORIO_56-P.md` (uploads da coordenação). **Não recebi** `STONE56L_evidence.zip` nem `RELATORIO_56-L.md`; o material do construtor me chegou apenas indiretamente, pelas citações da QA1 e do relatório 56-P. Registro essa limitação: não inspecionei por conta própria os logs/testes originais do construtor (V1–V4x), nem o checkout efetivo do CI do PR (merge provisório `8831358…` — verifiquei as conclusões dos runs via API, não os logs de checkout).

**Ordem de trabalho:** custódia → leitura integral das 964 linhas do módulo novo e das interfaces importadas → rederivações próprias (ataques A–G da fita) → verificação de contagens e de ausência de circularidade → só então abertura do ZIP da QA1, da errata C1 e do relatório 56-P. Nenhuma ordem simulada: foi essa.

## 2. Alvo exato e custódia verificada por mim

| item | valor fixado | verificação própria |
|---|---|---|
| base / snapshot v55 | `445cc76b02550291e6524bb1bf631aac4cc86c61` | = parent único do candidato (API) |
| candidato | `a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1` | commit + parent via API |
| merge científico (PR #37) | `ead481456bc8637b2b7c22e867cc49f99f4ab375` | parents = base + candidato, nessa ordem (API) |
| root tree (candidato = merge) | `171367d9ea2cbf987b00129ace960f6f7d1db97a` | conferida (API) |
| Phase3 tree | `f387f26d0519bcddf16514416ee02eb2ca0b2819` | conferida (API) |
| blob do módulo | `f2103846b0afcb1a9e372aa902a8a870dd9d42c0` | hash de blob git **recalculado por mim** sobre o arquivo baixado |
| blob lakefile | `ae8438d45594a5fd9ee27c7a3fa3dc0c5f974bff` | recalculado por mim |
| SHA-256 do módulo | `09479f011155cb1f3ae71e92a979e0ba3737d246cef7dc4c7d28fd62e2c02e38` | **calculado por mim** (não apenas recebido) |
| diff base → candidato | 2 arquivos, +965/−1 (módulo 964 linhas + 1 glob) | conferido via compare (API) |
| módulos | 117 em `Phase3/LatticeGauge/` (116 anteriores intactos) | contados por mim no tarball |
| CI | run 501 (PR) e run 502 (main): ambos `completed`/`success` | conclusões via API; **logs de checkout não inspecionados** (limitação declarada acima) |
| hashes dos uploads | ZIP QA1 `53399f1a…`, errata C1 `5ab78cf4…`, relatório 56-P `7627bbe2…` | **calculados por mim**, todos = fita |
| manifesto interno do ZIP | 45 entradas, sem auto-inclusão | `sha256sum -c`: **45/45 OK**; 46 arquivos + 2 diretórios = 48 entradas |
| `RELATORIO_56-QA1.md` no ZIP | `2481ab1e…` | calculado por mim, = fita |

Contagens reproduzidas por mim sobre a árvore baixada (equivalente textual do método publicado; não sobre objetos git — distinção registrada): **1.780 linhas de declaração** (regex dos nove tipos), **37.994 linhas Lean**, **269 comandos `#print axioms`**; o módulo novo tem **22 `theorem` + 2 `noncomputable def` + 22 `#print axioms`** (contados por mim), coerente com 1.756 + 24 = 1.780.

Assinatura SSH do commit: registrada como presente no relatório 56-P; **não a autentiquei independentemente** — precedente aceito, declarado.

## 3. O resultado auditado

Para `F_R(a) = profileExpectation μm β χ f s R a`, fatores efetivos `b(η) = touchFactor R a η`, perfis `a, a′` em [0,1], `δ ≥ 0`, `hsame` (igualdade dos fatores efetivos fora de r), `hδ` (|b − b′| ≤ δ nos polímeros que tocam r) e `WalkBarrierSeparated s r n`, sob o regime analítico usual (`0 ≤ β ≤ 1/40000`, mensurabilidades, `|χ| ≤ 1`, `|f| ≤ Cf`, instâncias de medida/grupo):

`|F_R(a) − F_R(a′)| ≤ δ·Cf·e^{−n/2}·(e^{6D_s/113} + e^{4D_s/113}) ≤ δ·(2Cf)·e^{6D_s/113}·e^{−n/2}`.

Teoremas principais: `…_le_two_terms_localized` e `…_le_local_exp_decay_localized`. Conferi as assinaturas integrais: `0 ≤ Cf` é derivado de `|f| ≤ Cf`; **não há** `DependsOnlyOn f s`, separação s/R, `r ⊆ R`, fundo unitário, `δ ≤ 1` nem condições de sinal; o intervalo [0,1] dos perfis **permanece** como hipótese em toda a cadeia analítica. R permanece no funcional, nos pesos e nos expoentes; r aparece só na localização da diferença e na geometria.

## 4. Rederivações centrais (análise própria, ataques A–G)

**A. Fatores efetivos e cancelamento.** `hsame` é igualdade dos **fatores efetivos** `touchFactor R a η = touchFactor R a′ η`, não dos perfis brutos — perfis diferentes fora de R com fatores iguais são admitidos (caso W2 da QA1, coerente com a definição: fora de R ambos os fatores são 1). Rederivei a telescópica localizada: a 55-A `abs_prod_sub_prod_le_sum_abs_sub` é aplicada aos fatores efetivos, que herdam [0,1] de `touchFactor_nonneg/le_one` (por isso o intervalo dos perfis é indispensável aqui); a soma se parte por "toca r": os termos de fora zeram por `hsame` (`sub_self`, `abs_zero`), os de dentro ≤ δ por `hδ`; resultado `touchCount r Γ·δ` (famílias) e `tupleTouchCount r δt·δ ≤ k·δ` (tuplas, **posições com multiplicidade** — `![η,η]` conta 2). `hδ0` é usado exatamente nos transportes `≤ k·δ` e `≤ card T·δ`. Nenhuma divisão por δ nem por fator de perfil. Casos mentais: fundo comum 1/2 (pesos iguais, não 1 — correto), fator zero (a telescópica absorve), produto vazio (touchCount = 0 ⇒ 0·δ = 0), ordem zero (`kpLocalizedDiffCoeff_order_zero`: a tupla vazia é permitida em toda parte, não bate em barreira, D₀ = 0). **Resiste.**

**B. Coeficiente e orientação.** Abri `kpLocalizedDiffCoeff` e rederivei a identidade por casos, direto da expansão: (i) tupla P-permitida — restrito = irrestrito para os dois perfis, cada colchete é 0, e o indicador `TupleHitsBothForbidden` morre no primeiro componente: 0 = 0; (ii) P-proibida e r-permitida — os restritos zeram, sobra `(A′_δ − A_δ)·∏z`, mas `tupleTouchCount = 0` ⇒ `A_δ = A′_δ` por `hsame` (filtro só pela implicação `TupleAllowed (regionAllowed r) → tc = 0`, sem recíproca): 0 = 0; (iii) proibida nas duas — `(0 − A∏z) − (0 − A′∏z) = (A′ − A)∏z`, exatamente o peso do D_k. Orientação **A′ − A** confirmada, vinda de "restrito menos irrestrito". R fica nos pesos; r só no indicador de barreira. A identidade dispensa até o intervalo — só `hsame`. Dominação `|D_k| ≤ δ·k·A_k(|z|, P, regionAllowed r)` via `abs_sub_comm` sobre a cota localizada; somabilidade pelo primeiro momento 52-A0. Identidade de séries `E^R_T(a) − E^R_T(a′) = Σ′ D_k` com as quatro séries somáveis pelo transporte KP **em R** (`abstractKP_profileDampedActivity R`), sem separação s/R e sem trocar R por r. **Resiste.**

**C. Erosão e controle exponencial.** A erosão consome apenas a separação s/r: `walkBarrierSeparated_barrierRegions_sub_familyMass` com a família vazia em r dá separação `n − m_T` (subtração natural **truncada** antes do cast) das regiões-barreira; `m_T > n` ⇒ fator 1 ⇒ cota `δ·q_T`, sem falso decaimento e sem 8/(3e). Controle bilateral κ = 2: ambos os expoentes `≤ q_T = b_T·(2/113)` pela barreira da 55-A **com R arbitrário** (vale para expoentes negativos, pois a cota é sobre |E| via `le_abs_self`); lema escalar da 54 com as duas hipóteses; `q ≤ e^q` absorvido; erosão recomprada. Sem `δ ≤ 1`, sem novo `exp(|x−y|)`, sem cardinalidade de R/r nem fator de volume na constante. **Resiste.**

**D. Ledger exato e duas colunas.** Rederivei `profileExpectation_sub_eq_two_column_ledger_localized` a partir da forma exponencial da 55-A aplicada aos dois lados (não da identidade final da 56): partição dos núcleos tocantes em permitidos/pontes por `sum_touchingFamilies_eq_activityAllowed_add_bridge`; nos **permitidos em r** a correção some por **igualdade** dos pesos (`profileWeight_eq_of_touchCount_zero_of_same` via `hsame`) — e não por ambos serem 1, o que seria inválido para fundo geral; por núcleo, `A·W·e^E = A′·W·e^E + (A − A′)·W·e^E` por `ring`. Coluna conectora com o peso do **segundo** perfil; coluna-ponte com `(A − A′)`, sinal **MAIS**, expoente do **primeiro** perfil, suporte em `activityBridgeCores s r`. Orientação coerente com o item B. **Resiste.**

**E. Ponte com duas regiões e orçamento.** `nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions`: a geometria é s/r (`activityBridgeCore_familyTotalCard_ge hT hsep` com `T ∈ activityBridgeCores s r` dá `n ≤ m_T`), enquanto o expoente vem de `abs_typedMarkedCoreWeight_mul_exp_profile_le … T s R` — legítimo porque a barreira de expoente da 55-A vale com R arbitrário; o lema histórico da 55-B (que amarra as duas regiões a uma só) **não é editado nem invocado** — a rota é reconstituída, o que é a única opção com o módulo congelado. `card T ≤ m_T ≤ e^{3m_T/8}`, pagamento `1 ≤ e^{−n/2}·e^{m_T/2}`, fusão `e^{m_T/2}·e^{3m_T/8} = e^{7m_T/8}` absorvida em `massTilt(7/8)`. Orçamentos: conector (1/2, 2) via `sum_halfTilt_two_le` ⇒ `e^{3·D_s·(2/113)} = e^{6D_s/113}`; ponte (7/8, 1) via `sum_sevenEighthsTilt_one_le` ⇒ `e^{2·D_s·(2/113)} = e^{4D_s/113}`; (7/8, 2) não aparece. **Resiste.**

**F. Fechamento e circularidade.** Fechei por conta própria: ledger + `abs_add` + as duas colunas ⇒ dois termos ⇒ capstone por `e^{4D_s/113} ≤ e^{6D_s/113}` (D_s ≥ 0). Direção **56 ⇒ 55** em `…_of_localized`: aplica o capstone **novo** com `R := r` e traduz as hipóteses por `localized_hypotheses_of_profile_hypotheses` (fora de r ambos os fatores são 1, logo `hsame`; em r, `touchFactor` desdobra e `hδ` passa). Verifiquei por busca textual: o capstone publicado da 55 (`…_le_local_exp_decay` do módulo 55-B) **não é referenciado em nenhuma prova do módulo novo** — nem o dois-termos, nem o ledger, nem a interface de ponte da 55-B. Importar a infraestrutura ≠ invocar o resultado final. **Sem circularidade.**

**G. Casos-limite.** δ = 0: cota 0 direta (nada dividido por δ) — aplicação efetiva, não conta de RHS. Fatores efetivos iguais ⇒ `F_R(a) = F_R(a′)` **exatamente** (`profileExpectation_eq_of_touchFactor_eq`), para perfis reais arbitrários, sem regime analítico — identidade de definições, e essa liberdade **não** é transportada ao teorema analítico (que mantém [0,1]). δ = 7: admissível, frouxo, correto. r = R: recupera a 55 (item F). r = ∅ sob `hsame`: todo polímero não toca ∅, logo todos os fatores iguais ⇒ igualdade exata (`profileExpectation_eq_of_same_empty_region`) — distinto de R = ∅, onde todos os fatores são 1 (55-A). Retirada de `hsame`: a aplicação simplesmente fica com a obrigação aberta — não é contraexemplo (classificação correta dos casos V4x/W7x). Identificação com Gibbs: **não** reivindicada com fundo não unitário — o cabeçalho o nega explicitamente, e corretamente: a localização não remove o fundo. Nenhuma instância geométrica concreta com s perto de R é afirmada; os testes são condicionais/algébricos. **Resiste.**

## 5. Tratamento conjunto da QA1 com a errata C1 (autoria corrigida)

Li `RELATORIO_56-QA1.md` e `ERRATA_56-QA1-C1.md` como **um único registro corrigido**:

- **Autoria dos testes:** V1–V4x são do **construtor** (reexecutados pela QA1 na segunda passagem, o que não muda a autoria); W0–W7x são da **QA1**. Os negativos V4x/W7x deixam a obrigação `hsame` aberta: falha de aplicação esperada, não evidência de falsidade — classificação que subscrevo.
- **Correções da C1 que reconferi:** (i) contagem de linhas de declaração = **1.780** pelo método publicado (reproduzi textualmente: 1.780; o 1.790 original vinha de padrão de onze alternativas); (ii) no rebuild do construtor as dependências foram **reaproveitadas do cache** (0 Built / 1.332 Replayed), não compiladas da fonte — os 4.599 avisos são reapresentação; (iii) 38 avisos nos testes descartáveis da QA1 (W1 = 2, W3 = 6, W4 = 26, W7 = 4), separados dos 114 herdados e dos zero do módulo novo; (iv) 22 certidões de teoremas comparáveis às do construtor + 2 verificações de definições em W0, estas fora das 269 do build; (v) quatro referências numéricas da matriz e caminhos do ZIP (`build_full_clean.log` na raiz). Todas são correções de **registro da auditoria**, sem mérito matemático; o PASS da QA1 se mantém, e a C1 prevalece nos pontos corrigidos.
- **Concordância:** as rederivações independentes da QA1 (coeficiente por casos com orientação checada por antisimetria, ledger rederivado sem o lema do candidato, fechamento pelas colunas sem os dois teoremas finais, κ = 2 rederivado, ponte duas regiões com R = univ/∅/r) coincidem com as minhas, feitas antes de abrir o pacote.

## 6. Quadro de achados

| # | declaração/linha | gravidade | justificativa | correção |
|---|---|---|---|---|
| — | — | — | **Nenhum achado matemático.** | — |
| — | — | — | **Nenhum achado documental novo.** Os registros preexistentes (observação sem mérito da QA1 §6: a ponte duas regiões reprova a rota da 55-B em vez de derivá-la — inevitável com o módulo congelado; as cinco precisões da C1, já retificadas) foram confirmados contra as fontes e não são reapresentados como descobertas. | — |
| — | — | — | **Melhorias opcionais:** nenhuma. | — |

## 7. Vereditos separados

- **Custódia:** conforme (SHAs, trees, blobs, diff, contagens, hashes dos uploads e manifesto interno verificados por mim; CI verificado quanto às conclusões, com a limitação declarada quanto aos logs de checkout; assinatura registrada, não autenticada — precedente aceito).
- **Matemática:** **sem defeito.** Os sete eixos de ataque da fita foram rederivados independentemente e resistem.
- **Documentação/interpretação:** conforme; cabeçalho e docstrings não excedem o enunciado (sem otimalidade, sem ineditismo, sem termodinâmico/contínuo/mass gap, sem remoção do fundo, sem Gibbs com fundo não unitário).
- **Execução própria:** nenhuma (sem Lean); toda execução citada é de terceiros e assim atribuída.

## 8. Veredito global

**PASS NO ESCOPO.**

A Pedra 56 entrega a localização da estabilidade de perfis na região onde os fatores efetivos mudam, com fundo comum de amortecimento preservado — constante, taxa e regime das Pedras 54/55, direção 56 ⇒ 55 sem circularidade, e as interfaces exatas (fatores iguais ⇒ funcionais iguais; r = ∅) corretamente separadas do teorema analítico.

Não editei fonte, candidato, relatórios, ZIPs ou manifests; sem push, PR, merge, tag, Release ou Zenodo; **Pedra 57 não iniciada**.

— Luan da bancada

**HARD STOP.**
