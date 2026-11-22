# RELATORIO_60-K-ADV — Primeira revisão adversarial da Pedra 60

**Candidato:** `778e2c7b27f0357110ba83e9b466984747577823` (ref de bundle `refs/heads/stone60`)
**Pai declarado:** `2ef6500deeb5dd7ddd70c5f208f690e9e0470353` (Version 59; remoto: `refs/heads/main`, `HEAD`, tag `zenodo-v59`)
**Módulo:** `Phase3/LatticeGauge/ActivityProfileDampingOptimalGeometry.lean`
**Base de interfaces:** v59 congelada (`PEDRA59_KIMI_INPUTS.zip`), conforme instrução
**Revisor:** Kimi (K-ADV) — primeira passagem, revisão adversarial por leitura
**Data da revisão:** 2026-11-23

---

## 1. Custódia e integridade

### 1.1 Arquivos recebidos (medidos por mim)

| Arquivo | Bytes | SHA-256 |
|---|---|---|
| `ActivityProfileDampingOptimalGeometry (1).lean` | 36.088 | `035a9cd5f18bd137bc989b18db0373fd9015272edcb589075a313b34d97948d9` |
| `stone60_candidate.bundle` | 9.903 | `4dcd00b91ee15c63de2675642668f9b5348dac5458d7e8bb8d5cb581a60f85fe` |
| `stone60_candidate.diff` | 45.826 | `27d583c633b9825144f8a0422d2d5d9d7d8c25094f00e74c5acd708540fa9f83` |

**Observação de custódia (sem impacto):** o nome do módulo carrega o sufixo `" (1)"`, marca típica de segundo download do mesmo arquivo. O conteúdo é byte a byte idêntico ao blob git do candidato (§1.3), portanto o sufixo é apenas de nomeação local. Registro para o ledger; nenhuma ação necessária.

**Truncamento:** módulo com 646 linhas, terminando em `end LatticeGauge` precedido do bloco de 50 certificados — arquivo íntegro, leitura completa (646/646 linhas). O diff anexado termina na linha de glob do lakefile — íntegro. Nenhum arquivo apareceu truncado; a leitura não parou em nenhum ponto.

### 1.2 Bundle e commit (verificado pessoalmente)

- `git bundle verify`: **OK** — bundle v2/sha1, contém `778e2c7b…` como `refs/heads/stone60`, pré-requisito `2ef6500d…`.
- O pré-requisito `2ef6500d…` está **publicamente disponível** no remoto (`HEAD` = `refs/heads/main` = tag `zenodo-v59`); buscado do GitHub e registrado localmente.
- Commit `778e2c7b27f0357110ba83e9b466984747577823`: tree `a7295ffe3dd1bec2496a1353f7a2fd8665490199`, parent `2ef6500d…`, autor/committer `Claude <noreply@anthropic.com>`, timestamp `2026-11-22T13:06:36Z`, com assinatura SSH embutida (**não verificada criptograficamente** — não possuo a chave pública; limitação L3).
- O candidato **não** consta no `ls-remote` público — situação normal de candidato local; a autenticação foi feita pela cadeia de hashes abaixo.
- **Encerramento positivo da limitação L3 da Pedra 59:** o candidato da 59, `dcd6e6b1…`, antes ausente do remoto, agora é `refs/heads/stone59` (e `refs/pull/44/head`) no GitHub. Aquela pendência de custódia está resolvida a favor da cadeia.

### 1.3 Identidade de conteúdo (recomputada por mim, independente das ferramentas git)

- **Módulo:** blob git `fbf6452ab07668d8b7965a3a35f9a11e3a194e9c` (36.088 bytes). Recomputei o identificador em Python (`sha1(b"blob %d\0" % len + dados)`): **confere**. `cmp` entre o upload e o blob extraído do bundle: **idênticos, byte a byte**.
- **Diff anexado × diff real:** `git diff 2ef6500d 778e2c7b` regenerado por mim; `cmp` com `stone60_candidate.diff`: **idênticos, byte a byte**.
- **Árvore raiz do candidato:** recomputada em Python a partir das entradas `ls-tree` (modos normalizados, `040000 → 40000`, como calibrado na Pedra 59): resultado `a7295ffe3dd1bec2496a1353f7a2fd8665490199` — **confere** com o cabeçalho do commit.
- **Árvore Phase3 do candidato:** recomputada: `6f40821434929b7949dafc91dfd5b63e02d4484d` (contém o módulo novo).
- **Diferença pai → candidato:** exatamente **dois caminhos** — adição do módulo (646 linhas) e uma linha no `[[lean_lib]] globs` de `Phase3/lakefile.toml` acrescentando `"LatticeGauge.ActivityProfileDampingOptimalGeometry"` ao final da lista. Nenhum outro arquivo tocado. **Nenhuma troca silenciosa de alvo.**

### 1.4 A "base v59 congelada" é exatamente o código do pai

- A árvore Phase3 do pai `2ef6500d` é `c3157cb9d428b74f73bf789588a3ab2f48d429e7` — **idêntica à árvore Phase3 declarada na FITA_59** para o candidato da 59.
- `diff -r` entre o snapshot `PEDRA59_KIMI/snapshot/Phase3` (pacote congelado) e `git archive 2ef6500d Phase3`: **idênticos, byte a byte, 120 módulos**; o módulo novo não existia lá (é adição pura; o commit passa a ter 121 módulos Phase3, coerente com "121 Built" da mensagem de commit).
- O pai difere do candidato da 59 (`dcd6e6b1…`) apenas em `docs/` e `formalization.yaml` (merge da branch `stone59-doc`, PR #45) — **código Phase3 intocado**.
- **Verificação cruzada de contagem:** a base congelada contém 361 comandos `#print axioms` nos módulos Phase3; 361 + 50 novos = **411**, exatamente o número de certificados declarado na mensagem de commit. Consistente.

**Conclusão de custódia:** cadeia upload ≡ blob ≡ bundle ≡ árvores recomputadas ≡ parent remoto, sem elos quebrados. O material sob revisão é exatamente o commit `778e2c7b…` sobre a base v59.

---

## 2. Escopo e o que foi lido

- **Módulo inteiro lido:** 646/646 linhas, todas as 50 declarações e os 50 comandos `#print axioms` finais.
- **Contagens mecânicas (grep):** 42 `theorem` + 4 `noncomputable def` + 2 `def` + 1 `structure` + 1 `noncomputable instance` = **50**; 50 `#print axioms`. Confere com a mensagem de commit ("42 theorems, 2 def, 4 noncomputable def, 1 structure, 1 instance; one `#print axioms` each").
- **Construções proibidas:** busca por `sorry|admit|native_decide|^axiom |unsafe|implemented_by|extern`: **nenhuma ocorrência**.
- **Interfaces da base v59 lidas na fonte congelada** (não de memória): `AdditiveCover` (59, l.117), `Admissible` (l.123), `budget` (l.128), `Reaches` (l.133), `optimalBudget` (l.312), `minCost` (l.320), `optimalBudget_admissible` (l.326), `optimalBudget_le_one` (l.336), `minCost_le_budget` (l.341), `minCost_nonneg` (l.348), `admissible_zero_of_touchFactor_eq` (l.376), `minCost_eq_zero_iff` (l.390), os dois capstones (l.457, l.478), `profileExpectation_eq_of_touchFactor_eq` (`ActivityProfileDampingLocality`, l.884).
- **Lean não foi executado.** Não há toolchain Lean/lake neste ambiente; esta revisão é por leitura. Alegações de compilação da mensagem de commit ("rc=0, 121 Built / 0 Replayed, 411 certificados `[propext, Classical.choice, Quot.sound]`, 0 warnings no módulo novo") são **declarações do construtor, não observações minhas** (limitação L1).

---

## 3. Análise adversarial, eixo a eixo

### 3.A — G0: `Reaches` como relação de equivalência (l.130–162)

`Reaches R r a b` (59, l.133) é, por definição, "todo polímero cujo fator efetivo muda toca alguma região". O teorema `reaches_iff_untouched_eq` explicita a contrapositiva: `Reaches a b ⟺ ∀ η, (∀ i, ¬ typedTouchesSupport η (r i)) → touchFactor R a η = touchFactor R b η`. Refiz os dois lados: (→) se o fator muda num polímero intocado, `Reaches` fornece um `i` que o toca — contradição; (←) se o fator muda, a contrapositiva da caracterização fornece o `i`. Correto, e **nenhuma cobertura de todos os polímeros é assumida** — a quantificação é universal com premissa, e polímeros intocados simplesmente satisfazem a conclusão. `refl/symm/trans` são imediatos e corretos; `Equivalence` fecha. Sem hipótese oculta: `a b : Polymer N → ℝ` arbitrários, sem cota [0,1] — verifiquei que os quatro lemas não usam cota alguma.

### 3.B — G1: transporte e adição de orçamentos (l.167–216)

- `additiveCover_symm` por `abs_sub_comm` — a cobertura é simétrica nos dois perfis. ✓
- `admissible_zero_self` usa `admissible_zero_of_touchFactor_eq` (59, l.376) com `fun _ => rfl`: o orçamento zero cobre `(a, a)`. ✓
- `coverSum_add`: distributividade da soma com `if`, índice a índice. **Regiões repetidas mantêm suas multiplicidades**, pois a soma é sobre `i : Fin m` (índices, não conjuntos) — verifiquei que nada no lema quotienta índices com a mesma região. ✓
- `admissible_add`: o ponto que sustenta o triângulo. Não-negatividade da soma por `add_nonneg`; cobertura por `|a−c| ≤ |a−b|+|b−c|` polímero a polímero (`abs_sub_le`) seguida de `add_le_add` sobre as duas coberturas. **Crucial e verificado na fonte:** `Admissible` (59, l.123) é `(∀ i, 0 ≤ δ i) ∧ AdditiveCover …` — **sem cota superior** `δ i ≤ 1`. A caixa `[0,1]^m` só existia na 59 para *existência* do minimizante; a *admissibilidade* é livre. Logo `δab + δbc` (coordenadas até 2) é legitimamente admissível. ✓
- `budget_add`: `B(δ) = Σ i, δ i·exp(−n i/2)` é linear em `δ`; a prova (`Finset.sum_add_distrib` + `ring`) não usa não-negatividade nem cota. ✓

Nenhum β, nenhuma integral, nenhuma separação, nenhum Cf nestes lemas — como anunciado. ✓

### 3.C — G2: `minCost` é simétrico, zero na diagonal, subaditivo (l.222–267)

- `minCost_proof_irrel` por `rfl`: irrelevância de provas **do kernel** (não é axioma adicional; `minCost` depende de hipóteses em `Prop`). O enunciado está correto ao *não* reivindicar unicidade do vetor minimizante — é uma afirmação sobre o valor. ✓
- `minCost_comm`: `le_antisymm` com `minCost_le_budget` nas duas direções, usando o `optimalBudget` do lado oposto transportado por `admissible_symm`. Refiz: `B*(a→b) ≤ B(δ*(b→a)) = B*(b→a)` (a igualdade é a definição de `minCost`, 59 l.320) e vice-versa. Não compara vetores, só valores. ✓
- `minCost_self`: `minCost_eq_zero_iff.mpr (fun _ => rfl)`. ✓
- `minCost_triangle` — **o coração da pedra, verificado elo a elo**:
  1. `δab := optimalBudget … hab` e `δbc := optimalBudget … hbc` são admissíveis (`optimalBudget_admissible`, 59 l.326);
  2. `admissible_add` dá `Admissible R r a c (δab + δbc)` — com coordenadas possivelmente > 1, o que é **legítimo** porque `minCost_le_budget` (59, l.341) compara com **todo** orçamento admissível, sem hipótese `δ ≤ 1` (conferido literalmente na assinatura da base congelada);
  3. `minCost_le_budget` dá `B*(a,c) ≤ B(δab + δbc)`;
  4. `budget_add` dá `B(δab + δbc) = B(δab) + B(δbc)`;
  5. as definições de `minCost` reescrevem o lado direito como `B*(a,b) + B*(b,c)`.

  A soma dos minimizantes **não é alegada ótima** — é apenas uma testemunha admissível, o que basta para a cota superior. É exatamente o uso para o qual a Pedra 59 tornou `minCost_le_budget` global. Sem hipótese residual. ✓

### 3.D — G3/G4: a componente e a instância de pseudométrica (l.274–346)

- `ProfileComponent R r n aref`: campos `prof`, `0 ≤ prof ≤ 1`, `Reaches R r aref prof`. **A pertinência não depende de `n`** — `n` é parâmetro do tipo, ausente dos campos; verifiquei a estrutura linha a linha. O tipo carrega `n` para a geometria ser inferível. Correto como documentado. ✓
- `ProfileComponent.reaches`: dois membros se alcançam por `symm`+`trans` via a referência. Logo `optimalDist` está definida em **todo** par do tipo — nenhum valor convencional para pares sem reach é necessário. É exatamente por isso que a pseudométrica vive na componente e não no espaço cru de perfis: fora dela, pares sem reach não têm `minCost` definido. ✓
- `optimalDist_nonneg/self/comm/triangle`: projeções diretas de G2. ✓
- `optimalDist_eq_zero_iff`: `d(x,y) = 0 ⟺ ∀ η, touchFactor R x η = touchFactor R y η` — igualdade dos fatores efetivos em **todos** os polímeros, não apenas nos intocados. Ponto sutil e correto: dentro da componente, `Reaches` já garante igualdade fora das regiões; distância zero **adiciona** a igualdade dentro das regiões (um polímero coberto com fator alterado forçaria `δ i > 0` em algum índice, e os pesos `exp(−n i/2) > 0` tornariam o custo positivo — este é o conteúdo de `minCost_eq_zero_iff` na 59). Perfis crus diferentes fora de `R` (fatores iguais) **não** são identificados pelo tipo — a estrutura é crua, a métrica tem kernel. Por isso **pseudo**métrica, não métrica. ✓
- `optimalDist_ref_indep`: perfis iguais em componentes de referências diferentes têm distâncias iguais; prova por `cases`+`subst`+`rfl` apoiada em irrelevância de provas. Verifiquei que `minCost` não menciona `aref` em seus argumentos — a referência organiza o domínio, não entra na otimização do par. ✓ (Escopo correto: independência apenas em `aref`, com `R r n` fixos — a distância **depende** de `n` via os pesos, e o lema não afirma o contrário.)
- `instPseudoMetricSpace`: os quatro campos explícitos (`dist`, `dist_self`, `dist_comm`, `dist_triangle`); uniformidade e bornologia são os defaults de Mathlib da estrutura. Coerente com o padrão da biblioteca; **elaboração não verificada por execução** (L1), mas a forma é a canônica de `PseudoMetricSpace` em Mathlib 4.15. `dist_eq_optimalDist`/`dist_eq_minCost` por `rfl` confirmam que o `dist` inferido é o `minCost` da 59 definicionalmente. ✓

### 3.E — G5: variações e cadeias (l.351–382)

- Três pontos: `abs_dist_sub_le` de Mathlib — `|d(x,z) − d(y,z)| ≤ d(x,y)`. ✓
- Quatro pontos: `dist_dist_dist_le` com `Real.dist_eq` reescrito para o valor absoluto — a forma usada (`dist` externo em ℝ) é consistente com o `rw`. Coerência sintática verificada; elaboração não executada (L1). ✓
- Poligonal `d(x₀,x_k) ≤ Σ d(x_j,x_{j+1})`: indução em `k` com `Fin.sum_univ_castSucc`; **k = 0 incluso** (soma vazia, `d(x₀,x₀) = 0 ≤ 0`). Refiz o passo: triângulo no último salto + hipótese de indução na cadeia curta + congruência de somas com `Fin.succ_castSucc`. ✓

### 3.F — G6: como as duas cotas da Pedra 59 viram as constantes de Lipschitz (l.391–533)

Mecanismo verificado argumento a argumento contra a base congelada:

1. Os capstones da 59 (l.457 e l.478) dão, sob reach, `|F_R(a) − F_R(a′)| ≤ C · minCost …` com `C = Cf·[e^{6D_s/113} + e^{4D_s/113}]` (dois termos) e `C = (2Cf)·e^{6D_s/113}` (compacta), respectivamente. As assinaturas batem **literalmente** com as chamadas da 60 (ordem de argumentos, hipóteses `hβ hχabs hsmall mf hCf hsep` e as cotas de perfil). ✓
2. Na componente, `minCost = dist` **definicionalmente** (G4), logo `|F(x) − F(y)| ≤ C · dist x y` — exatamente a forma exigida por `LipschitzWith.of_dist_le_mul` com `K : ℝ≥0`.
3. As constantes são empacotadas como `ℝ≥0` (`twoTermConst`, `compactConst`) com `0 ≤ Cf` **derivado** do majorante absoluto via `nonneg_of_abs_le_of_config hCf` (sem hipótese `0 ≤ Cf` explícita) e positividade das exponenciais. As coerções `↑K₂ = Cf·(e^{6D_s/113}+e^{4D_s/113})` e `↑K = (2Cf)·e^{6D_s/113}` são provadas por `rfl` (`coe_twoTermConst`, `coe_compactConst`) — **exatas**, não aproximadas, como o enunciado promete. ✓
4. `UniformContinuous` e `Continuous` seguem por `LipschitzWith.uniformContinuous`/`.continuous` — para a pseudométrica aqui construída, sem outra topologia reivindicada. ✓
5. Cadeias: `|F(x₀) − F(x_k)| ≤ K₂·Σ d` e idem com `K`, por `mul_le_mul_of_nonneg_left` sobre a poligonal (não-negatividade da constante justificada na prova). ✓
6. `functional_eq_of_dist_eq_zero`: `d = 0 ⟹ F(x) = F(y)` **sem o regime β pequeno** — a rota é algébrica: `d = 0` ⟹ fatores efetivos iguais em todo `η` (3.D) ⟹ funcionais iguais pela identidade da Pedra 56 (`profileExpectation_eq_of_touchFactor_eq`, Locality l.884, cuja docstring confirma "no KP regime, no separation, no bound on f"). Os `omit` removem corretamente as instâncias desnecessárias. Verifiquei que o teorema não carrega `hβ` nem `hsmall`. ✓

### 3.G — G7: compatibilidade (l.538–589)

`ofReach`/`ofReach'` colocam dois perfis [0,1] com reach na componente do primeiro; `dist_ofReach` é `rfl`; as duas recuperações reaplicam G6 e têm **os mesmos tipos** dos capstones publicados da 59. São transportes pela nova interface — declarados como tais ("compatibility check… not an independent derivation"), não como provas independentes. ✓

---

## 4. Hipóteses implícitas encontradas

1. `[NeZero N] [Fintype (Site N)]` (l.124) — herdadas de todo o projeto; necessárias às interfaces upstream (`touchFactor`, `supportLinkFinset`). Declaradas, não ocultas.
2. No bloco analítico (l.386–388): `G` grupo com estrutura mensurável (`MeasurableSpace`, `MeasurableMul₂`, `MeasurableInv`), `μm` medida de probabilidade σ-finita. Os `omit` em `twoTermConst`, `compactConst`, `coe_*` (removem as três de grupo) e em `functional_eq_of_dist_eq_zero` (remove também `SigmaFinite`/`IsProbabilityMeasure`) estão corretos e conservadores. As variáveis de `G`/`μm` são declaradas **depois** de G5 (l.386): a parte geométrica G0–G5 não pode tê-las capturado — verifiquei o posicionamento. ✓
3. `hsep : ∀ i, WalkBarrierSeparated s (r i) (n i)` só aparece nos teoremas analíticos (G6/G7) — exatamente as hipóteses dos capstones da 59, nem mais nem menos. ✓
4. A existência do minimizante (`exists_optimal`, via `Classical.choose` na 59) é **importada**, não re-provada — dependência herdada correta de `Classical.choice`, listada entre os axiomas esperados. ✓
5. A instância usa os defaults de uniformidade/bornologia de `PseudoMetricSpace`; nenhuma outra topologia é reivindicada (o header diz isso explicitamente). ✓
6. Irrelevância de provas do kernel sustenta `minCost_proof_irrel`, `optimalDist_eq_minCost` e `optimalDist_ref_indep` — mecanismo nativo, não axioma. ✓

## 5. Casos degenerados testados (por leitura)

- **`m = 0`:** `Reaches` colapsa em "fatores iguais em todo polímero"; o orçamento vazio é admissível com custo 0; distância 0 em toda a componente. O header declara isso (l.96) e a 59 já continha `touchFactor_eq_of_reaches_fin_zero` e `budget_fin_zero`. ✓
- **`R = ∅`:** todos os fatores efetivos são 1; reach trivial; distância 0 por razão distinta de `m = 0` — a distinção "duas razões diferentes" do header (l.96–98) é correta. ✓
- **Componente vazia:** possível (ex.: `m = 0`, `R ≠ ∅`, `aref ≡ 2` — nenhum perfil em [0,1] reproduz seus fatores). `PseudoMetricSpace` não exige `Nonempty`; todos os teoremas quantificam sobre membros e valem vacuamente; `LipschitzWith` idem. Nenhuma hipótese de não-vacuidade em lugar algum — verifiquei. ✓
- **Referência fora de [0,1]:** permitida; a referência não precisa ser membro; membros em [0,1] podem alcançá-la (a relação só restringe fatores fora das regiões). ✓
- **Regiões repetidas:** multiplicidades preservadas nas somas (índices, não conjuntos — §3.B). ✓
- **Soma de minimizantes com coordenadas até 2:** coberta pela generalidade de `minCost_le_budget` (§3.C) — o caso degenerado que teria quebrado o triângulo se a 59 exigisse `δ ≤ 1` na comparação. Não exige. ✓
- **`k = 0` na poligonal:** incluso e verificado (soma vazia, diagonal). ✓
- **Dependência em `n`:** a pertinência à componente não depende de `n`, mas a distância sim (pesos `exp(−n i/2)`); `optimalDist_ref_indep` é corretamente restrito a `n` fixo. Nenhuma conclusão indevida sobre independência de `n`. ✓

## 6. Conclusões mais fortes que os enunciados (caça a overclaim)

Nenhuma encontrada. Verifiquei especificamente:

- `optimalDist_eq_zero_iff` caracteriza o kernel pelos **fatores efetivos**, sem afirmar igualdade de perfis crus — o header diz exatamente isso (l.45–47, l.102–103). ✓
- Nenhum ponto reivindica unicidade do vetor minimizante; há *disclaimers* explícitos em `minCost_comm` (l.230–231), `minCost_triangle` (l.249–251) e no header (item 5). ✓
- As recuperações de G7 são declaradas como compatibilidade/transporte, não como derivações independentes da 59. ✓
- A seção "Limits" do header (l.100–109) nega precisamente o que um revisor tentaria inferir a mais: métrica (não pseudo), quociente, completude, equivalência com topologia produto/norma uniforme, extensão a pares sem reach, dualidade de PL, algoritmo, diferenciabilidade, monotonicidade do funcional, melhoria numérica das constantes. Escopo fechado e honesto. ✓
- A mensagem de commit não promete além do conteúdo: 50 declarações, as propriedades listadas, "constants are those of Stone 59; nothing is improved numerically". ✓

## 7. Limitações desta revisão

- **L1 — Sem execução Lean.** Nenhum Lean/lake/elan neste ambiente; não compilei o módulo nem verifiquei certificados por execução. As afirmações "rc=0, 121 Built / 0 Replayed, 411 certificados, 114 warnings herdados, 0 warnings no módulo novo" são da mensagem de commit. O que verifiquei: coerência sintática completa, assinaturas de todas as interfaces usadas contra a base v59 congelada, contagens mecânicas (50 declarações = 42+4+2+1+1; 50 `#print axioms`; 361 base + 50 = 411 ✓), ausência de construções proibidas, e redesenvolvimento independente de todas as cadeias de prova G0–G7.
- **L2 — Materiais citados, não fornecidos.** As fitas 60-A/60-L e o arquivo de viabilidade `T60A_optimal_geometry_tests.lean` são citados no cabeçalho; os testes "live outside the tree" (mensagem de commit). Não foram auditados por não constarem do pacote.
- **L3 — Assinatura SSH não verificada.** O commit carrega assinatura SSH embutida; não possuo a chave pública para verificá-la. A autenticação do candidato foi feita pela cadeia de hashes (§1.3) e pelo parent remoto (§1.2). O candidato não consta no remoto — normal para candidato local. (A pendência análoga da Pedra 59 foi encerrada positivamente: `dcd6e6b1…` agora é público como `refs/heads/stone59`.)
- **Observação sem impacto:** sufixo `" (1)"` no nome do upload (§1.1); conteúdo idêntico ao blob.

## Veredito

**PASS NO ESCOPO.**

A Pedra 60 faz exatamente o que anuncia: caracteriza `Reaches` como equivalência, transporta e soma coberturas admissíveis, prova que o custo mínimo da 59 é simétrico, nulo na diagonal e subaditivo — com o ponto delicado (a soma de minimizantes fora da caixa [0,1]^m) legitimado pela generalidade de `minCost_le_budget` —, instala `PseudoMetricSpace` na componente de perfis alcançáveis com `dist` definicionalmente igual a `minCost`, caracteriza distância zero como igualdade de fatores efetivos (não de perfis crus), e transporta as duas cotas da 59 para constantes de Lipschitz exatas com coerções `rfl`, incluindo a igualdade do funcional a distância zero por rota algébrica sem regime. Sem hipóteses indevidas, sem conclusões além dos enunciados, sem construções proibidas, custódia íntegra de ponta a ponta. Veredito condicionado às limitações L1–L3 acima, nenhuma delas nova nesta cadeia.

Nenhuma modificação, publicação, commit, push, tag ou escrita no candidato foi feita ou autorizada por esta revisão.

**HARD STOP.**
