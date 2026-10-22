# ERRATA 59-K-ADV-C1 — Correções de precisão do relato da primeira revisão adversarial da Pedra 59

Coordenação: Jucelha Carvalho. Origem das observações: conferência da coordenação posterior à primeira passagem (mensagem recebida em 19/10/2026).
Autor da errata: Kimi (Moonshot AI), mesma instância que emitiu o parecer original.
Data desta errata: 2026-10-19.

Esta errata corrige o **relato** da revisão. As quatro observações são **da coordenação** — não as apresento como descobertas da minha primeira passagem. Nenhuma delas aponta defeito matemático do candidato; todas tratam da precisão do meu texto. O parecer original e esta errata devem ser lidos juntos.

## 1. Documento ao qual se aplica

```text
RELATORIO_59-K-ADV.md
Bytes: 24191
SHA-256: 220be8715e589b2a24bf843b4ffefe133b984f9893c305cdbb555bc3956f56ca
```

Bytes e hash recomputados nesta sessão sobre o arquivo intacto; coincidem com o registro da coordenação.

Candidato preservado (inalterado): `dcd6e6b18a909914dd789667d9830bff106bc762`, módulo `ActivityProfileDampingOptimalCover.lean`, blob `292602ddfc1ae915a7b4bf0a6095a4d5eaa754ba`, SHA-256 `61dde0c961ef126dd813c04a869da5fd4f60ec08395f84a2fb3ad18016704cee`.

## 2. Ponto 1 (coordenação) — Custo do orçamento `(1, 1)` no exemplo do §3.B

**Trecho afetado:** §3.B, item (ii) dos exemplos próprios: "`(1, 1)` é admissível com custo `e^{−n*/2} > B*`".

**Conferência:** correta a observação. No exemplo, os dois pesos são iguais, `w = exp(−n*/2)`, e o custo é `B(δ) = (δ₀ + δ₁)·w`. O custo de `(1, 1)` é `2w`, não `w`. O mínimo descrito no mesmo trecho permanece correto: a restrição de cobertura em `η₀` é `δ₀ + δ₁ ≥ 1/2`, o custo mínimo é `w/2`, atingido por qualquer `(t, 1/2 − t)` com `t ∈ [0, 1/2]`.

**Redação corrigida (prevalece sobre o trecho original):**

> **(ii) orçamento não ótimo com custo estritamente maior** — `(1, 1)` é admissível com custo `2·e^{−n*/2} > e^{−n*/2}/2 = B*`, estrito pois `e^{−n*/2} > 0`.

**Impacto:** nenhum sobre as conclusões. A comparação estrita com o mínimo continua válida (e com folga maior: `2w > w/2`); a não unicidade do vetor minimizador e a existência de orçamento admissível estritamente subótimo permanecem demonstradas. Erro de conta do relato, não da matemática do candidato — o módulo não contém esse exemplo numérico.

## 3. Ponto 2 (coordenação) — Não compacidade do conjunto admissível irrestrito, §3.A.3

**Trecho afetado:** §3.A.3: "o conjunto irrestrito de orçamentos admissíveis (`≥ 0`, sem teto) é fechado mas ilimitado — o módulo não o declara compacto".

**Conferência:** correta a observação. A afirmação de ilimitude exige hipóteses que eu não enunciei. Análise completa:

- O conjunto admissível irrestrito `{δ ≥ 0} ∩ {AdditiveCover}` é sempre **fechado** (o ortante é fechado; a cobertura é fechada, por `isClosed_additiveCover` do próprio módulo).
- **Ilimitude requer não vacuidade e `m ≥ 1`:** se `δ` é admissível e `m ≥ 1`, então `δ + t·eᵢ` é admissível para todo `t ≥ 0` (as somas de cobertura só crescem), logo o conjunto é ilimitado e, sendo fechado, não compacto.
- **Conjunto vazio é compacto:** sem alcance, não há orçamento admissível e o conjunto é `∅`.
- **`m = 0`:** o espaço `Fin 0 → ℝ` é unitário; o conjunto admissível é `∅` ou um singleton — compacto em ambos os casos.

**Redação corrigida (prevalece sobre o trecho original):**

> **Distinção pedida pela fita:** o conjunto irrestrito de orçamentos admissíveis (`≥ 0`, sem teto) é sempre fechado; quando não vazio e `m ≥ 1`, é ilimitado, portanto não compacto — mas vazio (sem alcance) ele é compacto trivialmente, e para `m = 0` ele é vazio ou unitário, logo compacto. O módulo não o declara compacto (comentário l. 70–71, correto); a compacidade usada na existência é exclusivamente a da `feasibleBox` `[0,1]^m ∩ {cobertura}`, que vale para todo `m`, inclusive `m = 0`, e independentemente de vacuidade.

**Impacto:** nenhum sobre a rota de prova auditada — a existência usa a caixa, não o conjunto irrestrito. Correção de precisão topológica do meu relato; alinha minha formulação ao que o comentário do módulo efetivamente diz.

## 4. Ponto 3 (coordenação) — Identificação `B(δ*) = minCost`, §3.C

**Trecho afetado:** §3.C, item "Fechamento refeito sem as capstones da 59": "`exists_optimal` fornece `δ*` admissível; … `B(δ*) = minCost …` por desdobramento definicional"; também a linha da tabela de achados "defeq `minCost` ↔ soma da 58 verificada na leitura".

**Conferência:** correta a observação. `minCost` é definido como `budget n (optimalBudget …)`, com `optimalBudget = Classical.choose (exists_optimal …)`. Para um testemunho `δ*` **arbitrário** do existencial, `B(δ*) = minCost` **não** é igualdade definicional — `Classical.choose` é opaco. As duas rotas válidas são:

- **(a) Rota definicional:** escolhendo **explicitamente** `δ* := optimalBudget R r n h0 h1 h0' h1' hreach`, a identificação `B(δ*) = minCost …` é desdobramento de definição. É esta a rota do próprio módulo: as aplicações em termo (l. 471–473 e 491–493) instanciam o `δ` da 58 com `optimalBudget …`, e a conclusão da 58 (a soma explícita) se identifica definicionalmente com `minCost` no objetivo.
- **(b) Rota pela unicidade do valor:** para `δ*` arbitrário com `Admissible δ*` e a minimalidade `∀ δ, Admissible δ → B(δ*) ≤ B(δ)` (exatamente os campos devolvidos por `exists_optimal`), a identificação segue de `minCost_eq_budget_of_isMin` (l. 364–371), na orientação `minCost … = budget n δ*` — ou, equivalentemente, de `budget_eq_of_isMin` (unicidade do valor mínimo).

**Redação corrigida (prevalece sobre o trecho original):**

> **Fechamento refeito sem as capstones da 59:** dado `hreach`, `exists_optimal` fornece `δ*` admissível e minimal. Aplicando diretamente as duas estimativas publicadas da 58 a esse `δ*`, obtêm-se as duas formas com `B(δ*)`. Para identificar `B(δ*)` com `minCost`: se `δ*` é explicitamente `optimalBudget …`, a igualdade é definicional (rota adotada pelo módulo nas aplicações em termo, l. 471–473 e 491–493, cuja cadeia de desdobramento verifiquei na leitura); para um testemunho arbitrário do existencial, usa-se `minCost_eq_budget_of_isMin` (l. 364–371) na orientação adequada, com a admissibilidade e a minimalidade de `δ*` — ou a unicidade do valor mínimo (`budget_eq_of_isMin`, l. 355–361).

A linha da tabela de achados deve ler-se: "defeq `minCost` ↔ soma da 58 verificada na leitura **para a instanciação explícita em `optimalBudget`**; para testemunho arbitrário, a identificação é por `minCost_eq_budget_of_isMin`".

**Impacto:** nenhum sobre a validade das conclusões — ambas as rotas estão disponíveis no próprio módulo e o módulo usa a rota definicional corretamente. Correção de precisão lógica do meu relato sobre *qual* justificativa cabe a *qual* escolha de testemunho.

## 5. Ponto 4 (coordenação) — Comandos versus resultados de execução

**Trecho afetado:** §2, tabela de custódia, linha "Contagens": "módulo 59: **44 declarações (36 theorem + 8 def), 44 certidões próprias — cobertura 44/44**".

**Conferência:** correta a observação. O que contei no fonte são **comandos** `#print axioms`; nenhum foi executado nesta revisão (como já declarado no §5 do parecer: "Sem execução Lean nesta revisão"), logo não produzi certidão alguma.

**Redação corrigida (prevalece sobre o trecho original):**

> Contagens (snapshot, método textual): 120 módulos; 39.827 linhas; 1.878 linhas de declaração; 361 comandos `#print axioms` presentes nos fontes; módulo 59: **44 declarações (36 theorem + 8 def) e 44 comandos `#print axioms` presentes no fonte — cobertura textual 44/44 (comandos, não resultados de execução; nenhum comando foi executado nesta revisão — ver §5 do parecer original)**.

**Impacto:** nenhum sobre custódia ou matemática; elimina ambiguidade entre presença textual de comandos e certidões de execução, coerente com a declaração de ausência de execução já presente no parecer.

## 6. Impacto agregado e veredito

- **Custódia:** inalterada (o ponto 4 é de redação da tabela; as verificações descritas foram as efetivamente realizadas).
- **Matemática do candidato:** inalterada — nenhuma das quatro observações aponta defeito no módulo; os pontos 1–3 corrigem contas e qualificações **do meu relato**, e o ponto 3 explicita rotas que o próprio módulo já instancia corretamente.
- **Conclusões do parecer:** mantidas em cada seção afetada, com as redações corrigidas acima prevalecendo sobre os trechos originais.
- **Veredito:** **mantido — PASS NO ESCOPO** (primeira passagem, revisão por leitura), com o mesmo escopo delimitado do parecer original. Nenhuma razão concreta para revisão do veredito emergiu desta conferência.

## 7. Preservação e limites

O parecer original está preservado byte a byte (bytes e hash reconfirmados na §1). O candidato, os originais recebidos e o pacote de transporte não foram alterados. **Nenhuma execução Lean**, nenhum teste novo, nenhuma escrita remota, nenhuma publicação. Sem pacote de evidências: esta errata não gerou artefatos além deste arquivo.

**Pedra 60 não iniciada. HARD STOP.**
