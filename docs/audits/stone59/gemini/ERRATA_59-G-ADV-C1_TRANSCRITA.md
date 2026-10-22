# `ERRATA_59-G-ADV-C1`

Esta errata complementa e preserva o parecer original `RELATORIO_59-G-ADV.md`, incorporando três precisões atribuídas à coordenação e recebidas após o encerramento da primeira passagem:

1. **Inexistência de `ActivityProfileMultiRegion.budget`:** Retifica-se a observação da Secção 4. A definição `ActivityProfileMultiRegion.budget` não existe; na Pedra 58 invoca-se apenas o teorema `ActivityProfileMultiRegion.budget_nonneg`, cujo enunciado utiliza diretamente a soma expandida. Na Pedra 59 (`ActivityProfileOptimalCover`), `budget` é uma definição nova e `budget_nonneg'` é um teorema. Retira-se a alegação de duplicação de definição anterior.

2. **Condições para não-compacidade do conjunto irrestrito:** Retifica-se a formulação do Eixo A. O conjunto irrestrito de orçamentos admissíveis $\{\delta \ge 0 \mid \text{AdditiveCover } \delta\}$ deixa de ser compacto somente quando é **não vazio** (sob `Reaches`) e **$m \ge 1$**. Quando o conjunto viável é vazio (falha de `Reaches`) ou quando $m = 0$, ele é compacto. A interseção com $[0,1]^m$ (`feasibleBox`) garante compacidade incondicionalmente.

3. **Natureza de $\chi$:** Retifica-se a nomenclatura da tabela do Eixo C. Nas assinaturas das Pedras 58 e 59, $\chi : G \to \mathbb{R}$ é apenas uma função real mensurável (`mχ : Measurable χ`) satisfazendo `hχabs : ∀ g : G, |χ g| ≤ 1`, sem hipótese de que seja um caráter de grupo.

**Impacto no veredito:** Estas precisões corrigem imprecisões descritivas do próprio relatório do revisor e **não alteram o veredito `PASS NO ESCOPO**`, pois o código de `ActivityProfileDampingOptimalCover.lean` já estava livre dessas inexatidões. Mantém-se a delimitação original: revisão por leitura, **sem execução Lean e sem recálculo de hashes nesta revisão**.

**HARD STOP.**
