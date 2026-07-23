# PEDRA 43 — ESTADO E MAPA COMPARATIVO (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 43ª.**
Base: main pós-42b (44 arquivos, ~360 teoremas, 0 axiomas, 0 sorry).
A 42b entregou: `penrose_identity` (φ(G) = (−1)^n·#PenroseTrees),
`penrose_identity_natAbs`, `tree_graph_bound` (|φ(G)| ≤ #SpanningTrees),
sanity desconexo/árvore, Fin 0 separado. CI verde em 2 rodadas
(1 vilão: direção `i a ha = b` na sobrejetividade do sum_bij — atlas).

## A. CONTAGEM BRUTA DE ÁRVORES

Objetivo: `(spanningTreeEdgeSets G).card ≤ (n+1)^n`.

Rota da injeção em funções de pais: cada árvore geradora ET determina
`penroseParent? (graphOfEdges ET) : Fin (n+1) → Option (Fin (n+1))` — já
TOTAL e já provado na 41a/41b que a árvore reconstrói suas arestas do
parent (`penroseTreeEdges_eq_of_isTree` + `penroseParent?_penroseTree`).
Logo o mapa ET ↦ parent-function é INJETIVO usando apenas material das
pedras 40-41: ET = availableEdges(penroseTree(graphOfEdges ET)) e
penroseTree é determinado pelo parent. Alvo formal:

  `spanningTreeEdgeSets G ↪ (Fin (n+1) → Option (Fin (n+1)))`
  card ≤ (n+2)^(n+1)  — bruto; refinável a (n+1)^n fixando parent 0 = none
  e parent v ∈ some (algo de profundidade menor), se Sol quiser a forma fina.

Custo: BAIXO (1 arquivo, ~6 lemas; `Fintype.card_fun`, `Fintype.card_option`
a censar). Cayley exato via Prüfer: custo ALTO na v4.15 (não há Prüfer;
seria uma pedra inteira nova de bijeção delicada) — NÃO recomendado agora.
A cota bruta (n+1)^n ou (n+2)^(n+1) já dá a escala n^n ~ n!·e^n que
conversa com 1/n!.

## B. TREE-GRAPH BOUND PONDERADO

No caso hard-core atual, f_ij ∈ {0, −1} e |f_ij| ∈ {0,1}: o lado direito
Σ_T ∏|f_ij| conta exatamente as árvores geradoras DENTRO do grafo de
incompatibilidade — que é o que `tree_graph_bound` já dá, pois
spanningTreeEdgeSets G só contém arestas de G (∏ = 1 nelas). Ou seja:
**na especialização hard-core, B já está provado pela 42b** — bastaria um
lema de apresentação. A generalidade ponderada (f_ij reais) exigiria
refazer 37→42 com pesos: custo MUITO ALTO, ganho nulo para o gás
hard-core que temos. NÃO recomendado.

## C. RETORNO AOS POLÍMEROS

Objetivo imediato (custo BAIXO, já maduro):

  `(ursellCoeff γ).natAbs ≤ (spanningTreeEdgeSets (polymerIncompatibilityGraph γ)).card`

— composição direta de `ursellCoeff := graphUrsellCoeff ∘
polymerIncompatibilityGraph` (37ª) com `tree_graph_bound` (42b).
Um lema, talvez dois (versão com a identidade exata em #PenroseTrees).

Depois, os três gargalos na ordem de dependência real:
1. contagem de árvores (= degrau A) — necessária para QUALQUER critério;
2. bound de `polymerWeight` — |w_β(C)| ≤ (2β)^|C| é quase imediato da 32ª
   (|m_p| ≤ 2β, produto sobre C) + cota do integrando; material pronto;
3. contagem de polímeros contendo uma plaqueta fixa — geometria do
   reticulado (vizinhança de plaquetas limitada), pedra nova de
   combinatória geométrica; o mais caro dos três.

## RECOMENDAÇÃO DE ORDEM

**43ª = C-imediato + A**, numa única entrega ou em (a)/(b):
(a) o corolário de polímeros (2 lemas, cola 37↔42b);
(b) a injeção parent-function e `#SpanningTrees ≤ (n+2)^(n+1)` (com a
    forma fina (n+1)^n como refinamento se o plumbing do Option couber).
Isso fecha a cadeia |ursellCoeff γ| ≤ (número explícito), deixando como
únicas frentes futuras o bound de polymerWeight (barato, 44ª?) e a
contagem geométrica de polímeros (45ª+) — uma frente por vez, sem abrir
três. B fica registrado como já-satisfeito no caso hard-core.

## O QUE NÃO ENTRA na 43ª (qualquer variante)

Prüfer/Cayley exato, pesos gerais f_ij, 1/n!, somas sobre tuplas,
log realZ, Kotecký–Preiss, limite termodinâmico, clustering, massa.

**Aguardando parecer. Nada será implementado antes.**
