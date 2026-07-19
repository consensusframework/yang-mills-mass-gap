# PEDRA 42b — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 42b.**
Base: main em `03cf539` (42a integrada, CI verde na primeira rodada, 43 arquivos,
~340 teoremas, 0 axiomas, 0 sorry).

## O que a 42a entregou (insumos prontos)

1. `spanningTreeEdgeSets G` com `mem_` explícito.
2. `penroseEdgeFiber G ET` = filter de `connectedSpanningEdgeSets G`;
   `mem_penroseEdgeFiber_iff_interval` (sob `hET`).
3. `penroseExtraEdges G ET` com os quatro lemas de coordenadas
   (`fiberToExtras_mem`, `extrasToFiber_mem`, `union_sdiff_fiber`,
   `sdiff_union_extras`) e o `penroseFiberEquiv` interno.
4. `card_union_extras` e `neg_one_pow_card_union` (sinal já fatorado).
5. `penroseEdgeFiber_disjoint` (ET₁ ≠ ET₂) e
   `biUnion_penroseEdgeFiber : biUnion = connectedSpanningEdgeSets G`.
6. Da 37ª, guardado desde então: `sum_powerset_neg_one_pow_card`
   (Σ_{F⊆X} (−1)^|F| = if X = ∅ then 1 else 0) — o gatilho (1−1)^m.

## Reindexação 1 (soma sobre fibras)

`graphUrsellCoeff G = Σ_{E ∈ CSES} (−1)^|E|`
`= Σ_{ET ∈ spanningTreeEdgeSets G} Σ_{E ∈ penroseEdgeFiber G ET} (−1)^|E|`

Ferramenta: `Finset.sum_biUnion` com `Set.PairwiseDisjoint` (mesma API usada na
34ª para `prod_biUnion`; censo v4.15 já feito). A disjunção vem de
`penroseEdgeFiber_disjoint`; a igualdade dos domínios de
`biUnion_penroseEdgeFiber`. Reescrita: `rw [← biUnion_penroseEdgeFiber, Finset.sum_biUnion hdisj]`.

## Reindexação 2 (fibra → powerset dos extras)

Para cada ET ∈ spanningTreeEdgeSets G (logo com `hET` disponível):
`Σ_{E ∈ fiber} (−1)^|E| = Σ_{F ∈ powerset(extraEdges)} (−1)^|ET ∪ F|`
via `Finset.sum_bij` (ou `sum_nbij'`) com i := (· \ ET), inversa (ET ∪ ·),
usando exatamente os quatro lemas do item 3 — nenhuma prova nova de conjunto.
Depois `neg_one_pow_card_union` fatora:
`= (−1)^|ET| · Σ_{F ⊆ extraEdges} (−1)^|F|`.

## Gatilho de cancelamento e sobreviventes

`sum_powerset_neg_one_pow_card` aplica-se ao Σ interno:
vale 1 se `penroseExtraEdges G ET = ∅`, e 0 caso contrário.
Definição nova (única definição da 42b):

`penroseTreeEdgeSets G := (spanningTreeEdgeSets G).filter (fun ET => penroseExtraEdges G ET = ∅)`

("árvores de Penrose": árvores geradoras cujo closure não adiciona aresta).
Lema de caracterização `mem_penroseTreeEdgeSets`. A soma externa reduz por
`Finset.sum_filter` (censo já feito, usada na 32ª) aos sobreviventes.

## Identidade de Penrose (capstone)

`graphUrsellCoeff G = Σ_{ET ∈ penroseTreeEdgeSets G} (−1)^|ET|`

e como toda árvore geradora em Fin (n+1) tem o mesmo número de arestas
(da 40ª: `penroseTreeEdges` tem card n; para um ET árvore, ET é ponto fixo,
logo |ET| = n), o sinal é constante:
`graphUrsellCoeff G = (−1)^n · (penroseTreeEdgeSets G).card` — forma fechada.

## Cota árvore-grafo

`(graphUrsellCoeff G).natAbs = (penroseTreeEdgeSets G).card`
`≤ (spanningTreeEdgeSets G).card` (via `Finset.card_filter_le`).
Declaração honesta mantida: contar árvores geradoras (Cayley (n+1)^{n−1} no
completo) fica FORA — nenhuma afirmação de convergência; a cota é estrutural.

## Fin 0

Toda a torre de Penrose vive em Fin (n+1). O coeficiente de Ursell em Fin 0
(tupla vazia de polímeros) não usa extração enraizada: será tratado à parte
no enunciado final se Sol quiser um teorema em `ursellCoeff` (tuplas), ou
omitido se o capstone ficar em `graphUrsellCoeff` sobre Fin (n+1) — decisão
do parecer. Nenhuma raiz artificial no tipo vazio; nenhuma generalização
para Fin n com `Nonempty`.

## O QUE NÃO ENTRA na 42b

Contagem de árvores (Cayley), convergência, log Z, série de cluster,
decaimento, massa, β > 0, qualquer soma infinita.

## Cabe numa única entrega?

SIM. Arquivo único `PenroseIdentity.lean`: 1 definição, ~8 enunciados
(caracterização do filtro, |ET| = n para árvores, reindexação 1, reindexação 2
por fibra, colapso do sinal, identidade, forma fechada, cota). Todas as APIs
já censadas em pedras anteriores (`sum_biUnion`, `sum_bij`, `sum_filter`,
`card_filter_le` — este último a confirmar no censo da Etapa Zero antes de
codar). Risco principal: plumbing do `sum_bij` com os quatro lemas — mitigado
pelo padrão da 36ª/38ª e pelas vacinas do atlas (beta-redução com `show`).

**Aguardando parecer. Nada será implementado antes.**
