# PEDRA 42 — MAPA: CANCELAMENTO POR FIBRAS E O TREE-GRAPH BOUND
# (teus 10 pontos do parecer da 41b, em EDGE SETS; NENHUMA
# implementação até autorização)

## Retorno ao domínio real da soma (tua instrução)
A soma de Ursell vive em Finset (OrderedEdge (n+1)) via
connectedSpanningEdgeSets G. Toda a teoria 40-41 transporta por:
graphOfEdges / availableEdges_graphOfEdges (inversos ✓ 40b) e
mem_connectedSpanningEdgeSets (E ⊆ available G ∧ Conexo).

## Os 10 pontos, custeados
1. spanningTreeEdgeSets G := (availableEdges G).powerset.filter
   (fun E => (graphOfEdges E).IsTree). Mem-caracterização. BAIXO.
2. Mapa em edge sets: πE E := penroseTreeEdges (graphOfEdges E).
   Boa definição: para E ∈ CSES, πE E ∈ spanningTreeEdgeSets
   (40b: isTree + πE ⊆ E ⊆ available). BAIXO.
3. Fibra em edge sets:
   πE E = ET ↔ ET ⊆ E ∧ E ⊆ penroseClosureEdges G (graphOfEdges ET):
   transporte da equivalência da 41b (fibras = intervalos) pela
   ponte grafo↔Finset: H := graphOfEdges E, T := graphOfEdges ET;
   precisa: (i) πE em termos de π: penroseTreeEdges (graphOfEdges E)
   vs availableEdges (π (graphOfEdges E)) — 40b id ✓;
   (ii) H ≤ H' ↔ E ⊆ E' para grafos gerados: graphOfEdges_mono (ida ✓
   39ª) e a volta via availableEdges_graphOfEdges — lema novo BARATO:
   graphOfEdges E ≤ graphOfEdges E' ↔ E ⊆ E' (mem por canonical).
   (iii) closure em edge sets: availableEdges (penroseClosure G T) =
   penroseClosureEdges G T — instância do id 40b ✓ GRÁTIS.
   CUSTO MÉDIO (burocracia de transporte, zero matemática nova).
4. extraEdges G ET := penroseClosureEdges G (graphOfEdges ET) \ ET.
   BAIXO.
5. Bijeção fibra ↔ powerset dos extras: E no intervalo ↔ E = ET ∪ F,
   F ⊆ extraEdges: ida F := E \ ET; volta união; inversas por
   sdiff/union com ET ⊆ E e disjunção ET ∩ extra = ∅ (Finset:
   union_sdiff_cancel etc — NOMES A CENSAR: Finset.union_sdiff_of_subset,
   sdiff_union_of_subset?, disjoint_sdiff). MÉDIO (burocracia sdiff).
6. Cardinalidade: |ET ∪ F| = |ET| + |F| por disjunção
   (Finset.card_union_of_disjoint ✓ nome a confirmar). BAIXO.
7. Soma alternada da fibra = (−1)^{|ET|} · Σ_{F ⊆ extra} (−1)^{|F|}:
   reindexação da soma da fibra pelo powerset via sum_nbij'/sum_bij
   (ida/volta do ponto 5) + pow_add. MÉDIO.
8. Lema da 37ª (sum_powerset_neg_one_pow_card) dispara:
   Σ_F (−1)^{|F|} = if extra = ∅ then 1 else 0 ✓ PRONTO.
9. Sobreviventes: fibras com extraEdges = ∅ — def
   IsPenroseTreeEdgeSet ET := ET ∈ spanningTreeEdgeSets G ∧
   extraEdges G ET = ∅ ("árvores de Penrose"). BAIXO.
10. CAPSTONES:
   (a) IDENTIDADE DE PENROSE:
       graphUrsellCoeff G = Σ_{ET Penrose-tree} (−1)^{|ET|}
       — via partição de CSES nas fibras: CSES = biUnion sobre
       spanningTreeEdgeSets das fibras-intervalo (disjunção = 41b;
       cobertura = πE); Finset.sum_biUnion (✓ 34ª) + pontos 7-8.
   (b) TREE-GRAPH BOUND:
       |graphUrsellCoeff G| ≤ (spanningTreeEdgeSets G).card
       — triângulo sobre (a) com |(−1)^k| = 1 (padrão da 39ª);
       refinamento |·| ≤ #PenroseTrees ≤ #spanningTrees GRÁTIS
       (subset filter). 

## Decisão de corte (pediste avaliação)
A matemática nova é ZERO — tudo é transporte + burocracia de Finsets
sobre teoremas prontos. MAS são ~10 lemas de ponte + 2 reindexações
(sum_biUnion das fibras; sum_bij fibra↔powerset). Estimativa: 350-420
linhas. RECOMENDO o corte:
- 42a: pontos 1-6 (ponte grafo↔edge-set, fibra em Finsets, bijeção
  com powerset dos extras) — termina no lema 5/6;
- 42b: pontos 7-10 (as duas reindexações de soma, o disparo do
  (1−1)^m guardado desde a 37ª, identidade de Penrose e bound).
Cabe numa se as pontes saírem lisas — mas as últimas três pedras
mostraram 2-3 rodadas de vilões sintáticos cada; o corte protege.

## Censo prévio obrigatório (antes da implementação)
Finset.card_union_of_disjoint / union_sdiff / sdiff_union_of_subset /
disjoint_sdiff_self_left — formas exatas na v4.15;
Finset.sum_biUnion (✓ já usada na 34ª com PairwiseDisjoint).

Aguardo parecer (inclusive corte a/b). — Fable
