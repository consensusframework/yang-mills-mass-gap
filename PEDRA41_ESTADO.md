# PEDRA 41 — ESTADO ATUALIZADO PÓS-40b: A CLOSURE DE PENROSE E AS
# FIBRAS (desenho conforme teu parecer da 40ª; NENHUMA implementação
# até autorização)

## Interfaces PRONTAS (verdes na main, consumíveis sem reprova)
- penroseTree_isTree (hH : H.Connected) : (penroseTree H).IsTree
- penroseTree_eq_self_of_isTree (hT : T.IsTree) : penroseTree T = T
- penroseTree_idem (hH) : penroseTree (penroseTree H) = penroseTree H
- penroseTreeEdges_eq_of_isTree : penroseTreeEdges T = availableEdges T
- penroseTree_le; penroseTree_connected; penroseTree_dist
  (igualdade FORMAL das distâncias); penroseParent? com minimalidade;
- availableEdges_graphOfEdges = id; isTree_of_connected_card;
- da 39ª: EdgeEssential, isTree_all_edges_essential;
- da 38ª: canonicalOrderedEdge + interface completa;
- da 37ª: connectedSpanningEdgeSets, mem-caracterização;
  sum_powerset_neg_one_pow_card (o (1−1)^m guardado para a 42ª).

## Desenho da closure (teus P1/P2, com a convenção de pai mínimo)
Para G ambiente e T ≤ G com T.IsTree (T candidata = penroseTree de
alguém, mas a def é para T arbitrária ≤ G):
depthT v := (dist em T da raiz) — pela retração+dist, para T = π(H)
coincide com penroseDepth H.
R_G(T) := T ∪ {e ∈ availableEdges G |
  P1: depthT(e.1) = depthT(e.2), OU
  P2: níveis consecutivos e, com v = endpoint fundo, u = raso:
      parent?_T(v) = some p com p < u}
(a aresta do próprio pai já está em T; P2 admite só as EXTRAS com
u ESTRITAMENTE acima do pai mínimo — orientação: parent < u,
consistente com min'.)
Em Finsets: closureEdges G T : Finset (OrderedEdge (n+1)) :=
  penroseTreeEdges-style filter sobre availableEdges G com o
  predicado P1 ∨ P2 formulado via depthT e penroseParent? T.

## Programa de teoremas (teus itens 1-7)
1. T ≤ R_G(T) ≤ G: por construção (filter de availableEdges G +
   união com arestas de T). BAIXO.
2. π(H) = T ⟹ T ≤ H ≤ R_G(T): T ≤ H é penroseTree_le transportado
   pela igualdade; H ≤ R_G(T) é o CORAÇÃO A: toda aresta de H ou está
   em T, ou liga mesma geração (P1 ✓), ou liga gerações consecutivas
   com raso ≥ pai — e ≠ pai ⟹ > pai por minimalidade (min'_le +
   ne). Usa: dist de H = dist de T (40a-dist + retração). MÉDIO.
3. T ≤ H ≤ R_G(T) ⟹ dist_H = dist_T: CORAÇÃO B — as arestas da
   closure não encurtam distâncias (P1 mantém nível, P2 desce ≤ 1
   nível já realizado pela árvore); duas desigualdades:
   dist_H ≤ dist_T por T ≤ H; dist_T ≤ dist_H por indução no
   comprimento de um caminho mínimo de H usando que cada aresta de
   R_G(T) tem |Δdepth| ≤ 1. MÉDIO-ALTO (indução em walk, padrão
   vacinado; SEM IsCycle).
4. candidatos de pai em H têm o MESMO mínimo que em T: com dist
   iguais, candidatos_H(v) ⊇ candidatos_T(v) ∋ pai_T; extras de P2
   têm rótulo > pai_T(v) ⟹ min inalterado (min'_le + a orientação
   ESTRITA do P2). MÉDIO — é onde a convenção parent < u paga.
5. π(H) = T: das 3-4, penroseParent?_H = penroseParent?_T pontual ⟹
   penroseTreeEdges iguais ⟹ árvores iguais. BAIXO após 4.
6-7. fibras = intervalos [T, R_G(T)], disjunção e cobertura dos
   conexos geradores: empacotamento de 2-5 (disjunção: T recuperável
   de H por π; cobertura: H conexo ⟹ T := π(H) serve). MÉDIO.

## Corte 41a/41b (custo provável, como pediste)
41a: def closure + item 1 + CORAÇÃO A (item 2). 
41b: CORAÇÃO B (item 3) + itens 4-7 (fibras completas).
Estimativa honesta: cada coração tem uma indução em walk nova; caber
numa pedra única é possível mas apertado — recomendo o corte.

## Pontos explícitos que exigiste
- Orientação: P2 com parent_T(v) < u (estrito; a aresta do pai já
  está em T e não é "extra").
- Mesma geração: entram TODAS (P1 sem condição de rótulo).
- Nenhuma aresta da closure reduz distância: é o CORAÇÃO B, item 3.
- n = 0 do Ursell: permanece fora (infra é Fin (n+1)); a costura
  Ursell↔fibras acontece na 42ª sobre o grafo de incompatibilidade,
  onde n = 0 já rende coeficiente 0 pela convenção da 37ª.

Aguardo parecer (inclusive sobre o corte a/b). — Fable
