# PEDRA 40 — PARTE (a) CONCLUÍDA; PARADA REGISTRADA PARA (b)
# (2026-07-17)

## Entregue (verde em 3 rodadas; PenroseTree.lean, ~400 linhas)
Sobre Fin (n+1), raiz 0, defs TOTAIS (sem prova como dado):
penroseDepth (= dist), penroseParentCandidates, penroseParent?
(menor candidato, Option), penroseTreeEdges, penroseTree. Teoremas:
depth 0 = 0; candidatos não vazios sob Connected (penúltimo da
geodésica: exists_walk_length_eq_dist + cases no reverse); spec/adj/
depth/ne/minimalidade do pai; penroseTree ≤ H SEM hipótese;
exclusividade das duas equações de pai numa aresta; card = n
(card_bij aresta ↦ filho-mais-fundo, 4 casos de injetividade);
indução forte com COMPRIMENTO EXATO ⟹ conectividade + igualdade
formal das distâncias (le_antisymm: dist_le do caminho-pai; map por
Hom.mapSpanningSubgraphs para a volta).
Placar pós-merge: 40 pedras, 39 arquivos, ~286 teoremas, 0 axiomas.

## APIs reais usadas (censo prévio no source v4.15)
SimpleGraph.dist/dist_self/dist_le/Reachable.exists_walk_length_eq_
dist (Metric.lean:162-187); Walk.length_reverse/length_cons/
length_concat/length_map; Hom.mapSpanningSubgraphs (Path.lean:1081);
Finset.min'/min'_mem/min'_le; Finset.card_bij; Finset.filter_ne'/
card_erase_of_mem; canonicalOrderedEdge/graphOfEdges (38ª/39ª).

## PARADA (itens 9 e 11 do parecer) — para tua decisão, Sol
FATO: a v4.15 NÃO tem a recíproca cardinal
(Connected ∧ #E = #V − 1 ⟹ IsAcyclic); Acyclic.lean traz apenas a
ida (IsTree.card_edgeFinset) e caracterizações por caminhos únicos.
FALLBACK autorizado (aciclicidade por profundidade máxima em ciclo):
exige cirurgia de Walk.IsCycle SEM censo prévio: IsCycle.rotate,
three_le_length, edges_reverse, support_rotate/IsRotated.mem_iff,
extração dos DOIS vizinhos no ciclo (cons no walk e no reverse),
head≠last em lista Nodup de comprimento ≥3. Estimativa: ~120 linhas,
6 nomes incertos, risco de 4+ rodadas cegas.
ITEM 11 (retração penroseTree T = T): a rota cardinal precisa
comparar (availableEdges T).card com T.edgeFinset.card (ponte
Sym2↔arestas canônicas, adiada desde a 39ª); a rota alternativa
(unicidade do vizinho-de-geração-anterior em árvore) precisa de
caminhos únicos — mesmo custo da aciclicidade.
OPÇÕES para a 40b:
(i) censo completo de Walk.IsCycle + fallback por ciclos;
(ii) provar NÓS a recíproca cardinal como lema geral (indução em
    remoção de aresta não-ponte, usando a 39ª EdgeEssential — médio,
    reutilizável, candidata a Mathlib);
(iii) ponte Sym2↔canônicas primeiro (útil também à 41) e rota
    cardinal via edgeFinset.
RECOMENDAÇÃO do executor: (ii)+(iii) juntas — mais reutilizáveis que
cirurgia de ciclos, e a (iii) já era dívida da 39ª.
NOTA para a 41ª: a partição usa T.IsTree como HIPÓTESE (árvores
dadas), então a 41 pode começar SEM a 40b — mas a idempotência
(item 11) é consumida no argumento das fibras; ordem sugerida:
40b → 41.
