# PEDRA 40 — ESTUDO: A REDUÇÃO DE PENROSE
# (encomenda do parecer da 39ª; NENHUMA implementação até autorização)

## Rota A — Partition scheme de Penrose
Ingredientes formais e custos:
1. Raiz: 0 : Fin n (n > 0 via Nonempty de Connected ✓ grátis).
2. Níveis por distância: SimpleGraph.dist existe na v4.15
   (Combinatorics/SimpleGraph/Metric.lean — VERIFICAR forma; é ℕ com
   Reachable). Para T ⊆ E conexo gerador: nível v := dist na
   graphOfEdges T. CUSTO: definições baratas; lemas de dist
   (dist_triangle em grafos? existência de caminho mínimo) — API a
   censar.
3. Penrose closure R(T) := T ∪ {arestas de G entre vértices de
   níveis iguais ou consecutivos compatíveis com a regra de Penrose}
   — a DEFINIÇÃO exata da regra (mesma-geração / geração-adjacente
   com comparação de pais) tem variantes; escolher a variante de
   Fernández–Procacci simplificada ou a original de Penrose. DECISÃO
   DE DESENHO para teu parecer: proponho a regra clássica:
   R(T) = T ∪ {e ∈ E(G) | os extremos de e têm níveis iguais OU
   níveis consecutivos}... (a original exige também comparação de
   índice do pai; detalhar na pedra).
4. O esquema: para cada árvore geradora T de G no "formato Penrose",
   o intervalo [T, R(T)] := {E | T ⊆ E ⊆ R(T)} particiona os
   conexos geradores; Σ_{E ∈ [T,R(T)]} (−1)^{|E|} =
   (−1)^{|T|}·[T = R(T)] (lema (1−1)^m da 37ª FINALMENTE consome!).
   Sobrevivem as árvores com R(T) = T ("árvores de Penrose").
5. Conclusão: |φ(G)| ≤ #{árvores geradoras de G}.
PARTIÇÃO é o osso: provar que todo E conexo gerador pertence a
EXATAMENTE um intervalo exige a árvore canônica de E (BFS/menor-pai)
e a compatibilidade da regra — é o núcleo de ~3 lemas médios-duros.

## Rota B — Deleção–contração
Contração de arestas: SimpleGraph tem map/quotient? A v4.15 NÃO tem
contração de arestas pronta com API rica (Subgraph/Minor em
desenvolvimento na época). Implementar contração sobre Fin n exigiria
quocientes de vértices e reindexação Fin (n-1) — exatamente a região
de tipos que evitamos. A recorrência φ(G) = φ(G−e) − φ(G/e)…
elegante, mas o custo de infraestrutura é ALTO e não reutiliza nada
do que temos. Tutte/broken circuits: idem, mais distante ainda.

## Recomendação e cortes (realistas, como pediste)
ROTA A, em três pedras:
- PEDRA 40: infraestrutura — árvore canônica de um conexo gerador
  (BFS por dist com pai de menor índice — determinístico em Fin n),
  spanningTreeOf E com: é árvore, ⊆ E, mesmo dist da raiz. SEM
  Penrose ainda. (Reuso: EdgeEssential/graphOfEdges da 39ª;
  dist da Mathlib.)
- PEDRA 41: a regra de Penrose, R(T), e a PARTIÇÃO dos conexos
  geradores em intervalos [T, R(T)] (o teorema duro).
- PEDRA 42: o cancelamento por intervalo (lema (1−1)^m da 37ª) e o
  capstone |φ(G)| ≤ #PenroseTrees ≤ #spanningTrees.
NÃO prometo que 41 cabe numa pedra — se a partição inflar, ela vira
41a (pertencimento) + 41b (unicidade).

## Verificações prévias obrigatórias (antes da 40 se autorizada)
- SimpleGraph.dist / Reachable.dist: forma exata, triangle, dist=0.
- Walk.length mínimo / existsShortestWalk? (nome real a censar).
- Nossa connectedWithin vs Connected da Mathlib no graphOfEdges:
  já compatível ✓ (33ª/39ª).

## Nota honesta
Depois da 42, teremos |φ| ≤ #árvores. Para Kotecký–Preiss ainda
faltará: cota de #árvores (Cayley ou bruta), a definição da série
truncada com resto, e o critério — cada um com estado próprio. O
abismo tem várias pontes; esta é a primeira e a mais comprida.

Aguardo parecer. — Fable
