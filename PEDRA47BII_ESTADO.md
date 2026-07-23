# PEDRA 47b-ii — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean foi escrita para a 47b-ii.**
Base: main pós-47b-i (51 arquivos, ~485 teoremas, 0 axiomas, 0 sorry).
Manuscrito congelado: PEDRA47A_PROOF.md @ ede2ba63d2 (pós-forja).
Disponível da 47b-i: rootedTuple, Tₙ/Aₙ, casos zero, ≥ 0, Aₙ ≤ Tₙ,
relabelagem de STE(⊤) e do somando enraizado, extendPermSucc.

## 1. REMOÇÃO DA RAIZ (formulação em edge sets)

Para ET ∈ STE(⊤_{Fin(n+1)}): rootEdges ET := filter (0 ∈ endpoints);
childEdges ET := ET ∖ rootEdges. Os vizinhos da raiz:
rootNeighbors ET := imagem dos endpoints ≠ 0 de rootEdges (card = k).
Toda a mecânica em Finsets de OrderedEdge (n+1), SEM grafos novos:
grau da raiz = card rootEdges (arestas com 0 são (0,j) canônicas —
0 < j sempre, sem case-split de ordem!). Vantagem estrutural: com a
raiz 0 sendo o MENOR índice, toda aresta da raiz é literalmente
⟨(0, j), _⟩ — a decomposição não usa canonicalOrderedEdge.

## 2. COMPONENTES E VIZINHO MARCADO ÚNICO

Para j ∈ rootNeighbors ET: componente de j := o conjunto de vértices
alcançáveis a partir de j em graphOfEdges (childEdges ET). Fatos:
(i) cada componente contém exatamente um vizinho da raiz (dois
fechariam ciclo por 0 — prova via a acyclicidade de ET... rota SEM
IsAcyclic: se j ≠ j' na mesma componente de childEdges, um walk
j→j' + as arestas (0,j),(0,j') dão dois caminhos 0→j' em árvore —
contradição via isTree_iff_existsUnique_path (censado na 45b-ii em
Acyclic.lean:125!) — API real: existsUnique_path);
(ii) as componentes particionam {1..n} (todo vértice ≠ 0 alcança 0
por um caminho cuja primeira aresta sai de algum rootEdge).
INFRAESTRUTURA: reachability em graphOfEdges (childEdges) — usar
SimpleGraph.Reachable direto (sem induce, como na 45b-ii).

## 3. RECONSTRUÇÃO BIJETIVA

Dados ordenados: k, tamanhos (n₁..n_k) com Σ(nⱼ+1) = n, partição
ordenada dos rótulos, marca rⱼ, árvore em cada bloco. Reconstrução:
ET = ⋃ⱼ (0,rⱼ) ∪ (arestas do bloco j). Bijetividade = a prova do §3
do manuscrito. FORMA LEAN: bijeção entre
  {ET ∈ STE(⊤)} × (nada)   e   Σ-empacotamento ORDENADO / k!
— realizada como CONTAGEM (item 7), não como Equiv com quociente.

## 4-5. DADOS ORDENADOS E AÇÃO DE Perm(Fin k)

ComponentData (empacotado, como o parecer mandou):
  OrderedRootData n k := { f : Fin k → RootBlock n // blocos disjuntos,
    não vazios, cobrem {1..n} }
onde RootBlock n := (B : Finset (Fin (n+1))) × (r ∈ B) × (árvore em B)
— árvore em B := edge set ⊆ arestas-com-endpoints-em-B que é árvore
sobre B (definição por card + conexidade em B, reutilizando o padrão
da recíproca cardinal 40b RELATIVIZADO a B — o único pedaço de
infraestrutura genuinamente novo; alternativa mais barata a avaliar
no parecer: NÃO definir árvore-sobre-B e sim trabalhar com o edge set
childEdges inteiro e a partição por componentes, extraindo os blocos
da própria ET — a bijeção vira ET ↔ (rootEdges, childEdges) com a
partição DERIVADA, e a contagem k! atua só na ENUMERAÇÃO dos
vizinhos da raiz: Perm (Fin k) age em (Fin k ≃ rootNeighbors) — AÇÃO
LIVRE SOBRE AS ENUMERAÇÕES, órbitas = nada a quocientar, contagem
card (enumerações) = k! literalmente (Fintype.card_equiv)! RECOMENDO
FORTEMENTE esta segunda rota: o k! não vem de famílias não ordenadas,
vem de contar as k! enumerações de um Finset de card k — zero
órbita-estabilizador, zero Σ-transporte).

## 6-7. MULTIPLICIDADE k! (rota recomendada)

Com a rota das enumerações: a soma sobre dados ordenados
  Σ_{e : Fin k ≃ rootNeighbors ET} (produto que não depende de e)
    = k! · (produto)
via Finset.sum_const + Fintype.card_equiv (censar: card (α ≃ β) =
(card α)! quando card α = card β — existe como Fintype.card_equiv?
nome real a censar; fallback: card (Fin k ≃ Fin k) = k! =
Fintype.card_perm, e transporte Fin k ≃ rootNeighbors fixado por
equivFin). Formulação multiplicativa como o parecer exigiu:
  card orderedData = k! * card unorderedFamilies
vira: soma-ordenada = k! · soma-por-ET, SEM divisão em tipos.

## 8. CÁLCULO DE F(B)

Com a rota das enumerações, F(B) nem precisa ser isolado: a
identificação bloco ↦ m!·T_m(η) é a ÚNICA peça restante — via a
relabelagem da 47b-i composta com Finset.equivFin B (B ≃ Fin (m+1)
com r ↦ 0: compor equivFin com um swap para levar r a 0 — swap +
extendPermSucc já existem). Enunciado-alvo:
  Σ_{árvores em B} Σ_{γ:B→P, γ_r=η} peso = m! · kpTreeCoeff m ρ η
   (na verdade = rootedTreeSum m ρ η, já com o m! DENTRO — melhor
    ainda: identificar com rootedTreeSum e NUNCA dividir).

## 9. CUSTO E DIVISÃO

A recorrência exata (Tₙ = Σ_k 1/k! Σ_comps Π) tem os ingredientes:
(a) partição por componentes da childEdges — pedra própria (47b-ii-a):
    itens 1-3, ~15 lemas, o vizinho único via existsUnique_path;
(b) contagem k! por enumerações + F(B) + recorrência montada
    (47b-ii-b): ~12 lemas.
Estimo DUAS entregas. A 47c (S_M, extensão a produtos, indução com
exp) fica após ambas — e é a mais barata das três (a álgebra do
manuscrito §6-7 com APIs já censadas: sum_le_sum, extensão por
superset não negativo, exponencial truncada ≤ exp — censar
Real.sum_le_exp / add_pow_le_pow_mul... na Etapa Zero própria).

## O QUE NÃO ENTRA (até ordem contrária)

Summable, tsum, convergência, log Z, limite termodinâmico; espécies;
quocientes de tipos.

**Aguardando parecer — em particular sobre a ROTA DAS ENUMERAÇÕES
para o k! (item 5), que elimina órbita-estabilizador por completo.**
