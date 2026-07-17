# PEDRA 38 — MAPA: SIMETRIA DO COEFICIENTE DE URSELL
# (encomenda do parecer da 37ª; NENHUMA implementação até autorização)

## Alvo
ursellCoeff (γ ∘ σ) = ursellCoeff γ para σ : Equiv.Perm (Fin n),
e a versão genérica: graphUrsellCoeff invariante por isomorfismo.

## Peças e observação estrutural
1. Ação: (γ ∘ σ) i := γ (σ i). O grafo de incompatibilidade de γ∘σ é
   o COMAP do de γ ao longo de σ:
   (incompat (γ∘σ)).Adj i j ↔ (incompat γ).Adj (σ i) (σ j)
   (i ≠ j ↔ σ i ≠ σ j pela injetividade — lema de uma linha).
2. Logo TODO o conteúdo é o caso genérico:
   graphUrsellCoeff (G.comap σ)? — melhor formular via isomorfismo:
   para e : G ≃g H (SimpleGraph.Iso), graphUrsellCoeff G =
   graphUrsellCoeff H; o caso de permutação é e := Iso do comap
   (SimpleGraph.Iso.comap? conferir construtor: Iso de relabeling é
   `SimpleGraph.Iso.map`? candidato real: `Equiv.toIso`?? —
   reconhecimento obrigatório; fallback: provar direto para
   comap/relabel sem a palavra Iso).

## Comparação de rotas (encomendada)
A. DIRETA com OrderedEdge + sum_bij:
   bijeção E ↦ E' entre connectedSpanningEdgeSets dos dois grafos.
   O mapa de arestas: ⟨(i,j), h⟩ ↦ par canônico de (σ i, σ j) —
   PONTO DELICADO: σ pode INVERTER a ordem (σ i > σ j), então o mapa
   de arestas canônicas é "ordena depois de aplicar" — definível
   (if σ i < σ j then ⟨(σi,σj)⟩ else ⟨(σj,σi)⟩), injetivo, com card
   preservado (é injeção em OrderedEdge; card via Finset.card_image_of_injective).
   Conexidade preservada: walk transportado vértice a vértice
   (indução em Walk, padrão vacinado das 35ª/36ª, com o passo usando
   a adjacência relabelada nos DOIS sentidos do if).
   Custo: MÉDIO. Todo em casa, zero API nova. Vilão previsível: o if
   da ordenação gera 2×2 casos no passo de aresta.
B. Via SimpleGraph.map/comap/Iso da Mathlib:
   ganharia Reachable/Connected transportados prontos
   (Iso.connected_iff? preconnected_iff visto no source:760 ✓ existe
   para Iso!). MAS a soma sobre connectedSpanningEdgeSets ainda
   exige a bijeção de Finsets de arestas canônicas — ou seja, a rota
   B só substitui a PARTE de conexidade da rota A; o sum_bij continua.
   Custo: MÉDIO-BAIXO se Iso.preconnected_iff aplicar limpo ao
   graphOfEdges transportado; risco: montar o Iso entre
   graphOfEdges E e graphOfEdges E' exige provar a igualdade de
   adjacência com o if — o mesmo 2×2 da rota A, só que dentro do Iso.
C. Custo v4.15: Iso.preconnected_iff confirmado no source
   (Path.lean:760); Connected via connected_iff + Nonempty (Fin n)
   dos dois lados ✓ trivial. Equiv.Perm ✓ core.

## Recomendação do executor
HÍBRIDA: usar a rota A para a estrutura (edgeMap + sum_bij, nossa
zona quente) e a rota B APENAS no lema de conexidade (transportar
Connected pelo Iso de vértices σ entre graphOfEdges E e
graphOfEdges (edgeMap σ E), se o Iso montar limpo; senão indução em
Walk como sempre). Enunciados públicos:
  - graphUrsellCoeff_relabel : ∀ σ : Equiv.Perm (Fin n),
      graphUrsellCoeff (G.comap σ) = graphUrsellCoeff G
    (ou formulação com Adj (σ i) (σ j) sem comap — decidir tu);
  - ursellCoeff_comp_perm : ursellCoeff (γ ∘ σ) = ursellCoeff γ;
  - docstring: SÓ AGORA o coeficiente é função da família não
    ordenada (o objetivo futuro do docstring da 37ª realiza-se).

## O que não entra (herdado)
Sem log Z, sem série, sem 1/n!, sem árvores/Penrose/tree-graph, sem
estimativas, sem Kotecký-Preiss, sem contagem, sem limite.

## Perguntas
(i) comap explícito no enunciado público, ou forma com Adj (σ i) (σ j)?
(ii) A versão por Iso genérico (G ≃g H ⟹ coeficientes iguais) entra
    já, ou só a permutação (suficiente para a série)?
(iii) edgeMap com if de ordenação: aceitas os 2×2 casos por decide/
    rcases, ou preferes lema auxiliar "canonicalize" com API própria?

Aguardo parecer. — Fable
