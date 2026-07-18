# PEDRA 41b — ESTADO: A DIREÇÃO INVERSA E AS FIBRAS COMPLETAS
# (teu roteiro A-H do parecer da 41a; NENHUMA implementação até
# autorização)

## Interfaces novas da 41a (verdes na main)
penroseSameLevelEdge/_iff; penroseForwardEdge/_iff (P2 estrito);
penroseClosureEdges/mem; penroseClosure; sanduíche; penroseTree_adj_
parent; penroseParent?_penroseTree (candidatos-singleton);
penroseDepth_adj_cases (tricotomia); edge_classification (coração A);
penroseTree_fiber_le_closure; InPenroseInterval;
inPenroseInterval_of_penroseTree_eq.

## Roteiro A-H com custos separados (como exigiste)
A. Arestas de H ⊆ R_G(T) alteram depth_T em ≤ 1:
   por mem_penroseClosureEdges: aresta de T (Δ=1 pelas equações de
   pai), P1 (Δ=0), P2 (Δ=1). Lema por casos sobre a caracterização —
   CUSTO BAIXO (sem indução).
B. Todo walk 0→v em H tem comprimento ≥ depth_T v:
   indução em walk (nil: depth_T 0 = 0; cons: |Δ| ≤ 1 por A) —
   formalmente: depth_T (endpoint) ≤ length + depth_T (start), com
   start = 0. INDUÇÃO NOVA (a única da 41b-parte-métrica): padrão
   vacinado nil/cons, SEM IsCycle. CUSTO MÉDIO.
C. T ≤ H dá caminho de comprimento depth_T v (exists_penroseTree_walk
   da 40a transportado por mapSpanningSubgraphs) — CUSTO BAIXO.
D. dist_H = depth_T (le_antisymm de B e C): dist_H ≤ depth_T por C
   (dist_le); depth_T ≤ dist_H por B no realizador
   (exists_walk_length_eq_dist). CUSTO BAIXO após B.
E-F. Candidatos de pai em H no nível v:
   candidatos_H(v) = {pai_T(v)} ∪ {extras com rótulo > pai_T(v)}:
   um candidato u (Adj_H + depth_H u + 1 = depth_H v, com depth_H =
   depth_T por D) vem de aresta de H ⊆ closure: se aresta de T → u é
   vizinho-de-geração-anterior em T → u = pai_T(v) (unicidade na
   árvore: candidatos_T(v) = {pai}, que é EXATAMENTE
   penroseParent?_penroseTree aplicado a T = π(T) via retração! ou
   direto: T árvore ⟹ candidatos_T v = {pai} — lema da 41a adaptado);
   se P1 → Δ=0 contradiz candidato; se P2 → parent_T(v) < u.
   Logo min = pai_T(v) (min'-argumento igual ao da 41a). CUSTO MÉDIO.
G. penroseTree H = T: pais pontualmente iguais (E-F) ⟹
   penroseTreeEdges H = penroseTreeEdges T = availableEdges T
   (retração 40b) ⟹ graphOfEdges iguais ⟹ = T (40b:
   graphOfEdges_availableEdges). Ext em Finset + funext de parent?:
   CUSTO BAIXO-MÉDIO (burocracia).
H. Equivalência final:
   penroseTree_eq_iff_inPenroseInterval
     (hH : H.Connected) (hHG : H ≤ G) (hT : T.IsTree) (hTG : T ≤ G) :
     penroseTree H = T ↔ InPenroseInterval G T H
   := ⟨41a, G⟩. CUSTO TRIVIAL.

## Hipóteses honestas
A direção inversa precisa de H CONEXO (senão dist_H = ⊤-ish e π(H)
não é T). No enunciado H: manter hH explícito; a 42ª somará sobre
CONEXOS geradores (CSES), onde a conectividade já vive no filtro.

## Riscos nomeados
1. B: a indução deve ser formulada como
   ∀ (w : H.Walk 0 v), depth_T v ≤ w.length — cuidado com o sentido
   (indução no walk a partir da RAIZ; cada passo muda depth_T em ≤1,
   então depth_T v ≤ n passos). Formulação robusta:
   ∀ {a b} (w : H.Walk a b), depth_T b ≤ depth_T a + w.length
   (geral, nil/cons limpos), depois a := 0.
2. E-F: "vizinho de geração anterior em T é único" — provar como
   lema-instância: candidatos_T(v) = {pai_T(v)} para T árvore — já
   temos o argumento (41a, candidatos-singleton) para T = π(H);
   para T árvore usa retração (T = π(T)) e o mesmo lema. GRÁTIS.
3. G: igualdade de Finsets de arestas por igualdade pontual dos
   parent? — mem_penroseTreeEdges é disjunção de equações de parent?:
   reescrever com a igualdade funcional. BAIXO.

## Corte interno se necessário
41b-i: A-D (métrica). 41b-ii: E-H (pais + equivalência). Só se a
rodada mostrar inflação; estimativa é que cabe numa pedra.

Aguardo parecer. — Fable
