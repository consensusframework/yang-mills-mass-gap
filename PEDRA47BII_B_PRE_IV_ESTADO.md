# ESTADO PRÉ-PORTÃO IV (47b-iiB) — para parecer antes do F(B)

Portões I, II, III VERDES no branch pedra47biib-sol (sem merge).

## 1. Assinatura exata — equivalência de atribuições

  globalAssignmentEquivOrderedAssignments (OD : OrderedDecomposition n k) :
    (Fin n → Polymer N) ≃ OrderedAssignmentData OD
com OrderedAssignmentData OD = { rootValue : Fin k → Polymer N,
tailValue : ∀ j, {x // x ∈ ODtail OD j} → Polymer N };
toFun = decomposeAssignment (restrições literais);
invFun = reconstructAssignment (dite sobre v = marked (blockIndex v),
blockIndex por escolha com unicidade da disjunção);
lemas de computação: reconstructAssignment_marked / _tail (fecham por
irrelevância definicional após alinhar o índice).

## 2. Assinatura exata — fatoração do peso

  enumeratedTreeWeight_factorization (ρ γ₀ γ) (hET : ET ∈ treesWithKRootNeighbors n k)
    (e : RootEnumeration ET k) :
    rootedTreeWeight ρ γ₀ γ ET
      = ∏ j : Fin k,
          (↑(incompatibilityIndicator γ₀ (orderedRootValue γ OD j))
            * ρ (orderedRootValue γ OD j)
            * orderedInternalRootedWeight ρ γ₀ γ OD j)
com OD := decompose hET e; provada via a versão de reconstrução
(reconWeight_factorization, para OD arbitrária) + decomposeThenReconstruct
reescrita DENTRO do have (motive dependente de hET no goal — atlas).

## 3. Definição exata — peso interno

  orderedInternalRootedWeight ρ γ₀ γ OD j : ℝ :=
    ↑(orderedInternalTreeIndicator γ₀ γ OD j)
      * ∏ v : {x // x ∈ ODtail OD j}, ρ (orderedTailAssignment γ OD j v)
onde orderedInternalTreeIndicator γ₀ γ OD j :=
  ∏ ed ∈ OD.itree j, hardCoreEdgeIndicator (rootedTuple γ₀ γ) ed
(representação pela atribuição global; arestas internas nunca tocam 0 —
independência do γ₀ é observação, não lema; se o Portão IV precisar dela,
custa ~8 linhas via cons_succ por aresta).

## 4. Como a 47b-i relabela árvore com raiz marcada para Fin (m+1)

Disponível: treeSum_comp_perm (invariância da soma de árvores sob
σ : Perm (Fin (n+1)) via relabelEdgeSet + sum_bij);
rootedSummand_comp_perm (caudas por π com extendPermSucc fixando 0);
relabelEdgeSet_mem_spanningTreeEdgeSets_top. O QUE FALTA para F(B):
a ponte BLOCO → Fin (m+1): as árvores internas vivem em
OrderedEdge (n+1) com suporte em succImage(block); a soma
fixedRootBlockSum precisa virar rootedTreeSum m ρ η. ROTA PROPOSTA:
não relabelar edge sets de bloco diretamente; em vez disso, DEFINIR
fixedRootBlockSum já como soma sobre (árvores sobre o BLOCO como
subconjunto) e provar a bijeção com árvores de ⊤ sobre Fin (m+1) via
uma equivalência de vértices bloco ≃ Fin (m+1) (equivFin composto com
swap para levar a marca ao 0) transportada a edge sets pelo relabel
canônico ENTRE TIPOS Fin — LACUNA HONESTA: nossa relabelagem da 38ª/47b-i
é Perm (Fin M) → Fin M (mesmo M); bloco tem m+1 vértices DENTRO de
Fin (n+1). Precisamos de UM lema novo de transporte entre tamanhos:
edge sets com suporte num S ⊆ Fin (n+1), |S| = m+1, ↔ edge sets sobre
Fin (m+1), via S.equivFin — mecanicamente análogo ao relabelOrderedEdge
da 38ª trocando Perm por Equiv S-induzido (canonicalOrderedEdge absorve
não-monotonicidade igual). Estimativa: ~80 linhas, padrão conhecido.
ALTERNATIVA que evita o transporte: provar F(B) por INDUÇÃO no tamanho
do bloco diretamente?? — NÃO recomendada (refaz a teoria). RECOMENDO o
transporte entre tamanhos como primeiro item do Portão IV.

## 5. Plano concreto — fixedRootBlockSum = m! · kpTreeCoeff m ρ η

(a) def fixedRootBlockSum ρ B r η := Σ sobre (t, δ) com t árvore-no-bloco
    (edge set com suporte em succImage B, conexo em B, |t| = |B|−1 — a
    caracterização cardinal LOCAL, agora com os dois lados disponíveis:
    ≥ pela conectividade [45b-ii tem o argumento de |E| ≥ |V|−1? — na
    verdade connected_card_availableEdges_ge da 40b! ✓] e ≤ pelo aperto
    global — no F(B) o t é quantificado, então a DEFINIÇÃO usa a
    condição cardinal explícita, sem aperto);
    δ : B → Polymer com δ r = η; peso = indicadores internos × atividades
    em B.erase r;
(b) transporte (item 4) leva a soma a Fin (m+1) com raiz 0;
(c) identificação termo a termo com o somando de rootedTreeSum m ρ η:
    árvores de ⊤ sobre Fin (m+1) = spanningTreeEdgeSets ⊤ ✓;
    atribuições δ com δ 0 = η ↔ (γ' : Fin m → Polymer) via Fin.cons ✓;
(d) resultado SEM divisão: fixedRootBlockSum = rootedTreeSum m ρ η
    (o m! fica DENTRO de rootedTreeSum por definição — a forma
    m!·kpTreeCoeff é corolário com div_mul_cancel, k!-style);
    RECOMENDO enunciar com rootedTreeSum como principal (nunca dividir).

## 6. APIs confirmadas

- somas reindexadas por Equiv: Fintype.sum_equiv / Equiv.sum_comp ✓
  (usadas na 47b-i via prod_comp; soma análoga mesma família);
- funções com valor fixado na raiz: Fin.cons + cons_zero/cons_succ ✓
  (rootedTuple é exatamente isso); a bijeção
  {δ // δ 0 = η} ≃ (Fin m → P) será via Fin.cons/Fin.tail —
  censar Fin.tail e cons_self_tail na Etapa Zero do IV;
- produtos sobre erase: mul_prod_erase ✓ (usada no III);
- ponte subtipo↔Finset: prod_coe_sort COMO TERMO com args nomeados
  (rw sintático NÃO unifica ↥s com Subtype cru — atlas, 2 ocorrências).

## 7. Riscos/coerções para o IV

- o transporte entre tamanhos (item 4) é o único bloco novo real;
- dites dependentes em reconstructAssignment: já domesticados
  (dif_pos com congrArg; subst do índice; rfl por irrelevância);
- casts ℕ→ℝ nos indicadores: push_cast deu conta no III;
- Fintype de {δ // δ r = η}: evitar subtipo de função — usar a bijeção
  com Fin m → P DIRETO na definição da soma (nunca somar sobre subtipo
  de funções).

**Aguardando parecer para abrir o Portão IV. Nada de F(B) antes.**
