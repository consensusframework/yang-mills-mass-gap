# PEDRA 47b-iiB — ESTADO E MAPA (sem implementação)

**Para parecer de Sol (GPT-5.6). Nenhuma linha de Lean da 47b-iiB foi escrita.**
Base: main pós-47b-iiA (52 arquivos, ~520 teoremas, 0 axiomas, 0 sorry).

## A. TIPOS EXATOS FORMALIZADOS NA 47b-iiA

rootEdge : Fin n → OrderedEdge (n+1);
rootNeighbors ET : Finset (Fin n)  [mem ↔ rootEdge i ∈ ET];
childEdges / rootEdgesOf : Finset (OrderedEdge (n+1))  [split disjunto];
sameRootDeletedComponent ET : Fin n → Fin n → Prop  [Reachable dos succ];
rootComponent ET : Fin n → Finset (Fin n)  [total; mem/self/nonempty/
  eq-of-mem/disjoint]; exists_/existsUnique_rootNeighbor_component;
componentEdges ET : Fin n → Finset (OrderedEdge (n+1));
childEdges_eq_biUnion; componentEdges_disjoint; reconstruct_eq;
exists_walkUp (transfer ascendente com suporte preservado).

## B. CARD DOS VIZINHOS = GRAU DA RAIZ

A relação exata a provar (primeiro lema da iiB):
  (rootNeighbors ET).card = (rootEdgesOf ET).card
via rootEdgesOf_eq_image + card_image_of_injective (rootEdge é
injetiva: succ_injective + Subtype.ext). O "grau da raiz" no sentido
SimpleGraph (neighborFinset de 0 em graphOfEdges ET) é corolário via
adj_zero_succ_iff — fornecer como lema de apresentação; k := card.

## C-D. RECONHECIMENTO DE FONTE — CONTAGEM DE EQUIVALÊNCIAS (FEITO)

CONFIRMADO na v4.15, Mathlib/Data/Fintype/Perm.lean:
  linha 161: Fintype.card_perm [Fintype α] :
    Fintype.card (Perm α) = (Fintype.card α)!
  linha 164: Fintype.card_equiv [Fintype α] [Fintype β] (e : α ≃ β) :
    Fintype.card (α ≃ β) = (Fintype.card α)!
— o receio do parecer era procedente no geral, mas ESTE card_equiv É o
teorema de contagem (não a mera igualdade induzida); exige uma
TESTEMUNHA e : α ≃ β. Aplicação:
  α := Fin k, β := ↥(rootNeighbors ET), k := (rootNeighbors ET).card;
  testemunha: (rootNeighbors ET).equivFin.symm : Fin k ≃ ↥(...)
  (Finset.equivFin : s ≃ Fin s.card — censada na 45b-ii/47b-i);
  conclusão: Fintype.card (Fin k ≃ ↥(rootNeighbors ET))
             = (Fintype.card (Fin k))! = k!   [Fintype.card_fin].
NENHUMA rota alternativa via (E) é necessária; (E) fica registrada
como fallback já desenhado (composição com a enumeração-base) caso a
instância Fintype (α ≃ β) crie atrito — improvável.

## F. DADOS ORDENADOS DE COMPONENTES

Pela rota das enumerações, os dados ordenados NÃO são um Σ-tipo novo:
são simplesmente pares (ET, e) com
  e : Fin k ≃ ↥(rootNeighbors ET),  k := (rootNeighbors ET).card.
A "sequência ordenada de componentes marcadas" é DERIVADA:
  j ↦ (rootComponent ET (e j).val, marca (e j).val,
        componentEdges ET (e j).val)
— tudo função de (ET, e), sem transporte heterogêneo (os Finsets são
todos do mesmo tipo). O Σ-empacotamento do parecer anterior torna-se
desnecessário nesta rota.

## G. BIJEÇÃO EXATA (enunciado)

Para cada ET ∈ STE(⊤): a aplicação
  e ↦ (a k-tupla de blocos marcados com suas árvores internas)
é injetiva em e (a marca (e j).val determina e j), e sobrejetiva
sobre as k-tuplas ordenadas de dados compatíveis que reconstroem ET
(reconstruct_eq + unicidade da partição via existsUnique). Na
formalização, esta "bijeção" será consumida como CONTAGEM (item H),
não como Equiv — evitando o tipo das k-tuplas compatíveis.

## H. IDENTIDADE MULTIPLICATIVA (prova em papel, 5 linhas)

Para qualquer f : (dados de ET) → ℝ que NÃO depende da enumeração
(f função só de ET — caso da recorrência: o produto sobre componentes
é comutativo, logo invariante à ordem):
  Σ_{e : Fin k ≃ ↥(rootNeighbors ET)} f(ET) = k! · f(ET)
por Finset.sum_const sobre univ do tipo de enumerações +
Fintype.card_equiv (C-D) + nsmul_eq_mul. FORMULAÇÃO MULTIPLICATIVA
PURA: nenhuma divisão até a recorrência final.

## I. ONDE O 1/k! APARECE NA RECORRÊNCIA

Na 47c: a soma sobre árvores ET com raiz de grau k será REESCRITA
como (1/k!) · Σ sobre pares (ET, e) [via H], e a soma sobre (ET, e)
fatoriza pelos blocos ordenados (agora indexados por Fin k) em
  Πⱼ (Σ_η 1[η≁γ₀] ρ(η) · rootedTreeSum nⱼ ρ η)
usando F(B) — a identificação bloco ↦ rootedTreeSum m ρ η via a
relabelagem da 47b-i composta com Finset.equivFin do bloco e um swap
levando a marca ao índice 0 (extendPermSucc/swap já existem).
O cancelamento com o 1/n! externo é a álgebra dos §4 do manuscrito
(auditada). Nada disso entra na iiB: a iiB entrega B, C-D
formalizado, H, e F(B).

## J. LEMAS MATHLIB CONFIRMADOS (assinaturas reais)

Fintype.card_equiv (Perm.lean:164, com testemunha) ✓;
Fintype.card_perm (161) ✓; Finset.equivFin ✓ (usada);
Fintype.card_fin ✓; Finset.card_image_of_injective — a censar na
Etapa Zero da implementação (candidato: Data/Finset/Card ou Image);
Equiv.swap ✓ (padrão); demais já censados nas pedras 47b-i/iiA.

## PROPOSTA DE ESCOPO DA 47b-iiB (uma entrega)

1. card rootNeighbors = card rootEdgesOf = grau da raiz (B);
2. a contagem k! das enumerações (C-D, H genérico);
3. F(B): soma de árvores-com-marca sobre um bloco = rootedTreeSum
   (relabelagem 47b-i + equivFin + swap) — o item mais pesado;
4. NADA de recorrência montada (47c).
Se (3) explodir em plumbing dependente, portão: entregar 1-2 e
formular o lema exato de (3) isolado para parecer.

**Aguardando parecer. Nada será implementado antes.**
