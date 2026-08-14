# PEDRA 47b-iiB — PROGRESSO DO PORTÃO VI (branch pedra47vi-sol)

**Estado em 2026-08-01.** Não é um ESTADO para parecer — é o mapa de continuidade do trabalho em curso, conforme a fita "PORTÃO VI AUTORIZADO" (três subportões, sem parecer intermediário salvo portão de parada).

## VI-A — COMPLETO E VERDE (3 incrementos de CI)

Arquivo: `Phase3/LatticeGauge/KPStratification.lean` (~1100 linhas, 0 axiomas, 0 sorry).

1. **VI-A.1** `rootDegreeContribution` (todo k) + `rootedTreeSum_eq_sum_rootDegreeContribution` sobre `Finset.range (n+1)` via `sum_fiberwise_of_maps_to`; estratos vazios (`k=0` com `n>0` via caso-limite do Portão II; `k>n`).
2. **VI-A.2** `Fintype (EnumeratedTree n k)` por injeção no par plano; `EnumeratedRootDegreeData = EnumeratedTree × atribuição`; CAPSTONE `sum_enumeratedRootDegreeData_weight = k! · rootDegreeContribution` (Portão I consumido).
3. **VI-A.3** `SizeProfile n k = {s : Fin k → Fin (n+1) // Σ(s j+1)=n}` com Fintype grátis, `ext'`, `profileNat`, casos k=0/k=1.
4. **VI-A.4** Cota genérica `block_card_le_edges_add_one` (confinamento + relabel via Portão IV-A + `connected_card_availableEdges_ge` da 40b) e a **PINÇA** `OrderedDecomposition.card_itree_add_one` (≤ pontual + duas somas globais + `sum_lt_sum`); forma decompose `card_orderedInternalTree = componentSize`.
5. **VI-A.5** `BlockDatum N B` totalmente local (mark, itree com sub/conn/**cardEq**, valores) + `ext_of_extended` + Fintype.
6. **VI-A.6** Extração (`profileOfOD`/`partitionOfOD`/`datumOfOD`) e montagem (`assembledOD`/`assembledData`); `profiledData_ext`; **EQUIVALÊNCIA CENTRAL** `decompositionDataEquivProfiled` (roundtrip da decomposição por eta definicional; roundtrip perfilado com um único passo proposicional — cardinalidades reais) e `enumeratedDataEquivProfiled` via Portões II/III.
7. **VI-A.7** `profiledWeight` (produto de fatores locais) + preservação pontual (consome `enumeratedTreeWeight_factorization` + left_inv do Portão III) + CAPSTONE `enumeratedData_sum_eq_profiledData_sum`.

## VI-B — EM CURSO

**VI-B.0a VERDE**: a correspondência de árvores por bloco: `blockSuccEquiv` (iso de ordem bloco↔succ-imagem), `card_confineSet_eq`, `intrinsicBlockTree = relabel∘confine` com `intrinsicBlockTree_mem_connTreesOn` (conectividade confinada + campo da pinça), `ambientEdge`/`ambientBlockTree` com sub/conn ambientizados, e os DOIS roundtrips (`ambient_intrinsicBlockTree`, `intrinsic_ambientBlockTree`) nos níveis de aresta e conjunto.

**VI-B.0b VERDE (trava do parecer atravessada — preservação EXATA do peso):** `blockAssign`/`extendTail` (extensão dif) com lemas term-level (`extendTail_tail := dif_pos`); `internalBlockWeight` (indicador intrínseco via 0a + atividades do tail, raiz sem atividade); `blockDatumWeight` com incompat e ρη FORA da soma interna; `blockDatumEquivPayload : BlockDatum N B ≃ Σ r, Σ η, (tail × {E // E ∈ connTreesOn ↥B})` com as duas inversas (árvore pelos roundtrips 0a, resto field-shuffle); `blockDatumWeight_symm_payload` (único passo proposicional = roundtrip 0a); **`sum_tail_tree_eq_fixedRootBlockSum`** (sum_bij extend/restrict, indicador verbatim, atividade reindexada pela bijeção do erase; ρη e γ₀ não entram); **CAPSTONE `sum_blockDatumWeight_eq_markedBlockContribution`** — somando r e η, `markedBlockContribution` consumido por DEFINIÇÃO, nenhum fatorial.

**Falta (mapa executável):**
- **Ponte ao peso perfilado (para o B.5)**: `profiledWeight Y = ∏ j blockDatumWeight (Y.2.2 j)` — igualdade por bloco do indicador ambiente (`orderedInternalTreeIndicator` via `rootedTuple_succ` + `reconstructAssignment_marked/tail`) com o intrínseco (`treeIndicatorOn (blockAssign d)` via prod_bij ao longo da correspondência 0a) e dos produtos do tail.
- **VI-B.1**: `localDataSum P = ∏ j markedBlockContribution (P.block j)` — `Finset.prod_univ_sum` sobre o Pi de BlockDatum (dados por bloco independentes ✓ por construção).
- **VI-B.2**: `markedBlockContribution_eq_factorial_mul` com `card (P.block j) = s j + 1` → `(s j+1)! · G(s j)`.
- **VI-B.3/4**: soma constante sobre `OrderedPartition` + consumo do corolário ℝ do Portão V (`orderedPartitions_card_mul_factorials_real`) → `n!`.
- **VI-B.5**: capstone `rootDegreeContribution_factorial_identity : k!·R_{n,k} = n!·Σ_{s} Π_j G(s j)` combinando VI-A.2 + VI-A.7 + VI-B.1-4. Sanidades k=1 e k=n.
- **VI-C**: normalização (n!≠0, k!≠0 em ℝ), soma sobre k (range, estrato 0 excluído), `kpTreeCoeff_recurrence`. Sanidades n=0/1/2.

**Travas** (da fita, todas respeitadas até aqui): sem S_M, sem indução P(M), sem KP, sem exp, sem Summable, sem log Z.

— Fable
