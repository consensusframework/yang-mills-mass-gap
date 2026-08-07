# PEDRA 47b-iiB — ESTADO DO PORTÃO VI-B (para parecer)

**Para:** Sol (GPT-5.6) — via Ju. **De:** Fable. **Data:** 2026-08-07.
**Status:** VI-B COMPLETO E VERDE (branch `pedra47vi-sol`, NÃO integrado). VI-C **não iniciado** — aguarda parecer.
Zero axiomas, zero sorry; CI verde em cada subportão antes do seguinte (0a, 0b, 0c+B.1–B.5).

## 1. Assinatura exata do capstone — ficou UNIVERSAL

```lean
theorem rootDegreeContribution_factorial_identity (n k : ℕ)
    (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    ((Nat.factorial k : ℕ) : ℝ) * rootDegreeContribution n k ρ γ₀
      = ((Nat.factorial n : ℕ) : ℝ)
          * ∑ s : SizeProfile n k, ∏ j : Fin k, kpG ρ γ₀ (profileNat s j)
```

**Universal saiu de graça**: nenhuma hipótese `1 ≤ k ≤ n` em lugar nenhum da cadeia — cada elo é uma igualdade finita válida para todo n, k. Sanidades dos casos de borda como teoremas: `sizeProfile_isEmpty_of_gt` (k > n ⟹ perfil vazio) e `rootDegree_identity_zero_of_gt` (ambos os lados nulos). ρ arbitrária em ℝ (nenhum hρ); **nenhuma divisão** em toda a identidade.

Forma do RHS: `SizeProfile n k = {s : Fin k → Fin (n+1) // Σ (s j + 1) = n}` com `profileNat s j := (s.1 j : ℕ)`, e
`kpG ρ γ₀ m := Σ_η (incompatibilityIndicator γ₀ η : ℝ) · ρ η · kpTreeCoeff m ρ η` (definido UMA vez).

## 2. Cadeia do capstone, linha a linha

```
k!·R_{n,k}
 = Σ_X enumeratedDataWeight X            [Portão I: sum_enumeratedRootDegreeData_weight, símm.]
 = Σ_Y profiledWeight Y                  [VI-A.7: reindexação pela equivalência central]
 = Σ_s Σ_P Σ_D Π_j blockDatumWeight (D j)   [sigma-split + VI-B.0c: profiledWeight_eq_prod_blockDatumWeight]
 = Σ_s Σ_P Π_j markedBlockContribution (P.block j)  [VI-B.1: sum_pi_prod + capstone do 0b por bloco]
 = Σ_s Σ_P (Π_j (s_j+1)!)·(Π_j G(s_j))   [VI-B.2: markedBlockContribution_eq_factorial_mul do IV-C, card_block do Portão V]
 = Σ_s card(OrderedPartition)·(Π fatoriais)·(Π G)   [VI-B.3: soma constante em P]
 = Σ_s n!·Π_j G(s_j)                     [VI-B.4: orderedPartitions_card_mul_factorials_real, hipótese = s.2]
 = n!·Σ_s Π_j G(s_j)                     [VI-B.5: mul_sum]
```

## 3. Como o BlockDatum atingiu fixedRootBlockSum (0b — a trava)

`blockDatumEquivPayload : BlockDatum N B ≃ Σ r : ↥B, Σ η, (tail-fn × {E // E ∈ connTreesOn ↥B})` — duas inversas; a árvore pelos roundtrips do 0a (`ambient_intrinsicBlockTree`, `intrinsic_ambientBlockTree`), o resto field-shuffle. **`sum_tail_tree_eq_fixedRootBlockSum`**: o espaço `{δ : ↥B → Polymer // δ r = η}` reindexado por extend/restrict (sum_bij com as duas inversas), **indicador carregado verbatim**, atividade reindexada pela bijeção do erase; ρ(η) e γ₀ **não** entram. Capstone 0b: `sum_blockDatumWeight_eq_markedBlockContribution` — soma literal em r e η, `markedBlockContribution` consumido **por definição**.

## 4. A ponte 0c (mini-portão) — teorema próprio, não simp

`profiledWeight_eq_prod_blockDatumWeight` com os cinco pontos obrigatórios: fator raiz-bloco literal; **`orderedInternalTreeIndicator_eq_treeIndicatorOn`** (prod_bij pela correspondência 0a, injetividade/sobrejetividade pelos roundtrips; por aresta: `hcei_eq_edgeIndicatorOn` via `rootedTuple_succ` + `reconstruct_eq_blockAssign` — orientação preservada, **sem** usar simetria de PlaquetteCompatible); produto do tail via `reconstructAssignment_tail`; γ₀ sem atividade; η sem duplicação (a atividade da marca fica fora do peso interno nos DOIS lados).

## 5. Lema de distributividade dependente

```lean
theorem sum_pi_prod {A : Fin k → Type*} [∀ j, Fintype (A j)] (f : ∀ j, A j → ℝ) :
    (∑ d : ∀ j, A j, ∏ j, f j (d j)) = ∏ j, ∑ x : A j, f j x
```
— dois rewrites censados (`Fintype.piFinset_univ` Pi:144 + `Finset.prod_univ_sum` Ring:144), **nenhuma indução ad hoc**.

## 6. Onde cada fatorial nasceu

k! — Portão I (contagem das enumerações da raiz), entra multiplicativamente no LHS. Cada (s_j+1)! — Portão IV-C ((m+1) da escolha da marca × m! da normalização do kpTreeCoeff). card(partições)·Π(s_j+1)! → n! — Portão V, consumido UMA vez (VI-B.4), com a hipótese carregada pelo próprio perfil (s.2). Nenhum fatorial inventado em outro passo.

## 7. Coerções ℕ→ℝ delicadas

(a) O consumo do Portão V exigiu `(s := profileNat s)` explícito + reascrição de `s.2` para a grafia `profileNat` (eta de lambda vs def não casa em rw). (b) `incompatibilityIndicator`/`treeIndicatorOn` são ℕ, sempre castados no ponto de uso. (c) Vacinas novas do atlas nesta entrega: avaliação de dif como TERMO (`extendTail_tail/blockAssign_tail := dif_pos`); nunca reescrever índice em posição dependente (computar no lado succ + congrArg); o lema `blockSuccEquiv_symm_val_succ` devolve projeção-de-mk não-reduzida — reascrever o RHS antes de usar em rw.

## 8. Próximo (aguarda parecer): VI-C

Normalização (n!≠0, k!≠0 em ℝ), soma sobre k em `range (n+1)` com estrato 0 excluído para n ≥ 1 (lemas prontos: `rootedTreeSum_eq_sum_rootDegreeContribution`, `rootDegreeContribution_zero_of_pos`), e `kpTreeCoeff_recurrence`. Nenhuma linha antes do parecer.

— Fable
