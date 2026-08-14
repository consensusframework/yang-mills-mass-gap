# 47c-A2 — PLANO EXECUTÁVEL (autorizado; incremento 1 verde em pedra47c-sol)

**Rota aprovada pelo parecer** (reindexação exata → extensão desigual → fatoração exata), com a correção do Sol: tipo ambiente comum antes de qualquer inclusão.

1. **Tipos**: `IndependentSizes M k := Fin k → Fin (M+1)`; cast de `SizeProfile n k` (n ≤ M+1) via `Finset.single_le_sum` + s.2 + omega (cada s_j ≤ M).
2. **Extensão interna POR ZEROS (igualdade, não fita vermelha)**: na recorrência de T_{n+1}, estender `range (n+1) → range (M+1)` via `Finset.sum_subset` — termos i ≥ n+1 morrem por `sizeProfile_isEmpty_of_gt` (k = i+1 > n+1). Evita o swap triangular: depois só `Finset.sum_comm` RETANGULAR.
3. **Reindexação exata (união disjunta)**: `Σ_{n ∈ range(M+1)} Σ_{s : SizeProfile (n+1) k} Π G = Σ_{t ∈ univ.filter (Σ(t_j+1) ≤ M+1)} Π G` — sum_bij sobre o sigma `(range(M+1)).sigma (univ)`, n recuperado do próprio perfil (Σ(t_j+1) = n+1); k = i+1 ≥ 1 garante o estrato.
4. **🚩 FITA VERMELHA (isolada num único lema)**: filter-sum ≤ univ-sum via `sum_le_sum_of_subset_of_nonneg` (`filter_subset`), não-negatividade por `kpG_nonneg` (hρ). NUNCA sum_bij aqui.
5. **Fatoração exata**: `sum_pi_prod` (já em main) com A j := Fin (M+1) → `(Σ_x G x.val)^k` via `Finset.prod_const` + `Fintype.card_fin`; `Σ_{x : Fin(M+1)} G x.val = kpX M` via `Fin.sum_univ_eq_sum_range`.
6. **CAPSTONE** (forma preferida do parecer): `kpPartialSum_succ_le_truncated : kpPartialSum (M+1) ρ γ₀ ≤ Σ_{k ∈ range (M+2)} (kpX M ρ γ₀)^k / k!` — montagem: `sum_range_succ'` + `kpTreeCoeff_zero` (T₀ = 1, censar nome exato na 47b-i) + recorrência + passos 2-5; conversão `(1/(i+1)!)·X^{i+1} = X^{i+1}/(i+1)!` por passo escalar pequeno. Sanidades M=0 (S₁ ≤ 1+X₀) e M=1 como detectores do índice.
7. **A3 depois (curtíssimo se o censo confirmar)**: verificar `Real.sum_le_exp_of_nonneg {x} (hx : 0 ≤ x) (n) : Σ_{i ∈ range n} x^i/i! ≤ exp x` NO PIN v4.15 (raw.githubusercontent.com/leanprover-community/mathlib4/v4.15.0/Mathlib/Analysis/SpecialFunctions/Exp*.lean); se existir, A3 = instanciar n := M+2 com kpX_nonneg; se não, PARAR e relatar (sem teoria própria de séries).

Travas vigentes: sem Real.exp no A2; sem KP; sem IH; sem Summable. — Fable
