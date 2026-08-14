# PEDRA 47c — ESTADO (mapa para parecer; NADA implementado)

**Para:** Sol — via Ju. **De:** Fable. **Data:** 2026-08-14.
**Pedra 47b-iiB COMPLETA e integrada a main:** merge `803ef6e26dd6c525f60d8955f552d742ebc18596`; placar 60 arquivos, ~700 teoremas, 0 axiomas, 0 sorry; CI restaurado para main.

## 1. O que 47c consumirá (assinaturas exatas, em main)

```lean
theorem kpTreeCoeff_recurrence (n : ℕ) (hn : 0 < n) (ρ : Polymer N → ℝ) (γ₀ : Polymer N) :
    kpTreeCoeff n ρ γ₀
      = ∑ i ∈ Finset.range n, (1 / ((Nat.factorial (i + 1) : ℕ) : ℝ))
          * ∑ s : SizeProfile n (i + 1), ∏ j : Fin (i + 1), kpG ρ γ₀ (profileNat s j)
```
com `SizeProfile n k = {s : Fin k → Fin (n+1) // Σ (s j + 1) = n}`, `profileNat s j = (s.1 j : ℕ)`,
`kpG ρ γ₀ m = Σ_η (incompatibilityIndicator γ₀ η : ℝ) · ρ η · kpTreeCoeff m ρ η`.
Também em main: `rootDegreeContribution_factorial_identity` e `rootDegreeContribution_normalized_identity` (ambas universais), `sizeProfile_sum_add_k` (auditoria Σ s_j + k = n).

Não-negatividade disponível: `rootedTreeWeight_nonneg` (hρ pontual) → kpTreeCoeff ≥ 0 sob hρ é corolário curto (soma/quociente de não-negativos; n! > 0) — **a provar em 47c**, não existe ainda como lema nomeado. kpG ≥ 0 sob hρ idem.

## 2. Desenho de S_M e do passo de indução

`S_M γ := Σ n ∈ range (M+1), kpTreeCoeff n ρ γ` (ρ fixo, γ percorre polímeros). Motivo simultâneo, como no manuscrito congelado `ede2ba63d2` (correção obrigatória do Kimi): `P(M) := ∀ γ, S_M γ ≤ Real.exp (a γ)`.

Passo: para 1 ≤ n ≤ M+1, a recorrência dá kpTreeCoeff n como soma sobre estratos; majorar cada `kpG(s_j) = Σ_η incompat·ρ·kpTreeCoeff (s_j)` usando P(M') nos coeficientes menores e a hipótese KP abstrata **uma única vez**.

## 3. 🚩 A FITA VERMELHA (o único lugar de perigo, marcado como o Sol exigiu)

Na majorante por produtos independentes: os perfis satisfazem `Σ s_j = n − k ≤ M − k` (via `sizeProfile_sum_add_k` e n ≤ M). Substituir a soma RESTRITA sobre perfis por escolhas INDEPENDENTES de s_j ≤ M−1 **AUMENTA O DOMÍNIO** — é uma **DESIGUALDADE**, válida somente APÓS a não-negatividade dos somandos (hρ ≥ 0 entra AQUI, pela primeira vez), formalizada como `Finset.sum_le_sum_of_subset_of_nonneg` (censado) sobre uma injeção de índices — **nunca** como reindexação/equivalência. Nenhum sum_bij neste passo.

## 4. Restante do mapa

Exponencial truncada ≤ Real.exp: API real a censar (`Real.add_one_le_exp`, `Real.sum_le_exp_of...` — censo obrigatório antes de codificar; fallback: indução própria com `Real.exp_add` + produto). Hipótese KP abstrata consumida na forma da pedra 46 (`kp_hypothesis`), especialização final `kp_hypothesis_beta_le_one_div_40000` com β ≤ 1/40000. `Summable`/limites: **totalmente reservados à pedra 48**. Travas de 47c: sem log Z, sem limite termodinâmico, sem clustering, sem gap.

Aguardo o parecer. Nenhuma linha de 47c antes dele. — Fable
