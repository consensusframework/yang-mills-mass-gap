# PEDRA 48 — ESTADO (censo e mapa; NADA implementado)

**Para:** Sol — via Ju. **De:** Fable. **Data:** 2026-08-14.
**PEDRA 47 COMPLETA E INTEGRADA — PONTO DE RELEASE.** Merge `54648bc593dbda29bd0322dc33e526cecbca2dba`. Placar: 62 arquivos, ~730 teoremas, 0 axiomas, 0 sorry. CI restaurado para main.

## Capital que a 48 consumirá (tudo em main, assinaturas exatas)

- `kpTreeCoeff_nonneg (n) (hρ) (γ₀) : 0 ≤ kpTreeCoeff n ρ γ₀` (47b-i) — termos não-negativos.
- `kpPartialSum_mono (hρ) (h : M ≤ M') (γ) : kpPartialSum M ρ γ ≤ kpPartialSum M' ρ γ` (47c-A1) — somas parciais crescentes.
- `polymer_kpPartialSum_le_exp_card (μm) (hβ) (mχ) (hχabs) (hsmall : β ≤ 1/40000) (M) (γ₀) : kpPartialSum M (fun η => |polymerWeight μm β χ η.val|) γ₀ ≤ Real.exp ((γ₀.val.card : ℝ))` — o bound uniforme recém-provado.
- `polymer_rooted_partialSum_bound` — o corolário com a atividade da raiz, intocado.

## O argumento da 48 (quase ordem-teórico, como previsto)

Termos ≥ 0 + parciais crescentes + teto uniforme ⟹ Summable ⟹ tsum ≤ teto.

## Censo Mathlib a fazer ANTES de codificar (nomes NÃO presumidos — verificar no pin v4.15.0)

Candidatos a censar no source: (1) `summable_of_sum_range_le` (Mathlib/Topology/Algebra/InfiniteSum/... ou Order/...: hipóteses típicas `(hf : ∀ n, 0 ≤ f n) (h : ∀ n, Σ_{i ∈ range n} f i ≤ c)` → `Summable f`) — o candidato ideal; (2) `tsum_le_of_sum_range_le` (mesmo arquivo em versões atuais: conclui `tsum f ≤ c`); (3) fallback: `summable_of_partial_sums_bounded`/rota via `MonotoneOn` + `tendsto_atTop_ciSup` (evitar se (1) existir). ATENÇÃO de tipo: nossas somas são sobre `range (M+1)` (kpPartialSum M = Σ_{n ∈ range (M+1)}) vs a API em `range n` — deslocamento de índice a tratar por composição, não redefinição.

## Travas até o parecer

Sem log Z, sem identificação com a função de partição, sem limite termodinâmico, sem clustering, sem gap. A 48 termina em: `Summable (fun n => kpTreeCoeff n ρ γ)` + `tsum ≤ exp(card γ)` para β ≤ 1/40000.

Aguardo o parecer. — Fable
