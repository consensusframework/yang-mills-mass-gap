# Release v49 — The Finite-Volume Cluster-Expansion Identity for the Log-Partition Function

**Frozen scientific sentence (the release ruler):**

> *Finite-volume, small-β cluster-expansion identity for the log-partition function:*
> **log Z_β = Σ'ₙ Bₙ(w_β)** for **0 ≤ β ≤ 1/40000**, with the signed unrooted
> Ursell series absolutely convergent.

This is a finite-volume lattice identity under small coupling. It is NOT a
thermodynamic-limit statement, NOT clustering/exponential decay, NOT a
continuum result, NOT a mass-gap or Clay-problem claim.

## The machine-checked chain (stone 49, complete)

| Step | Statement | File |
|---|---|---|
| 49A | Σ_γ₀ z(γ₀)·Cₙ(z,γ₀) = (n+1)·B_{n+1}(z) — unrooting | KPUnrooted.lean |
| 49B | Σ'ₖ \|B_k(w)\| ≤ Σ_γ₀ \|w(γ₀)\|·e^{card γ₀} — absolute summability | KPUnrooted/KPSpecialization |
| 49C-I | realZ = typedPolymerGas (finite identity, no smallness) | KPTypedGas.lean |
| 49C-II | typedPolymerGas = Σ_{n≤card} Aₙ (all-graph coefficients; n! audited) | KPGasCoefficients.lean |
| 49C-III | (n+1)·A_{n+1} = Σⱼ (j+1)·B_{j+1}·A_{n−j} (root-component recurrence) | KPRootComponent.lean |
| 49C-IV | finite support + abs. summability + recurrence ⟹ Σaₙ = exp(Σ'bₙ) (abstract engine) | ExpRecurrenceEngine.lean, KPExpIdentity.lean |
| 49C-V | typed gas = exp(Σ'Bₙ) ⟹ Z_β = e^{C_β} ⟹ Z_β > 0 (corollary) ⟹ log Z_β = Σ'Bₙ | KPClusterExpansion / KPPartitionExp / KPLogPartition |

Architectural note recorded in the sources: nonvanishing of Z_β is an OUTPUT
of the expansion here (Z = e^C ⟹ Z > 0 ⟹ log Z = C); the preexisting physical
positivity is never consulted, and the log step is Real.log_exp — no division,
no nonvanishing hypothesis anywhere in the chain. 1/Z = e^{−C} now follows
from the expansion itself (architectural independence from the earlier
physical proof, which remains valid).

## Verification and review

- **Formal verification:** Lean 4 (Mathlib pinned v4.15.0), GitHub Actions CI
  as sole judge. 0 scientific axioms, 0 `sorry` in Phase 3 (72 files,
  ~1110 declarations).
- **External adversarial mathematical review:** Kimi 3 (Moonshot AI) — 8
  audits across the stone (49A, 49B, 49C-I, 49C-III, the analytic engine and
  the final semantic chain), all GREEN, no substantive finding.
- **Independent review:** Grok (xAI) — APPROVED.
- **External reproducibility/release review:** Manus AI 1.6 — APPROVED, with
  the GREEN classification explicitly delimited to the finite-volume identity.

The model reviews are adversarial and reproducibility review; the formal
verification is the kernel + CI.

## Provenance

- Mathematics frozen at branch `pedra49-sol`, commit
  `86fbd65450e2ccf67ee0bc6bf4f106a33d2aa14b` (the object all four reviews
  examined). This release integrates that object plus documentation only.
- Roles: Arquitetura — GPT-5.6 "Sol" (OpenAI); Execução — Claude Fable 5
  (Anthropic); Coordenação — Jucelha Carvalho; Juiz — GitHub Actions CI.
- Concept DOI (all versions): 10.5281/zenodo.17397622. Version DOI and frozen
  tag `zenodo-v49`: recorded in the final release commit.
