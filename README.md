# Conditional Lean 4 Formalization Exercises Around the Yang-Mills Mass Gap

**Status: exploratory / conditional formalization — NOT a proof (partial or otherwise) of the Clay Millennium Problem.**

## What this repository is

This repository contains **two clearly separated layers**. **Legacy
Phases 1-2** are conditional formalization experiments whose physical
content is carried by explicit assumptions and axioms; their theorems are
logical consequences of those assumptions. **Phase 3** is a new,
independently built finite-lattice gauge theory library: the results in
its verification table are **axiom-free beyond Lean and Mathlib
foundations** (see VERIFICATION_STATUS.md and the structural audit in
docs/audit/AUDIT_ZERO_V2_SUMMARY.md).

## What this repository is NOT

- It is **not** a proof of the Yang-Mills mass gap, in whole or in part.
- It does **not** construct the Yang-Mills measure, a Hilbert space, a Hamiltonian, or verify Wightman/Osterwalder-Schrader axioms — the actual content of the Clay problem.


## Build status

As of July 12, 2026: **Phase 2 compiles** (25/25 modules); **Phase 3
(LatticeGauge) contains 32 verified stones — ~171 axiom-free theorems**:
lattice, Wilson action, gauge and translation invariance, Gibbs measure,
Wilson loops, expectation values, Haar measure instantiated on U(n) with
right- AND inversion-invariance proved by uniqueness, the formal statement
of the lattice mass gap (open target, stated not proved), finite-link
independence, the FRESH-LINK THEOREM (Haar-distributed holonomies), and
the exact β = 0 expectation formula for Wilson-path observables —
unconditional on U(n) up to explicit structural hypotheses. The local
analysis package at β = 0 is complete: continuity
(|⟨f⟩_β − ⟨f⟩₀| ≤ 2CBβ·exp(βB)), linear response
(d/dβ ⟨f⟩_β|₀ = −Cov₀(f, S)) and the first-order Taylor remainder
(≤ 4CB²β²·exp(βB) for βB ≤ 1). Response identities hold at EVERY
β₀ ≥ 0: fluctuation–response (d/dβ ⟨f⟩_β = −Cov_β(f, S)), the
second-response/third-cumulant pair (no formal iteratedDeriv wrapper is
claimed), Wilson-observable specializations, the log-partition response
(d/dβ log Z_β = −⟨S⟩_β; log partition function, not "free energy"), and
Gibbs-variance positivity (d/dβ[−⟨S⟩_β] = Var_β(S) ≥ 0 — pointwise sign,
no convexity wrapper claimed). The independence structure of the β = 0
product state is characterized: exact factorization of link-disjoint
Wilson observables (binary, finite families, one-vs-block vanishing of
the third connected cumulant — order 3 only), and, at the measure level,
official Mathlib IndepFun/iIndepFun independence, the joint law of a
pair equal to the product of its marginals, and the finite joint tuple
law (the random vector of link-disjoint Wilson loops has exactly the
product distribution of its marginals), and its stability under
coordinate-wise measurable post-composition — every derived statistic
inherits the product law. The first step of cluster-expansion MECHANICS
is in place at level (a): the finite plaquette-activity (Mayer subset)
identity with local activity bounds — an exact algebraic identity, NOT
a connected-cluster expansion, with no convergence or volume-uniformity
claim. These are finite-volume results;
the constants are not uniform in the lattice size; they are preparatory
perturbative statements, not a completed cluster expansion or
thermodynamic-limit result. A structural audit is under way. The current live tree contains 922
inventoried declarations, including 99 CORE; approximately 503 additional
declarations were moved intact into the historical archive during the
first audit pass. Stable artifacts are available under docs/audit/. First successful builds: July 5, 2026. The original
files, reconstructed after the loss of the previous repository, contained
truncated declarations and could not have compiled as published. Phase 1 does
not yet have a working Lake project and is not covered by CI.

## Honest accounting — LEGACY SNAPSHOT (2026-07-05 scope and methodology; NOT the current live-tree census, which lives in docs/audit/AUDIT_ZERO_V2_SUMMARY.md)

| Metric | Value |
|---|---|
| `axiom` declarations | 293  |
| Theorems/lemmas (live tree) | see census above |
| Theorems unconditional, LEGACY Phases 1-2 | ~0 substantive — elementary real-analysis facts |
| Theorems unconditional, Phase 3 (2026-07) | ~171 (see Build status; census artifacts in docs/audit/) |
| `sorry` in code | present in 21 files across |
| Axioms that assert LLM outputs (`gemini_*`) | **0** — all removed or converted to explicit hypotheses (Etapa 0/1, July 2026) |
| Axioms equivalent to open problems (incl. the mass gap itself) | ~60 |

### Example of what is actually proven

`Theorem15_UniversalPhysicalBound` proves: *if* a function `Delta0 : ℝ → ℝ` is strictly decreasing on [0.5, 1.18] *and* takes assumed values at the endpoints, *then* it is bounded between those values. This is an elementary fact about monotone functions; the Yang-Mills content resides entirely in the five axioms it imports.

## Authorship and method

Coordinated by **Jucelha Carvalho** ([ORCID: 0009-0004-6047-2306](https://orcid.org/0009-0004-6047-2306)) using multiple AI assistants (Manus AI 1.6, Claude Fable 5, GPT-5.6 "Sol", Claude Opus 4.5/4.6/4.7, GPT-5.2, Gemini 3 Pro) for drafting Lean code.

AI cross-validation is **not** equivalent to peer review or numerical simulation. Earlier claims of "numerical validation by Gemini" referred to LLM-generated assertions, not executed lattice computations, and are retracted. All former `gemini_*` axioms have been removed (21 orphans) or converted into explicit named hypotheses (`def ...Assumption : Prop`) that theorems carry in their signatures.

## Roadmap

See [`PHASE3_ROADMAP.md`](PHASE3_ROADMAP.md) for a revised, realistic plan focused on:

1. Eliminating Group A axioms via Mathlib imports (weeks)
2. Removing all `gemini_*` axioms (weeks)
3. A tractable formalization target: **the lattice strong-coupling mass gap** (Osterwalder–Seiler 1978) — a known theorem, never formalized in Lean 4

## Audit

See [`AXIOM_AUDIT.md`](AXIOM_AUDIT.md) for the complete inventory of all 404 axiom declarations, classified into:
- ✅ Group A: Already in Mathlib4 (~15)
- 🔬 Group B: Known results, not yet formalized (~40)
- 🔴 Group C: Open problems / circular assumptions (~60)
- ⚠️ Group D: LLM assertions with no probative value (~110)

## Citation

If citing, please cite as a *conditional formalization exercise*, not as progress on the Millennium Problem.

```
Carvalho, J. et al. (2026). Conditional Lean 4 Formalization Exercises Around the
Yang-Mills Mass Gap. GitHub repository.
https://github.com/consensusframework/yang-mills-mass-gap
```

## Contact

- **Email:** jucelha@smarttourbrasil.com.br
- **ORCID:** https://orcid.org/0009-0004-6047-2306

## Team

- **Jucelha Carvalho** — Lead Researcher & Coordinator | jucelha@smarttourbrasil.com.br | [ORCID](https://orcid.org/0009-0004-6047-2306)
- **Claude Fable 5** — Lean 4 code audit, Etapas 0-1, Phase 3 stones 1-32 execution, structural census, kernel X-ray instrumentation (Anthropic)
- **GPT-5.6 "Sol"** — Architecture of stones 12, 14, 15, 17-32 (single-link marginal, n-link independence, fresh-link theorem, continuity bound, linear response, Taylor remainder, fluctuation-response, second response, Wilson responses, log-partition response, Gibbs variance, disjoint-support factorizations, third connected cumulant, measure-level independence and mutual independence); epistemic veto of a false factorization; naming discipline (log partition, not free energy; response identities, not curvature; order-3 cumulant only); audit methodology and documentation reviews (OpenAI)
- **Claude Opus 4.5/4.6/4.7** — Lean 4 Formal Verification, Sorry Elimination (Anthropic)
- **GPT-5.2** — Axiom Reformulation & Strategic Planning (OpenAI)
- **Gemini 3 Pro** — historical draft generation (Google); former "numerical validation" claims RETRACTED and not treated as evidence
- **Manus AI 1.6** — DevOps, Integration & Project Coordination
