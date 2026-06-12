# Conditional Lean 4 Formalization Exercises Around the Yang-Mills Mass Gap

**Status: exploratory / conditional formalization — NOT a proof (partial or otherwise) of the Clay Millennium Problem.**

## What this repository is

A collection of Lean 4 files exploring how statements *about* a hypothetical Yang-Mills mass gap function could be organized formally. All physical content is **assumed via explicit `axiom` declarations**; the theorems proven are logical consequences of those assumptions.

## What this repository is NOT

- It is **not** a proof of the Yang-Mills mass gap, in whole or in part.
- It does **not** construct the Yang-Mills measure, a Hilbert space, a Hamiltonian, or verify Wightman/Osterwalder-Schrader axioms — the actual content of the Clay problem.
- Percentages such as "~50% of the Millennium Prize Problem" from earlier versions of this README were **not defensible** and are retracted.

## Honest accounting (see AXIOM_AUDIT.md)

| Metric | Value |
|---|---|
| `axiom` declarations | 404 (329 unique) |
| Theorems/lemmas | ~442 |
| Theorems unconditional (axiom-free beyond Lean/Mathlib) | ~0 substantive — provable statements are elementary real-analysis facts |
| `sorry` in code | present in 21 files across Phase 1 and Phase 2 — earlier "zero sorry" claim was incorrect |
| Axioms that assert LLM outputs (`gemini_*`) | ~110 — scheduled for removal, no probative value |
| Axioms equivalent to open problems (incl. the mass gap itself) | ~60 |

### Example of what is actually proven

`Theorem15_UniversalPhysicalBound` proves: *if* a function `Delta0 : ℝ → ℝ` is strictly decreasing on [0.5, 1.18] *and* takes assumed values at the endpoints, *then* it is bounded between those values. This is an elementary fact about monotone functions; the Yang-Mills content resides entirely in the five axioms it imports.

## Authorship and method

Coordinated by **Jucelha Carvalho** ([ORCID: 0009-0004-6047-2306](https://orcid.org/0009-0004-6047-2306)) using multiple AI assistants (Manus AI 1.6, Claude Opus 4.5/4.6/4.7, GPT-5.2, Gemini 3 Pro) for drafting Lean code.

AI cross-validation is **not** equivalent to peer review or numerical simulation. Earlier claims of "numerical validation by Gemini" referred to LLM-generated assertions, not executed lattice computations, and are retracted. The `gemini_*` axioms in the codebase record these assertions and will be removed in the next cleanup phase.

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
- **Claude Mithos Flabe 5** — Lean 4 Code Audit & Etapa 0 Hygiene (Anthropic)
- **Claude Opus 4.5/4.6/4.7** — Lean 4 Formal Verification, Sorry Elimination (Anthropic)
- **GPT-5.2** — Axiom Reformulation & Strategic Planning (OpenAI)
- **Gemini 3 Pro** — Numerical Validation (Google)
- **Manus AI 1.6** — DevOps, Integration & Project Coordination
