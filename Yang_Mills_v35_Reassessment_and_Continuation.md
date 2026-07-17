# From Conditional Formalization to an Axiom-Free Finite-Lattice Program
## Reassessment and Continuation of a Multi-Phase Lean 4 Project
## Around the Yang–Mills Mass Gap

**Version 35 — July 2026**

**Version-specific DOI:** 10.5281/zenodo.21416570
**Concept DOI:** 10.5281/zenodo.17397622
**Reassesses Version 34:** 10.5281/zenodo.20432205

**Jucelha Carvalho**
Lead Researcher and Project Coordinator
ORCID: 0009-0004-6047-2306

With AI research assistants acknowledged in the Contributors section.

---

## Abstract

This document reassesses and continues a multi-phase Lean 4
formalization project around the Yang–Mills existence and mass-gap
problem.

Version 34, published in May 2026, presented an axiomatic and hybrid
formalization framework developed through human-led, multi-model AI
collaboration. It also introduced a significant methodological advance:
a systematic `sorry` audit that replaced an earlier "zero sorry"
description with explicitly documented unresolved proof obligations.

Following the suspension of the original GitHub repository, the project
reconstructed its codebase from surviving and later-recovered materials.
A structural, dependency and kernel-level audit subsequently clarified
the formal status of the legacy results.

The audit showed that the earlier phases are best understood as
conditional formalizations: their Lean theorems establish consequences
of explicit assumptions, but do not establish the physical assumptions
themselves.

In response, the project adopted a different strategy. A new finite-
lattice gauge theory library, `Phase3/LatticeGauge`, is being developed
independently, without scientific axioms and without `sorry`. It currently
formalizes finite-volume lattice gauge theory, Haar-product probability,
Wilson observables, response identities, finite Mayer identities,
plaquette connectivity and the first exact algebraic foundations for a
future cluster expansion.

This work is not a proof, partial proof or claimed solution of the
Yang–Mills Existence and Mass Gap Millennium Problem.

---

## 1. Purpose of this version

The May 2026 document, "Version 34.0 FINAL", represented the project as
it was understood at that stage, using the models, tools, source
materials and verification practices then available.

Version 34 should not be read only through the corrections that followed
it. It recorded substantial work in formal architecture, theorem
decomposition, Lean implementation, physical hypothesis generation,
documentation and multi-model coordination.

It also contained a genuine methodological advance: the audit led by
Claude Opus 4.7 eliminated 104 `sorry` statements and retained seven
unresolved statements as explicitly documented proof obligations.

The subsequent repository reconstruction and formal audit made it
possible to distinguish more precisely among:

- machine-checked deductions;
- deductions conditional on scientific assumptions;
- imported or literature-based assumptions;
- open-problem assumptions;
- incomplete proofs;
- exploratory numerical assessments;
- executed computational experiments;
- physical conjectures and research directions.

This version updates the evidentiary classification of the earlier
claims. It does not judge or diminish the people or AI systems that
produced them.

Each generation contributed to the vocabulary, architecture, debugging
experience, research hypotheses, repository recovery and formal
discipline that made the current development possible.

Earlier Zenodo versions remain accessible as an unmodified historical
record of that evolution.

---

## 2. A change of strategy, not the execution of the old roadmap

Version 34 used "Phase 3" to describe a proposed direct construction of
continuum Yang–Mills theory, followed by a final phase intended to prepare
a complete proof and Clay Institute submission.

The current `Phase3/LatticeGauge` library is not the execution of that
timeline.

It is a deliberate strategic reset.

Instead of treating the conditional legacy framework as the foundation
for an immediate continuum construction, the project returned to a
finite and explicitly controlled mathematical setting.

The new path begins with:

- finite periodic lattices;
- compact gauge groups;
- Haar probability measures;
- local plaquette actions;
- Wilson paths and loops;
- finite-volume Gibbs expectations;
- independence and correlation identities;
- finite combinatorics of plaquettes and connected components.

Historical modules may guide questions and architecture, but no
conditional conclusion from the earlier phases is imported as a
scientific premise of the new library.

Every result entering the new Phase 3 must be defined and proved again
inside the axiom-free development.

---

## 3. Previous statements and their current classification

The following table updates the scientific classification of statements
made in Version 34.

| Statement in Version 34 | Current audited classification |
|---|---|
| "Approximately 50% of the Millennium Problem"; Phases 1 and 2 complete; projected timeline to Clay submission | No longer maintained as a measure of progress or as a timeline. There is no justified percentage that maps the conditional modules to completion of the Millennium Problem. |
| "The four central axioms were proved, conditional on numerical validation" | The axioms were reorganized or restated as explicit hypotheses. This was useful for transparency, but did not establish the hypotheses. Several of them contain mathematical content equivalent or closely related to unresolved problems. |
| "115+ theorems"; 104 `sorry` statements eliminated; 7 remaining | The theorem counts described the reconstructed tree available at that time. The elimination and explicit retention of unresolved `sorry`s was a genuine methodological improvement. Current counts are maintained through the repository audit and versioned census artifacts. |
| General "95–99% numerical validation" percentages | Reclassified as exploratory model-generated assessments unless supported by a recovered, executable and reproducible computation. These percentages are not treated as evidence establishing the formal assumptions. |
| Prediction Δ = 1.220 GeV compared with 1.206 GeV | Reclassified as an exploratory model-generated estimate and comparison with physical or literature values, not as a proof and not, by itself, as an executed simulation of the project. |
| Reported analysis of 110 configurations and 0% topological pairing | Preserved as a distinct historical computational experiment. Its final description must state whether the original data, scripts and execution artifacts were recovered and independently rerun. The reported null result contributed to refinement of the original pairing hypothesis. |
| "Three fundamental discoveries": holography, thermodynamic mass gap and Gribov control | Preserved as exploratory hypotheses and research directions. They are not presented as established physical discoveries. |
| The five bridges and the bound 1.452 ≤ Δ₀(g) ≤ 1.655 GeV | The Lean deductions are conditional results about functions satisfying assumed endpoint, monotonicity, regularity or limit properties. The physical Yang–Mills content resides in the assumptions. |
| "Complete hybrid verification methodology" | Reclassified as an important historical human–AI workflow combining formal deduction, hypothesis generation, exploratory computation and documentation. These forms of evidence are now reported separately rather than treated as interchangeable. |

---

## 4. The entropic hypothesis and the contribution of Gemini 3 Pro

Gemini 3 Pro played a substantial role in the early scientific and
architectural development of the project.

Its contributions included:

- formulation and development of the entropic mass-gap hypothesis;
- exploration of a possible relationship among ultraviolet and infrared
  degrees of freedom, entanglement entropy, Gribov-sector structure and
  the mass gap;
- exploratory numerical and physical assessments;
- early holographic and thermodynamic interpretations;
- draft generation and organization of the historical formalization
  program.

These contributions led to concrete modules and definitions in the
legacy codebase, including the `ScaleSeparation` and
`EntropicPrinciple` families.

The later audit clarified that the decisive implication from the
entropic structures to a positive mass gap had been represented by an
assumption rather than derived from a constructed quantum state space.

This changes the evidentiary classification of the result, but not the
historical importance of the contribution.

The entropic and entanglement line remains a possible long-term research
program. A rigorous treatment would first require infrastructure that
the project does not yet possess, including:

- an appropriate Hilbert-space or operator-algebraic formulation;
- gauge constraints and a physical state space;
- regional or algebraic subsystems;
- reduced states or suitable gauge-theoretic analogues;
- rigorously defined entropy and mutual information.

No claim is made that such a construction will prove the mass gap.
The direction is preserved as a scientifically motivated future question.

---

## 5. Current machine-verified development

**Reference commit:** `[SHA of tag zenodo-v35 — inserted in the published PDF]`
**Repository tag:** `zenodo-v35`
**Final CI status:** green — https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/29539151917

At the reference commit, `Phase3/LatticeGauge` contains:

- 35 verified project milestones ("stones");
- 34 Lean source files;
- 211 theorem and lemma declarations (plus 64 supporting definitions);
- zero scientific `axiom` declarations;
- zero `sorry`.

Principal declarations have been inspected with `#print axioms`.
Their reported dependencies are limited to the standard Lean/Mathlib
foundations used by the project, such as:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

The verified library includes:

- finite periodic lattices, sites, directions, links and plaquettes;
- lattice gauge configurations;
- Wilson action and local plaquette observables;
- gauge and translation invariance;
- finite-volume Gibbs weights, partition functions and expectations;
- Wilson paths and Wilson loops;
- Haar probability measure instantiated on `U(n)`;
- right-invariance and inversion-invariance established using Haar
  uniqueness;
- finite-link independence in the product Haar state;
- Haar-distributed fresh-link holonomies;
- exact β = 0 expectation formulas for suitable Wilson-path
  observables;
- finite-volume continuity and Taylor estimates around β = 0;
- fluctuation–response, covariance, variance and third-cumulant
  identities;
- binary and finite-family factorization for observables with disjoint
  link supports;
- official Mathlib `IndepFun` and `iIndepFun` formulations;
- finite joint product laws and their preservation under measurable
  coordinate-wise post-composition;
- an exact finite plaquette-activity/Mayer subset identity;
- connectivity of plaquettes through shared links;
- canonical decomposition into connected plaquette components;
- exact factorization of each Mayer term over those components;
- finite plaquette polymers and their canonical decomposition into
  compatible families.

These results are exact finite-volume statements.
They provide algebraic, combinatorial and probabilistic infrastructure
for a future cluster-expansion development.

They do not yet establish:

- convergence of a cluster expansion;
- estimates uniform in lattice volume;
- a thermodynamic limit;
- a continuum limit;
- exponential clustering in the required setting;
- construction of the physical Hilbert space;
- construction or spectral analysis of a Yang–Mills Hamiltonian;
- the Osterwalder–Schrader or Wightman axioms;
- a Yang–Mills mass gap.

---

## 6. Repository history and reconstruction

This is the second public GitHub repository of the project.

The original repository was suspended by GitHub. The project team did
not receive an explanation that enabled restoration and could not access
the repository contents in order to export the complete material.

The current repository was reconstructed from surviving local files,
documents, build artifacts, model-session outputs and later-recovered
Lean modules.

A subsequent forensic audit identified three broad layers:

1. early exploratory formalization;
2. conditional and axiom-based formalization;
3. the new finite-lattice, axiom-free library.

The recovered files are preserved as research provenance. They document
the evolution of definitions, attempted proof architectures, research
questions and human–AI collaboration.

No claim is made that the reconstructed historical repository is
byte-for-byte identical to the inaccessible original repository.

To reduce future platform risk, the release associated with this version
includes a versioned source snapshot and checksum manifest.

---

## 7. Cumulative human–AI collaboration

The project is coordinated by Jucelha Carvalho.

The AI systems listed below participated at different stages and under
different technical conditions. Their roles are cumulative descriptions,
not rankings.

### Jucelha Carvalho

Research direction, project coordination, multi-model orchestration,
scope decisions, repository reconstruction, validation workflow,
documentation and integration supervision.

### Claude Fable 5 — Anthropic

Lean 4 implementation and debugging, Mathlib source reconnaissance,
structural and kernel-dependency audits, Phase 3 milestone execution,
build verification, CI integration and technical-state documentation.

### GPT-5.6 "Sol" — OpenAI

Theorem and milestone architecture, mathematical review, probabilistic
and cluster-expansion roadmap, scope control, adversarial examination of
proposed statements, detection of invalid factorization claims, naming
discipline, audit methodology and documentation review.

### Claude Opus 4.5, 4.6 and 4.7 — Anthropic

Lean formalization, proof development, reduction and documentation of
incomplete proofs, Phase 1 and Phase 2 work, `sorry` audit, historical-code
recovery, forensic inventory and dependency mapping.

### GPT-5.2 — OpenAI

Early axiom reformulation, conditional-theorem architecture and strategic
planning.

### Gemini 3 Pro — Google

Entropic mass-gap hypothesis, quantum-information and holographic
research directions, exploratory numerical and physical assessments,
draft generation and historical architecture.

### Manus AI 1.6

DevOps, repository integration, workflow coordination and project
operations.

No single model produced the project.
The present verified library was made possible by accumulated
contributions across all of these stages.

AI cross-validation is not a substitute for mathematical peer review,
independent reproduction or numerical simulation.

Lean verification establishes that a formal conclusion follows from its
formal definitions and hypotheses. It does not, by itself, establish that
the formalization captures every mathematical and physical requirement
of the Yang–Mills Millennium Problem.

---

## 8. Citation

To cite this specific version:

Carvalho, J. (2026).
*From Conditional Formalization to an Axiom-Free Finite-Lattice Program:
Reassessment and Continuation of a Multi-Phase Lean 4 Project Around the
Yang–Mills Mass Gap* (Version 35).
Zenodo.
https://doi.org/10.5281/zenodo.21416570

For the evolving collection of versions:

Concept DOI:
https://doi.org/10.5281/zenodo.17397622

Version 34 reassessed in this document:

Carvalho, J. et al. (2026).
*Towards a Formal Verification of the Yang–Mills Mass Gap in Lean 4,
Version 34.0 FINAL*.
Zenodo.
https://doi.org/10.5281/zenodo.20432205

---

## Contact

Jucelha Carvalho
Email: jucelha@smarttourbrasil.com.br
ORCID: https://orcid.org/0009-0004-6047-2306
