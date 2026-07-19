# A Multi-Phase Lean 4 Formalization Program Around the Yang–Mills Mass Gap

> **Status:** exploratory formalization research.
> This repository is **not a proof, partial proof, or claimed solution** of the
> Yang–Mills Existence and Mass Gap Millennium Problem.

## Repository history and reconstruction

This is the **second public repository** of the project.

The original repository was suspended by GitHub without an explanation available
to the project team. Because access to the repository was not restored, the
maintainers were unable to export or retrieve its complete contents.

This repository was therefore reconstructed from surviving local files, papers,
build artifacts, documentation, model-session outputs, and later-recovered Lean
modules. The reconstruction was not initially complete: portions of the original
phase structure and several files were recovered only later through a dedicated
forensic audit.

The recovered material made it possible to identify and document three distinct
stages of the project:

1. early exploratory formalization;
2. conditional and axiom-based formalization;
3. a new finite-lattice gauge theory library built independently and without
   scientific axioms.

Historical files are preserved as research provenance. They document the
evolution of the ideas, definitions, attempted architectures, and human–AI
collaboration that preceded the current verified development path.

No claim is made that the reconstructed historical tree is byte-for-byte
identical to the inaccessible original repository.

---

## Project structure

### Phase 1 — Early exploratory formalization

Phase 1 contains the earliest Lean experiments, conceptual decompositions, draft
definitions, and preliminary attempts to express parts of the Yang–Mills program.

This phase was created with the models, libraries, tooling, and project knowledge
available at the time. Its value is primarily historical and architectural: it
records the first formal vocabulary and the initial decomposition of a very large
research problem into smaller formalization targets.

Phase 1 does not currently have a complete working Lake project and is not covered
by continuous integration.

### Phase 2 — Conditional formalization

Phase 2 contains conditional Lean formalizations in which substantial physical or
mathematical content is represented by explicit assumptions, hypotheses, or
axioms.

The resulting theorems should be read in the form:

> **If the stated assumptions hold, then the formal conclusion follows.**

These modules do not establish the assumptions themselves and therefore do not
constitute progress toward solving the Clay problem. They remain useful as:

- dependency maps;
- formal statement experiments;
- records of earlier research directions;
- organizational scaffolding for possible future formalizations;
- documentation of the project's methodological evolution.

Phase 2 currently compiles as a 25-module Lake project.

### Phase 3 — Finite-lattice gauge theory

Phase 3 is a new and independently constructed Lean 4 library for finite-lattice
gauge theory.

Unlike the legacy phases, the verified Phase 3 development path introduces no
scientific axioms and contains no `sorry`. Its principal declarations are checked
with `#print axioms` and depend only on the standard Lean/Mathlib foundations:

- `propext`;
- `Classical.choice`;
- `Quot.sound`.

Phase 3 does not import the conditional conclusions of Phases 1–2 as mathematical
foundations. Historical material may inform research questions and architecture,
but any result entering Phase 3 must be defined and proved again within the
axiom-free development.

### Historical archive

Recovered, superseded, incomplete, or alternative modules are retained in the
historical archive and audit directories.

The archive is not part of the trusted Phase 3 proof path. Its purpose is to
preserve provenance, document earlier approaches, and prevent the loss of
potentially useful definitions or research questions.

---

## Current verified status

**Last updated: July 19, 2026**

- **Phase 2:** 25/25 modules compile.
- **Phase 3 / `LatticeGauge`:** 42 verified stones (stone 42 complete: the exact Penrose identity and the finite tree-graph bound).
- **Phase 3 source files:** 44.
- **Phase 3 declarations:** approximately 360 verified theorems and supporting
  definitions.
- **Scientific axioms introduced in Phase 3:** 0.
- **`sorry` declarations in Phase 3:** 0.

The Phase 3 library currently includes formalizations of:

- finite periodic lattices, sites, directions, links, and plaquettes;
- lattice gauge configurations;
- Wilson action and plaquette observables;
- gauge and translation invariance;
- finite-volume Gibbs weights, partition functions, and expectations;
- Wilson paths and Wilson loops;
- Haar probability measure instantiated on `U(n)`;
- right-invariance and inversion-invariance obtained from Haar uniqueness;
- finite-link independence in the product Haar state;
- Haar-distributed fresh-link holonomies;
- exact β = 0 expectation formulas for suitable Wilson-path observables;
- finite-volume continuity and first-order Taylor estimates around β = 0;
- fluctuation–response identities at arbitrary β ≥ 0;
- covariance, variance, and third connected-cumulant identities;
- binary and finite-family factorization for link-disjoint observables;
- `IndepFun` and `iIndepFun` formulations using the official Mathlib API;
- product laws for finite tuples of link-disjoint Wilson observables;
- stability of those product laws under coordinate-wise measurable
  post-composition;
- the exact finite plaquette-activity/Mayer subset identity;
- finite plaquette connectivity through shared links;
- canonical decomposition into connected plaquette components;
- exact factorization of every Mayer term over its connected components;
- an exact finite-volume representation of `realZ` as a sum of products of
  connected-component weights;
- plaquette polymers (nonempty, admissible, intrinsically link-connected
  plaquette sets), their compatibility relation, and the proof that the
  canonical decomposition of an admissible subset is a compatible polymer
  family;
- the exact finite polymer-gas representation of `realZ` (hard-core gas over
  compatible polymer families);
- finite Ursell coefficients as signed sums over connected spanning edge sets,
  with permutation invariance, elementary bounds, and the exact tree case;
- the canonical rooted BFS tree extraction (total, deterministic), the local
  cardinal tree converse, the Penrose closure with strict consecutive-level
  edges, and the proof that the fibres of the extraction are exactly the
  Penrose boolean intervals;
- the transport of the fibre theory to edge-set `Finset`s: fibres over a
  spanning tree are boolean intervals with free extra-edge coordinates,
  disjoint, and exactly covering the connected spanning edge sets;
- the exact Penrose identity `graphUrsellCoeff G = (−1)^n · #PenroseTrees(G)`
  obtained by two formal reindexations and the (1−1)^m cancellation, and the
  finite tree-graph bound `|φ(G)| ≤ #SpanningTrees(G)` as its corollary.

The latest results establish the **finite algebraic and probabilistic foundations**
needed for a future cluster-expansion development.

They do not yet establish convergence of a cluster expansion.

---

## Scientific scope and limitations

The verified results are finite-volume statements.

At the present stage, the project does **not**:

- construct four-dimensional continuum Yang–Mills theory;
- construct the continuum Yang–Mills measure;
- construct the physical Hilbert space;
- define and control the Yang–Mills Hamiltonian;
- verify the Wightman axioms;
- verify the Osterwalder–Schrader axioms;
- prove reflection positivity for the required continuum construction;
- establish a thermodynamic or continuum limit;
- establish bounds uniform in lattice volume;
- prove exponential clustering in the required setting;
- prove the Yang–Mills mass gap.

A formal statement of a lattice mass-gap target may appear in the library, but the
target is explicitly marked as open and is not asserted as a theorem.

Nothing in this repository should be cited as a solution or partial solution of
the Clay Millennium Problem.

---

## Verification discipline

The current Phase 3 workflow follows these rules:

1. no new scientific `axiom` declarations;
2. no `sorry`;
3. complete local build before integration;
4. continuous-integration verification after integration;
5. `#print axioms` inspection for principal declarations;
6. exact documentation of hypotheses and mathematical scope;
7. explicit separation between:
   - finite identities;
   - analytic estimates;
   - volume-uniform estimates;
   - thermodynamic or continuum limits;
   - physical conclusions;
8. no claim stronger than the formal theorem actually proves.

Names and documentation are chosen conservatively. For example:

- `log Z` is called the **log partition function**, not automatically free energy;
- pointwise response identities are not called convexity results without the
  corresponding formal wrapper;
- a third connected cumulant is not presented as a theorem about cumulants of
  every order;
- a finite Mayer identity is not presented as a completed cluster expansion.

Detailed verification and structural-audit artifacts are available in:

- [`VERIFICATION_STATUS.md`](VERIFICATION_STATUS.md)
- [`docs/audit/`](docs/audit/)
- [`PHASE3_ROADMAP.md`](PHASE3_ROADMAP.md)

---

## Historical assumptions and audit

The earlier phases contain explicit assumptions, conditional results, unfinished
proofs, alternative drafts, and exploratory model-generated estimates.

These materials were produced during different stages of the project, with
different generations of AI models, different Mathlib knowledge, different
context windows, and different levels of access to the repository.

Later audits classify declarations according to their formal role:

- verified definition or theorem;
- theorem conditional on explicit hypotheses;
- literature-based assumption not yet formalized;
- open-problem assumption;
- incomplete proof;
- exploratory numerical or conceptual input;
- superseded historical module.

This classification is intended to clarify mathematical status, **not to diminish
the contribution of earlier models or collaborators**.

Each stage contributed something necessary to the next one: vocabulary,
architecture, attempted decompositions, Lean structures, debugging experience,
research questions, documentation, recovery material, or verified code.

Some early statements described as numerical validation were generated as
exploratory model outputs rather than produced by an executed lattice simulation.
They are now preserved and labelled according to that origin. This is a
clarification of evidence type, not a judgment on the models that generated them.

The historical audit is a record of how the project learned to distinguish more
precisely between assumptions, conditional consequences, machine-checked results,
and open research targets.

---

## Human-led, multi-model methodology

The project is coordinated by **Jucelha Carvalho**
([ORCID 0009-0004-6047-2306](https://orcid.org/0009-0004-6047-2306)).

AI systems have been used as computational research assistants for:

- Lean 4 drafting and implementation;
- theorem architecture;
- source-code and Mathlib API inspection;
- debugging and build repair;
- axiom and dependency audits;
- documentation;
- repository reconstruction;
- research planning;
- adversarial checking of proposed statements;
- CI and integration support.

The project evolved across several model generations. No single model produced
the entire repository, and the current Phase 3 library depends on the accumulated
work of the models and human coordination that preceded it.

AI cross-validation is not a substitute for mathematical peer review, independent
reproduction, or numerical simulation. Machine-checked Lean proofs verify that a
formal conclusion follows from its formal definitions and hypotheses; they do not
by themselves establish that the formalization captures every required aspect of
the physical Yang–Mills problem.

---

## Current roadmap

The immediate Phase 3 roadmap is:

1. define finite connected plaquette polymers — **done (stone 35)**;
2. prove the correspondence between plaquette subsets and compatible polymer
   families (forward direction done in stone 35; inverse direction in
   progress);
3. rewrite the finite-volume partition function as an exact polymer-gas sum;
4. introduce connected coefficients and the combinatorics required for a genuine
   cluster expansion;
5. prove finite-volume convergence estimates;
6. investigate estimates uniform in lattice volume;
7. study the consequences for connected correlations and clustering.

Later stages would require substantially new infrastructure, including:

- thermodynamic limits;
- continuum scaling;
- reflection positivity;
- Hilbert-space reconstruction;
- Hamiltonian and spectral theory;
- rigorous treatment of gauge constraints;
- possible entropy and entanglement structures;
- comparison with known constructive strong-coupling results.

These are long-term research directions, not completed results.

---

## Citation

Please cite this repository as an exploratory, multi-phase Lean 4 formalization
project, not as progress establishing the Millennium Problem.

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21416570.svg)](https://doi.org/10.5281/zenodo.21416570)

```text
Carvalho, J. (2026).
From Conditional Formalization to an Axiom-Free Finite-Lattice Program:
Reassessment and Continuation of a Multi-Phase Lean 4 Project Around the
Yang-Mills Mass Gap (Version 35). Zenodo.
https://doi.org/10.5281/zenodo.21416570
```

Concept DOI (all versions): https://doi.org/10.5281/zenodo.17397622
Frozen source tag for this version: `zenodo-v35` (commit bfd8e46).

## Contact

- Jucelha Carvalho
- Email: jucelha@smarttourbrasil.com.br
- ORCID: <https://orcid.org/0009-0004-6047-2306>

## Project contributors and computational assistants

### Human coordination

- **Jucelha Carvalho** — Lead researcher and project coordinator; research
  direction, multi-model orchestration, repository recovery, scope decisions,
  validation workflow, documentation, and integration supervision.

### AI research assistants

- **Claude Fable 5 (Anthropic)** — Lean 4 implementation and debugging,
  structural census, kernel-dependency inspection, Mathlib source
  reconnaissance, Phase 3 stone execution, build verification, CI integration,
  and technical state documentation.
- **GPT-5.6 "Sol" (OpenAI)** — theorem and stone architecture, probabilistic and
  cluster-expansion roadmap, scope control, mathematical review, counterexample
  and false-factorization detection, naming discipline, audit methodology, and
  documentation review.
- **Claude Opus 4.5 / 4.6 / 4.7 (Anthropic)** — formal-verification work,
  incomplete-proof reduction, historical-code recovery, forensic inventory,
  dependency mapping, and comparative audit of reconstructed modules.
- **GPT-5.2 (OpenAI)** — early axiom reformulation, conditional-theorem design,
  and strategic planning.
- **Gemini 3 Pro (Google)** — early conceptual exploration, draft generation,
  numerical and physical hypothesis exploration, and historical architecture.
- **Manus AI 1.6** — DevOps, repository integration, workflow coordination, and
  project operations.

The roles above describe contributions made at different stages of the project.
They are not rankings. The present repository exists because those contributions
were cumulative.
