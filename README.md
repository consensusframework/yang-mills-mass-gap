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

**Last updated: August 14, 2026**

- **Phase 2:** 25/25 modules compile.
- **Phase 3 / `LatticeGauge`:** stone deliveries verified and integrated
  (STONES 1–47 COMPLETE; for stone 47: the paper proof of the finite
  Kotecký–Preiss induction is frozen and adversarially audited, and its
  formal layers b-i, b-iiA and the six-gate A-package of b-iiB are
  integrated — the k! enumeration count, the bidirectional
  tree/decomposition equivalence, the exact weight factorization, the rooted
  transport between finite linear types, the block-sum identification
  fixedRootBlockSum = rootedTreeSum, the formal F(B) with its (m+1)!
  factor audit, GATE V (the multinomial as a theorem), and GATE VI
  COMPLETE: root-degree stratification, finite size profiles, the
  per-block pinch, the profiled central equivalence with EXACT weight
  preservation, the block-to-fixedRootBlockSum bridge, the UNIVERSAL
  identity k!·R = n!·Σ_s Π G with no division, and THE EXACT
  RECURRENCE kpTreeCoeff_recurrence in range-n form for arbitrary real
  activities — no sign, no KP, no analysis; STONE 47 COMPLETE — 47c: the
  ABSTRACT FINITE KP INDUCTION (S_M(γ) ≤ exp(a γ) under an abstract
  smallness interface, KP hypothesis consumed exactly once) and its
  specialization: for 0 ≤ β ≤ 1/40000, EVERY finite partial sum of the
  rooted cluster coefficients with the real polymer activity is
  uniformly bounded by exp(card γ) — no passage M → ∞ anywhere;
  convergence (Summable/tsum) is stone 48).
- **Phase 3 source files:** 63.
- **Phase 3 declarations:** approximately 740 verified theorem/lemma declarations and supporting
  definitions.
- **Scientific axioms introduced in Phase 3:** 0.
- **`sorry` declarations in Phase 3:** 0.

**Milestone of the current chapter.** The Kotecký–Preiss smallness
hypothesis for this lattice polymer gas is machine-verified with fully
traced constants: for 0 ≤ β ≤ 1/40000,
`Σ_{D incompatible with C} |w_β(D)|·e^{|D|} ≤ |C|`.
Stone 47 establishes the exact rooted-tree recurrence and the abstract
finite Kotecký–Preiss induction, yielding a uniform bound on every
finite partial sum of the rooted cluster coefficients. STONE 48 now
completes the passage to the infinite series: for 0 ≤ β ≤ 1/40000, the
concrete signed rooted Ursell series is absolutely convergent, with
Σₙ |Cₙ(w_β,χ, γ₀)| ≤ exp(card γ₀). No log-Z identification, no realZ ≠ 0,
no thermodynamic limit, no clustering, and no mass-gap statement is
claimed.

The Phase 3 library proceeds in five arcs — foundations and the Haar/U(n)
state, the exact β = 0 probabilistic chapter, the exact expansion mechanics
(Mayer → components → polymers → gas), the Penrose/tree-graph combinatorics,
and the Kotecký–Preiss bounds chapter — and currently includes
formalizations of:

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
  finite tree-graph bound `|φ(G)| ≤ #SpanningTrees(G)` as its corollary;
- the hard-core tree-graph bound for polymer tuples: the Ursell coefficient
  of a tuple is controlled by a sum over labelled trees of the complete graph
  with a hard-core incompatibility indicator on every edge — the format that
  preserves the local constraints needed by future activity sums;
- the exponential activity bound |w_β(C)| ≤ (2β)^|C| for every finite block
  (volume-independent, no independence inside the block; no decay, no series,
  no convergence claim);
- the link-covering inequality: the sum of any nonnegative weight over the
  polymers incompatible with a block C is at most the sum over the ≤ 4·|C|
  support links of C of the rooted per-link sums — with the Kotecký–Preiss
  shaped weight |w_β(D)|·exp(α·|D|) as documented specialization;
- the uniform local geometry of the plaquette lattice: at most 16 plaquettes
  use a fixed link and the stone-33 adjacency graph has degree at most 64 —
  constants with no volume parameter in their types — reducing the control of
  all polymers incompatible with C to the size-counting of connected polymers
  containing a fixed root plaquette;
- the doubled-walk counting: every rooted connected polymer of size m+1 is
  the exact visited set of some closed walk of length 2m (a covering by the
  image of walks — no canonical tree, no injectivity), so at most 64^(2m)
  rooted polymers per plaquette and 16·64^(2m) per link, with the weighted
  one-size slice bounds;
- the finite geometric majorant (no infinite series anywhere) and the
  KOTECKÝ–PREISS SMALLNESS HYPOTHESIS, verified with fully traced constants:
  Σ_{D incompatible with C} |w_β(D)|·e^{|D|} ≤ |C| whenever
  0 ≤ β ≤ 1/40000 (symbolic threshold β ≤ 1/(8320·e)); this hypothesis is
  consumed by the abstract finite KP induction completed in stone 47, and
  by stone 48 the passage to `Summable`/`tsum` is COMPLETE: the concrete
  signed rooted Ursell series is absolutely convergent in this regime;
- the finite rooted cluster coefficients: Aₙ (rooted Ursell, no root
  activity) and its labelled-tree majorant Tₙ as finite sums over the real
  polymer universe, with A₀ = T₀ = 1, nonnegativity, Aₙ ≤ Tₙ from the
  hard-core tree bound, and named relabeling lemmas (tree universe and
  rooted summand invariant under index permutations) — the first formal
  layer beneath the Kotecký–Preiss induction, whose complete paper proof
  (`PEDRA47A_PROOF.md`, frozen at commit `ede2ba63d2`) survived independent
  adversarial audit by a fourth model (Kimi/Moonshot) before any
  formalization began;
- the root-removal partition of spanning trees: the root neighbours (typed
  to exclude the root), the child forest with the root isolated, exactly one
  root neighbour per connected component (via the unique-path
  characterization of trees), the disjoint edge factorization, and the exact
  reconstruction;
- the A-package of the enumeration route: exactly k! enumerations of the
  root neighbours (counted, not divided); enumerated trees ≃ admissible
  ordered decompositions with both inverses; global assignments ≃ ordered
  per-component data; the exact factorization of the rooted tree weight over
  its components; the rooted transport of tree sums between finite linear
  types; the identification of the fixed-root block sum with the standard
  coefficient sum (no factorial), then m!·kpTreeCoeff; and the formal F(B):
  summing over the m+1 possible marks turns m! into (m+1)!, with the origin
  of every factor recorded in the kernel.

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

1. Stone 49 — unroot the convergent rooted series (the exact finite
   relation Σ_γ₀ z(γ₀)·Cₙ(z,γ₀) = (n+1)·B_{n+1}(z)), prove absolute
   summability of the unrooted coefficients, and only then attack the
   exp/log identification with the finite-volume polymer-gas
   representation of stone 36;
2. develop volume-uniform estimates;
3. investigate connected correlations and exponential clustering;
4. only thereafter study thermodynamic/continuum limits and the additional
   structures required for any mass-gap program.

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

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21939929.svg)](https://doi.org/10.5281/zenodo.21939929)

```text
Carvalho, J. (2026).
From Conditional Formalization to an Axiom-Free Finite-Lattice Program:
Reassessment and Continuation of a Multi-Phase Lean 4 Project Around the
Yang-Mills Mass Gap (Version 47). Zenodo.
https://doi.org/10.5281/zenodo.21939929
```

Concept DOI (all versions): https://doi.org/10.5281/zenodo.17397622
Frozen source tag for this version: `zenodo-v47`.

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
- **Kimi 3 (Moonshot AI)** — independent adversarial audit of the finite
  Kotecký–Preiss induction manuscript (stone 47a-P, frozen at `ede2ba63d2`):
  verification of the recurrence, the factorial cancellations, the 1/k!
  multiplicity under repetitions, and the non-circularity of the KP
  hypothesis, with corrections incorporated before any formalization.
- **Gemini 3 Pro (Google)** — early conceptual exploration, draft generation,
  numerical and physical hypothesis exploration, and historical architecture.
- **Manus AI 1.6** — DevOps, repository integration, workflow coordination, and
  project operations.

The roles above describe contributions made at different stages of the project.
They are not rankings. The present repository exists because those contributions
were cumulative.
