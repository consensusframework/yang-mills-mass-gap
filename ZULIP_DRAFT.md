# Draft — post for leanprover.zulipchat.com

**Where to post (in this order):**
1. **#Machine Learning for Theorem Proving** — main post (most receptive
   audience for AI-assisted formalization with this discipline);
2. **#mathlib4** — separate, shorter message JUST about question 1
   (the U(n)/Haar PR candidates), where maintainers actually decide;
3. #maths — optional cross-reference later.

**Title suggestion:** Lattice gauge theory foundations in Lean 4 (Wilson
action, Haar on U(n), gauge invariance) — feedback welcome

---

Hi everyone! I coordinate a small independent project formalizing lattice
gauge theory foundations in Lean 4 (Mathlib v4.15).

**Full disclosure:** the formalization is AI-assisted (multiple LLMs over
time), human-coordinated, with the compiler as sole judge — every claim
below is `lake build` green on CI, and no proof was ever accepted on model
confidence. The recent stones were CROSS-LAB work: architecture reviews by
GPT-5.6 (including an epistemic veto that stopped a false Wilson-loop
factorization before implementation), execution by Claude (Fable 5),
verdict by CI. Full per-commit credits in the git history; the working
protocol is documented in HANDOFF_AI.md. An earlier phase of the project did NOT have this discipline;
it was fully retracted (see the repo's VERIFICATION_STATUS.md and
HANDOFF_AI.md for the whole story — we think the failure is as instructive
as the recovery). Everything below is
axiom-free and CI-checked (GitHub Actions, `lake build`):

- 4D periodic lattice, gauge configurations, plaquette holonomy, Wilson
  action; S ≥ 0 and S(vacuum) = 0;
- gauge invariance of the Wilson action (class functions);
- Gibbs weight and partition function; 0 < Z ≤ 1 over any probability
  measure on the gauge group;
- Wilson loops along arbitrary paths; inductive transformation law;
  gauge invariance of closed loops;
- expectation values: ⟨c⟩ = c, |⟨f⟩| ≤ C for bounded observables;
- ⟨f ∘ gauge⟩ = ⟨f⟩ for bi-invariant measures (measure-preserving gauge
  action on the product measure);
- the normalized real trace on `Matrix.unitaryGroup (Fin n) ℂ`:
  χ(1) = 1, class function, |χ| ≤ 1;
- Haar probability measure on U(n) built from scratch on v4.15:
  topological-group instances, compactness (Tychonoff + closedness),
  RIGHT invariance AND inv-invariance proved via uniqueness of Haar;
- translation invariance of the action, the product measure and the
  Gibbs state; truncated correlations with an a-priori bound; and the
  FORMAL STATEMENT of the lattice mass gap (exponential clustering) —
  stated, explicitly NOT claimed as proved;
- the β = 0 regime EXACTLY SOLVED: the Gibbs state is the product Haar
  state; single-, pair- and n-link marginals (any finite injective
  family of links is jointly Haar-independent); disjoint-support
  factorization and vanishing truncated correlations;
- the FRESH-LINK THEOREM: if the first link of a path does not reappear
  in its tail, the holonomy is Haar-distributed (one independent Haar
  factor erases the tail's memory — no probabilistic induction);
- capstone, UNCONDITIONAL on U(n) with concrete Haar: for every
  nonempty non-self-repeating loop, ⟨Wilson loop⟩ at β = 0 equals the
  character integral ∫ χ dHaar. Zero hypotheses.

Repo: https://github.com/consensusframework/yang-mills-mass-gap
(Phase3/LatticeGauge; the repo's Phases 1-2 are historical conditional
material, honestly labelled — see VERIFICATION_STATUS.md.)

Questions:
1. Would the unitary-group topological instances and the compact-group
   right-invariance of Haar be welcome as Mathlib PRs? (I saw
   Topology/Algebra/Star/Unitary.lean landed on master in 2025 — our
   file ports that pattern to v4.15 and adds compactness + Haar; we would
   of course rebase against master for any PR.)
2. Any advice on the long-term target — strong-coupling cluster
   expansion / Osterwalder–Seiler mass gap for lattice Yang-Mills?
   With β = 0 exactly solved and HasLatticeMassGap formally stated,
   the next climb is β > 0 perturbation of the product state. We know
   this is a multi-year, community-scale effort; we're looking for
   guidance and collaborators, not making claims.
3. We are also mid-way through a structural audit (AUDIT_ZERO, branch
   audit-zero): 1425 declarations inventoried, 97 CORE — the legacy
   conditional phases are being reclassified, not counted as results.

**Important honesty note:** this project makes NO claim on the Clay
problem. The repository documents exactly what is proved and what is
assumed. We'd rather be corrected here than anywhere else.
