# Draft — post for leanprover.zulipchat.com, stream #maths

**Title suggestion:** Lattice gauge theory foundations in Lean 4 (Wilson
action, Haar on U(n), gauge invariance) — feedback welcome

---

Hi everyone! I coordinate a small independent project formalizing lattice
gauge theory foundations in Lean 4 (Mathlib v4.15). Everything below is
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
  and RIGHT invariance proved via uniqueness of Haar measure.

Repo: https://github.com/consensusframework/yang-mills-mass-gap
(Phase3/LatticeGauge; the repo's Phases 1-2 are historical conditional
material, honestly labelled — see VERIFICATION_STATUS.md.)

Questions:
1. Would the unitary-group topological instances and the compact-group
   right-invariance of Haar be welcome as Mathlib PRs? (I saw
   Topology/Algebra/Star/Unitary.lean landed on master in 2025 — our
   file ports that pattern to v4.15 and adds compactness + Haar.)
2. Any advice on the long-term target — strong-coupling cluster
   expansion / Osterwalder–Seiler mass gap for lattice Yang-Mills?
   We know this is a multi-year, community-scale effort; we're looking
   for guidance and collaborators, not making claims.

**Important honesty note:** this project makes NO claim on the Clay
problem. An earlier phase of the project overclaimed; it has been fully
retracted and the repository now documents exactly what is proved and
what is assumed. We'd rather be corrected here than anywhere else.
