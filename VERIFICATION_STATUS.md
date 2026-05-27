# Verification Status — Yang-Mills Mass Gap (Lean 4)

**Last updated:** May 2026
**Project version:** v33 — Phases 1 & 2

---

## Purpose of this document

This is the **honest, complete disclosure** of the verification status of every
theorem in this repository. It exists because the README's high-level summary
("0 `sorry` in Phase 2", "115+ theorems") is true but incomplete: the
verification methodology is **hybrid** (formal Lean 4 + external numerical
validation encoded as axioms), and a careful reader is entitled to know
exactly which steps are formal and which rely on validated axioms.

If you are a referee, mathematician, physicist, or future collaborator —
**read this file before drawing conclusions about the project's status.**

---

## Methodology: hybrid formal + numerical verification

This project combines three kinds of reasoning:

1. **Formal Lean 4 proofs** — derivations by `linarith`, `tendsto_nhds_unique`,
   `ge_of_tendsto`, `le_of_tendsto`, case analysis, rewriting, and other
   Lean tactics, from clearly stated hypotheses.
2. **External numerical validation** by Gemini 3 Pro via lattice QCD
   simulations, encoded as axioms whose name begins with `gemini_*`.
3. **Structural / object-level axioms** that introduce abstract objects
   (`mass_gap`, `Delta0`, `beta_lattice`, …) that are not constructed
   inside Lean but treated as primitives.

Every theorem in Phase 2 has **zero `sorry` tactics**, in the sense that
`grep -rn '^[[:space:]]*sorry' Phase2/` returns nothing. But every Phase 2
theorem also depends on one or more axioms of types (2) and/or (3). The
table below documents this precisely.

**There is precedent for this methodology.** The Flyspeck project (formal
verification of the Kepler conjecture, Hales et al.) combined formal HOL
Light proofs with numerically validated nonlinear inequalities in
essentially the same way.

---

## Phase 2 — theorem-by-theorem honest status

Each row says: (a) whether the proof uses formal Lean tactics, (b) which
Gemini-validated axioms it consumes, and (c) which structural axioms it
declares or relies on. **All 15 theorems are hybrid.**

| # | Title | Formal tactics? | Gemini axioms consumed | Structural axioms declared |
|---|---|---|---|---|
| 1 | β-function negativity | ❌ direct axiom application | `gemini_beta_validation` | — (uses `beta`, `in_convergence_region`) |
| 2 | Running coupling monotonicity | ❌ direct axiom application | `gemini_running_monotonicity` | `rg_equation`, `initial_condition`, `running_coupling_in_region` |
| 3 | Bound preservation | ✅ `linarith`/algebra | `gemini_bound_validation` | `coupling_stays_bounded_aux` |
| 4 | Mass gap persistence | ✅ `linarith`/algebra | `gemini_mass_gap_monotone_in_g`, `gemini_phase1_gap_uniform_in_a` | `ge_trans`, `le_refl_float`, `gap_positive_from_bound`, `ne_of_gt_float`, `g0_positive` |
| 5 | Lipschitz continuity (g) | ✅ `linarith`/algebra | `gemini_lipschitz_constant_validation` | `continuity_from_lipschitz`, `gap_bounded_aux` |
| 6 | Lipschitz continuity (a) | ✅ `linarith`/algebra | `gemini_lipschitz_in_a_validation`, `gemini_lipschitz_constant_validation` | `continuum_limit_exists_aux`, `gap_stable_aux` |
| 7 | Quantitative monotonicity | ✅ `linarith`/algebra | `gemini_mass_gap_mono_quant_validation` | `two_sided_upper_bound`, `gap_change_full_range_aux`, `no_plateaus_aux` |
| 8 | Joint Lipschitz | ✅ Lean tactics | (via `GeminiValidation5/6/8`) | — |
| 9 | Asymptotic expansion | ✅ Lean tactics | (via `GeminiValidation9`) | `expansion_form`, `c2_negative_axiom`, `Delta0_positive_axiom` |
| 10 | Continuum limit existence | ✅ Lean tactics | `gemini_continuum_limit_exists` | `limit_unique_aux` |
| 11 | Continuum mass gap lower bound (Positivity Bridge 🌉) | ❌ direct axiom application | `gemini_continuum_mass_gap_minimum` | — |
| 12 | Continuum Lipschitz in g (Regularity Bridge 🌉) | ✅ Lean tactics | `gemini_continuum_lipschitz_tight` | `mass_gap`, `Delta0`, `mass_gap_lipschitz_in_g`, `mass_gap_tendsto_continuum`, `mass_gap_lower_bound_continuum` |
| 13 | Continuum monotonicity in g (Order Bridge 🌉) | ✅ Lean tactics | (via `GeminiValidation13`) | `mass_gap`, `Delta0`, `mass_gap_monotonic_in_g`, `mass_gap_tendsto_continuum`, `continuum_gap_quantitative_separation`, `mass_gap_lower_bound_continuum` |
| 14 | RG invariance (Physical Reality Bridge 🌉) | ✅ `tendsto_nhds_unique` and others | `gemini_scheme_max_diff` | `mass_gap_A`, `mass_gap_B`, `Delta0`, `mass_gap_A_tendsto`, `mass_gap_B_tendsto`, `scheme_diff_O_a` |
| 15 | Universal physical bound (Grand Synthesis 🎯) | ✅ Lean tactics | (via `GeminiValidation15`) | `Delta0`, `continuum_mass_gap_lower_bound`, `continuum_lipschitz_in_g`, `continuum_monotonic_in_g`, `Delta0_at_gmin = 1.655`, `Delta0_at_gmax = 1.452` |

### What this table says, summarized:

- **All 15 theorems are hybrid.** None is purely formal — every one depends
  on at least one axiom (Gemini-validated or structural).
- **Theorems 1, 2, and 11** are essentially direct applications of a
  Gemini-validated axiom (the formal layer is thin).
- **Theorems 3–10 and 12–15** use real Lean tactics (`linarith`,
  `tendsto_nhds_unique`, case analysis, etc.) to combine multiple axioms
  into the final statement. The formal layer is substantive but rests on
  axioms.
- **Theorem 15 (Grand Synthesis)** assumes `Delta0(0.50) = 1.655` and
  `Delta0(1.18) = 1.452` as axioms; these are the Gemini-measured boundary
  values from which the bound `1.452 ≤ Δ₀(g) ≤ 1.655 GeV` follows by
  monotonicity.

---

## Complete axiom inventory for Phase 2

### A. Object-level axioms — define the mathematical objects

| Axiom | File | Purpose |
|---|---|---|
| `beta_lattice` | `BetaFunction.lean` | β-function as abstract numerical oracle |
| `lattice_spacing_valid` | `ConvergenceRegion.lean` | Abstract predicate on lattice spacing |
| `coupling_in_nonperturbative_regime` | `ConvergenceRegion.lean` | Abstract predicate on coupling |
| `mass_gap` (multiple files) | Theorems 12, 13, 14 | Mass gap as abstract function |
| `Delta0` (multiple files) | Theorems 12, 13, 14, 15 | Continuum mass gap as abstract function |
| `mass_gap_A`, `mass_gap_B` | Theorem 14 | Mass gaps in two RG schemes |

### B. Float / arithmetic utility axioms

These are Lean-level facts about `Float` that would be theorems in a fully
developed `Float` library but are taken as axioms here:

| Axiom | File | Statement |
|---|---|---|
| `ge_trans` | Theorem 4 | Transitivity of ≥ on `Float` |
| `le_refl_float` | Theorem 4 | Reflexivity of ≤ on `Float` |
| `ne_of_gt_float` | Theorem 4 | x > 0 → x ≠ 0 |
| `g0_positive` | Theorem 4 | g₀ > 0 |
| `lt_implies_ne` | Theorem 2 (older variant) | x < y → x ≠ y |

### C. RG-flow structural axioms

| Axiom | File | Purpose |
|---|---|---|
| `rg_equation` | Theorem 2 | dg/dμ = β/μ (existential form) |
| `initial_condition` | Theorem 2 | g(μ₀) = g₀ |
| `running_coupling_in_region` | Theorem 2 | Running coupling stays in domain |
| `mass_gap_tendsto_continuum` | Theorems 12, 13 | Continuum limit of mass gap |
| `mass_gap_A_tendsto`, `mass_gap_B_tendsto` | Theorem 14 | Scheme limits |
| `scheme_diff_O_a` | Theorem 14 | Scheme difference is O(a) |

### D. Numerical validation axioms (Gemini 3 Pro)

These are the **Gemini-validated** axioms. Each name begins with `gemini_*`
for easy auditing. Each is documented in source with its validation grid
and confidence level.

| Axiom | Theorem(s) using it |
|---|---|
| `gemini_beta_validation` | 1 |
| `gemini_running_monotonicity` | 2 |
| `gemini_bound_validation` | 3 |
| `gemini_mass_gap_monotone_in_g` | 4 |
| `gemini_phase1_gap_uniform_in_a` | 4 |
| `gemini_lipschitz_constant_validation` | 5, 6, 7 |
| `gemini_lipschitz_in_a_validation` | 6 |
| `gemini_mass_gap_mono_quant_validation` | 7 |
| `gemini_continuum_limit_exists` | 10 |
| `gemini_continuum_mass_gap_minimum` | 11 |
| `gemini_continuum_lipschitz_tight` | 12 |
| `gemini_scheme_max_diff` | 14 |
| Other `gemini_validation_*` (in GeminiValidation13/15) | 13, 15 |

### E. Boundary-value axioms

| Axiom | File | Statement |
|---|---|---|
| `Delta0_at_gmin` | Theorem 15 | Δ₀(0.50) = 1.655 GeV (Gemini-measured) |
| `Delta0_at_gmax` | Theorem 15 | Δ₀(1.18) = 1.452 GeV (Gemini-measured) |

---

## What a careful reader should conclude

- **Phase 2 has 0 `sorry` tactics across all 15 theorems.** ✅
- **No Phase 2 theorem is purely formal.** Every one depends on at least
  one axiom (Gemini-validated or structural).
- **The Five Bridges and the Grand Synthesis use real Lean tactics** to
  chain together Gemini axioms and structural axioms into the final
  statements. The formal layer is **non-trivial** but is **not** a
  derivation from first principles — it is the rigorous assembly of
  Gemini-validated facts within Lean.
- **The bound `1.452 ≤ Δ₀(g) ≤ 1.655 GeV`** holds conditionally on the
  axioms inventoried above — in particular, on the Gemini-measured
  boundary values `Δ₀(0.50) = 1.655` and `Δ₀(1.18) = 1.452`.
- **Replacing axioms by formal proofs** is a clear future workstream.
  Each `gemini_*` axiom is a candidate for replacement by either (a) a
  Lean proof from a constructive `mass_gap` definition or (b) a fully
  certified interval-arithmetic computation (Flyspeck-style).

---

## Phase 1 — current status

Phase 1 (strong-coupling mass gap) is a substantial architectural
framework: 87 Lean 4 files, ~20,500 lines, covering BFS convergence,
cluster decomposition, BRST cohomology, Faddeev–Popov determinants,
Gribov regions, the entropic principle, and the Bochner–Weitzenböck
identity.

**Current Phase 1 `sorry` count:** ~131 `sorry` tactics across ~38 files,
distributed mostly across auxiliary lemmas (Sobolev embedding, geometric
series, integral of constants, technical bounds). These are explicitly
marked in source with comments describing what remains.

**Honest characterization:** Phase 1 is a **framework with proven core
structure and pending auxiliary lemmas**, not a fully `sorry`-free
development. The Phase 2 theorems do not consume the Phase 1 `sorry`
sites — Phase 2 reasons about the RG flow taking the strong-coupling
mass gap as a hypothesis (encoded in the axioms above). Closing Phase 1
`sorry` sites is a separate workstream.

---

## Reproducibility & auditability

- Every Gemini-validated axiom cites its validation grid and confidence
  level in its docstring.
- Gemini validation scripts are in `Phase2/RGFlow_Work/GeminiValidation*.lean`.
- Any reader can run `grep -rn "^axiom" Phase2/` to enumerate every
  axiom Phase 2 depends on.
- Any reader can run `grep -rn "^[[:space:]]*sorry" Phase2/` to verify
  Phase 2 has zero `sorry` tactics.
- Any reader can run `grep -rn "gemini_" Phase2/` to enumerate all
  Gemini-validation references.

---

## Contact

Questions, corrections, and pull requests are welcome. Please open an
issue on the repository, or contact Jucelha Carvalho directly.

— *Smart Tour Brasil & collaborators*
