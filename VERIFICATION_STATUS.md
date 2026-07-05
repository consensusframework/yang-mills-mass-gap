# Verification Status — Thorne Taxonomy

**Last updated:** July 5, 2026 (Etapa 1)

## The three boxes

Following Kip Thorne's discipline for *Interstellar* — every scientific element
labelled as **established truth**, **educated guess**, or **speculation**, and
never allowed to masquerade as one another — every statement in this repository
falls into exactly one box:

### 📗 Box 1 — Established truth (machine-checked)
Statements proven in Lean 4 with `#print axioms` showing only the standard
foundations (`propext`, `Classical.choice`, `Quot.sound`) — or additionally
depending *only on explicitly named hypotheses in their own signature*.
After the Etapa 0/1 cleanup, the Phase 2 theorems are honest **conditionals**:
"IF the named physical assumptions hold, THEN…". The mathematical content of
most is elementary (transitivity, monotone-function bounds); their value is
organizational, not mathematical depth.

### 📙 Box 2 — Educated guess (literature-backed assumptions)
`axiom` declarations matching results known in mathematical physics but never
formalized in Lean (Uhlenbeck compactness, Bishop-Gromov, cluster expansion
bounds, Atiyah-Singer...). Marked 🔬 in AXIOM_AUDIT.md. Each could in principle
be replaced by a real proof — at a cost of person-years each.

### 📕 Box 3 — Speculation (open problems and heuristics)
`axiom` declarations equivalent to open problems — including the existence of
the Yang-Mills measure, the mass gap itself (`mass_gap`, `Delta0`,
`mass_gap_tendsto_continuum`), gap persistence, Gribov cancellation, and all
holographic principles. Marked 🔴 in AXIOM_AUDIT.md. **No theorem that
consumes a Box-3 axiom constitutes progress on the Clay problem.**

### 🗑️ Removed — formerly a fourth, illegitimate box
`gemini_*` axioms recorded LLM assertions ("confidence 1000%") as mathematics.
As of Etapa 0/1 they are deleted (21 orphans) or converted into explicit
hypotheses (`def ...Assumption : Prop`) that theorems must declare openly.
Phase 1 still contains 61 pending conversion (see PHASE1_GEMINI_CONVERSION_MAP.md).

## Current state (branch etapa0-higiene)

| Item | Status |
|---|---|
| CI | 3 jobs green on `main` (Phases 1, 2, 3) |
| Phase 2 | 25/25 modules compile; theorems conditional with named hypotheses |
| Phase 1 | Restructured; 10/76 modules compile; rest catalogued (PHASE1_BUILD_STATUS) |
| **Phase 3 (LatticeGauge)** | **8 files, ~31 theorems, 0 axioms — pure Box 1:** Wilson action, gauge invariance, Gibbs measure (0 < Z ≤ 1), Wilson loops (closed-loop gauge invariance), expectation values (⟨c⟩ = c, |⟨f⟩| ≤ C), the capstone |⟨Wilson loop⟩| ≤ 1 with proved uniform action bound, and GAUGE INVARIANCE OF THE GIBBS EXPECTATION (⟨f∘gauge⟩ = ⟨f⟩ for bi-invariant measures, via measure-preserving gauge action), and the PHYSICAL character on U(n): normalized real trace with χ(1)=1, class function, |χ| ≤ 1 (unitary column bound) — the abstract framework instantiates on genuine matrix gauge groups |
| gemini_* axioms | 0 anywhere |
| Claim on Clay problem | **None.** See README. |

## Rule going forward

New material enters `main` only if: (1) CI green; (2) every new `axiom` is
classified into Box 2 or Box 3 in AXIOM_AUDIT.md at the same commit; (3) no
statement moves boxes without a proof or a retraction note.
