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
| **Phase 3 (LatticeGauge)** | **18 files, ~83 theorems, 0 axioms — pure Box 1:** Wilson action, gauge invariance, Gibbs measure (0 < Z ≤ 1), Wilson loops (closed-loop gauge invariance), expectation values (⟨c⟩ = c, |⟨f⟩| ≤ C), the capstone |⟨Wilson loop⟩| ≤ 1 with proved uniform action bound, and GAUGE INVARIANCE OF THE GIBBS EXPECTATION (⟨f∘gauge⟩ = ⟨f⟩ for bi-invariant measures, via measure-preserving gauge action), and the PHYSICAL character on U(n): normalized real trace with χ(1)=1, class function, |χ| ≤ 1 (unitary column bound) — the abstract framework instantiates on genuine matrix gauge groups; HAAR PROBABILITY MEASURE ON U(n) constructed from first principles (topological group instances, compactness via Tychonoff, RIGHT invariance proved via Haar uniqueness) with UNCONDITIONAL capstones: |⟨W⟩| ≤ 1 and gauge invariance of the Gibbs expectation on U(n); TRANSLATION INVARIANCE of action, measure and Gibbs state; truncated correlations with a-priori bound; and — stated, NOT proved — the formal definition HasLatticeMassGap (open target, stated not proved); and the ELEVENTH STONE: at β = 0 the Gibbs state is the product Haar state, observables with disjoint link-supports FACTORIZE (independence), and truncated correlations VANISH — the first proven clustering statement (trivial regime, honestly labelled), the base camp of the cluster expansion; and the TWELFTH STONE (inter-lab collaboration: strategy by GPT-5.6 "Sol"/OpenAI, execution by Claude Fable 5/Anthropic, verdict by CI): the SINGLE-LINK LAW — one link variable is exactly Haar-distributed (eval pushforward of the product measure), linkCharacterIntegral defined, ⟨ψ(U_ℓ)⟩₀ = ∫ψ dμ; and the THIRTEENTH STONE: the joint law of two distinct links is μ⊗μ (pair independence), two-point factorization, connected single-link correlator = 0 at β=0; and the FOURTEENTH STONE (architecture: Sol/GPT-5.6 incl. the epistemic veto of a false Wilson-loop product formula; implementation: Fable via Measure.pi_eq boxes): n-LINK INDEPENDENCE — any finite injective family of links has joint law μ^⊗ι, with n-point factorization and ⟨∏fᵢ(U ℓᵢ)⟩₀ = ∏ linkCharacterIntegral; and the FIFTEENTH STONE — THE FRESH-LINK THEOREM (architecture Sol/GPT-5.6, execution Fable): holonomies of nonempty paths whose first link does not reappear (in particular Nodup paths) are HAAR-DISTRIBUTED, via Haar absorption (X·Y and X⁻¹·Y remain Haar for independent Y) with no probabilistic induction; and the SIXTEENTH STONE — the first CLOSED FORMULA for a physical observable: ⟨Wilson loop⟩₀ = ∫ χ dμ for every nonempty non-self-repeating loop (the β = 0 sector of this finite-lattice model characterized exactly); Haar on U(n) is also INV-INVARIANT (uniqueness mirror), making the fresh-link theorem and ⟨Wilson loop⟩₀ = ∫χ dHaar unconditional on the physical gauge group (with a presentation corollary for closed loops); and the SEVENTEENTH STONE — the first β > 0 result: the FINITE-VOLUME CONTINUITY BOUND from β = 0, |⟨f⟩_β − ⟨f⟩₀| ≤ 2CBβ·exp(βB), with window and Wilson-path corollaries (finite-volume only; B grows with the lattice); and the EIGHTEENTH STONE — LINEAR RESPONSE: d/dβ⟨f⟩_β|₀ = −Cov₀(f, S), the first explicit bridge between the β-perturbation and product-state correlations (finite volume, derivative at zero, no thermodynamic uniformity); and the NINETEENTH STONE — the FIRST-ORDER TAYLOR REMAINDER: |⟨f⟩_β − ⟨f⟩₀ + β·Cov₀(f,S)| ≤ 4CB²β²·exp(βB) for βB ≤ 1, closing the β=0 analysis package. TWENTIETH STONE — the FLUCTUATION–RESPONSE IDENTITY in finite volume: d/dβ⟨f⟩_β = −Cov_β(f, S) at every β₀ ≥ 0, with gibbsCovariance as a first-class definition — the response of any bounded observable to the coupling is exactly its correlation with the action, at any temperature. TWENTY-FIRST STONE — the SECOND-RESPONSE / THIRD-CUMULANT identity: d/dβ[−Cov_β(f,S)] = Cov_β(f,S²) − 2⟨S⟩_β·Cov_β(f,S) at every β₀ ≥ 0, built entirely on top of stone 20 (no iteratedDeriv wrapper claimed). TWENTY-SECOND STONE — FIRST- AND SECOND-RESPONSE IDENTITIES FOR WILSON OBSERVABLES: the pair (20,21) specialized to W = χ(holonomy), with the action bound produced internally; unconditional U(n)/Haar corollaries where only structural conditions (NeZero N, NeZero n, β₀ ≥ 0, closed path) remain. TWENTY-THIRD STONE — the LOG-PARTITION RESPONSE identity: d/dβ log Z_β = −⟨S⟩_β at every β₀ ≥ 0 with pointwise sign ≤ 0 (log partition function, deliberately not called free energy). TWENTY-FOURTH STONE — GIBBS VARIANCE POSITIVITY AND ACTION-FLUCTUATION RESPONSE: Var_β(f) ≥ 0 by the centered-square route, and d/dβ[−⟨S⟩_β] = Var_β(S) ≥ 0 — the first genuine fluctuation inequality (no formal convexity wrapper claimed) (value, continuity, derivative, remainder) by elementary means |
| gemini_* axioms | 0 anywhere |
| Claim on Clay problem | **None.** See README. |

## Rule going forward

New material enters `main` only if: (1) CI green; (2) every new `axiom` is
classified into Box 2 or Box 3 in AXIOM_AUDIT.md at the same commit; (3) no
statement moves boxes without a proof or a retraction note.
