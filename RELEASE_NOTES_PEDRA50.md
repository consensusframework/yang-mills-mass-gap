# Release v50 — Finite-Volume Exponential Covariance Decay (Exponential Clustering at Small β)

**Frozen scientific sentence (the release ruler):**

> *Stone 50 establishes exponential clustering of the covariance in finite
> volume, in the regime **0 ≤ β ≤ 1/40000**, for bounded observables with
> disjoint finite link supports separated by walks:*
> **|Cov_β(f,g)| ≤ 3 · Cf · Cg · exp(6D/113) · exp(−n/2)**,
> *where `D` is the sum of the local cardinalities of `supportLinkFinset s`
> and `supportLinkFinset s'`, and `n` is the `WalkBarrierSeparated`
> separation parameter.*

Principal declaration: `LatticeGauge.abs_gibbsCovariance_le_local_exp_decay`.

Explicitly: finite volume; small coupling (β ≤ 1/40000); exponential rate 1/2
in the separation parameter; the prefactor depends only on the local supports
of the two observables, **not** on the ambient volume; no external
nonvanishing hypothesis on `Z` anywhere in the chain — positivity and
nonvanishing of the partition function and of the restricted gases are
**outputs** of the cluster expansion.

This is a finite-volume lattice result under small coupling. It is NOT a
thermodynamic-limit statement, NOT an infinite-volume result, NOT a
continuum result, NOT a Yang–Mills mass-gap claim, and NOT a solution of the
Clay Millennium Problem.

## The machine-checked chain (stone 50, complete)

27 scientific gates (A0–A19c) plus 3 hygiene/packaging passes, all judged by
CI on the pinned toolchain. The chain, in arcs:

| Arc | Content | New modules |
|---|---|---|
| A0–A2 | Atomic cancellation unit; marked numerator, touch/remote split, collective machine E₀[f·Πall] = E₀[f·Πtouch]·Π_remote E₀[B_C]; marked gas and exact normalization Z[f] = Σ_Γ M_f(Touch)·Π_remote w | ObservableBlockFactorization, ObservableMayer, ObservableGas |
| A3–A5 | Connected cancellation ⟨f⟩ = Σ_T core(T)·exp(C_restricted − C_full); localization C_rest − C_full = −Σ' forbidden connected clusters; the connector cluster (inclusion–exclusion + cross-ratio of gases = exp(connectorSum)) — all metric-free | RestrictedGas, ForbiddenClusters, ConnectorClusters |
| A6–A8 | Geometry: connector ⟹ geometric bridge ⟹ barrier separation; walk separation ⟹ additive mass; absolute unrooting \|connector\| ≤ KP envelope | BarrierBridge, WalkSeparation, KPAbsoluteUnrooted |
| A9–A12 | Marked root (filtered positive connector, marked series); abstract mass tilt; concrete tilted KP at λ = 1/2 for β ≤ 1/40000; local prefactor Σ'\|connector\| ≤ e^{−n/2}·min(\|barrier_P\|,\|barrier_Q\|)·(2/113) | KPBarrierConnectorPositive, KPBarrierMarkedRoot, KPBarrierMarkedSeries, KPConnectorMassTilt, KPConnectorTiltSpecialization, KPConnectorEnvelopeLocalization |
| A13–A16 | Doubly marked atom Cov = (Z[fg]·Z − Z[f]·Z[g])/Z²; bridge-witness mass dichotomy; bridge-core toll; restricted-gas localization with positivity as output | CovarianceMayerWiring, CovarianceBridgeMass, CovarianceBridgeCoreTilt, CovarianceRestrictedGasLocalization |
| A17–A18e | Local core budget (generic lam + κ·8/113 ≤ 1); bridge-free dictionary (good pairs); bad-pair toll (joint mass); exact numerator ledger; connector normalization (bracket = R·R'·(e^C − 1) by direct KP positivity, no \|C\| ≤ 1 hypothesis); exact barrier erosion n − (mass T + mass T') | CovarianceCoreLocalBudget, CovarianceBridgeFreePairing, CovarianceBadPairMass, CovarianceNumeratorLedger, CovarianceConnectorLedger, CovarianceBarrierErosion |
| A19a–A19c | Eroded connector control (global \|e^x−1\| ≤ \|x\|·e^{\|x\|}); normalized columns N_f = markedCoreGasTerm/Z with the three column bounds; **capstone**: exact ledger socket + triangular assembly + e^{3Da}+2e^{2Da} ≤ 3e^{3Da} ⟹ \|Cov_β(f,g)\| ≤ 3·Cf·Cg·e^{6D/113}·e^{−n/2} | CovarianceConnectorControl, CovarianceNormalizedColumns, CovarianceDecay |

Architectural notes recorded in the sources: nonvanishing of `Z` and of the
restricted gases is an OUTPUT of the expansion (exponential representation),
never a hypothesis; the connector bracket is normalized by direct
Kotecký–Preiss positivity with no global `field_simp`; the good column pays
the κ = 2 budget (1/2 + 16/113 = 145/226 < 1), the bridge and bad columns pay
κ = 1; barrier erosion `n − (mass T + mass T')` is repurchased by the half
tilt; and `|e^x − 1| ≤ |x|·e^{|x|}` is used globally, with no auxiliary
smallness hypothesis on the connector sum.

## Technical census

- 28 new Lean modules; 7,536 inserted Lean source lines.
- No preexisting Lean source from v49 modified.
- 27 scientific gates + 3 passes.
- Lean 4 / Mathlib pinned at `v4.15.0`.
- 0 scientific `sorry`; no project-local scientific axiom.
- Capstone axiom dependencies exactly: `propext`, `Classical.choice`,
  `Quot.sound` (see AXIOM_AUDIT.md, Pedra 50 section).

Known hygiene debt (deliberately untouched during frozen-candidate
integration): 114 build warnings in the full Phase 3 build — 87 inherited
from the v49 base, 27 across 12 new Stone 50 modules; `CovarianceDecay.lean`
itself has zero warnings. These are hygiene debt, not elaboration or kernel
failures.

## Verification and review — evidence taxonomy

The categories below are deliberately kept distinct:

1. **Original CI on the frozen candidate:** GitHub Actions run `33195194820`
   (`success`, `run_attempt 1`) on SHA
   `ced893efe2a25995d1961e527842f68489f4fc2f`, all three phases green.
2. **Integration CI on the release PR:** run `33253642393` (`success`,
   `run_attempt 1`), three phases green, on the merge head
   `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea`.
3. **Two artifact-verified local reproductions** of the frozen candidate:
   Manus (Linux) and GPT-5.6/Codex (Windows) — same SHA, Lean 4.15.0, same
   Mathlib revision (`9837ca9d65d9de6fad1ef4381750ca688774e608`), 100 local
   modules built, the five capstone certificates showing only
   `[propext, Classical.choice, Quot.sound]`; custody packages and hashes
   cross-checked (the Manus and GPT manifests are byte-identical).
4. **One additional local reproduction reported:** Grok (Linux) — same SHA
   and toolchain, build exit code 0, same certificates and warning count;
   counted as corroboration, not as an artifact-verified reproduction, since
   the raw logs were not attached to the coordinator review.
5. **Separate adversarial mathematical audit:** Kimi (Moonshot AI) —
   line-by-line reading of the critical covariance path; APPROVED in the
   audited scope; no mathematical error demonstrated. This is a mathematical
   audit, **not** a build reproduction.

The Lean kernel and the reproducible builds remain the formal judges; model
reviews are adversarial/reproducibility review, not the verification itself.

## Provenance

- Mathematics frozen at branch `pedra50-sol`, commit
  `ced893efe2a25995d1961e527842f68489f4fc2f` (the object all audits and
  reproductions examined). This release integrates that object plus
  documentation and CI-trigger restoration only.
- Integration path: branch `release-v50`, merge commit
  `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea` (first parent: the audited
  candidate; second parent: post-v49 `main` documentation), Draft PR #12.
- Roles: Arquitetura — GPT-5.6 "Sol" (OpenAI); Execução — Claude Fable 5
  (Anthropic); Coordenação — Jucelha Carvalho; Juiz — GitHub Actions CI
  (Lean 4 + Mathlib v4.15.0); auditoria adversarial — Kimi (Moonshot AI);
  reproduções — Manus (Linux), GPT-5.6/Codex (Windows), Grok (Linux,
  reported).
- The project is human-led and developed through a multi-model AI
  collaboration; model output is treated as untrusted until checked by Lean
  and CI. Commits after gate A16 carry the declared coauthorship trailer
  `Co-authored-by: Claude <noreply@anthropic.com>`; earlier frozen commits
  are preserved without retroactive rewriting.
- Concept DOI (all versions): 10.5281/zenodo.17397622.
- Version DOI for v50: **to be assigned at Zenodo publication** (procedure:
  new version on the concept record → reserve DOI → upload the frozen
  package → publish → register the DOI here and in README). No DOI is
  invented in advance. Frozen tag: to be created only after integration and
  a further explicit authorization.
