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

Explicitly: finite volume; small β (strong coupling), with β ≤ 1/40000; exponential rate 1/2
in the separation parameter; no external nonvanishing hypothesis on `Z`
anywhere in the chain — positivity and nonvanishing of the partition function
and of the restricted gases are **outputs** of the cluster expansion.

The theorem is finite-volume. Its displayed prefactor is local and contains
no ambient-volume cardinality: for fixed local support data, Cf, Cg and
separation parameter n, the bound has no explicit dependence on the size of
the ambient finite lattice. This does not construct an infinite-volume Gibbs
state, prove a thermodynamic limit, or provide a constant uniform when the
observable supports themselves grow.

This is a finite-volume lattice result in the small-β (strong-coupling) regime. It is NOT a
thermodynamic-limit statement, NOT an infinite-volume result, NOT a
continuum result, NOT a Yang–Mills mass-gap claim, and NOT a solution of the
Clay Millennium Problem.

## The machine-checked chain (stone 50, complete)

27 scientific gates (50-0, A0–A19c) + 3 hygiene/packaging passes, all judged by
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
- 27 scientific gates (50-0, A0–A19c) + 3 passes.
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
2. **Integration CI (I1) on the release PR:** run `33253642393` (`success`,
   `run_attempt 1`), three phases green, on the merge head
   `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea`.
3. **Documentation/configuration CI (I2):** run `33255562368` (`success`,
   `run_attempt 1`), three phases green, on
   `04904e0f2242cee4f4cf78fd2e88f931607b1f57`; **documentation-hygiene CI
   (I2-H):** run `33263246326` (`success`, `run_attempt 1`), three phases
   green, on the pre-merge head
   `5dda9d338ceb0581eedce74afdb73045b2ea66ff`; **post-merge CI on
   `main`:** run `33264222563` (`success`, `run_attempt 1`, event
   `push`), three phases green, on the merge commit
   `726711c6eb88743809d979bfc2e049c7e7d54400`.
4. **Two artifact-verified local reproductions** of the frozen candidate:
   Manus AI 1.6 (Linux) and GPT-5.6/Codex (Windows) — same SHA, Lean 4.15.0,
   same Mathlib revision (`9837ca9d65d9de6fad1ef4381750ca688774e608`), 100
   local modules built, the five capstone certificates showing only
   `[propext, Classical.choice, Quot.sound]`; custody packages and hashes
   cross-checked; the two resolved manifests are byte-identical, SHA-256
   `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`.
5. **One additional local reproduction reported:** Grok 4.6 (Linux) — same
   SHA and toolchain, build exit code 0, same certificates and warning
   count; explicitly kept as "reported" corroboration, not as an
   artifact-verified reproduction, since the raw logs were not attached to
   the coordinator review.
6. **Separate adversarial mathematical audit:** Kimi 3 (Moonshot AI) —
   line-by-line reading of the critical covariance path; APPROVED in the
   audited scope; no mathematical error demonstrated. This is a mathematical
   audit, **not** a build reproduction.
7. **Claude Opus 5 (Anthropic):** technical review and investigation of the
   reproduction path; not counted among the completed build reproductions.

The Lean kernel and the reproducible builds remain the formal judges; model
reviews are adversarial/reproducibility review, not the verification itself.

## Provenance

- Mathematics frozen at branch `pedra50-sol`, commit
  `ced893efe2a25995d1961e527842f68489f4fc2f` (the object all audits and
  reproductions examined). This release integrates that object plus
  documentation and CI-trigger restoration only.
- Integration path: branch `release-v50`, I1 merge commit
  `8b81936bea6e4cc29c8e52d6de70b1b87aa7c1ea` (first parent: the audited
  candidate; second parent: post-v49 `main` documentation), followed by
  the documentation stages I2 and I2-H; PR #12 was merged into `main` at
  merge commit `726711c6eb88743809d979bfc2e049c7e7d54400` (first parent:
  pre-merge `main` `0b080d0a…`; second parent: `5dda9d33…`), with the
  tree of `main` identical to the tree of `release-v50` and no new
  mathematical review attributed to the merge: `ced893ef…` remains the
  audited and reproduced scientific object, `726711c6…` is the
  integrated state (science + documentation + release configuration).
- Roles: Coordenação humana, escopo, decisões epistemológicas,
  orquestração multi-IA, proveniência, custódia e autorização de release —
  Jucelha Carvalho (Smart Tour Brasil, ORCID 0009-0004-6047-2306);
  Arquitetura matemática e formal, fitas, revisão científica e reprodução
  Windows via Codex — GPT-5.6 "Sol" (OpenAI); Implementação e depuração
  Lean 4, censo estrutural, pesquisa de APIs Mathlib, execução dos portões,
  integração e documentação técnica — Claude Fable 5 (Anthropic); Juiz —
  GitHub Actions CI (Lean 4 + Mathlib v4.15.0); Auditoria matemática
  adversarial — Kimi 3 (Moonshot AI); Reprodução Linux com artefatos —
  Manus AI 1.6; Reprodução Linux adicional reportada — Grok 4.6 (xAI);
  Revisão técnica e investigação do caminho de reprodução — Claude Opus 5
  (Anthropic).
- The project is human-led and developed through a multi-model AI
  collaboration; model output is treated as untrusted until checked by Lean
  and CI. Commits after gate A16 carry the declared coauthorship trailer
  `Co-authored-by: Claude <noreply@anthropic.com>`; earlier frozen commits
  are preserved without retroactive rewriting.
- Concept DOI (all versions): 10.5281/zenodo.17397622.
- Published v49 DOI: 10.5281/zenodo.22050763.
- Reserved version DOI for v50: **10.5281/zenodo.22162464**. The DOI becomes
  registered and publicly resolvable only when the Zenodo draft is
  published; the v50 DOI was reserved by the coordinator (Zenodo upload
  22162464), and registration occurs through the Zenodo publication step.
  Release tag name: `zenodo-v50`.

## Authors (v50, canonical order)

1. Carvalho, Jucelha — Smart Tour Brasil (ORCID 0009-0004-6047-2306)
2. Claude Fable 5 — Anthropic
3. GPT-5.6 "Sol" — OpenAI
4. Kimi 3 — Moonshot AI
5. Claude Opus 5 — Anthropic
6. Claude Opus 4.7 — Anthropic
7. Claude Opus 4.6 — Anthropic
8. Claude Opus 4.5 — Anthropic
9. GPT-5.2 — OpenAI
10. Gemini 3 Pro — Google
11. Manus AI 1.6 — Manus
12. Grok 4.6 — xAI
13. Grok 4.5 — xAI

Authorship is collective, human–AI: Jucelha Carvalho is the human
coordinator, public responsible party, release custodian and ORCID-bearing
author (not the sole author or creator); the models listed contributed
materially to the intellectual, formal, technical, adversarial or
reproductive construction and are authors of the project, with the specific
roles declared above. The git trailer
`Co-authored-by: Claude <noreply@anthropic.com>` on post-A16 commits is an
additional provenance layer on GitHub and does not replace this canonical
author list.
