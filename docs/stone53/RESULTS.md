# Stone 53 — Lipschitz stability of the damped functional in the damping parameter

Integrated state of `main` at commit
[`a7ae1c0cb81aa8829c056482afc74f9629485fd6`](https://github.com/consensusframework/yang-mills-mass-gap/commit/a7ae1c0cb81aa8829c056482afc74f9629485fd6)
(merge of [PR #28](https://github.com/consensusframework/yang-mills-mass-gap/pull/28);
root tree `0e156fc6c53b5c6c27d71f1e3c589ea63be45f4a`, `Phase3/` tree
`99758dfc339edf0e412133ca7f5826ecab45b56d`). Stone 53 is integrated on `main`
and CI-verified; it is **not** part of any deposited Zenodo version and has no
DOI of its own. The most recent deposited version is Version 52 (DOI
[10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731), tag
`zenodo-v52` → commit `f4015c5c…`, which does not contain Stone 53).

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. Nothing here constructs a thermodynamic or continuum limit, a second
> Gibbs measure, a boundary condition or a spatial-mixing theorem; nothing
> here asserts monotonicity of the damped functional in θ or a derivative in
> θ; and nothing here proves a mass gap or any continuum statement of the
> Clay Millennium Problem.

## 1. The statement

Principal declaration:
`LatticeGauge.abs_activityDampedExpectation_sub_activityDampedExpectation_le_local_exp_decay`
([`Phase3/LatticeGauge/ActivityDampingLipschitz.lean`](../../Phase3/LatticeGauge/ActivityDampingLipschitz.lean)).

Write `F(θ) = activityDampedExpectation μm β χ f s r θ` (the normalized polymer
functional of Stone 52, in which the activity of every polymer touching the
region `r` is multiplied by `θ`) and `D_s = card (supportLinkFinset s)`. For
`θ, θ′ ∈ [0, 1]`:

```
|F(θ) − F(θ′)|
    ≤ |θ − θ′| · Cf · exp(−n / 2) · [exp(8 · D_s / 113) + exp(4 · D_s / 113)]
    ≤ |θ − θ′| · (2 · Cf) · exp(8 · D_s / 113) · exp(−n / 2).
```

The first line is the two-term estimate
(`abs_activityDampedExpectation_sub_activityDampedExpectation_le_two_terms`);
the capstone follows from `exp(4·D_s/113) ≤ exp(8·D_s/113)` (`D_s ≥ 0`). The
Lipschitz constant `2·Cf·exp(8·D_s/113)·exp(−n/2)` is the constant of the
Stone 52 capstone, now uniform in `θ`, `θ′` and `r`. Nothing is divided by
`|θ − θ′|` (nor by `1 − θ`): `θ = θ′` is covered by the same theorem, with
bound `0`.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`.

| Hypothesis | Meaning | ledger | column bounds, two-term form, capstone | identification with Gibbs (θ′ = 1) |
|---|---|---|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 | yes | yes | (representation hypotheses of 52-A) |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | bounded measurable function `χ : G → ℝ` | yes | yes | yes |
| `h0 h1 h0' h1' : 0 ≤ θ ≤ 1, 0 ≤ θ′ ≤ 1` | damping parameters | yes | yes | (`θ′ = 1`) |
| `mf : Measurable f` | measurability of the observable | no | yes | yes |
| `hCf : ∀ U, \|f U\| ≤ Cf` | absolute majorant of `f` | no | yes | yes |
| `hsep : WalkBarrierSeparated s r n` | walk-barrier separation of the set `s` from the damped region `r` at scale `n` | no | yes | — |
| `hf : DependsOnlyOn f s` | `f` depends only on the links of `s` | no | **no** | **yes** |

Three levels are to be distinguished:

- the **exact two-parameter ledger** (§4) is an identity between finite sums
  and needs neither `Measurable f`, nor a majorant, nor separation, nor
  `DependsOnlyOn f s`;
- the **column bounds, the two-term estimate and the capstone** need
  `Measurable f`, the majorant `Cf` and `WalkBarrierSeparated s r n`, and do
  **not** need `DependsOnlyOn f s`;
- the **identification of `F(1)` with the Gibbs expectation** (52-A,
  `activityDampedExpectation_one`) needs `DependsOnlyOn f s`; it is used only
  in the endpoint `θ′ = 1` below.

Without `DependsOnlyOn f s`, `s` is a parameter of the functional
`activityDampedExpectation μm β χ f s r θ` (the set whose touching cores index
the polymer representation), and the theorem says nothing about whether `s`
is a support of `f`. `0 ≤ Cf` is **derived** from `hCf` at the trivial
configuration (`nonneg_of_abs_le_of_config`, the lemma of 52-E), not assumed;
this is the only declaration of `ActivityDampingStability.lean` consumed by
the Stone 53 proofs (the Stone 52 capstone itself is not used).

## 2. Endpoints

| Endpoint | Declaration | Content |
|---|---|---|
| `θ = θ′` | `activityDampedExpectation_sub_self` | the difference is `0`, with no hypotheses (`sub_self`); `lipschitz_bound_self` is the algebra of the right-hand side (the bound is `0` at `θ = θ′`). The effective application of the capstone at `θ = θ′` is exercised in the auditor's test U4a (`docs/audits/stone53/`), not by these two declarations. |
| `θ′ = 1` | `abs_activityDampedExpectation_sub_gibbsExpectation_le_of_damping_one`, `abs_gibbsExpectation_sub_activityDampedExpectation_le_of_lipschitz` | with `DependsOnlyOn f s`, `F(1)` is the Gibbs expectation (52-A) and `\|θ − 1\| = 1 − θ`: the Stone 52 capstone is recovered with the same constant. The second declaration has literally the statement of the Stone 52 capstone; that two proofs of one statement are definitionally equal (`rfl`, proof irrelevance) certifies nothing about their derivations. |
| `θ′ = 0` | `abs_activityDampedExpectation_sub_activityRestrictedExpectation_le` | `\|F(θ) − activityRestrictedExpectation f s r\| ≤ θ·2·Cf·exp(8·D_s/113)·exp(−n/2)`, the distance to the Stone 51 functional with the factor `θ` (`activityDampedExpectation_zero`, 52-A); no `DependsOnlyOn f s`. |
| `r = ∅` | `activityDampedExpectation_sub_activityDampedExpectation_empty_region`, `two_column_lipschitz_ledger_empty_region` | `F(θ) = F(θ′)` exactly, for **every real** `θ, θ′` (both are the undamped ratio, 52-A); both ledger columns vanish termwise. |

The estimate itself is stated for `θ, θ′ ∈ [0, 1]` only; nothing is
extrapolated outside that interval. (The scalar step `|θ^j − θ′^j| ≤ j·|θ − θ′|`
is proved from Mathlib's `abs_pow_sub_pow_le`, which gives
`|a^j − b^j| ≤ |a − b|·j·max(|a|, |b|)^(j−1)` without any hypothesis on `a`,
`b`; imposing `max(|a|, |b|) ≤ 1` yields the linear bound, on `[−1, 1]` as
well as on `[0, 1]`. This does not enlarge the domain of the capstone.)

## 3. What is proved and what is not

Proved: a Lipschitz estimate in the damping parameter for the damped
functional, at fixed `β`, `χ`, `f`, `s`, `r`, `n`, with the Stone 52 constant
and no separate factor of the ambient volume or of `card r`.

Not proved, and not claimed: monotonicity of `F` in `θ`; differentiability in
`θ`; any statement about a second Gibbs measure, a modified action or a
boundary condition; uniformity when the observable supports themselves grow;
thermodynamic limit; continuum limit; mass gap.

## 4. The two modules

Two new modules (1,204 Lean lines; 29 top-level declaration lines, a textual
count by `grep -cE` of lines beginning with `theorem`, `lemma`, `def`,
`abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or `class`
followed by a space, at commit `abad1667…` — here all 29 are `theorem`; 29
in-file `#print axioms` certificates), each a leaf over the integrated Stone
52; no pre-existing module was modified; the only change outside the new
files is the two new globs in `Phase3/lakefile.toml` (111 → 113 modules).

| Gate | Module | Lines / decls / certs | Content |
|---|---|---|---|
| 53-A | `ActivityDampingLipschitzInfrastructure.lean` | 555 / 11 / 11 | `\|θ^j − θ′^j\| ≤ j·\|θ − θ′\|` on `[0,1]`; `\|θ − θ′\| ≤ 1`; termwise monotonicity of `kpForbiddenRootEnvelope`; **the damped exponent pays only the local barrier**, `\|E_T(θ)\| ≤ b_T·(2/113)` (the generic forbidden-cluster chain of Stone 50 — `tsum_restricted_sub_full`, `tsum_abs_kpForbiddenUnrootedCoeff_le`, `kpForbiddenRootEnvelope_le_barrierLinkCount` — transported by the damped Kotecký–Preiss hypothesis of 52-A), hence `\|W_T·e^{E_T(θ)}\| ≤ Cf·e^{b_T·(2/113)}·Π M` (κ = 1); two-parameter domination of the damped connector coefficients `\|c_k(θ) − c_k(θ′)\| ≤ \|θ − θ′\|·k·A_k`; the eroded bound `\|C_θ − C_θ′\| ≤ \|θ − θ′\|·e^{−((n − m_T : ℕ))/2}·q′` with the natural truncated subtraction (`m_T > n` gives the factor `1`, never an explosion); `E_T(θ) − E_T(θ′) = C_θ − C_θ′`; the exponential control `\|e^{E_T(θ)} − e^{E_T(θ′)}\| ≤ \|θ − θ′\|·e^{−n/2}·e^{m_T/2 + 3·b_T·(2/113)}` (κ = 3, with `d = \|θ − θ′\|·e^{−((n − m_T:ℕ))/2} ≤ 1` paid explicitly); the damped bridge first moment `card T·\|W_T·e^{E_T(θ)}\| ≤ e^{−n/2}·Cf·e^{b_T·(2/113)}·Π massTilt(7/8)` (κ = 1, tilt 1/2 + 3/8 = 7/8, `n ≤ m_T` from the bridge geometry) |
| 53-B | `ActivityDampingLipschitz.lean` | 649 / 18 / 18 | the exact two-parameter ledger (below); the connector column bounded with `\|θ − θ′\|` in front through the budget `(1/2, 3)` (`sum_halfTilt_three_le`, prefactor `exp(8·D_s/113)`); the bridge column through `\|θ^t − θ′^t\| ≤ card T·\|θ − θ′\|`, the damped first moment and the budget `(7/8, 1)` (`sum_sevenEighthsTilt_one_le`, prefactor `exp(4·D_s/113)`); the two-term estimate; the capstone; the endpoints of §2 |

The exact ledger
(`activityDampedExpectation_sub_eq_two_column_lipschitz_ledger`), a direct
identity between the two damped functionals — no detour through the Gibbs
expectation, which would only give a factor `2 − θ − θ′` — with the bridge
column entering with a **plus** sign and the weight `θ′^t` on the connector
column:

```
F(θ) − F(θ′)
  = Σ_{T touching s}  θ′^{touchCount r T} · W_T · (e^{E_T(θ)} − e^{E_T(θ′)})
  + Σ_{T bridge core} (θ^{touchCount r T} − θ′^{touchCount r T}) · W_T · e^{E_T(θ)}.
```

On region-allowed cores both weights are `1`, so the correction is supported
on the bridge cores exactly. The point that keeps the bridge column inside an
admissible budget is the κ = 1 cost of the damped normalized term: the
alternative route through `N_f·e^{C_θ}` would cost κ = 2 and land on the budget
`(7/8, 2)`, which is inadmissible (`7/8 + 2·8/113 > 1`). Constants: `2/113`
per link (Stone 50 envelope), exponential rate `1/2`, `β ≤ 1/40000`; the factor
`8/(3e)` of 52-A0 stays inside the auxiliary lemma `nat_le_exp_three_eighths`
(absorbed by `8/(3e) ≤ 1`) and appears in no statement.

## 5. Kernel certificates and CI

- Every one of the 29 declarations of the two modules carries an in-file
  `#print axioms` certificate; each reports `[propext, Classical.choice,
  Quot.sound]`. They are emitted during `lake build` and are visible in the CI
  logs of runs 483 and 484; the dedicated CI step `Kernel certificates` still
  checks the three capstones of Versions 49, 50 and 51 and was not extended.
- Hygiene in the two modules: 0 `sorry`, 0 `admit`, 0 scientific `axiom`,
  0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`; 114 inherited build
  warnings (unchanged since Version 50), none in the two new modules; one
  informational message (`ActivityDampingLipschitzInfrastructure.lean:415:4:
  Try this: ring_nf`), identical in the constructor's, the auditor's and the
  CI logs.
- Publication protocol: one candidate commit over the then-current `main`,
  delivered as a verifiable git bundle; the QA1 audit (below) before
  publication; push of the audited commit, a non-draft pull request,
  `build-phase3` green on the pull-request head, a normal merge commit with
  the expected head SHA locked (no squash, no rebase), and `build-phase3`
  green again on `main` at the merge commit.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `abad16674ab9b713c7ef9d0344c8f5cc02b09739` | [#28](https://github.com/consensusframework/yang-mills-mass-gap/pull/28) | [483](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34788347617) (id 34788347617) | `a7ae1c0cb81aa8829c056482afc74f9629485fd6` | [484](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34788866465) (id 34788866465) |

Custody note: the pull-request run 483 is associated with the head
`abad1667…`, but its effective checkout was the provisional merge commit
`03e7bff8eab5551b34fe52f21aa10a2326490f48` ("Merge abad1667… into
f4015c5c…"; the job log records `HEAD is now at 03e7bff`), as for every
pull-request run in this repository. Run 484 compiled the definitive merge
`a7ae1c0c…` itself. The merge commit has parents `f4015c5c…` (the base, the
Version 52 commit) and `abad1667…`, and its tree `0e156fc6…` is the tree of
the candidate; both runs report `Build completed successfully`, 113
`LatticeGauge` modules built, 0 replayed, 0 errors, no `sorryAx`. Full record
of the publication: [`docs/audits/stone53/publication/RELATORIO_53-P.md`](../audits/stone53/publication/RELATORIO_53-P.md).

Toolchain at `a7ae1c0c…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`); the library has 113 modules and 34,585 Lean source
lines.

## 6. Relation to Stone 52

Stone 52 bounds the deviation of `F(θ)` from the Gibbs expectation by
`(1 − θ)·2·Cf·exp(8·D_s/113)·exp(−n/2)`, for one damping parameter and under
`DependsOnlyOn f s`. Stone 53 bounds the deviation between `F(θ)` and `F(θ′)`
by `|θ − θ′|` times the same constant, without `DependsOnlyOn f s`; at
`θ′ = 1` and under `DependsOnlyOn f s` it gives back the Stone 52 capstone.
The derivation of Stone 53 consumes the Stone 52 infrastructure (the damped
functional and its exponential form, the damped connector series and their
summability, the budgets) and the 52-E lemma `nonneg_of_abs_le_of_config`,
but not the Stone 52 capstone.

## 7. Audits and reviews

Recorded, with hashes and provenance, in
[`docs/audits/stone53/`](../audits/stone53/README.md):

- **53-QA1** — independent reproduction by execution of the candidate
  `abad1667…` by a separate instance of Claude Fable 5.1 on its own pinned
  bench (`.lake/build` deleted; 113 modules built, 0 replayed, exit 0; 29/29
  own `#print axioms` certificates standard, 0 `sorryAx`; own tests U0–U5).
  Same model as the constructor, distinct instance and bench; explicitly not
  blind. Verdict `PASS NO ESCOPO`.
- **53-K-ADV** — final adversarial mathematical and code review by Kimi 3
  ("Luan"), a different model family, by reading and without Lean execution;
  not blind. One review with one errata (C1), to be read together, the errata
  prevailing on the four points it corrects. Verdict `PASS NO ESCOPO`,
  maintained.
- **53-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).

These are audits and reviews by AI models; no human peer review of the
mathematics has taken place.
