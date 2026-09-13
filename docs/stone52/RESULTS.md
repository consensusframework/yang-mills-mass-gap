# Stone 52 — Local exponential stability under continuous remote polymer-activity damping

Integrated state of `main` at commit
[`6231d5cb3f19d2f36f9719a4a78eab7a68bf8c3c`](https://github.com/consensusframework/yang-mills-mass-gap/commit/6231d5cb3f19d2f36f9719a4a78eab7a68bf8c3c)
(merge of [PR #25](https://github.com/consensusframework/yang-mills-mass-gap/pull/25)).
Stone 52 is integrated on `main` and CI-verified; it is **not** part of any
deposited Zenodo version. The most recent deposited version remains Version 51
(DOI [10.5281/zenodo.22305341](https://doi.org/10.5281/zenodo.22305341), tag
`zenodo-v51`).

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. Nothing here constructs a thermodynamic or continuum limit, a second
> Gibbs measure, a boundary condition or a spatial-mixing theorem, and nothing
> here proves a mass gap or any continuum statement of the Clay Millennium
> Problem.

## 1. The statement

Principal declaration:
`LatticeGauge.abs_gibbsExpectation_sub_activityDampedExpectation_le_local_exp_decay`
([`Phase3/LatticeGauge/ActivityDampingStability.lean`](../../Phase3/LatticeGauge/ActivityDampingStability.lean)).

For `D_s = card (supportLinkFinset s)`:

```
|gibbsExpectation f − activityDampedExpectation f s r θ|
    ≤ (1 − θ) · (2 · Cf) · exp(8 · D_s / 113) · exp(−n / 2).
```

The proof passes through the sharper two-term estimate
(`abs_gibbsExpectation_sub_activityDampedExpectation_le_two_terms`):

```
|gibbsExpectation f − activityDampedExpectation f s r θ|
    ≤ (1 − θ) · Cf · exp(−n / 2) · [exp(8 · D_s / 113) + exp(4 · D_s / 113)],
```

and the capstone follows from `exp(4·D_s/113) ≤ exp(8·D_s/113)` (`D_s ≥ 0`).
The only step that loses a constant is this explicit majorization; nothing is
divided by `(1 − θ)`, so `θ = 1` is covered by the same theorem (bound `0`).

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`. No compactness,
Haar or invariance assumption on `χ` appears in the capstone's signature.

| Hypothesis | Meaning |
|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | bounded measurable function `χ : G → ℝ`; the capstone does not require `χ` to be a representation character |
| `hf : DependsOnlyOn f s` | local observable, depending only on the links of `s` |
| `mf : Measurable f` | measurability |
| `hCf : ∀ U, \|f U\| ≤ Cf` | absolute majorant of `f` |
| `hsep : WalkBarrierSeparated s r n` | walk-barrier separation of the support `s` from the damped region `r` at scale `n` |
| `h0 : 0 ≤ θ`, `h1 : θ ≤ 1` | damping parameter |

`0 ≤ Cf` is **not** an additional hypothesis: it is derived from `hCf` at the
trivial configuration (`nonneg_of_abs_le_of_config`, via `trivialConfig N G`).
By contrast, the Stone 51 capstone keeps `hCf0 : 0 ≤ Cf` explicit; the
asymmetry is an interface convention, not a mathematical difference.

### The damped functional

`activityDampedExpectation μm β χ f s r θ` is the normalized polymer functional
`activityDampedMarkedGas / activityDampedPolymerGas` built from the damped
activity

```
dampedActivity z r θ η = if η touches r then θ · z η else z η
```

(`Phase3/LatticeGauge/ActivityDampedObservableGas.lean`): the activity of every
polymer touching `r` is multiplied by `θ`; activities outside `r` are
unchanged. It is a normalized polymer functional obtained by damping
activities. It is **not** a second Gibbs measure, a modified physical action,
a boundary condition or a switch-off of the interaction, and no such
interpretation is claimed.

## 2. Endpoints

| Endpoint | Declaration | Content |
|---|---|---|
| `θ = 0` | `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_of_damping_zero` | recovers the Stone 51 estimate `\|gibbs f − activityRestrictedExpectation f s r\| ≤ 2·Cf·exp(8·D_s/113)·exp(−n/2)` with the same constant and rate, from the Stone 52 capstone and `activityDampedExpectation_zero` (52-A). The Stone 51 capstone module is **not** imported: the comparison is documentary, not a formal dependency. |
| `θ = 1` | `gibbsExpectation_sub_activityDampedExpectation_one_eq_zero` | exact identity with the Gibbs expectation, under the hypotheses of the published representation only (no smallness, no separation). `capstone_bound_one` is the algebra of the right-hand side at `θ = 1`; the effective application of the capstone at `θ = 1` was tested in the 52-E audit. |
| `r = ∅` | `gibbsExpectation_sub_activityDampedExpectation_empty_region_eq_zero` | exact identity for **every real θ** (representation hypotheses only). There is no separate declaration for "the bound at `r = ∅`"; the bound is an immediate consequence of the identity for `θ ≤ 1`. |

The estimate itself is stated for `0 ≤ θ ≤ 1` only; nothing is extrapolated
outside that interval.

## 3. What is proved and what is not

Proved: a bound on the deviation of the damped functional from the Gibbs
expectation, for one damping parameter `θ`, at walk-barrier separation `n`,
with a prefactor depending on the local support size `D_s` and no separate
factor of the ambient volume or of `card r`.

Not proved, and not claimed: monotonicity of the actual deviation in `θ`;
continuity in `θ` as a separate theorem; any estimate proportional to
`|θ − θ′|` between two damping parameters; uniformity when the observable
supports themselves grow; thermodynamic limit; continuum limit; mass gap. The
absence of a volume factor in the prefactor is a finite-lattice fact and does
not construct an infinite-volume object.

## 4. The chain of gates

Six new modules (3,319 Lean lines; 158 top-level declaration lines, a
textual count by `grep -cE` of lines beginning with `theorem`, `lemma`,
`def`, `abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or
`class` at commit `6231d5c…`, not an exhaustive inventory of the
declarations elaborated by Lean; 76 in-file `#print axioms` certificates),
each a leaf over the previous one; no pre-existing module was modified at
any gate.

| Gate | Module | Lines / decls / certs | Content |
|---|---|---|---|
| 52-A0 | `ActivityDampingBudgets.lean` | 690 / 35 / 11 | Damped powers `0 ≤ θ^j ≤ 1`, `1 − θ^j ≤ j(1−θ)`; mass absorption `x ≤ (8/(3e))·e^{3x/8}` with `8/(3e) ≤ 1`; tilted Kotecký–Preiss at `λ = 7/8`; first moments of connectors and bridge cores; core budget `(7/8, 1)`, with `(1/2, 3)` kept from Stone 51 |
| 52-A (C1) | `ActivityDampedObservableGas.lean` | 926 / 66 / 19 | `dampedActivity`, touch counts of families and tuples (multiplicities kept), `∏ z_θ = θ^{touchCount}·∏ z`, damped polymer gas / marked gas / normalized functional `activityDampedExpectation`, true normalization, positivity of the denominator from transported KP, endpoints `θ = 0` (Stone 51 functional) and `θ = 1` (Gibbs), coefficient bridges `kpSignedUnrootedCoeff_dampedActivity`, `kpConnectorUnrootedCoeff_dampedActivity`, empty-region and concatenation interfaces |
| 52-B | `ActivityDampingLedger.lean` | 435 / 16 / 12 | Damped core exponent `E_T(θ)`, damped gas ratio as an exponential, and the exact two-column ledger (below) with its endpoints |
| 52-C | `ActivityDampingConnector.lean` | 568 / 19 / 13 | Damped connector coefficient and series, coefficient-level inclusion–exclusion, domination `\|c_k\| ≤ (1−θ)·k·A_k`, summability, orientation `E_T(θ) − E_T(1) = C_{T,r}(θ)`, factorization `e^{E_T(1)} − e^{E_T(θ)} = e^{E_T(1)}·(1 − e^{C})`, eroded bound with natural truncated subtraction `n − m_T`, exponential control `\|1 − e^{C}\| ≤ d·e^{2q′}` with `d ≤ 1` |
| 52-D | `ActivityDampingColumnBounds.lean` | 484 / 15 / 14 | The two columns estimated separately with `(1 − θ)` in front: connector column `≤ (1−θ)·Cf·e^{−n/2}·e^{8·D_s/113}` (budget `(1/2, 3)`), bridge column `≤ (1−θ)·Cf·e^{−n/2}·e^{4·D_s/113}` (budget `(7/8, 1)`); sums of absolute values and absolute values of sums; the estimated sums are literally the 52-B columns |
| 52-E | `ActivityDampingStability.lean` | 216 / 7 / 7 | Ledger + triangle inequality + the two column bounds: the two-term estimate and the capstone; endpoints |

The exact 52-B ledger (`gibbsExpectation_sub_activityDampedExpectation_eq_two_column_ledger`),
with the bridge column entering with a **plus** sign:

```
gibbsExpectation f − activityDampedExpectation f s r θ
  = Σ_{T touching s}  θ^{touchCount r T} · W_T · (e^{E_T(1)} − e^{E_T(θ)})
  + Σ_{T bridge core} (1 − θ^{touchCount r T}) · W_T · e^{E_T(1)}.
```

Constants: `2/113` per link (Stone 50 envelope), exponential rate `1/2`,
`β ≤ 1/40000`. The factor `8/(3e)` of 52-A0 appears in the auxiliary
absorption and first-moment statements of that gate; it is absorbed there
(`8/(3e) ≤ 1`) and does not appear in the final column bounds of 52-D or in
the 52-E capstone. The budget `(7/8, 3)` is inadmissible and is not used.

## 5. Kernel certificates and CI

- The seven declarations of `ActivityDampingStability.lean` carry in-file
  `#print axioms` certificates; each reports `[propext, Classical.choice,
  Quot.sound]`. These certificates are emitted during `lake build` and are
  visible in the CI logs of runs 477 and 478 (below); the dedicated CI step
  `Kernel certificates` still checks the three capstones of Versions 49, 50
  and 51 and was not extended by Stone 52.
- Every gate: one commit over the then-current `main`, delivered as a
  verifiable git bundle, audited on a separate pinned bench (see
  [`docs/audits/stone52/`](../audits/stone52/README.md)), published by push of
  the audited bundle, a non-draft pull request, `build-phase3` green on the
  pull-request head, a normal merge commit (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit.

| Gate | Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|---|
| 52-A0 | `76e10feb40a064e5813828fc1feae7c0949d3ec6` | [#20](https://github.com/consensusframework/yang-mills-mass-gap/pull/20) | [467](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34111613859) | `d62f50d25153d43ca1e8e3aed717614c0973e5f1` | [468](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34112690184) |
| 52-A (C1) | `4f4044333193fb734a7103ea01f6c472ed464563` | [#21](https://github.com/consensusframework/yang-mills-mass-gap/pull/21) | [469](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34140152550) | `d4fb2937864b787dea996f6d474939cb40024d8b` | [470](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34140983255) |
| 52-B | `322f29c331e13f2e257da15c7f6e17fc1efe0e19` | [#22](https://github.com/consensusframework/yang-mills-mass-gap/pull/22) | [471](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34593924081) | `eb3051fdd4a888eaf7bf29ebf33f597f0e81ddb5` | [472](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34595543271) |
| 52-C | `6502ca9f51754d7e084106e8fa1022ca0fa2427a` | [#23](https://github.com/consensusframework/yang-mills-mass-gap/pull/23) | [473](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34620460290) | `2708eb9f33fe1cfc3a439c3f0a97217ce13ebd2d` | [474](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34621786455) |
| 52-D | `6168e2336495a968e4c74005b61d7e33e5f1cb76` | [#24](https://github.com/consensusframework/yang-mills-mass-gap/pull/24) | [475](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34649505620) | `2a391941847e7e1eb0ccfc690462beb62c74f818` | [476](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34650581470) |
| 52-E | `8b638c94a7db54eb8b5780f962e0e79d522db6ad` | [#25](https://github.com/consensusframework/yang-mills-mass-gap/pull/25) | [477](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34718082173) | `6231d5cb3f19d2f36f9719a4a78eab7a68bf8c3c` | [478](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/34719046299) |

Custody note for 52-E: the pull-request run 477 is associated with the head
`8b638c9…`, but its checkout was the provisional merge commit
`0f29e1fa0423b45f923e3418690a185bcd681c14` ("Merge 8b638c9… into
2a39194…"); the job log records `HEAD is now at 0f29e1f` (checked by the
publishing instance from the run log). That the tree and the parents of this
provisional merge coincide with those of the definitive merge `6231d5c…` was
checked directly by the coordinating GPT instance (GPT Astra) during the
review of the 52-E publication; the provisional ref is no longer served by
GitHub and was not re-checked here. Run 478 compiled `6231d5c…` itself. The
merge commit `6231d5c…` has tree `343a69ded589e607f3ad2863047ef049a8763c4f`,
which is also the tree of the candidate `8b638c9…`. The candidate commit
carries an SSH signature that GitHub reports as `unknown_key`; the merge
commit's signature is verified by GitHub.

Toolchain at `6231d5c…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`); the library has 111 modules and 33,381 Lean source
lines; the full clean CI build reports 114 inherited warnings (unchanged since
Version 50) and none in the six new modules.

## 6. Relation to Stone 51

Stone 51 suppresses the activities of every polymer touching `r` (hard
restriction, `θ = 0`). Stone 52 replaces the hard restriction by a continuous
damping `θ ∈ [0, 1]` and proves that the deviation from Gibbs is controlled by
the same constant, multiplied by `(1 − θ)`. At `θ = 0` the Stone 51 estimate
is recovered with the same constant `2·Cf·exp(8·D_s/113)·exp(−n/2)`; the
derivation of Stone 52 does not use the Stone 51 capstone.

## 7. Audits

Seven stage audits (52-A0 QA1, 52-A QA1, 52-A/C1 QA2, 52-B QA1, 52-C QA1,
52-D QA1, 52-E QA1), all by a separate instance of Claude Fable 5.1 on its own
pinned bench, with their evidence packages and reports preserved byte for
byte in [`docs/audits/stone52/`](../audits/stone52/README.md). The verdicts are
literal: `PASS WITH RESERVATIONS` (A0, A), `PASS — C1 READY FOR PUBLICATION`
(A/C1 QA2), `PASS` (B, C, D, E). These are audits by an AI model of the same
family as the implementer, with declared prior exposure from 52-B on and
explicitly non-blind for 52-E; they are not human peer review.
