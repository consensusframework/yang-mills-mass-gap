# Stone 56 — localized stability of the profile-damped functional with a common damping background

Integrated state of `main` at commit
[`ead481456bc8637b2b7c22e867cc49f99f4ab375`](https://github.com/consensusframework/yang-mills-mass-gap/commit/ead481456bc8637b2b7c22e867cc49f99f4ab375)
(merge of [PR #37](https://github.com/consensusframework/yang-mills-mass-gap/pull/37);
parents `445cc76b02550291e6524bb1bf631aac4cc86c61` and
`a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1`; root tree
`171367d9ea2cbf987b00129ace960f6f7d1db97a`, `Phase3/` tree
`f387f26d0519bcddf16514416ee02eb2ca0b2819`). At consolidation time
(2026-09-29) Stone 56 was integrated on `main`, audited and CI-verified, but
not part of any release and without a deposit of its own: the most recent
version is **Version 55** (commit `445cc76b02550291e6524bb1bf631aac4cc86c61`,
tag `zenodo-v55`, GitHub Release published on 2026-09-20, Zenodo record DOI
[10.5281/zenodo.22850085](https://doi.org/10.5281/zenodo.22850085) published
on 2026-09-19, as confirmed by the coordinator and by a capture of the record
page; see §8). Stone 56 is later than the Version 55 snapshot and is not in
that deposit. The DOI 10.5281/zenodo.22949184 is **reserved** for the future
Version 56 record, which is not published at this stage; the snapshot of that
version will be the final documentary merge, not the scientific merge above.

> **Update (2026-10-09).** The state described above is the one observed at
> the consolidation of 2026-09-29 and is kept as written. Since then the
> consolidated state was frozen as **Version 56** at commit
> `95091fdd07398a7b42901829ad61e4e2c26d5aaa` (merge of PR #38, the
> documentary consolidation of this stone), tag `zenodo-v56`, with a GitHub
> Release published by the coordinator on 2026-10-01 and the Zenodo record
> DOI [10.5281/zenodo.22949184](https://doi.org/10.5281/zenodo.22949184)
> published (confirmed by the coordinator; the exact Zenodo date was not
> established by the later documentary session); see §8. Stone 57, integrated
> later at `b66c255c…`, is documented in
> [`docs/stone57/RESULTS.md`](../stone57/RESULTS.md). The mathematics, the
> audits and the counts of this document (117 modules) refer to Stone 56 and
> are unchanged.

> **Scope.** Everything below is a theorem about a finite periodic
> four-dimensional lattice in the small-β (strong-coupling, Wilson convention)
> regime `0 ≤ β ≤ 1/40000`. "Distance" is walk separation in the plaquette
> graph. The program is a formal, machine-checked study of finite-volume
> lattice gauge theory directed at the Yang–Mills existence and mass-gap
> problem: the finite-volume stability results are established; the
> thermodynamic and continuum limits and the mass gap remain open and are
> not claimed here. The object is the normalized polymer functional of Stone
> 55 with the damping region kept everywhere: no new Gibbs measure, boundary
> condition, modified action, per-link profile or physical switch-off is
> constructed or claimed; nothing asserts monotonicity or differentiability in
> the profile, a spatial-mixing theorem, a minimal change region, a Euclidean
> distance or a restriction on the size of the regions; no optimality,
> sharpness or bibliographic priority is claimed for the constant or the route.

## 1. The statement

Principal declaration:
`LatticeGauge.abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_localized`
([`Phase3/LatticeGauge/ActivityProfileDampingLocality.lean`](../../Phase3/LatticeGauge/ActivityProfileDampingLocality.lean)).

Three regions enter, with distinct roles:

- **`R`** — the region of the damping. It is the region used in the
  definition of the functional and stays in every weight, activity and
  exponent: `F_R(a) = profileExpectation μm β χ f s R a` (Stone 55), the
  effective factors `b(η) = touchFactor R a η`, `b′(η) = touchFactor R a′ η`.
- **`r`** — the region that localizes the differences of the effective
  factors: outside `r` they agree, on `r` they differ by at most `δ`.
- **`s`** — the regional parameter of the functional (the set whose touching
  cores index the polymer representation); it is asserted to be a support of
  `f` only where the hypothesis `DependsOnlyOn f s` is present, which is not
  the case in the comparison below.

Write `D_s = card (supportLinkFinset s)`. For profiles `a, a′` with values in
`[0, 1]` and `δ ≥ 0`:

```
|F_R(a) − F_R(a′)|
    ≤ δ · Cf · exp(−n / 2) · [exp(6 · D_s / 113) + exp(4 · D_s / 113)]
    ≤ δ · (2 · Cf) · exp(6 · D_s / 113) · exp(−n / 2).
```

The first line is the two-term estimate
(`abs_profileExpectation_sub_profileExpectation_le_two_terms_localized`); the
capstone follows from `exp(4·D_s/113) ≤ exp(6·D_s/113)` (`D_s ≥ 0`). **The
constant, the rate `exp(−n/2)` and the regime are those of Stones 54 and 55;
what is new is that the separation `n` refers to the change region `r`, while
a common damping background outside `r` — near `s` included — is
preserved.** Nothing is divided by `δ` or by a factor of a profile; no
`δ ≤ 1` is required.

### Hypotheses, exactly as elaborated

Context of the module: `{N : ℕ} [NeZero N] [Fintype (Site N)]`,
`{G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]`,
`(μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]`.

| Hypothesis | Meaning |
|---|---|
| `hβ : 0 ≤ β`, `hsmall : β ≤ 1/40000` | small-β (strong-coupling) regime; the Kotecký–Preiss smallness of Stone 46 |
| `mχ : Measurable χ`, `hχabs : ∀ g, \|χ g\| ≤ 1` | `χ : G → ℝ` is a bounded measurable real function |
| `R : Set (Link N)` | the damping region, explicit and arbitrary |
| `mf : Measurable f`, `hCf : ∀ U, \|f U\| ≤ Cf` | measurability and an absolute majorant of the observable; `0 ≤ Cf` is **derived** (`nonneg_of_abs_le_of_config`, 52-E), not assumed |
| `hsep : WalkBarrierSeparated s r n` | walk-barrier separation of the set `s` from the **change** region `r` at scale `n` |
| `hδ0 : 0 ≤ δ` | the majorant is non-negative; no upper bound on `δ` |
| `h0 h1 h0' h1' : ∀ η, 0 ≤ a η ≤ 1, 0 ≤ a′ η ≤ 1` | the two profiles take values in `[0, 1]` |
| `hsame : ∀ η, ¬ typedTouchesSupport η r → touchFactor R a η = touchFactor R a′ η` | the effective factors agree outside `r` (the common background; not necessarily 1) |
| `hδ : ∀ η, typedTouchesSupport η r → \|touchFactor R a η − touchFactor R a′ η\| ≤ δ` | the majorant of the difference of the effective factors, on `r` only |

Not required: any separation of `s` from `R`; `r ⊆ R`; a unit background
outside `r`; `δ ≤ 1`; a sign condition on activities or exponents;
`DependsOnlyOn f s`. No factor of `card R` or `card r` enters the constant.
Replacing `R` by `r` in the definition of the functional would remove the
background and change the object; the module keeps `R` everywhere and proves
the localized cancellation directly. The bound is uniform in the admissible
background; this does not mean that the functional is independent of the
background, nor that the background may be replaced by the unit profile (with
a non-unit background the unit-profile identification with the Gibbs
expectation does not follow from the localization and is not claimed).

**Three levels of hypotheses.** (i) The algebraic identities on the effective
factors — equal weights on families and tuples avoiding `r`
(`profileWeight_eq_of_touchCount_zero_of_same`,
`tupleProfileWeight_eq_of_tupleTouchCount_zero_of_same`), the finite
identity of the coefficients (`kpLocalizedDiff_inclusion_exclusion`) and the
exact equality of the functionals under equal effective factors
(`profileExpectation_eq_of_touchFactor_eq`) — use `hsame` only, or nothing at
all: no interval, no regime, no bound on `f`. (ii) The series identity
(`profileCoreExponent_sub_eq_localizedConnectorDiff`) and the exponential
ledger (`profileExpectation_sub_eq_two_column_ledger_localized`) use the KP
regime and the intervals `[0, 1]` (for the exponential representation, with
the KP hypothesis transported with region `R`) and `hsame`; they do not use
`mf`, `hCf`, `hsep` or `hδ`. (iii) The bounds — the localized telescoping
bounds (interval and `hδ`), the eroded bound, the exponential control, the two
columns, the two-term estimate and the capstone — add `hδ`, `hsep` and, from
the columns onwards, `mf` and `hCf`. The declaration matrices in
[`docs/audits/stone56/`](../audits/stone56/README.md) record the list of each
declaration.

## 2. The route

- **Effective factors and cancellation.** `hsame` is an equality of the
  effective factors `touchFactor R ·`, not of the raw profiles: raw values may
  differ where they are never read. Families and tuples avoiding `r` have
  **equal** weights under the two profiles, not weight 1. The telescoping
  lemma of 55-A (`abs_prod_sub_prod_le_sum_abs_sub`) applied to the effective
  factors — which inherit `[0, 1]` from the interval of the profiles — with
  the sum split by "touches `r`" gives `|A_Γ − A′_Γ| ≤ touchCount r Γ·δ` and,
  for tuples, `|A_δ − A′_δ| ≤ tupleTouchCount r δ·δ ≤ k·δ` (positions counted,
  repetitions included: `![η, η]` counts 2); the family bound against
  `card T·δ` follows.
- **The localized difference coefficient, orientation `A′ − A`.**
  `kpLocalizedDiffCoeff k z P r R a a′` sums, over the tuples hitting the
  `P`-barrier and the `r`-barrier, `(A′_δ − A_δ)·Ursell·∏ z`, divided by
  `k!`. Its identity with
  `[c_k(restr(z_a, P)) − c_k(z_a)] − [c_k(restr(z_{a′}, P)) − c_k(z_{a′})]`
  (`z_a = profileDampedActivity z R a`) is proved directly from the
  expansion: a `P`-allowed tuple cancels between restricted and unrestricted;
  a tuple avoiding `r` has `A_δ = A′_δ` by `hsame` (the regional filter enters
  only through `TupleAllowed (regionAllowed r) δ → tupleTouchCount r δ = 0`,
  no converse); the remaining tuples carry `A′ − A`, the orientation coming
  from "restricted minus unrestricted". The order-0 coefficient is 0. The
  domination `|D_k| ≤ δ·k·A_k(|z|, P, regionAllowed r)` pays the weight
  difference by the localized tuple bound and the rest by the positive
  connector coefficient of the original `|z|`.
- **Series and erosion.** `E^R_T(a) − E^R_T(a′) = Σ′ D_k`
  (`localizedConnectorDiff`), the four cluster series being summable by the
  KP transport with region `R` (`abstractKP_profileDampedActivity R`; no
  separation of `s` from `R`). The eroded bound
  `|Σ′ D_k| ≤ δ·e^{−((n − m_T : ℕ))/2}·q_T`, `q_T = card(barrierLinkFinset T s)·(2/113)`,
  uses only the separation of `s` and `r` (the barrier regions of `T` at `s`
  and of `∅` at `r` keep separation `n − m_T`), with the natural truncated
  subtraction: when `m_T > n` the factor is `1`, never an explosion; no
  `8/(3e)`.
- **Bilateral exponential control at κ = 2.** Both exponents are `≤ q_T`
  (`abs_profileCoreExponent_le_barrier` of 55-A, valid with `R` arbitrary);
  the scalar bound of Stone 54 (`abs_exp_sub_exp_le_exp_mul_abs_sub`),
  `q ≤ e^q` and the repurchased erosion give
  `|e^{E^R_T(a)} − e^{E^R_T(a′)}| ≤ δ·e^{−n/2}·e^{m_T/2 + 2·q_T}`.
- **The localized ledger.** From the exponential form of 55-A on both sides,
  the touching cores split by `r`:
  `F_R(a) − F_R(a′) = Σ_{T touching} A′_T·W_T·(e^{E^R_T(a)} − e^{E^R_T(a′)})
  + Σ_{T ∈ activityBridgeCores s r} (A_T − A′_T)·W_T·e^{E^R_T(a)}` — the
  second profile's weight on the connector column, the weight difference
  `A − A′` with the **plus** sign and the first profile's exponent on the
  bridge column; on the `r`-allowed cores the correction vanishes by
  **equality** of the weights (`hsame`), which need not be 1.
- **Connector column, budget (1/2, 2).** `0 ≤ A′_T ≤ 1` (with `R`), the
  Mayer majorant `|W_T| ≤ Cf·Π M`, the κ = 2 control and the generic budget
  `sum_halfTilt_two_le` give `δ·Cf·e^{−n/2}·e^{6 D_s/113}`.
- **Bridge column, κ = 1, budget (7/8, 1), two regions.**
  `nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions` bounds the
  first moment `card T·|W_T·e^{E^R_T(a)}|` with the exponent taken at `R`
  (`abs_typedMarkedCoreWeight_mul_exp_profile_le`, 55-B, valid with `R`
  arbitrary) and the geometry at `r` (`activityBridgeCore_familyTotalCard_ge`
  with `T ∈ activityBridgeCores s r`): `card T ≤ m_T ≤ e^{3 m_T/8}`, the
  payment `1 ≤ e^{−n/2}·e^{m_T/2}`, the fusion `e^{7 m_T/8}` absorbed in the
  tilt 7/8. The published 55-B interface ties both regions to one `r`; it is
  not edited and not invoked — the strategy actually adopted was to
  reconstitute its route with two regions, preserving the historical
  interface. With `|A_T − A′_T| ≤ card T·δ` and `sum_sevenEighthsTilt_one_le`
  the column closes with `δ·Cf·e^{−n/2}·e^{4 D_s/113}`.
- **Closure.** Ledger, triangle inequality and the two columns give the
  two-term estimate; the capstone follows with `e^{4 D_s/113} ≤ e^{6 D_s/113}`
  and `0 ≤ Cf` derived.

## 3. Endpoints and interfaces

The two definitions are `kpLocalizedDiffCoeff` and `localizedConnectorDiff`.
The four interfaces at the end of the module:

| Interface | Declaration | Content |
|---|---|---|
| translation `r = R` | `localized_hypotheses_of_profile_hypotheses` | the Stone 55 hypothesis `\|a − a′\| ≤ δ` on the polymers touching `R` gives `hsame` (both effective factors are 1 outside `R`) and the effective majorant on `R` |
| equal effective factors | `profileExpectation_eq_of_touchFactor_eq` | `touchFactor R a = touchFactor R a′` pointwise ⇒ `F_R(a) = F_R(a′)` **exactly**, for arbitrary real profiles (an identity of definitions; no KP regime, no separation, no bound on `f`). The analytic bounds keep the interval `[0, 1]`; this freedom is not transported to them |
| `r = ∅` | `profileExpectation_eq_of_same_empty_region` | under `hsame` with `r = ∅` every effective factor agrees (no polymer touches `∅`), hence exact equality — as an application of the previous interface. Distinct from `R = ∅`, where every effective factor is 1 and the functionals agree by the Stone 55 empty-region identity |
| recovery of Stone 55 | `abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_localized` | with `R := r` and the translated hypotheses, the localized capstone gives the Stone 55 bound. Direction 56 ⇒ 55: the published Stone 55 capstone is not used in any proof of the module (the statement is rederived; the Stone 55 theorem is untouched) |

Further cases: `δ = 0` gives the bound 0 by effective application of the
capstone (nothing is divided by `δ`); `δ > 1` (for example `δ = 7`) is
admissible and merely loose; raw profiles that differ only where they are
never read (outside `R`) have equal effective factors and equal functionals;
a profile with a value outside `[0, 1]` is outside the analytic hypotheses
(the auditor's test W7x and the constructor's test V4x, expected to fail, are
application failures by a missing hypothesis, not counterexamples). The tests
of the constructor and of the auditor use geometric premises
(`typedTouchesSupport` as hypotheses); no concrete lattice instance was
constructed.

## 4. The module

One new module (964 Lean lines; 24 top-level declaration lines, a textual
count by `grep -cE` of lines beginning with `theorem`, `lemma`, `def`,
`abbrev`, `structure`, `noncomputable def`, `instance`, `inductive` or `class`
followed by a space, at commit `a2fcf8e9…` — 22 `theorem` and 2
`noncomputable def`; 22 in-file `#print axioms` certificates, one per
theorem), a leaf over Stone 55; no pre-existing module was modified; the only
change outside the new file is its glob in `Phase3/lakefile.toml`
(116 → 117 modules).

| Gate | Module | Lines / decls / certs | Content |
|---|---|---|---|
| 56-L | `ActivityProfileDampingLocality.lean` (blob `f2103846…`) | 964 / 2 defs + 22 thms / 22 | the localized weight identities and bounds (56-L.1); the localized difference coefficient, its inclusion–exclusion, order 0 and domination (56-L.2); the translation of the Stone 55 hypotheses (56-L.3); the localized series, the exponent difference and the erosion (56-L.4); the κ = 2 control (56-L.5); the ledger (56-L.6); the connector column (56-L.7); the two-region bridge first moment and the bridge column (56-L.8); the two-term estimate and the capstone (56-L.9); the exact identities and the recovery of Stone 55 (56-L.10) |

Imports: `Mathlib` and `LatticeGauge.ActivityProfileDampingStability`
(Stone 55). From Stone 55 the module consumes the definitions, the telescoping
lemma, the domination and KP transport, the exponential form and the barrier
bound of 55-A, and only `abs_typedMarkedCoreWeight_mul_exp_profile_le` of
55-B; from Stone 54 the scalar helpers `abs_exp_sub_exp_le_exp_mul_abs_sub`
and `le_exp_self`; the generic barrier route, first moments, budgets, erosion
and gas identities of Stones 50–53 as published (the import of
`CovarianceDecay` remains inherited through Stone 54, record I1 of the
Stone 54 audit).

Origin of the proposal: the scientific architecture of GPT Astra (feasibility
tape 56-A; construction 56-L). The feasibility file of 56-A (2 definitions and
33 theorems, of which 18 in the chain and 15 in its test section, plus one
`example`) was promoted to this module; the definitive scientific count of
Stone 56 is that of the module: 22 theorems and 2 definitions. No
optimality, priority or exclusivity of the route is claimed.

## 5. Kernel certificates and CI

- Every one of the 22 theorems carries an in-file `#print axioms`
  certificate; each reports `[propext, Classical.choice, Quot.sound]`. They are
  emitted during `lake build` and are visible in the CI logs of runs 501 and
  502; the dedicated CI step `Kernel certificates` still checks the three
  capstones of Versions 49–51 and was not extended. The library carries 269
  in-file `#print axioms` commands at `ead48145…` (247 + 22; the CI logs show
  272 axiom outputs = 269 + the 3 of the workflow step); these are certificate
  commands, not a count of theorems. The two definitions are not certified by
  the build; the auditor's test W0 adds two checks for them.
- Hygiene in the module: 0 `sorry`, 0 `admit`, 0 scientific `axiom`,
  0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`, no division by `δ`
  or by a factor of a profile; 114 inherited build warnings (unchanged since
  Version 50), none in the new module.
- Publication protocol: one candidate commit over the then-current `main`
  (the Version 55 snapshot `445cc76b…`), delivered as a verifiable git
  bundle; the QA1 audit before publication; push of the audited commit, a
  non-draft pull request, `build-phase3` green on the pull-request head, a
  normal merge with the expected head SHA locked (no squash, no rebase), and
  `build-phase3` green again on `main` at the merge commit; then the
  adversarial review of the integrated state.

| Candidate | PR | PR run (`build-phase3`) | Merge commit on `main` | `main` run |
|---|---|---|---|---|
| `a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1` | [#37](https://github.com/consensusframework/yang-mills-mass-gap/pull/37) | [501](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/36079842381) (id 36079842381, job 107899166265) | `ead481456bc8637b2b7c22e867cc49f99f4ab375` | [502](https://github.com/consensusframework/yang-mills-mass-gap/actions/runs/36080653020) (id 36080653020, job 107901627271) |

Custody note: the pull-request run 501 is associated with the head
`a2fcf8e9…`, but its effective checkout was the provisional merge commit
`8831358` ("Merge a2fcf8e9… into 445cc76b…"), as recorded in the job log read
by the publishing instance (`docs/audits/stone56/publication/RELATORIO_56-P.md`);
run 502 compiled the definitive merge `ead48145…` itself (job log read by the
same instance). The run metadata alone do not prove the effective checkout;
the attribution is to the log reading. The merge commit has parents
`445cc76b…` (the base, the Version 55 commit) and `a2fcf8e9…`, and its tree
`171367d9…` is the tree of the candidate. Both runs: `Build completed
successfully`; the dependency manifest `c376bbe9…1227` recorded and verified
after the resolution and after the build, the nine dependencies checked out at
the recorded revisions, no `lake update`; 117 `LatticeGauge` modules built,
0 replayed (dependencies: 9 built, 0 replayed); 0 errors; 114 warnings, all in
`LatticeGauge/`, none in the new module, none from dependencies; 272 axiom
outputs, all standard, the 22 of the new module included; no `sorryAx`.

Toolchain at `ead48145…`: Lean `4.15.0`, Mathlib `v4.15.0` (pinned in
`Phase3/lakefile.toml`; resolved manifest `Phase3/lake-manifest.json`,
SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`,
Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608`); the library has 117
modules, 37,994 Lean source lines and 1,780 top-level declaration lines by the
textual count (1,756 at Version 55 plus the 24 of this module).

## 6. Relation to Stone 55

Stone 55 proved the stability under a profile of factors when the same region
`r` enters the definition of the damping and the separation hypothesis. Stone
56 separates the two: the damping region `R` stays in the functional, the
weights and the exponents, and the separation refers to the region `r` where
the effective factors change; a common damping background elsewhere is
preserved. The constant, rate and regime are unchanged, and the Stone 55
statement is recovered as an application with `R := r`. The Stone 55 capstone
remains published and valid and is not used in the proofs of Stone 56.

## 7. Audits and reviews

Recorded, with hashes and provenance, in
[`docs/audits/stone56/`](../audits/stone56/README.md):

- **56-QA1 with its errata C1** — reproduction by execution of the candidate
  `a2fcf8e9…` by a separate instance of Claude Fable 5.1 on its own bench
  (dependencies from the committed manifest, no `lake update`; `.lake/build`
  deleted; 117 modules built, 0 replayed, exit 0, 721 s; 269/269 certificates
  standard, 0 `sorryAx`; inherited warning blocks identical to the Version 55
  baseline, none in the new module; own tests W0–W7x, the ledger, the
  coefficient identity and the closure re-derived by independent routes).
  Same model as the constructor, distinct instance and bench; prior exposure
  declared, not blind. Verdict `PASS NO ESCOPO`. The errata C1, issued by the
  same auditing instance, corrects the audit's own record (the
  declaration-line count, the description of the constructor's dependency
  cache, the warnings of the auditor's disposable tests, the sources of the
  certificates, four matrix references and the paths inside the package) and
  is to be read together with the report, C1 prevailing; no mathematical
  finding and no change to the candidate.
- **56-K-ADV** — adversarial review by Luan / Kimi 3, a different model
  family, by reading and mathematical analysis, without Lean execution, with
  declared prior exposure to Stones 49–55 (not blind), of the candidate
  sources and of the scientific merge `ead48145…` (dated 2026-09-25, received
  by the consolidation on 2026-09-29). Verdict `PASS NO ESCOPO`; no
  mathematical or new documentary finding; no errata. The review declares that
  it did not receive the constructor's evidence package or construction
  report, and that it checked the CI runs through the API without inspecting
  the checkout logs; the custody of the integration checkouts is in the
  publication report and the CI logs.
- **56-P** — the publication report of the constructing/publishing instance
  (a custody record, not an audit).
- **GPT Astra** — scientific architecture and review: the feasibility,
  construction, publication and consolidation tapes; reading of the module and
  of the reports, checks of the evidence, Git objects and publication
  metadata; no Lean build of its own.

These are audits and reviews by AI models with human coordination; no
specialized human mathematical review of the proofs is documented at this
stage.

## 8. Version records

| Step | Record |
|---|---|
| Version 55 | commit `445cc76b02550291e6524bb1bf631aac4cc86c61` (merge of PR #36), tag `zenodo-v55` (simple tag), GitHub Release [`zenodo-v55`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v55) published on 2026-09-20 with four assets (`yang-mills-mass-gap-zenodo-v55.zip`, `RELEASE_NOTES_PEDRA55.md`, `MANIFEST_v55.txt` and the checksum file, named `SHA256SUMS.6.txt` on the Release); Zenodo record DOI [10.5281/zenodo.22850085](https://doi.org/10.5281/zenodo.22850085) (concept DOI 10.5281/zenodo.17397622), **published on Zenodo on 2026-09-19**, as confirmed by the coordinator and by a capture of the record page; the consolidating session could not reach Zenodo itself, so the confirmation is attributed to the coordination and the capture, not to a direct consultation. The deposit contains Stones 52–55 and the committed dependency manifest, and not Stone 56 |
| Stone 56 (state at the consolidation of 2026-09-29, kept as written) | integrated on `main` at `ead48145…` (2026-09-25, PR #37), audited (QA1 2026-09-24 with errata C1 2026-09-24; Kimi 3 review 2026-09-25) and CI-verified; **no tag, no Release and no deposit of its own**. It is cited by its commit. The DOI 10.5281/zenodo.22949184 is **reserved** for the future Version 56 record (a Zenodo draft, not a published deposit, per the coordinator's capture; a reserved DOI is not a deposit and must not be cited as one); the snapshot of that version will be the final documentary merge, not created here |
| Version 56 (record added on 2026-10-09) | commit `95091fdd07398a7b42901829ad61e4e2c26d5aaa` (merge of PR #38, the documentary consolidation of this stone; root tree `8b723878…`, `Phase3/` tree `f387f26d…`, identical to the tree above), tag `zenodo-v56` (simple tag), GitHub Release [`zenodo-v56`](https://github.com/consensusframework/yang-mills-mass-gap/releases/tag/zenodo-v56) published by the coordinator on 2026-10-01 with four assets (`yang-mills-mass-gap-zenodo-v56.zip`, `RELEASE_NOTES_PEDRA56.md` as revised by the coordinator before the upload, `MANIFEST_v56.txt` and the checksum file, named `SHA256SUMS.8.txt` on the Release); Zenodo record DOI [10.5281/zenodo.22949184](https://doi.org/10.5281/zenodo.22949184) (concept DOI 10.5281/zenodo.17397622), **published**, as confirmed by the coordinator — the exact Zenodo publication date was not established by the documentary session of 2026-10-09, which did not consult Zenodo. The deposit contains Stones 52–56 and the committed dependency manifest, and not Stone 57 |
