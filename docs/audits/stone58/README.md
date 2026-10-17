# Stone 58 — independent evidence: QA1 reproduction, adversarial review with its errata, and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 58 candidate `d942edd3986ac8cb13a8d5958bf1e11461434794` (see
[`docs/stone58/RESULTS.md`](../../stone58/RESULTS.md)), integrated on `main` at
`69706b9a13a23b0f132418f2390d4030e1fcc78b` (PR #42): the audit evidence
package of the QA1 reproduction with its report and its two matrices, the
adversarial review by Kimi together with its errata C1, and the publication
report of the constructing/publishing instance. It follows the organization
of [`docs/audits/stone57/`](../stone57/README.md); unlike Stone 57, no
complementary execution on a third platform was received for this stone, and
none is recorded. The QA1 package is the primary record of the audit; its
report and matrices are extracted here only for reading convenience and are
byte-identical to the copies inside the package. Nothing in this directory is
a Lean module: the package contains disposable test files (including a test
that is *expected to fail*), build logs and matrices, and none of it enters
the `LatticeGauge` library, the `lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are
in English or mixed); they are not translated, normalized or edited. The
constructor's own materials (the construction report `RELATORIO_58-AL.md`,
SHA-256 `b55079dcd932839d674e37dbcb36a6d9c8832128aad7df16cbb3bc32f8fb6dce`,
and the package `STONE58L_evidence.zip`, SHA-256
`7af10568c51ffbc7d92b03bbcd46924057c75728874ffc5e50c145f6b4106a83`, internal
manifest 32/32, with its bundle, diff, matrices and tests T1–T8x) are **not**
part of this collection: they are the implementer's material, not an audit;
the audit and the review cite them by hash. The transport package prepared by
the coordination for the reviewer (`PEDRA58_KIMI_INPUTS.zip`, 792,640 bytes,
SHA-256 `ac7713048df1bad95d65d5d32d3e6503e4bada70a3f63a325e09bf0e2fb1f959`,
17 files, internal manifest 16/16) is a package of copies and context, not a
third audit, and is not in the tree; its integrity is attributed to the
reviewer's errata and to the coordination, not verified here.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra / Can (AI model) | different model family from the constructor | tapes (feasibility and construction 58-AL, integration 58-P, this consolidation); reading of the module, the reports, the packages and the logs; conference of Git objects and publication metadata; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | feasibility tests (gate 58-A), Lean implementation of the module, local commit and bundle with the constructor's API tests T1–T8x and a clean rebuild of the 119 modules (gate 58-L), then, after QA1, push, pull request, merge and CI follow-up (58-P), and this consolidation, in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (dependencies reused from its Stone 57 bench, materialized then from the Mathlib community cache at the nine manifest revisions, 9/9 revisions checked, no `lake update`, not recompiled; project artifacts removed before the build; 119 modules built, 0 replayed, exit 0; own `#print axioms` of 32 declarations; own tests Q0–Q8x; the constructor's tests T1–T8x re-executed in a second pass); preliminary conclusions recorded before opening the constructor's material | **not blind** (prior exposure to the earlier stones declared; the constructor's report read beforehand to identify the target); not a different model family; not human review |
| Adversarial review and errata | Kimi (Moonshot AI), as the documents identify the reviewer | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis of the module and the interfaces consumed, with own custody checks (hashes of the transport and evidence packages; the Git objects of the merge, the candidate and the base; the diff; the counts); **no Lean execution**; one errata by the same instance correcting four points of its own report | **not blind** (same conversation instance as the Stone 57 review; the tape disclosed the target and the earlier results); reading only; did not download the CI logs of runs 511/512; did not verify the SSH signature; did not consult Zenodo or the Release |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions, manual publication; in this round, the documentary conference of the packages, the matrices and the logs | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model. No
Lean execution is attributed to GPT Astra / Can, to Kimi or to the
coordination. The historical credits of "Kimi 3" and, for Stone 57, "Kimi K3"
are preserved as written; the Stone 58 documents identify the reviewer as
"Kimi (Moonshot AI)" and no build or version is inferred. The historical
credits of "Manus AI 1.6" and the Stone 57 execution on the "Manus Sandbox"
platform are records of other stones and are not attributed to Stone 58.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_58_evidence.zip`](packages/QA1_58_evidence.zip) | `b23ce8ed4b8838fea877bfdb00d127892788c5ee657360280481e73916b067c9` | Fable 5.1, QA instance | `d942edd3…` (candidate; published as [PR #42](https://github.com/consensusframework/yang-mills-mass-gap/pull/42), merge `69706b9a…`) | `PASS NO ESCOPO` | 2026-10-15 (clean build 16:36–17:04 UTC) |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_58-QA1.md`](reports/RELATORIO_58-QA1.md) | `de495f379fe1a38193ba2d4c01a9f1f489e6c79471eeb5ec6175a936e3a0f308` | Fable 5.1, QA instance | `d942edd3…` | `PASS NO ESCOPO` | 2026-10-15 |
| 3 | QA1 declaration matrix (extracted) | [`reports/58_QA1_DECLARATION_MATRIX.tsv`](reports/58_QA1_DECLARATION_MATRIX.tsv) | `6f9202ac794c2667f6422752d66284d39bc3737b0becb8af313fdcc19cfc618d` | Fable 5.1, QA instance | `d942edd3…` | 32 items (28 theorems, 4 definitions) | 2026-10-15 |
| 4 | QA1 test matrix (extracted) | [`reports/58_QA1_TEST_MATRIX.tsv`](reports/58_QA1_TEST_MATRIX.tsv) | `9f12217dacee69414eb5ab97e04e3d67aa215e9216a787a5039097f8f61f9475` | Fable 5.1, QA instance | `d942edd3…` | Q0–Q6 positive, Q7 by reading; Q8x expected application failure; T1–T8x (constructor's) re-executed | 2026-10-15 |
| 5 | Adversarial review | [`kimi/RELATORIO_58-K-ADV.md`](kimi/RELATORIO_58-K-ADV.md) | `348c163fe5327488d3437dfd77219b2d52544659c6066643aa90f7d473176e33` | Kimi (Moonshot AI) | `69706b9a…` (merge), `d942edd3…` (candidate) and `18c6ff08…` (base), via the public Git objects | `PASS NO ESCOPO` | 2026-10-16 |
| 6 | Errata C1 of the review | [`kimi/ERRATA_58-K-ADV-C1.md`](kimi/ERRATA_58-K-ADV-C1.md) | `4b22730bcca0870e1406aafc1b4f69208fc1edd98bb393ea4545ba43da831268` | Kimi (Moonshot AI), same instance | applies to item 5 (hash `348c163f…`); the scientific target unchanged | verdict `PASS NO ESCOPO` maintained; four corrections of the report | 2026-10-16 |
| 7 | Publication report (FITA 58-P) | [`publication/RELATORIO_58-P.md`](publication/RELATORIO_58-P.md) | `70b42fc2e8294fc3f21860b82786a089d036e075fe606f6de37eeb4bd0035723` | Fable 5.1, constructing/publishing instance | `d942edd3…` → `69706b9a…` | n/a (record) | 2026-10-15 |

The seven hashes were supplied as references by the coordinator in the
consolidation tape (the hash of the publication report as the publisher's
own reference) and match the files received; the publication report is the
original kept on the publisher's bench. SHA-256 of every file of this
directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv` and the seven materials: 9 entries; no self-inclusion).
Machine-readable provenance: [`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_58_evidence.zip` (39 entries: 37 files and 2 directories,
`tests/` and `builder_tests_rerun/`, at the root of the archive; internal
manifest `SHA256SUMS_58-QA1.txt`, 36 entries — every file of the package
except the manifest itself). Contents: the report,
`PRELIMINARY_CONCLUSIONS_first_pass.md` (written before the auditor opened
the constructor's tests, matrices, logs and scripts), the two matrices,
`environment.txt` (the cloud container of the Stone 57 audit, which survived;
elan 4.2.4; Lean 4.15.0, Lake 5.0.0-1165156; clone with the push URL
disabled and a detached worktree at the candidate `d942edd3…`; manifest
SHA-256 `c376bbe9…1227`; the `.lake/packages` dependencies materialized in
the Stone 57 audit from the Mathlib community cache and moved into the
worktree, 9/9 revisions checked, not recompiled), `prebuild_artifacts.txt`
(project build artifacts removed before the build: none left),
`build_full_clean.log` (105,147 bytes, SHA-256
`71a6faa01a4b5a469a1f63778836ca11a9f294fb3fc80a5151129bb81a0a5d80`; single
integral `rm -rf .lake/build && lake build`, 2026-10-15T16:36:52Z →
17:04:30Z, exit 0, 1,658 s, **119 modules built, 119 distinct names, 0
replayed**, 0 errors, 317 certificates all standard, 86 of them printed
across lines, 0 `sorryAx`; dependencies 0 built / 0 replayed with no
dependency diagnostic emitted — a reuse of the cache, which says nothing
about the warnings of a recompilation of the dependencies), its `.result`
and instants, the manifests before and after the build (identical),
`compare_warning_blocks.py` and `warnings_block_comparison.txt` (the full
multi-line warning blocks against the Stone 57 baseline — the QA1 log of
Stone 57 inside `docs/audits/stone57/packages/QA1_57_evidence.zip`, whose
external and internal manifests the auditor validated first: 114 blocks of
`LatticeGauge/`, identical multiset, 113 distinct file:line pairs, **0 in
`ActivityProfileDampingAdditiveCover`**, the comparator relabelled for the
Stone 58 module), `tests/` (the `.lean` files Q0–Q6 and Q8x, their final
logs and the preserved attempt logs of the auditor's own slips) and
`builder_tests_rerun/` (the constructor's `T58L_api_tests.lean`, `T58L_T8x`
and `T58A_T8x` re-executed on the auditor's bench, with the same results).
Logs are not duplicated outside the package. The QA1 declaration matrix lists
the 32 declarations of the module with lines and names equal to the
constructor's matrix.

Key results reported by the auditor (not re-executed here): 317/317
certificates in the clean build and **32/32** in the test Q0 — the 26
declarations with an in-file command (22 theorems and 4 definitions) plus the
six auxiliaries without one (`regionCost_nonneg`, `regionCost_of_not_touch`,
`regionCost_of_touch`, `prefixCost_zero`, `prefixCost_nonneg`,
`touchFactor_additiveProfile`) — all equal to `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`; the 32 are the auditor's checks and are not added
to the 320 outputs of the CI; `#check` of the two capstones, the five
recoveries, the chain lemma and `additive_of_cover` with the absences
verified on the elaborated types (no `owner` or decomposition, no `m > 0`,
no disjointness, no `r i ⊆ R`, no separation `s`/`R`, no unit background, no
`δ i ≤ 1`, no sign condition, no `DependsOnlyOn`; `0 ≤ Cf` derived); the
scalar move re-proved by the auditor's own route (start, permanence for
`t ≥ 0`, saturation, increment `≤ u` for **any real `t`** with an instance at
`t = −1`; numerical instances in both directions, negatives, equality,
capacities `0`, insufficient, exact and excess; the monotonicity of the
scalar path proved separately, with nothing on `F_R`) (Q1); the stages
`1/4 → 1/2 → 3/4` and the reverse path with two budgets `1/4`, and the
**global witness** — `a ≡ 1/4`, `a′ = 3/4` at `η₀` and `1/4` elsewhere,
budgets `![1/4, 1/4]`: `hadd` proved for **every** polymer
(`Q2_hadd_global`), no single index paying `1/2` at `η₀`
(`Q2_no_single_payer`, the Stone 57 cover false there), and the capstone
applied to those profiles with the limits in `[0, 1]` proved (Q2; contacts
of `η₀` with `R`, `r 0`, `r 1` by hypothesis; no universal numerical gain
inferred); the prefixes `C_0 = 0`, `C_(i+1) = C_i + c_i` (own route by
trichotomy), `C_m = ∑ c_i`, the exactly null step outside `r i` even with
contact with `r 1`, capacities `1/8, 7, 0` in both directions, repeated
regions `r 0 = r 1` accumulating (`C_2 = δ₀ + δ₁`), the background `1/2`
preserved by `move_self` and distinguished from "no factor changes" (Q3);
`p_0 = a`, the limits, the endpoint under `hadd` re-derived, raw profiles
`3/10` vs `9/10` off `R` with equal effective factors, `R = ∅`, `m = 0` with
profiles outside `[0, 1]`, zero budgets by interface and by effective
application, effectively equal profiles (Q4); the **own closure** — own
telescoping, the chain assembled with the Stone 56 two-term estimate at
every step and the Stone 56 identity at the endpoint, the factorization of
`B`, `0 ≤ Cf` derived, the compact form — without the two capstones and
without the chain lemma, reusing the published local lemmas, with three
certificates of its own test theorems that are not counted among the 317 of
the project (Q5); `hcover ⇒ hadd` re-derived, the compact Stone 57 recovery
and the Stone 56 recovery re-derived, the types of the compact recovery and
of the one-region recovery compared with the published Stone 57 theorems by
definitional equality in both directions, zero budgets by effective
application, and the classification of `rfl` between two proof terms of the
same proposition (proof irrelevance, definitional) against the algebraic
rewriting `3·D·(2/113) = 6·D/113` (`ring`) (Q6); the Stone 57 capstone and
its two-term form with no use in the code of the module, no conversion to a
single owner, E1–E6 checked (Q7, by reading and grep); the expected
application failure of the obligation `1/2 ≤ 1/4 + 0`, proved false
(`Q8x_obligation_false`) and failing with the goal `False` open (Q8x),
classified as an impossible hypothesis and not as a counterexample. The
auditor's disposable tests emitted 61 warnings (Q1: 2, Q2: 3, Q3: 2, Q6: 54,
unused binders in the `example`s comparing types), separate from the 114
inherited warnings of the project and from the 0 of the new module. The
tests **T1–T8x** belong to the constructor (delivered in
`STONE58L_evidence.zip`, re-executed by QA1 in its second pass, which does
not change their authorship; the positive test has 15 `#check` and no
`#print axioms`); the tests **Q0–Q8x** belong to QA1. The geometric tests are
parameterized by `typedTouchesSupport` hypotheses; no concrete lattice
instance is constructed.

## Reading the QA1 record: the precisions D1–D3, T2/Q2 and C58-Q6

The QA1 report, the two matrices and the archived preliminary conclusions
are preserved exactly as received. **No errata was issued by the auditing
instance**, and none is attributed to it. The audit recorded, in its second
pass (§6 of its report), four observations on the **constructor's** report
and tests, which the coordination accepted in the integration tape 58-P; the
coordination added one precision of its own on the auditor's test Q6. None
of them concerns the candidate, its hypotheses, proofs or compilation
results, and the verdict `PASS NO ESCOPO` stands. The materials are to be
read with them:

- **D1 — what the `rfl` of the constructor's test T6 states.** The test
  states an equality between two theorem constants (the Stone 57 capstone
  recovered through the additive route and the published Stone 57 capstone,
  and likewise for the one-region recovery). It is an equality of two **proof
  terms** of the same proposition, closed by proof irrelevance (a
  definitional equality); it says nothing about the bodies of the proofs
  being syntactically identical. The comment in the constructor's test source
  already says this; the sentence of the constructor's report
  (`RELATORIO_58-AL.md` §2, "igualdade de proposições, não de termos de
  prova") is inverted, and its tests matrix needs the qualification
  "syntactically" for "not same proof term". Confirmed by the auditor's Q6f.
- **D2 — four definitions.** The constructor's report says "3 definições" in
  one paragraph of its §2; the module has 4 definitions (`move`,
  `regionCost`, `prefixCost`, `additiveProfile`) and 28 theorems, and the 26
  in-file commands cover 22 theorems and the 4 definitions. The source is not
  affected.
- **D3 — the label of the inherited comparator.** The constructor's
  `compare_warning_blocks.py` and `warnings_block_comparison.txt` (in
  `STONE58L_evidence.zip`) print the name of the Stone 57 module in their
  last-but-one line; the comparison of the 114 blocks is correct, and the
  zero count in `ActivityProfileDampingAdditiveCover` was recomputed by the
  auditor with the correct name (and, in the publication report, by the CI
  analyzer).
- **Scope of T2 and Q2.** The constructor's T2 proves the additive obligation
  at the witness coordinate, the impossibility of a single payer and the
  three stages of the effective factor; it does not prove `hadd` for every
  polymer of the profiles of its statement. The auditor's Q2 proves the
  additive cover for **every** polymer of its parametric profiles, the
  absence of a single payer at the witness and an application of the
  capstone. In both, the contacts and the geometric context are hypotheses;
  no concrete lattice was built. Not a defect of the capstones.
- **C58-Q6 — the coordination's precision on the auditor's Q6.** The source
  `tests/q6_recoveries.lean` re-derives `hcover ⇒ hadd` (Q6a), the
  **compact** Stone 57 recovery (Q6b) and the Stone 56 recovery (Q6d), with
  comparisons of types of the compact forms in both directions (Q6c, Q6c′),
  zero budgets (Q6e) and the classification (Q6f). It does **not** contain a
  separate re-derivation of the Stone 57 **two-term** recovery, although the
  auditor's report and test matrix are worded broadly ("57 (duas formas)").
  That recovery exists in the module, is among the 32 declarations certified
  in Q0, and Q5 re-derives the additive two-term estimate, which can be
  specialized through `hcover ⇒ hadd`. The evidence is described here with
  its real scope; the precision was recorded in the integration tape, is
  repeated in the publication report and is reaffirmed by the reviewer's
  errata C1 (its point C1-4). It is not an errata issued by the QA1.

These precisions qualify the reports of tests and descriptions; they
required no change to the module and no new compilation. The review by Kimi
confirmed them as precisions (its §4), finding no new defect.

## Reading the Kimi review together with its errata C1

`kimi/RELATORIO_58-K-ADV.md` and `kimi/ERRATA_58-K-ADV-C1.md` are **two
documents of one review** and are to be read together; both are preserved
exactly as received, and no merged or silently corrected version is
produced. The reviewer identifies itself as "Kimi (Moonshot AI)", in the
same conversation instance that reviewed Stone 57 (where it identified
itself as "Kimi K3"); the historical credits of the project say "Kimi 3" and
are kept as written, without inferring a technical identity or altering the
past. Prior exposure is declared and the review is not blind.

The review records: the real order of work (hashes of the transport package
and of the internal manifests first; the public Git objects of the merge,
the candidate and the base — parents, trees, the blob of the module, the
diff +661/−1, the manifest `c376bbe9…`, and its own recomputation of the
counts 118 → 119 modules, 38,521 → 39,181 lines, 1,802 → 1,834 declaration
lines, 291 → 317 `#print axioms`, 32 declaration lines and 26 commands in
the module; then the first pass — the module in full and the interfaces
consumed, with the reviewer's own re-derivation of points A–F: the
additive cover and its reach (`hcover ⇒ hadd` re-derived; the converse false
on the witness with budgets `1/4, 1/4`), the truncated move (start,
permanence, saturation, increment for any real `t`), the prefixes and the
intermediate profiles (no owner reintroduced, overlapping regions charged at
each step, the endpoint by effective factors), the quantitative closure and
the real dependencies (the Stone 57 capstones with no use in code), the
degenerate cases and the expected failure, and the correspondence of the
docstrings with the code; then the second pass over the constructor's and
the auditor's materials, confirming D1–D3, T2/Q2 and C58-Q6 as precisions
of reporting). It records what the reviewer did **not** do: **no Lean
execution** (no build, no test, no elaboration of snippets); the CI logs of
runs 511/512 were not downloaded (their numbers — 320 outputs, 318 names, 87
multi-line lists, the checkouts — are attributed to the publication report
and to the coordination's conference, and the verdict does not depend on
them); the SSH signatures were not verified; Zenodo and the Release were not
consulted. Verdict `PASS NO ESCOPO`, no finding.

**The errata C1** (2026-10-16, by the same instance, after the coordination's
conference recorded in the tape 58-K-C1) corrects four points of the
**report** and keeps the verdict; it is not an additional mathematical
review and not an errata of the QA1. Where it corrects, its wording
prevails over the corresponding passages of the review:

1. **The transport package's manifest is 16/16, not 6/6.** The reviewer had
   run `sha256sum -c` with the output truncated to the last five lines and
   had inspected only the six originals; the errata re-extracts the
   persistent package (17 files, all paths safe) and verifies the manifest
   in full: 16/16, covering every file except the manifest itself (six
   originals, four Lean modules and three configuration files of context,
   `CONTEXTO_GIT.tsv`, the tape and a read-me). The six originals had been
   individually checked against the tape and were correct. The reviewer
   distinguishes the activity declared at the time from the later full
   re-verification and does not claim the latter retroactively.
2. **Divisions in the module.** The sentence "there is no division in the
   module" was too broad. The errata's scan of the source with comments and
   docstrings removed finds 39 code lines containing `/`, all of them
   divisions by the fixed non-zero constants `2`, `113` and `40000` (the
   regime `1/40000`, the exponents `6·D_s/113`, `4·D_s/113`, `2/113`, the
   decay `−(n i)/2`); **none** divides by a budget `δ i`, an accumulated
   capacity, a difference of profiles, `Cf` or any variable quantity of the
   data. The coordination reproduced that count by a documentary scan, not
   by Lean execution. The same precise wording applies to the summaries of
   the constructor and the auditor ("nothing divided" is to be read as
   "nothing divided by budgets, capacities or differences"); their originals
   are preserved.
3. **Raw profiles versus effective factors in the auditor's Q2.** For
   `η ≠ η₀` in `Q2_hadd_global` the **raw profiles** are both `1/4`; the
   **effective factors** are both `1/4` when the polymer touches `R` and both
   `1` when it does not; the effective difference is zero in both cases,
   which is the fact used in the proof together with the non-negativity of
   the sum. The review's phrase "factors equal to 1/4 off the witness
   coordinate" is corrected accordingly.
4. **Activities actually performed and the traceability of the sampling.**
   The opening "Nenhum." of the review's §5 is corrected to: no Lean test or
   build was executed; there were Git custody and hash checks, counts on the
   Git objects, the full reading of the source and of the third-party
   evidence, and a scalar numerical sampling in Python of
   `move`/`abs_move_add_sub_move_le`, which is not a formal proof. The
   script, the parameters or seed and the output of that sampling were **not
   preserved** (ephemeral environment, cleaned between sessions); the figure
   "10⁵ random points" in the review is not auditable from records; the
   errata does not repeat the sampling and does not reconstruct a record to
   present it as an earlier execution. It is recorded here as a declared
   activity with a traceability limitation, **not used as proof or as
   reproducible numerical evidence**; the reviewer states that the verdict
   never rested on it. No additional numerical artifact was received.

A fifth point (C1-4 in the errata's numbering) harmonizes the review's
sentence on the auditor's Q6 with the precision C58-Q6 above. The errata
also states that the temporary directory of the original review had been
cleaned, so that every re-verification in it was made on a fresh extraction
of the persistent transport package, and that the custody checks on the Git
objects were not redone (the target was reaffirmed and the hash of the
standalone module re-confirmed).

## Records for the consolidation

- **No documentary record on the module**: neither the QA1 nor the review
  found an imprecision in the candidate or in its docstrings; the precisions
  E1–E6 of the construction tape were incorporated in the docstrings of the
  integrated module before the audit.
- **D1–D3, T2/Q2, C58-Q6 and C1** — recorded above; the originals are not
  edited; the corrections of reporting are not defects of the code and not
  additional audits.
- **CI count 320/318.** The runs 511 and 512 emit 320 axiom lists (317 of
  the build + 3 of the workflow step), all standard, for 318 distinct
  names: two workflow outputs repeat names of the build (multiplicity 2) and
  the third, `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name absent
  from the build's list (not a new theorem); 87 of the 320 lists are printed
  across lines in those runs (86 of the 317 in the QA1 clean build); the
  parsing recomposes each list up to its closing bracket and checks names and
  multiplicities, not only the total. The 26 commands of the module are
  included. The 32 certificates of Q0 and the 3 of Q5 are the auditor's own
  and are not added to the 320.
- **Reporting precision on dependencies.** "119 built / 0 replayed" refers to
  the project modules in the clean builds of the constructor and of QA1 and
  in the CI. On the constructor's bench the Mathlib cache servers were denied
  by the session's network policy, so the pinned dependencies were **compiled
  from source once, as a preparation of the bench** (5,826 targets, 0
  errors), and the clean rebuild of the candidate then records them as 0
  built / 1,332 replayed — with 4,599 dependency warning blocks replayed from
  that preparation, separate from the 114 project blocks; the QA1 log
  records 0 / 0 with no dependency diagnostics (a reuse of its Stone 57
  cache); on the CI runner (runs 511–512) the nine `Built` targets outside
  `LatticeGauge` are the Mathlib cache tool — four Lean modules (`Cache.IO`,
  `Cache.Hashing`, `Cache.Requests`, `Cache.Main`), their four C objects and
  the executable `cache` — not nine rebuilt packages; the nine package
  revisions are verified against the manifest in a separate step, and the
  remaining dependency artifacts are obtained from the cache. The phrase
  "compiled from source" describes the constructor's one-time preparation
  of its bench, not the rebuild of the candidate, not the QA1 reproduction
  and not the CI.
- **Commit identity.** The candidate `d942edd3…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH signature header present, trailers `Co-Authored-By: Claude Fable 5.1`
  and `Claude-Session`), accepted by the precedent of Stones 52–57; the QA1,
  the review and this consolidation record the signature as present, not as
  independently authenticated; identity and signature were not redone.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the seven materials against the reference hashes supplied by
the coordinator in the consolidation tape (and, for the publication report,
against the original kept on the publisher's bench); the internal manifest
of the QA1 package (36 entries, all verified; no absolute paths, path
traversal, duplicates or symbolic links; 39 entries, 37 files and 2
directories; CRC without errors); the byte-identity of the standalone QA1
report and of the two matrices with their copies inside the package; the
correspondence between the candidate commit, the pull request, the merge
commit and the CI runs of `main` (PR #42; runs 511 and 512; parents, root
tree and `Phase3/` tree of `69706b9a…`); the identity of the `Phase3/` tree
of this documentary commit with that of `69706b9a…` (`58a60e8b…`); the
historical manifests of `docs/audits/stone52/` to `stone57/` (20, 9, 8, 9, 9
and 12 entries, all verified, no self-inclusion). The Zenodo record of
Version 57 could not be reached from the consolidating session; its
publication is recorded as confirmed by the coordinator, and the Release
metadata as read through the GitHub API.

Reported by the auditor and the reviewer and **not** re-executed here: the
build, the `#print axioms` runs, the tests and the mathematical readings; no
Lean was executed in this consolidation. Internal manifest integrity is not
by itself proof of authorship or of the execution of those builds; the
primary machine evidence for the integrated code is the CI history of
`main` (runs 511 and 512, see `RESULTS.md`).
