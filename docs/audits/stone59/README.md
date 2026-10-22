# Stone 59 — independent evidence: QA1 reproduction, two adversarial reviews with their errata, and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 59 candidate `dcd6e6b18a909914dd789667d9830bff106bc762` (see
[`docs/stone59/RESULTS.md`](../../stone59/RESULTS.md)), integrated on `main` at
`1dab07ab9da3052c7b957f858ccaf084501ecf4d` (PR #44): the audit evidence
package of the QA1 reproduction with its report and its two matrices, the
adversarial review by Gemini in three files (the first part as received, the
continuation and the errata C1 as transcriptions by the coordination), the
adversarial review by Kimi together with its errata C1, the publication
report of the constructing/publishing instance with its operational package
(the two CI logs), and a portable log-reading script written afterwards by
the coordination. It follows the organization of
[`docs/audits/stone58/`](../stone58/README.md), with two additions: a second
adversarial reading (Gemini) and the operational package of the publication.
No complementary execution on a third platform was received for this stone,
and none is recorded. The QA1 package is the primary record of the audit;
its report and matrices are extracted here only for reading convenience and
are byte-identical to the copies inside the package. Nothing in this
directory is a Lean module: the packages contain disposable test files
(including tests that are *expected to fail*), build and CI logs and
matrices, and none of it enters the `LatticeGauge` library, the
`lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices
are in Portuguese or mixed; the Gemini review is in European Portuguese);
they are not translated, normalized or edited. The constructor's own
materials (the construction report `RELATORIO_59-AL.md`, 19,959 bytes,
SHA-256 `a62a05dc8d981981df2ec724cf1ec6f7f5b3be90d49bf8177e423f626d2e10b7`,
the package `STONE59L_evidence.zip`, 298,025 bytes, SHA-256
`b355625a80de9bc6c165de366f684c1bb5e8dd5d41fb8f002e850d682358c823`, internal
manifest 31/31, with its bundle, diff, matrices and tests T1–T8x, and the
bundle `stone59.bundle`, 9,868 bytes, SHA-256
`7295ab50ff2288d051390dff69c28a4c5a014470246f9e39aa963647ebd5f279`) are
**not** part of this collection: they are the implementer's material, not an
audit; the audit and the reviews cite them by hash. The transport packages
prepared by the coordination for the reviewers and for the publishing
instance (`PEDRA59_PUBLICACAO.zip`, 407,880 bytes, SHA-256
`51b0a801b5eb034dffbecf864875f941f757a3727a2b71bc5c50f2799af12e01`, 16 files,
internal manifest 15/15; `PEDRA59_CONSOLIDACAO.zip`, 295,834 bytes, SHA-256
`753ef57612f4b66838995522fc6f612e2940fa0b156577acb04e3ad212fd40e3`, 19
files, internal manifest 18/18; the reviewers' input packages
`PEDRA59_KIMI_INPUTS.zip` and `PEDRA59_GEMINI_INPUTS.zip`, whose hashes are
recorded in the respective reviews) are packages of copies and context, not
audits, and are not in the tree.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra / Can (AI model) | different model family from the constructor | tapes (feasibility and construction 59-AL, integration 59-P, this consolidation); reading of the module, the reports, the packages and the logs; conference of Git objects and publication metadata; after the integration, a documentary conference of the two CI logs re-read through the GitHub tool and the writing of the script `tools/verify_ci59.py`; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | feasibility tests (gate 59-A, four elaboration attempts), Lean implementation of the module, local commit and bundle with the constructor's API tests T1–T8x and a clean rebuild of the 120 modules (gate 59-L), then, after QA1 and the two readings, push, pull request, merge and CI follow-up (59-P), and this consolidation, in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (the commit reconstructed from the bundle; dependencies reused from its Stone 57/58 bench, materialized then from the Mathlib community cache at the nine manifest revisions, 9/9 revisions checked, no `lake update`, not recompiled; project artifacts removed before the build; 120 modules built, 0 replayed, exit 0; own `#print axioms` of the 44 declarations; own tests Q0–Q8x; the constructor's tests T1–T8x re-executed in a second pass); preliminary conclusions recorded before opening the constructor's material | **not blind** (prior exposure to the earlier stones declared; the constructor's report read beforehand to identify the target); not a different model family; not human review |
| Adversarial review and errata (first) | Gemini (interface web), as the document identifies the reviewer | **different model family** from the constructor, the QA instance, the architect and the other reviewer | review by reading and mathematical analysis of the module and of the Stone 58 module, with a textual comparison of the transport manifests; **no Lean execution, no hash recomputation**; one errata, prompted by the coordination's conference, received as a chat message and transcribed | **not blind** (prior exposure to the Version 58 Zenodo record and to the authorial comments of the sources declared); reading only; the technical continuation and the errata are transcriptions, not files exported by the reviewer |
| Adversarial review and errata (second) | Kimi (Moonshot AI), as the documents identify the reviewer | **different model family** from the constructor, the QA instance, the architect and the other reviewer | review by reading and mathematical analysis of the module and the interfaces consumed, with own custody checks (hashes of the transport package; the Git blobs of the 125 packaged files, the `Phase3/` and root trees recomputed and compared with the public base; the diff of two paths; the counts); **no Lean execution**; one errata by the same instance, prompted by the coordination's conference, correcting four points of its own report | **not blind** (same conversation instance as the Stone 57 and 58 reviews; the tape disclosed the target); reading only; the commit object was not yet on GitHub, so its authorship, message and signature were not authenticated by the reviewer; did not consult the CI logs, Zenodo or the Release |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions, manual publication of Version 58; in this round, the conference of the packages, the matrices and the logs together with the architect | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model. No
Lean execution is attributed to GPT Astra / Can, to Gemini, to Kimi or to
the coordination. The historical credits of "Kimi 3" and, for Stone 57,
"Kimi K3" are preserved as written; the Stone 58 and 59 documents identify
the reviewer as "Kimi (Moonshot AI)" and no build or version is inferred.
The Gemini review identifies itself only as "Gemini (interface web)"; the
model name suggested by the coordination when inviting the review is not
promoted to a technically verified identity, and the historical credit
"Gemini 3 Pro" of the early phases is a record of other work. The
historical credits of "Manus AI 1.6" and the Stone 57 execution on the
"Manus Sandbox" platform are records of other stones and are not attributed
to Stone 59.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_59_evidence.zip`](packages/QA1_59_evidence.zip) | `b86b026ee1b1d9f9ff38ef7cb9e9e9e44c829dadd9d7b6e94a381ee692fa9eda` | Fable 5.1, QA instance | `dcd6e6b1…` (candidate, reconstructed from the bundle; published as [PR #44](https://github.com/consensusframework/yang-mills-mass-gap/pull/44), merge `1dab07ab…`) | `PASS NO ESCOPO` | 2026-10-18 (clean build 13:31–13:52 UTC) |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_59-QA1.md`](reports/RELATORIO_59-QA1.md) | `acb23db6a5f3ed28ce015476a981b5b31681429c92a3090b74a33c3ef5944ade` | Fable 5.1, QA instance | `dcd6e6b1…` | `PASS NO ESCOPO` | 2026-10-18 |
| 3 | QA1 declaration matrix (extracted) | [`reports/59_QA1_DECLARATION_MATRIX.tsv`](reports/59_QA1_DECLARATION_MATRIX.tsv) | `e7c5d135194e3befbdf3f0f768a5fbd741a8dd73181a71ce802150392b3411db` | Fable 5.1, QA instance | `dcd6e6b1…` | 44 items (36 theorems, 8 definitions) | 2026-10-18 |
| 4 | QA1 test matrix (extracted) | [`reports/59_QA1_TEST_MATRIX.tsv`](reports/59_QA1_TEST_MATRIX.tsv) | `61deef91ca1abb103472a0e4ddaf95830857f6322adea09d92dfb370864da5ea` | Fable 5.1, QA instance | `dcd6e6b1…` | Q0–Q6 positive, Q7 by `#check` and grep; Q8x expected application failure; T1–T8x (constructor's) re-executed | 2026-10-18 |
| 5 | Adversarial review (Gemini), first part as received | [`gemini/RELATORIO_59-G-ADV_PARTE1_RECEBIDA.txt`](gemini/RELATORIO_59-G-ADV_PARTE1_RECEBIDA.txt) | `e6a3572af44a27981627765c66b71dc625c2cb6769aa0126f32eec89b7f19f5f` | Gemini (interface web) | `dcd6e6b1…` (candidate) and the base `52cc0915…`, by the packaged files | (verdict in the continuation) | 2026-10-18 (date stated in the document) |
| 6 | Adversarial review (Gemini), technical continuation, transcribed | [`gemini/RELATORIO_59-G-ADV_CONTINUACAO_TRANSCRITA.md`](gemini/RELATORIO_59-G-ADV_CONTINUACAO_TRANSCRITA.md) | `2447694dd349243fde794dd4f5f172a1d46271f35ef265757333a793e7821a97` | Gemini (interface web); transcription by the coordination of a chat message | `dcd6e6b1…` | `PASS NO ESCOPO` | not recorded in the transcription |
| 7 | Errata C1 of the Gemini review, transcribed | [`gemini/ERRATA_59-G-ADV-C1_TRANSCRITA.md`](gemini/ERRATA_59-G-ADV-C1_TRANSCRITA.md) | `db39562fdf6a430758c0d3b7784d19c84da62a026f5ed425a5d445f2fcc0f744` | Gemini (interface web); transcription by the coordination of a chat message | applies to items 5–6; the scientific target unchanged | verdict `PASS NO ESCOPO` maintained; three corrections of the report | not recorded in the transcription |
| 8 | Adversarial review (Kimi) | [`kimi/RELATORIO_59-K-ADV.md`](kimi/RELATORIO_59-K-ADV.md) | `220be8715e589b2a24bf843b4ffefe133b984f9893c305cdbb555bc3956f56ca` | Kimi (Moonshot AI) | `dcd6e6b1…` (candidate, by the packaged files, trees recomputed) and `52cc0915…` (base, via the public Git objects) | `PASS NO ESCOPO` | 2026-10-19 |
| 9 | Errata C1 of the Kimi review | [`kimi/ERRATA_59-K-ADV-C1.md`](kimi/ERRATA_59-K-ADV-C1.md) | `891875aab9ffe791519c5a7f65dd1e4703ad7c42be36e4864eb6ee7b8bff846f` | Kimi (Moonshot AI), same instance | applies to item 8 (hash `220be871…`); the scientific target unchanged | verdict `PASS NO ESCOPO` maintained; four corrections of the report | 2026-10-19 |
| 10 | Publication report (FITA 59-P) | [`publication/RELATORIO_59-P.md`](publication/RELATORIO_59-P.md) | `5e8fbc7b742275d96526ebfc55be5569a584491fd53c2658c559b59735e9e595` | Fable 5.1, constructing/publishing instance | `dcd6e6b1…` → `1dab07ab…` | n/a (record) | 2026-10-21 |
| 11 | Publication operational package (the two CI logs) | [`packages/STONE59P_evidence.zip`](packages/STONE59P_evidence.zip) | `54b0e4dc098225556a0619174b66599c854b0d2015160deee9725bb019aadae2` | Fable 5.1, constructing/publishing instance | runs 515 (checkout `edcb4fde…`) and 516 (checkout `1dab07ab…`) | n/a (record) | 2026-10-21 |
| 12 | Portable CI-log reading script | [`tools/verify_ci59.py`](tools/verify_ci59.py) | `5f110a9ea442b15bdbe3eff3077b7bd7f6d7fd2a04d576a8cb674db59a7e25d4` | GPT Astra / Can, coordination | reads items 11 and the frozen module source; no Lean | n/a (tool; see C59-P2) | 2026-10-21 |

The eleven hashes of items 1–11 were supplied as references by the
coordinator in the consolidation tape (the hashes of items 10 and 11 as
the publisher's own references, those of the QA1 and of the Kimi errata as
computed by the coordination on the files received) and match the files
received; the publication report and its package are the originals kept on
the publisher's bench. SHA-256 of every file of this directory except the
manifest itself: [`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers
this README, `PROVENANCE.tsv`, the eleven materials and the script: 14
entries; no self-inclusion). Machine-readable provenance:
[`PROVENANCE.tsv`](PROVENANCE.tsv) (12 columns, 12 materials).

## The QA1 package

`packages/QA1_59_evidence.zip` (38 entries: 36 files and 2 directories,
`tests/` and `builder_tests_rerun/`, at the root of the archive; internal
manifest `SHA256SUMS_59-QA1.txt`, 35 entries — every file of the package
except the manifest itself). Contents: the report,
`PRELIMINARY_CONCLUSIONS_first_pass.md` (written before the auditor opened
the constructor's tests, matrices, logs and scripts), the two matrices,
`environment.txt` (the cloud container of the Stone 57 and 58 audits, which
survived; elan 4.2.4; Lean 4.15.0, Lake 5.0.0-1165156; clone with the push
URL disabled and a detached worktree at the candidate `dcd6e6b1…`,
reconstructed from the bundle through a temporary local ref; manifest
SHA-256 `c376bbe9…1227`; the `.lake/packages` dependencies materialized in
the Stone 57 audit from the Mathlib community cache and moved into the
worktree, 9/9 revisions checked, not recompiled), `prebuild_artifacts.txt`
(project build artifacts removed before the build: none left),
`build_full_clean.log` (SHA-256
`42817399cb566dffab0f584e26e94eb9bbad6aa16455f37b97b6b36ad21dd219`; single
integral `rm -rf .lake/build && lake build`, 2026-10-18T13:31:47Z →
13:52:03Z, exit 0, 1,216 s, **120 modules built, 120 distinct names, 0
replayed**, 0 errors, 361 certificates all standard, 104 of them printed
across lines, 0 `sorryAx`; dependencies 0 built / 0 replayed with no
dependency diagnostic emitted — a reuse of the cache, which says nothing
about the warnings of a recompilation of the dependencies), its `.result`
and instants, the manifests before and after the build (identical),
`compare_warning_blocks.py` and `warnings_block_comparison.txt` (the full
multi-line warning blocks against the Stone 58 baseline — the QA1 log of
Stone 58 inside `docs/audits/stone58/packages/QA1_58_evidence.zip`, whose
external and internal manifests the auditor validated first: 114 blocks of
`LatticeGauge/`, identical multiset, 113 distinct file:line pairs, **0 in
`ActivityProfileDampingOptimalCover`**, the comparator relabelled for the
Stone 59 module), `tests/` (the `.lean` files Q0–Q6 and Q8x, their final
logs and the preserved attempt logs of the auditor's own slips) and
`builder_tests_rerun/` (the logs of the constructor's `T59L_api_tests.lean`
and `T59L_T8x_EXPECT_FAIL.lean` re-executed on the auditor's bench, with
the same results). Logs are not duplicated outside the package. The QA1
declaration matrix lists the 44 declarations of the module with lines and
names equal to the constructor's matrix. The log `build_full_clean.log` of
this package is the warning baseline used by the publication (59-P) and by
the script of item 12.

Key results reported by the auditor (not re-executed here): 361/361
certificates in the clean build and **44/44** in the test Q0, all equal to
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; the 44 of Q0 are
the auditor's checks and are not added to the 364 outputs of the CI;
`#check` of the two capstones, the two comparisons, the two recoveries, the
two exact identities, `exists_optimal`, `optimalBudget` and `minCost` (the
hypothesis `hreach` visible in their types) and the interfaces consumed from
Stones 58, 56 and 52-E, with the absences verified on the elaborated types
(no minimizer, budget or decomposition supplied by the user, no `m > 0`, no
disjointness, no `r i ⊆ R`, no separation `s`/`R`, no unit background, no
`δ ≤ 1` on the budgets compared, no sign condition, no `DependsOnlyOn`;
`0 ≤ Cf` derived); `Reaches ↔ ∃ admissible` re-derived from the definitions
and the clipping re-proved by the auditor's own case split, with the
**necessity of the profile bounds** for the clipping exhibited (a profile
value `2` on a polymer touching `R` and `r 0`: the budget `2` covers, its
clip `1` does not) (Q1); the closedness of the cover set over all polymers
(no `Fintype (Polymer N)`), the compactness of the box, the non-emptiness
under reach, the continuity of the cost, the existence on the box and its
promotion to **all** admissible budgets by clipping, re-proved without
`exists_optimal`, the `m = 0` case, and the cost unbounded on the
unrestricted admissible set (so that no compactness of that set is used)
(Q2); equal costs of two minimizers, `B* = 0 ↔` equal effective factors,
`m = 0` with raw profiles outside `[0, 1]` off `R` (`a′ = −7`), `R = ∅`
with raw values `1/3` and `2/3`, a common factor `1/2` on `R` with raw
differences off `R` (`B* = 0`, equal functionals), the algebraic identities
for arbitrary reals separated from the typed domain of `B*`, and the
classification of `rfl` between proof terms as proof irrelevance (Q3); the
**global witness** — `a ≡ 1/4`, `a′ = 3/4` at `η₀` and `1/4` elsewhere,
scales `(0, 4)`: admissibility of `(1/4, 1/4)` and `(0, 1/2)` for **every**
polymer, `δ 0 + δ 1 ≥ 1/2` for every admissible budget, the lower bound and
**`B* = (1/2)·e^{−2}`** through `minCost_eq_budget_of_isMin`,
`B* < 1/4 + e^{−2}/4`, the complete compact bounds strictly ordered when
`Cf > 0` and both `0` when `Cf = 0` (Q4; the contacts of `η₀` with `R`,
`r 0` and `r 1` by hypothesis); **non-uniqueness** with equal scales
`(0, 0)`: `(1/2, 0)` and `(0, 1/2)` admissible, distinct, both global
minimizers with `B* = 1/2` (Q5); the **own closure** — a minimizer taken
from `exists_optimal`, the two Stone 58 estimates applied directly, the two
forms and the comparisons with any admissible budget by minimality and
signs, without the new capstones, comparisons or wrappers; explicit
applications of **both** recoveries with `δ ≡ 7`; the types of the
recoveries and of the Stone 58 capstones definitionally equal in both
directions (Q6); the absence of the forbidden hypotheses in the types, the
optimization without `β`, the Stone 57 capstones unused and the limits of
the header checked (Q7, by `#check` and grep); the configuration without
reach (a change `1/2` on a polymer touching `R` and no region): `¬ ∃
admissible` and `¬ Reaches` **proved**, and the application with `m = 1`
failing on the single obligation `typedTouchesSupport η₀ (r₁ 0)`, negated by
its hypothesis (Q8x), classified as an impossible hypothesis and not as a
counterexample. The auditor's disposable tests emitted 62 warnings (Q4: 6,
Q5: 4, Q6: 52, unused binders in the `example`s comparing types), separate
from the 114 inherited warnings of the project and from the 0 of the new
module. The tests **T1–T8x** belong to the constructor (delivered in
`STONE59L_evidence.zip`, re-executed by QA1 in its second pass, which does
not change their authorship; the positive test has 13 `#check` and no
`#print axioms`); the tests **Q0–Q8x** belong to QA1. The geometric tests
are parameterized by `typedTouchesSupport` hypotheses; no concrete lattice
instance is constructed.

## Reading the QA1 record: the observations of its §6 on the constructor's report

The QA1 report, the two matrices and the archived preliminary conclusions
are preserved exactly as received. **No errata was issued by the auditing
instance**, and none is attributed to it. The audit recorded, in its second
pass (§6 of its report), five observations on the **constructor's** report,
matrices and scripts (`RELATORIO_59-AL.md` and `STONE59L_evidence.zip`),
which the coordination accepted in the integration tape 59-P and which the
publishing instance recorded in the body of PR #44. None of them concerns
the candidate, its hypotheses, proofs or compilation results, and the
verdict `PASS NO ESCOPO` stands. The materials are to be read with them:

1. **Counts of the constructor's package and the lakefile.** The package
   has 38 entries = 32 files + 6 directories, manifest 31/31 (the 32nd file
   being the manifest). The sentence "0 base files changed" of the
   constructor's report is imprecise: `Phase3/lakefile.toml` is a
   pre-existing file and was modified (the new glob only); the 119 modules
   and every other path are intact.
2. **A hypothesis that does not exist, and the reach of `omit`.** The
   constructor's remark that "no positivity hypothesis (`t ≥ 0`) was needed"
   refers to a parameter of the Stone 58 route that has no counterpart in
   this optimization; the non-negativity of this stone is in `Admissible`,
   in the profile bounds and in `β ≥ 0`, with `0 ≤ Cf` derived. The
   constructor's report attributes the `omit` of the three measurable
   instances to four theorems; the source applies it only to the two
   comparisons of right-hand sides, the two recoveries keep the instances,
   and the two exact identities carry a different `omit` (the four measure
   instances).
3. **Bench paths versus package paths.** The constructor's tests matrix
   names its files by their bench paths (`L/…`); in the delivered package
   they are under `tests/`.
4. **What T6 and T7 test.** `w_admissible` uses the joint condition
   `1/2 ≤ δ 0 + δ 1` with non-negativity and the weighted step is in
   `w_minCost`; T7 uses the **compact** form of Stone 58 and
   `mul_le_mul_of_nonneg_left`, and does not call
   `optimal_two_terms_le_additive_two_terms` as the constructor's
   description suggests; T6 applies `δ ≡ 7` to the compact form only (the
   auditor's Q6b applies both forms). The `rfl`s are between proof terms,
   as the test source itself notes.
5. **Baseline, replay and a textual slip.** The warning baseline of the
   constructor's rebuild is the QA1 log of Stone 58, not a CI log (as one
   sentence of its report says); the 4,599 dependency warning blocks of that
   rebuild are a replay of the one-time preparation of the constructor's
   bench, not a new compilation; and the abbreviation `c376bbe9…c227` in
   the summary table of the constructor's report is a textual slip for
   `…1227`, the hash of the base manifest (written in full elsewhere in the
   same report and in its artifacts).

These observations qualify the reports, matrices and scripts; they required
no change to the module and no new compilation.

## Reading the Gemini review together with its errata C1

`gemini/RELATORIO_59-G-ADV_PARTE1_RECEBIDA.txt`,
`gemini/RELATORIO_59-G-ADV_CONTINUACAO_TRANSCRITA.md` and
`gemini/ERRATA_59-G-ADV-C1_TRANSCRITA.md` are **three files of one review**
and are to be read in that order. The first is a copy, under a safe name,
of the file received from the reviewer's interface (`Texto
colado(20261018-205856).txt`), which ends at a cut inside its section 4; the
second is the coordination's transcription of the technical continuation
received as a chat message (it resumes, and partly repeats, the item at
which the first part was cut; conversational openings and closings omitted;
statements later corrected by C1 retained); the third is the coordination's
transcription of the errata, received as a chat message, with its imperfect
Markdown closing of the verdict preserved. **No integral original file of
the review exists**, and the transcriptions are not byte-equivalent to any
export by the reviewer; no hash issued by the reviewer is attributed to
them, and no cryptographic authorship is reconstructed from them. A later
consolidated document of this review exists on the coordination's side and
is **not** substituted here: the three files are the version used in the
integration (59-P). The reviewer identifies itself only as an instance of
Gemini in the web interface, without a local Lean toolchain or shell: the
review is by reading and mathematical analysis, with the manifests of its
transport package cross-checked textually and **no hash recomputed**; prior
exposure declared (the Version 58 Zenodo record and the authorial comments
of the sources, read as declared exposure and not as observed execution);
not blind; no report of the constructor, the QA1 or Kimi consulted.

The review records: the frozen target checked documentally (the commit,
parents, trees, blob, SHA-256 and manifest hash of the tape); the axes A–D
of its tape re-derived in its own words — the feasibility equivalence with
the role of the profile bounds located in one direction only, the
configuration without reach classified as a failure of the hypothesis and
not as a counterexample, the clipping with the two cases and the necessity
of the profile bounds (a change `2` covered by `δ = 2` and not by its clip),
the compactness of the box and the promotion of the minimum to all
admissible budgets, the definition of `B*` by choice carrying the existence
hypotheses, the positivity of the weights and `B* = 0 ↔` equal effective
factors, the uniqueness of the value against the non-uniqueness of the
vector and the proof irrelevance of `rfl`, the degenerate cases `m = 0` and
`R = ∅`, the separation of the algebraic interfaces (arbitrary real
profiles) from the typed ones, two examples of its own (a non-optimal
budget with coordinate `2 > 1`, and two distinct minimizers `(1, 0)`,
`(0, 1)` with repeated regions and a change `1`), the signatures of Stones
58 and 59 side by side, `0 ≤ Cf` derived and the `Cf = 0` case, the `omit`s,
the absence of parasitic hypotheses, the intentional dependency 58 → 59 →
recovery of 58, and the reach of the word "optimal" as restricted to the
budgets of a fixed family. Verdict `PASS NO ESCOPO`; no correction proposed
to the candidate.

**The errata C1** (received after the first pass, prompted by the
coordination's conference and not a finding of the first pass) corrects
three points of the **report** and keeps the verdict. Where it corrects, its
wording prevails over the corresponding passages:

1. **There is no definition `ActivityProfileMultiRegion.budget`.** Stone 58
   uses the theorem `ActivityProfileMultiRegion.budget_nonneg`, whose
   statement carries the expanded sum; in Stone 59, `budget` is a new
   definition and `budget_nonneg'` a theorem. The remark on a duplicated
   earlier definition is withdrawn.
2. **When the unrestricted set is not compact.** The set of admissible
   budgets without upper bound fails to be compact only when it is
   **non-empty** (under `Reaches`) and **`m ≥ 1`**; empty (reach failing) or
   with `m = 0` it is compact. The box `feasibleBox` is compact
   unconditionally.
3. **The nature of `χ`.** In the signatures of Stones 58 and 59, `χ : G → ℝ`
   is a measurable real function with `|χ| ≤ 1`, not assumed to be a group
   character.

The original wording stays in the received files; the precision is given
here. The code of the module was free of these inexactitudes.

## Reading the Kimi review together with its errata C1

`kimi/RELATORIO_59-K-ADV.md` and `kimi/ERRATA_59-K-ADV-C1.md` are **two
documents of one review** and are to be read together; both are preserved
exactly as received, and no merged or silently corrected version is
produced. The reviewer identifies itself as "Kimi (Moonshot AI)", in the
same conversation instance that reviewed Stones 57 and 58; the historical
credits of the project say "Kimi 3" and are kept as written, without
inferring a technical identity or altering the past. Prior exposure is
declared and the review is not blind; no report, test or opinion of the
other participants was consulted (the reviewer's package did not contain
them, by design).

The review records: its custody work — the transport package
`PEDRA59_KIMI_INPUTS.zip` (542,179 bytes, SHA-256 `f10ee151…`, manifest
131/131 with exact coverage), the module identical to the tape's hash, the
Git blobs of the 125 packaged files recomputed from their bytes, the
`LatticeGauge/` and `Phase3/` trees recomputed and equal to the tape's, the
root tree of the candidate recomputed from the public root of the base by
replacing the `Phase3/` entry and equal to the tape's, the base `52cc0915…`
confirmed as the public `main` with 123 of the 125 paths byte-identical to
its blobs and the two differences being exactly the declared ones (the new
module; one line of the lakefile), and the counts; then the first pass — the
module in full and the interfaces consumed, with the reviewer's own
re-derivation of the axes A–D: the feasibility equivalence (where the
profile bounds enter), the configuration without reach, the clipping (what
fails without the profile bounds), the attained minimum and its promotion
from the box to all admissible budgets, the definition of `B*`, the
positivity of the weights and `B* = 0`, uniqueness of the value and not of
the vector, its own examples with repeated regions and equal scales (a
one-parameter family of minimizers, a non-optimal budget of strictly larger
cost), the degenerate cases, the separation of interfaces, the signatures
side by side, the `omit`s, `0 ≤ Cf` derived, the direction of the
inequalities and the `Cf = 0` case, the closure refolded by hand, the
hypotheses searched for and not found, the hygiene of the source (divisions
only by fixed constants), the logical dependency on Stone 58, and the reach
of "optimal". It records what the reviewer did **not** do: **no Lean
execution** (no build, no test; the toolchain absent from its environment);
the constructor's test file not observed (not in its package, by design);
and the **commit object not authenticated**: `dcd6e6b1…` was not on GitHub
at the time of the review (the API answered "No commit found" and the fetch
was refused), so the association between the commit identifier and the
audited content was taken from the coordination, the reviewer having
verified independently the association content ↔ trees ↔ public base. That
limitation belongs to the moment of the review and is not rewritten now
that the commit is public through PR #44; it is not a failure of the
bundle, which the QA1 verified. Verdict `PASS NO ESCOPO`, no finding; a
recommendation that the next stage include a build of the module (which the
QA1 had, in fact, already done — the reviewer's package did not contain the
audit, by design).

**The errata C1** (2026-10-19, by the same instance, after the
coordination's conference) corrects four points of the **report** and keeps
the verdict; it is not an additional mathematical review and not an errata
of the QA1. The four observations are the coordination's, as the errata
itself states, not discoveries of the first pass. Where it corrects, its
wording prevails:

1. **The cost of `(1, 1)` in the reviewer's example.** With two regions of
   equal weight `w = exp(−n*/2)`, the cost of the budget `(1, 1)` is `2w`,
   not `w`; the minimum `w/2` and the family of minimizers `(t, 1/2 − t)`,
   `t ∈ [0, 1/2]`, stand, and `2w > w/2` remains strict.
2. **When the unrestricted set is not compact.** Non-compactness requires
   the set to be non-empty and `m ≥ 1`; the empty set and the `m = 0` case
   are compact. The existence uses the box only.
3. **`B(δ*) = minCost` for an arbitrary witness.** For a witness `δ*` of
   `exists_optimal` taken at random, the identification is **not**
   definitional (`Classical.choose` is opaque): it follows from
   `minCost_eq_budget_of_isMin` (or `budget_eq_of_isMin`), using the
   admissibility and minimality of `δ*`. The definitional unfolding applies
   when `δ*` is `optimalBudget …` itself, which is the route the module
   uses in its two capstones. The line of the review's table of findings is
   to be read with that distinction.
4. **Commands versus executions.** The "44 certificates, coverage 44/44" of
   the custody table are 44 `#print axioms` **commands** present in the
   source; none was executed by the reviewer, as its §5 already declared.

## Publication and the coordination's precisions C59-P1 and C59-P2

`publication/RELATORIO_59-P.md` and `packages/STONE59P_evidence.zip` are
preserved exactly as received from the publishing instance. The package
(24 entries: 20 files and 4 directories `ci/`, `evidence/`, `tools/`,
`qa1_baseline/`; internal manifest `SHA256SUMS_59P.txt`, 19 entries — every
file except the manifest itself) contains the two job logs as obtained
through the GitHub tool (`ci/run515.raw`, `ci/run516.raw`, JSON with the
field `logs_content`; their extracted texts, the versions with the
timestamps removed and the certificate maps), the publisher's analyzer
`ci/analyze59.py` and its two warning comparisons, the remote snapshots
before the push and after the merge, the push log, the ruleset read through
the API, the pull-request and merge records, the warning comparator and the
QA1 baseline log. The report records the custody of the materials, the
Etapa Zero checks (the remote at the base, no `stone59` ref, no open pull
request, the ruleset 22341147 active with `build-phase3` required and no
bypass), the push of the candidate, PR #44, run 515 (id 39605343046, job
119239976474; effective checkout `edcb4fde…`, the provisional merge, whose
parents and tree were verified locally), the merge `1dab07ab…` with the
expected head locked (parents base + candidate, trees equal to the
candidate's, the diff candidate → merge empty, all branches and tags
preserved), run 516 (id 39607407756, job 119247067798; effective checkout
`1dab07ab…`), and the inspection of both logs (120/0, manifest confirmed
twice, nine revisions, 114 warning blocks equal to the QA1 baseline, 364
outputs for 362 names, 105 multi-line lists, 44/44 of the module, no
`sorryAx`, the three outputs of the separate step identified). The direct
download host of the job logs was denied by the session's network policy;
the logs were obtained through the GitHub tool and are the texts preserved
in the package.

Two precisions, **by the coordination (conference of 2026-10-21)**, on the
publisher's delivery — not errata by the publishing instance, the QA1,
Gemini or Kimi — are recorded here and are to be read with the report:

- **C59-P1 — the count of the operational package.** The delivery message
  said "19 entries"; the ZIP has 24 entries = 20 files + 4 directories, and
  19 is the number of files covered by the internal manifest, which does not
  include itself. Integrity 19/19 and hashes correct; nothing concerns the
  code.
- **C59-P2 — portability of the analyzer.** The publisher's `ci/analyze59.py`
  reads the list of the 44 module names from a `certs_module.tsv` by an
  absolute path of the publisher's bench, a file not included in the
  package; the invocation suggested in §9 of the report is therefore not
  portable on its own. The original script stays in the package unchanged.
  The coordination wrote afterwards the script `tools/verify_ci59.py`
  (item 12), which receives the log, the frozen module source and the QA1
  baseline as arguments, checks the fixed hashes of the source
  (`61dde0c9…`) and of the baseline (`42817399…`), derives the 44 names from
  the source, requires the effective checkout SHA as printed by `git log`
  in the job, and reads the log (120 unique project builds, no project
  replay, success, no build error, 364 outputs for 362 names all standard,
  the 44 module outputs exactly once, the workflow `sorryAx` check
  completed, two manifest confirmations, nine revisions, the 114 project
  warning blocks equal as a multiset to the baseline, none in the new
  module); it does not execute Lean and does not modify its inputs. It was
  written after the integration and was not used by the publishing instance
  in the original publication; its first draft was adjusted to distinguish
  the text of `echo` commands containing `::error::` from an error actually
  emitted, and only the validated version is delivered. The coordination
  exercised it on the two original logs with conforming output, and this
  consolidation re-ran it on the two logs of item 11 from the root of the
  repository with the same result on each (`PASS documentary log checks`,
  effective SHA `edcb4fde…` for run 515 and `1dab07ab…` for run 516; 120
  built, 0 replayed, 114 warnings, 364 outputs, 362 names, 44 module
  outputs, 105 multi-line lists). It is an aid to reading the preserved
  evidence; it does not replace the inspection of the workflow, of the Git
  tree, of the effective revisions of the dependencies or of the logs of
  new runs, and the count of multi-line lists is observed, never imposed.

  ```sh
  # from the root of the repository, after extracting packages/STONE59P_evidence.zip into "$p59"
  python3 docs/audits/stone59/tools/verify_ci59.py --log "$p59/ci/run515.raw" \
    --module-source Phase3/LatticeGauge/ActivityProfileDampingOptimalCover.lean \
    --baseline "$p59/qa1_baseline/build_full_clean.log" --expect-sha edcb4fdeefddeb6e6d2291538b9bf47a9057735f
  python3 docs/audits/stone59/tools/verify_ci59.py --log "$p59/ci/run516.raw" \
    --module-source Phase3/LatticeGauge/ActivityProfileDampingOptimalCover.lean \
    --baseline "$p59/qa1_baseline/build_full_clean.log" --expect-sha 1dab07ab9da3052c7b957f858ccaf084501ecf4d
  ```

## Records for the consolidation

- **No documentary record on the module**: neither the QA1 nor the two
  reviews found an imprecision in the candidate or in its docstrings; no
  reviewer requested any change to the candidate, and no code was changed
  after the audits.
- **The five observations of the QA1 §6, the Gemini C1, the Kimi C1 and
  C59-P1/P2** — recorded above; the originals are not edited; the
  corrections of reporting are not defects of the code and not additional
  audits; the errata of Gemini and Kimi were prompted by the coordination's
  conference after the first passes and are not attributed to discoveries of
  those passes.
- **CI count 364/362.** The runs 515 and 516 emit 364 axiom lists (361 of
  the build + 3 of the workflow step), all standard, for 362 distinct
  names: two workflow outputs repeat names of the build (multiplicity 2)
  and the third, `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name
  absent from the build's list (not a new theorem); 105 of the 364 lists are
  printed across lines in those runs (104 of the 361 in the QA1 clean
  build); the parsing recomposes each list up to its closing bracket and
  checks names and multiplicities, not only the total. The 44 commands of
  the module are included. The 44 certificates of Q0 and those of the
  auditor's other tests are the auditor's own and are not added to the 364.
- **Reporting precision on dependencies.** "120 built / 0 replayed" refers
  to the project modules in the clean builds of the constructor and of QA1
  and in the CI. The constructor's bench reuses the pinned dependencies
  compiled from source once as a preparation of that bench during Stone 58
  (the cache servers being denied by the session's network policy), so its
  clean rebuild records them as 0 built / 1,332 replayed with 4,599
  dependency warning blocks replayed from that preparation, separate from
  the 114 project blocks; the QA1 log records 0 / 0 with no dependency
  diagnostics (a reuse of its cache); on the CI runner (runs 515–516) the
  nine `Built` targets outside `LatticeGauge` are the Mathlib cache tool —
  four Lean modules (`Cache.IO`, `Cache.Hashing`, `Cache.Requests`,
  `Cache.Main`), their four C objects and the executable `cache` — not nine
  rebuilt packages; the nine package revisions are verified against the
  manifest in a separate step, and the remaining dependency artifacts are
  obtained from the cache.
- **Commit identity.** The candidate `dcd6e6b1…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH signature header present, trailers `Co-Authored-By: Claude Fable 5.1`
  and `Claude-Session`), accepted by the precedent of Stones 52–58; the QA1,
  the reviews, the publication and this consolidation record the signature
  as present, not as independently authenticated; identity and signature
  were not redone. The merge `1dab07ab…` was created by GitHub.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the eleven materials and of the script against the reference
hashes supplied by the coordinator in the consolidation tape (and, for the
publication report and its package, against the originals kept on the
publisher's bench; for the constructor's copies of the QA1 and Kimi
materials, against the copies received in the integration tape); the
internal manifests of the QA1 package (35 entries, all verified; no
absolute paths, path traversal, duplicates or symbolic links; 38 entries,
36 files and 2 directories; CRC without errors) and of the publication
package (19 entries, all verified; 24 entries, 20 files and 4 directories);
the byte-identity of the standalone QA1 report and of the two matrices with
their copies inside the package; the correspondence between the candidate
commit, the pull request, the merge commit and the CI runs of `main`
(PR #44; runs 515 and 516; parents, root tree and `Phase3/` tree of
`1dab07ab…`); the Version 58 Release read through the GitHub API (tag
`zenodo-v58` → `52cc0915…`, published 2026-10-18T12:00:16Z, four assets with
the sizes and digests of the packaging delivery); the identity of the
`Phase3/` tree of this documentary commit with that of `1dab07ab…`
(`c3157cb9…`); the historical manifests of `docs/audits/stone52/` to
`stone58/` (20, 9, 8, 9, 9, 12 and 9 entries, all verified, no
self-inclusion); and the script of item 12 run on the two logs of item 11.
The Zenodo record of Version 58 was not consulted from the consolidating
session; its publication is recorded as confirmed by the coordinator.

Reported by the auditor, the reviewers and the publisher and **not**
re-executed here: the build, the `#print axioms` runs, the tests and the
mathematical readings; no Lean was executed in this consolidation. Internal
manifest integrity is not by itself proof of authorship or of the execution
of those builds; the primary machine evidence for the integrated code is the
CI history of `main` (runs 515 and 516, see `RESULTS.md`).
