# Stone 57 — independent evidence: QA1 reproduction, adversarial review, complementary execution and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 57 candidate `c936d4617f3e6f35ea1431c2fa9496b235940f5a` (see
[`docs/stone57/RESULTS.md`](../../stone57/RESULTS.md)), integrated on `main` at
`b66c255c83bba02dc8d53158279296bbf7ea005c` (PR #39): the audit evidence
package of the QA1 reproduction with its report and its two matrices, the
adversarial review by Kimi K3, the publication report of the
constructing/publishing instance, and — new in this stone — the evidence
package, report, checksum and delivery validation of a complementary
execution on the Manus Sandbox platform. It follows the organization of
[`docs/audits/stone56/`](../stone56/README.md), with one more kind of
evidence. The QA1 package is the primary record of the audit; its report and
matrices are extracted here only for reading convenience and are
byte-identical to the copies inside the package. Nothing in this directory is
a Lean module: the packages contain disposable test files (including tests
that are *expected to fail*), build logs and matrices, and none of it enters
the `LatticeGauge` library, the `lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are
in English or mixed); they are not translated, normalized or edited. The
constructor's own materials (the feasibility report and package of 57-A, the
construction report and package `STONE57L_evidence.zip` with its bundle,
diff, matrices and tests W1–W9/W8x) are **not** part of this collection: they
are the implementer's material, not an audit; the audit and the review cite
them by hash.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra / Can (AI model) | different model family from the constructor | tapes (feasibility 57-A, construction 57-L, integration 57-P, this consolidation); reading of the module, the reports, the packages and the logs; conference of Git objects and publication metadata; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | feasibility tests (57-A), Lean implementation of the module, local commit and bundle with the constructor's API tests W1–W9/W8x and a clean rebuild of the 118 modules (57-L), then, after QA1, push, pull request, merge and CI follow-up (57-P), and this consolidation, in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution on a fresh bench (dependencies from the Mathlib community cache at the nine manifest revisions, no `lake update`; no prior project artifacts; 118 modules built, 0 replayed, exit 0; own `#print axioms`; own tests Q0–Q8x; the constructor's tests W1–W9/W8x re-executed in a second pass); preliminary conclusions recorded before opening the constructor's material | **not blind** (prior exposure declared; the constructor's report read beforehand to identify the target); not a different model family; not human review |
| Adversarial review | Kimi K3 (AI model), as the review identifies itself | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis of the module, the Stone 56 interfaces, the matrices and the tests; own custody checks (hashes of the uploads, bundle verification, diff, trees, blobs and counts recomputed on the public Git objects of the base, the candidate and the merge); own parsing of the clean logs of QA1 and of the constructor; **no Lean execution** | **not blind** (the tape disclosed the target and the earlier results); reading only; did not receive the standalone 57-P report; did not download the full CI logs; did not consult Zenodo or the Release |
| Complementary execution | Manus Sandbox (platform, as declared; the model identifier was not exposed) | a third bench; the executed tests are the QA1 tests, byte-identical | directed execution on the integrated state `b66c255c…`: disposable checkout of the fixed SHA with the push URL disabled, Lean 4.15.0 / Lake 5.0.0, dependencies at the nine manifest revisions, Mathlib cache; `lake build` of the new module (104 modules of its import chain built, 0 replayed — not a full rebuild), Q0, Q3, Q4, Q5, Q8x and a `#check` of the two capstones re-executed | a re-execution of the auditor's tests on another bench, not new tests, not an independent re-derivation and not an additional mathematical audit; nothing is inferred about the model from the platform name |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions, manual publication; in this round, the documentary conference of the packages and logs | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model. No
Lean execution is attributed to GPT Astra / Can, to Kimi K3 or to the
coordination. The historical credits of "Manus AI 1.6" (earlier stones)
are preserved separately and are not attributed to this execution.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_57_evidence.zip`](packages/QA1_57_evidence.zip) | `e495b4760e9e174a1da37c5583c0cd12fc1f0c8431548826f073a209b0b790ea` | Fable 5.1, QA instance | `c936d461…` (candidate; published as [PR #39](https://github.com/consensusframework/yang-mills-mass-gap/pull/39), merge `b66c255c…`) | `PASS NO ESCOPO` (sem observações de mérito) | 2026-10-09 (clean build 12:55–13:08 UTC) |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_57-QA1.md`](reports/RELATORIO_57-QA1.md) | `59664df41f9e2b7cfa9058b99ea912c8c5ba27e4ecf733b6da71b729dbcb45ed` | Fable 5.1, QA instance | `c936d461…` | `PASS NO ESCOPO` | 2026-10-09 |
| 3 | QA1 declaration matrix (extracted) | [`reports/57_QA1_DECLARATION_MATRIX.tsv`](reports/57_QA1_DECLARATION_MATRIX.tsv) | `8b3d08afadc43ea8aa3039ad3bdeee81f5b745188c2d574bf7468642a3915b66` | Fable 5.1, QA instance | `c936d461…` | 22 items (19 theorems, 3 definitions) | 2026-10-09 |
| 4 | QA1 test matrix (extracted) | [`reports/57_QA1_TEST_MATRIX.tsv`](reports/57_QA1_TEST_MATRIX.tsv) | `caf32cfc5ab94544e6644d8e3c3998f1b0c7cbc123f20968f28a1b17d8ab88eb` | Fable 5.1, QA instance | `c936d461…` | Q0–Q7 positive; Q8x expected application failure; W1–W9/W8x (constructor's) re-executed | 2026-10-09 |
| 5 | Adversarial review | [`kimi/RELATORIO_57-K-ADV.md`](kimi/RELATORIO_57-K-ADV.md) | `6c3aaf85e6304dab9a4710e74bc051e3659c185763df783e698d1e9ad7c58b74` | Kimi K3 | `c936d461…` (sources), `b66c255c…` (merge) and `95091fdd…` (base), via the public Git objects | `PASS NO ESCOPO` | not dated in the document; received 2026-10-09 |
| 6 | Publication report (FITA 57-P) | [`publication/RELATORIO_57-P.md`](publication/RELATORIO_57-P.md) | `f4cc55596eeff13a8097e6e12a34a93ec80227586fb26513beb21d481b4f5648` | Fable 5.1, constructing/publishing instance | `c936d461…` → `b66c255c…` | n/a (record) | 2026-10-09 |
| 7 | Manus execution evidence package | [`packages/MANUS_57_EXEC_evidence.zip`](packages/MANUS_57_EXEC_evidence.zip) | `b1cca824e77a2050b78d4ffe340f4b57080d5700cd2b156eaa87cef796e268e3` | Manus Sandbox (platform) | `b66c255c…` (integrated state) | `EXECUÇÃO CONCLUÍDA NO ESCOPO` (in the report) | 2026-10-09 (execution 19:51–20:13 UTC) |
| 8 | Manus execution report (PDF) | [`manus/RELATORIO_57-MANUS-EXEC.pdf`](manus/RELATORIO_57-MANUS-EXEC.pdf) | `97b77bebdf4f3f9c4a37cc6a3d0fe70a0c25c5dbbe4aab0af2e06db3f344c38c` | Manus Sandbox (platform) | `b66c255c…` | `EXECUÇÃO CONCLUÍDA NO ESCOPO` | received 2026-10-09 |
| 9 | Manus package checksum (as received) | [`manus/MANUS_57_EXEC_evidence.zip.sha256`](manus/MANUS_57_EXEC_evidence.zip.sha256) | `a8fa9370755bbcb95792aa35f5ab58d571e44d160c625c15b4174550f9821781` | Manus Sandbox (platform) | — | digest of item 7, with the absolute path of the origin bench | received 2026-10-09 |
| 10 | Manus delivery validation | [`manus/PACKAGE_DELIVERY_VALIDATION_57.txt`](manus/PACKAGE_DELIVERY_VALIDATION_57.txt) | `e5be1050c3adc369bb591047ec92d2bb97517c55a4c8a40faf9f567f896e2774` | Manus Sandbox (platform) | — | internal manifest 36/36 OK; `unzip -t` no errors; digest of item 7 | received 2026-10-09 |

The ten hashes were supplied as references by the coordinator in the
consolidation tape (the hash of the publication report as the publisher's
own reference) and match the files received; the publication report is the
original kept on the publisher's bench. SHA-256 of every file of this
directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv` and the ten materials: 12 entries; no self-inclusion).
Machine-readable provenance: [`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_57_evidence.zip` (48 entries: 46 files and 2 directories,
`tests/` and `builder_tests_rerun/`, at the root of the archive; internal
manifest `SHA256SUMS_57-QA1.txt`, 45 entries — every file of the package
except the manifest itself). Contents: the report,
`PRELIMINARY_CONCLUSIONS_first_pass.md` (written before the auditor opened
the constructor's material), the two matrices, `environment.txt` (fresh
cloud container, 2026-10-09; elan 4.2.4; Lean 4.15.0, Lake 5.0.0-1165156;
clone with the push URL disabled; candidate `c936d461…`; manifest SHA-256
`c376bbe9…1227`), `deps_cache_get.log` with its instants (the Mathlib
community cache, 5,826 files), `prebuild_artifacts.txt` (`.lake/build`
absent before the build), `build_full_clean.log` (SHA-256
`5bd23aab5d2ab848c915557dfa6a6487b9beb4326e7edef73a053b9aca9a386f`; single
integral `lake build`, 2026-10-09T12:55:31Z → 13:08:45Z, exit 0, 794 s,
**118 modules built, 0 replayed**, 0 errors, 291 certificates all standard,
74 of them printed across lines, 0 `sorryAx`; dependencies 0 built / 0
replayed with no dependency diagnostic emitted — a reuse of the cache, which
says nothing about the warnings of a recompilation of the dependencies), its
`.result` and instants, the manifests before the dependencies, before and
after the build (identical), `compare_warning_blocks.py` and
`warnings_block_comparison.txt` (the full multi-line warning blocks against
the Stone 56 baseline — the QA1 log of Stone 56 inside
`docs/audits/stone56/packages/QA1_56_evidence.zip`: 114 blocks of
`LatticeGauge/`, identical multiset, 0 in the new module), `tests/` (the
`.lean` files Q0–Q7 and Q8x, their final logs and the preserved first-attempt
logs of the auditor's own slips) and `builder_tests_rerun/` (the
constructor's `T57L_api_tests.lean` and `W8x` re-executed on the auditor's
bench, with the same results). Logs are not duplicated outside the package.

Key results reported by the auditor (not re-executed here): 291/291 own
certificates in the clean build and 22/22 in the test Q0 (19 theorems + 3
definitions) equal to `[propext, Classical.choice, Quot.sound]`, no
`sorryAx`; `#check` of the two capstones and the two interfaces with the
absences verified on the elaborated types (no `owner`, no `m > 0`, no
disjointness, no `r i ⊆ R`, no separation `s`/`R`, no unit background, no
`δ i ≤ 1`, no `DependsOnlyOn`, no sign condition); the one-region
compatibility with the Stone 56 capstone in both directions (Q1); the empty
family and `δ ≡ 0` (Q2); overlap and distinct amplitudes (Q3); background
`1/2`, ignored values, the last profile by effective factors, zero factor
(Q4); the two-step closure with the auditor's **own** intermediate profile
and step hypotheses, using only the Stone 56 estimate and the triangle
inequality (Q5, two certificates of its own test theorems, not counted among
the 291 of the project); `δ = 7` with general `Cf`, `Cf = 0` separately, the
exact scalar comparison `1/2 + e^{−2}/2 < 1` and the strict comparison of the
full bounds only under `Cf > 0` (Q6); a duplicated family costing twice, the
owner not minimizing `B` (Q7); the expected application failure of the
last-step obligation under the owner `none` with differing effective factors
(Q8x, goal `False`), classified as such and not as a counterexample. The
auditor's disposable tests emitted 34 warnings (Q1: 28, Q4: 4, Q6: 2),
separate from the 114 inherited warnings of the project and from the 0 of
the new module. The tests **W1–W9/W8x** belong to the constructor (delivered
in `STONE57L_evidence.zip`, re-executed by QA1 in its second pass, which does
not change their authorship); the tests **Q0–Q8x** belong to QA1. The
geometric tests are parameterized by `typedTouchesSupport` hypotheses; no
concrete lattice instance is constructed.

## Reading the QA1 record: three precisions of the coordination and Q4d

The QA1 report, the two matrices and the archived preliminary conclusions
are preserved exactly as received. **No errata was issued by the auditing
instance**, and none is attributed to it. The coordination (Can, in the
integration tape 57-P, from its own reading of the test sources) recorded
three precisions on the *descriptions* of the tests and one on their
reading; they do not concern the candidate, its hypotheses, proofs or
compilation results, and the verdict `PASS NO ESCOPO` stands. The audit is to
be read with them:

- **D1 — what Q3c fixes.** The report (§4.2), the preliminary conclusions and
  the test matrix describe `|Δ| = 1/2 > 1/10` at the overlapping polymer. In
  `tests/q3_overlap.lean` the first proof of Q3c shows that the difference
  between stages 1 and 2 is zero for any profiles on that polymer, already
  switched; the second applies `step_bound` with the majorants `![1/2, 1/10]`
  and the owner hypothesis. Neither fixes, by hypothesis or by proof, the
  numerical equality `|b(η₁) − b′(η₁)| = 1/2`. Correct formulation: Q3c
  verifies generically the absence of a second switch and the bound `1/10` on
  the second step, without requiring the global difference of that polymer
  to be bounded by `1/10`; the `step_bound` example uses `1/2` as the owner's
  majorant. No numerical instance with global difference exactly `1/2`, and
  no concrete lattice with that variation, was constructed. The generic
  proof supports the audited mechanism.
- **D2 — admissibility of `owner ≡ none`.** The abbreviation "owner ≡ none ⇔
  all factors equal" (test matrix, Q4b/b′) is to be read as: the constant
  owner `none` satisfies the obligation `howner_none` if and only if all
  effective factors agree. Equal factors do not force an arbitrary owner to
  return `none`; a coordinate without change may receive `some i` when the
  other obligations hold. The source comments already qualify this by
  admissibility.
- **D3 — selection is not an equivalence between values.** The phrase
  "`p_k η = a′ η` iff moved" of the preliminary conclusions (§Mathematics.1)
  is the definition by cases: `p_k η` selects `a′ η` if moved, and `a η`
  otherwise; when `a η = a′ η` the value coincides with `a′ η` also without
  `moved`. The code and the final report use the correct selection; the
  preliminary abbreviation is not a formal biconditional.
- **Q4d — raw versus effective change.** The application allows a raw profile
  value `0`; the effective change at that polymer occurs when it touches
  `R`. The test proves the general application, which also covers the case
  without an effective change, and does not assume that touch separately; it
  is not a concrete geometry nor a proof that the polymer touches `R`.

These precisions qualify reports of tests and one preliminary sentence; they
required no change to the module and no new compilation. The review by Kimi
K3 confirmed them as precisions (its §4), finding no new defect.

## Reading the Kimi K3 review, with its declared limits

`kimi/RELATORIO_57-K-ADV.md` is one review with no errata; it is preserved
exactly as received. The reviewer identifies itself as "Kimi K3 (Moonshot
AI)"; the historical credits of the project say "Kimi 3" and are kept as
written, without inferring a new technical identity or altering the past.
It records: the real order of reading (the tape and the constructor's report
first, then the custody of the uploads, the module in full, the matrices,
the public Git objects, the Stone 56 interfaces, and only then the QA1 report
and evidence); its own recomputation of the hashes of the three uploads, of
the internal manifests (45/45 and 19/19), of the diff, trees, blobs and
counts on the Git objects (117 → 118 modules, 37,994 → 38,521 lines, 1,780
→ 1,802 declaration lines, 269 → 291 `#print axioms`), and its own parsing of
the two clean logs (291 lists, 291 distinct names, 74 multi-line, all
standard, no `sorryAx`; 114 project warnings in both); the interfaces of
Stone 56 opened at the merge; the adversarial re-derivation of the owner and
cover (including the attempted attacks: a cover without a majorant, an
assignment to the wrong index in an overlap), the intermediate profiles, the
step hypotheses, the application of Stone 56, the telescoping and the
constant, and the limit cases (`m = 0`, `m = 1`, `δ ≡ 0`, `δ = 7`, `Cf = 0`,
background `1/2`, zero factor, `R = ∅`, repeated regions); the confirmation
of D1–D3 and Q4d as precisions; and the structural check of the CI count
(294 lists = 291 + 3; 292 distinct names, the third workflow name
`logPartition_eq_tsum_unrooted` being absent from the build's list). It also
records what the reviewer did **not** do: no Lean execution; the standalone
57-P report not received (hash only informed); the CI logs of runs 505/506
not downloaded in full; Zenodo and the Release not consulted; the SSH
signature of the candidate not verified independently. Verdict `PASS NO
ESCOPO`, no finding.

## Reading the Manus execution, with its limits and the qualification M1

`packages/MANUS_57_EXEC_evidence.zip` (46 entries: 37 files and 9
directories, under the prefix `MANUS_57_EXEC_evidence/`; internal manifest
`SHA256SUMS_57-MANUS-EXEC.txt`, 36 entries — every file except itself; the
only executable file is the controller `controller/run_manus_57.sh`). Contents:
`inputs/` (the execution tape, the Kimi review and the QA1 package as
received — copies of the received materials, not new audits; the QA1 copy and
the review copy are byte-identical to items 1 and 5), `source/Phase3/` (the
module, the manifest, the lakefile and the toolchain effectively used — all
four byte-identical to the Git objects of the merge `b66c255c…`), `tests/`
(five sources — Q0, Q3, Q4, Q5, Q8x — byte-identical to the QA1 tests),
`runtime_checks/check_capstone_signatures.lean` (the platform's own `#check`
of the two capstones), the controller, `raw_logs/` (toolchain installation,
checkout custody, QA1 custody, execution status, instruction inventory,
preflight, `lake env true`, dependencies and pins, Mathlib cache, pre-build
inventory, the directed build, the five test logs, the signature checks, the
final integrity and the metrics) and `INDEX_57_MANUS_EXEC.md`. The technical
report was delivered as a **PDF** (`manus/RELATORIO_57-MANUS-EXEC.pdf`, nine
pages, preserved byte for byte under an ASCII canonical name; the Markdown
original on the origin machine was not received and is not reconstructed
from the PDF); the checksum file (`manus/MANUS_57_EXEC_evidence.zip.sha256`)
carries the absolute path of the origin bench and is preserved as received —
its digest equals the SHA-256 of the package computed here by file name;
`manus/PACKAGE_DELIVERY_VALIDATION_57.txt` is the platform's own validation
of the package.

Results recorded in the logs (read here; the execution is the platform's):
clone of the fixed SHA `b66c255c…` with `remote.origin.pushurl` set to
`DISABLED`; Lean 4.15.0, Lake 5.0.0-1165156; manifest `c376bbe9…1227`,
Mathlib `9837ca9d…` and the other eight revisions as pinned, no `lake
update`; `lake exe cache get` (5,826 files); `lake build
LatticeGauge.ActivityProfileDampingMultiRegion` from 2026-10-09T19:54:35Z,
exit 0, 1,083 s, **104 `LatticeGauge` modules built / 0 replayed** —
exactly the import chain of the module, **not a full rebuild of the 118
modules**; 102 warning headers in 43 imported pre-existing modules, 0 in the
new module — exactly the corresponding subset of the QA1 baseline blocks (no
block only in this log); Q0: 22 certificates, 22 distinct names, all
standard, no `sorryAx`; Q3, Q4, Q5: exit 0 (Q4 with four test warnings; Q5
with two certificates of its own test theorems, which are not new
declarations of the project); Q8x: exit 1 on the open obligation `⊢ False`
under the constant owner `none` with `typedTouchesSupport η R` — the expected
application failure, not a timeout, a broken import or an incompatibility;
`#check` of the two capstones: `hcover` explicit, no public `owner`;
tracked diff empty and final state clean. Verdict of the executor:
**EXECUÇÃO CONCLUÍDA NO ESCOPO** for the merge `b66c255c…`.

The test sources being byte-identical copies of the QA1 tests, the
contribution of this execution is their **re-execution on a third bench**;
it is neither the conception of new tests nor an independent re-derivation
of Q5, and it is not counted as an additional independent mathematical
audit. The platform is recorded as declared ("Manus Sandbox"); the model
identifier was not exposed, and no model family, blindness or additional
mathematical authorship is inferred. The historical contributions of
"Manus AI 1.6" (reproducibility and release reviews of Stones 48–50,
reproduction of gate 51-A) are a separate record.

**M1 — qualification by the coordination on the pre-build inventory**
(recorded in the documentary conference of this round; not an errata issued
by the platform; the PDF, the controller, the logs and the package are
preserved as received). `raw_logs/09_prebuild_project_artifacts.log` and the
controller inspect `.lake/build/lib/lean/LatticeGauge` and
`.lake/build/lib/lean`. In the pinned Lean/Lake version the default build
directory is `.lake/build/lib` and the project's directory is
`.lake/build/lib/LatticeGauge` (Lake `Defaults.lean` at v4.15.0,
`defaultBuildDir` and `defaultLeanLibDir`); the lakefile does not redefine
them. That isolated inventory therefore does not prove the global absence of
prior `.olean` files. The positive evidence available stands: a fresh clone
recorded in the custody log, and the build log with the 104 modules of the
chain marked **Built**, none **Replayed**, exit 0, with fixed sources and
the subsequent tests. The inventory at the wrong path is not to be presented
as a certificate of cleanliness; no recompilation is needed for this
documentary consolidation. Two further occurrences admitted by the execution
itself are recorded as such: the preflight first tried to read
`checkout/lean-toolchain` (`No such file or directory`, in
`raw_logs/05_preflight.log`) and then read `Phase3/lean-toolchain`, with Lean
4.15.0 confirmed in the execution — a path error, not a change of pin; and
the controller does not use `set -e` in its blocks, so a final exit code of
zero does not by itself mean that every intermediate command succeeded —
conformity is attributed to the checks and contents actually examined.

## Records for the consolidation

- **No documentary record on the module**: neither the QA1, nor the review,
  nor the execution found an imprecision in the candidate or in its
  docstrings; the precisions E1–E5 of the construction tape were
  incorporated in the docstrings of the integrated module before the audit.
- **D1–D3 and Q4d** — recorded above; the originals are not edited.
- **M1** — recorded above.
- **CI count 294/292.** The runs 505 and 506 emit 294 axiom lists (291 of
  the build + 3 of the workflow step), all standard, for 292 distinct
  names: two workflow outputs repeat names of the build and the third,
  `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name absent from the
  build's list (not a new theorem). The integration tape 57-P described the
  three workflow outputs as repetitions; the publication report delivered
  already distinguishes the two repetitions, and the correct reading is the
  one above. Not attributed to the QA1.
- **Reporting precision**: "118 built / 0 replayed" refers to the project
  modules in the clean builds of the constructor and of QA1 and in the CI;
  the constructor's log records the dependencies as 0 built / 1,332 replayed
  from its cache, the QA1 log records 0 / 0 with no dependency diagnostics,
  and the CI runner records 9 built / 0 replayed; the Manus directed build
  records 104 / 0 for the chain of the module. None of these is a
  recompilation of the dependencies from source.
- **Commit identity.** The candidate `c936d461…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH signature header present, trailers `Co-Authored-By: Claude Fable 5.1`
  and `Claude-Session`), accepted by the precedent of Stones 52–56; the QA1,
  the review and this consolidation record the signature as present, not as
  independently authenticated; identity and signature were not redone.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the ten materials against the reference hashes supplied by
the coordinator in the consolidation tape (and, for the publication report,
against the original kept on the publisher's bench); the internal manifests
of the two packages (45 entries and 36 entries, all verified; no absolute
paths, path traversal or duplicates; 48 and 46 entries); the byte-identity of
the standalone QA1 report with its copy inside the package, of the extracted
report and matrices with their copies inside the package, of the QA1 package
and the Kimi review inside the Manus package with items 1 and 5, of the five
Manus test sources with the QA1 tests, and of the four Manus source files
with the Git objects of the merge; the correspondence between the candidate
commit, the pull request, the merge commit and the CI runs of `main` (PR
#39; runs 505 and 506; parents, root tree and `Phase3/` tree of
`b66c255c…`); the identity of the `Phase3/` tree of this documentary commit
with that of `b66c255c…` (`cc1bfb26…`); the historical manifests of
`docs/audits/stone52/` to `stone56/` (20, 9, 8, 9 and 9 entries, all
verified, no self-inclusion); the warning blocks of the Manus directed build
against the QA1 baseline (102 blocks, all in the baseline, none new). The
text of the Manus PDF could not be extracted by the tools available in the
consolidating session; its content is described from the package logs, the
delivery validation and the coordination's conference recorded in the
consolidation tape.

Reported by the auditor, the reviewer and the platform and **not**
re-executed here: the builds, the `#print axioms` runs, the tests and the
mathematical readings. Internal manifest integrity is not by itself proof of
authorship or of the execution of those builds; the primary machine evidence
for the integrated code is the CI history of `main` (runs 505 and 506, see
`RESULTS.md`).
