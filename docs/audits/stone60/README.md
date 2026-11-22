# Stone 60 — independent evidence: QA1 reproduction with its addendum, the Kimi adversarial review with its two errata, and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 60 candidate `778e2c7b27f0357110ba83e9b466984747577823` (see
[`docs/stone60/RESULTS.md`](../../stone60/RESULTS.md)), integrated on `main` at
`58eb3d1bf3cc2b3393c7608581905530053d0e96` (PR #46): the audit evidence
package of the QA1 reproduction with its report, its two matrices and its
addendum A1, the adversarial review by Kimi together with its two errata C1
and C2, and the publication report of the constructing/publishing instance
with its operational package (the two CI logs). It follows the organization
of [`docs/audits/stone59/`](../stone59/README.md), with two differences: no
Gemini review was received for this stone (Gemini did not take part in this
round), and the Kimi review carries two errata instead of one. No
complementary execution on a third platform was received for this stone, and
none is recorded. The QA1 package is the primary record of the audit; its
report and matrices are extracted here only for reading convenience and are
byte-identical to the copies inside the package; the addendum A1 is a
separate file that the auditor delivered outside the package and that does
not enter it. Nothing in this directory is a Lean module: the packages
contain disposable test files (including tests that are *expected to
fail*), build and CI logs and matrices, and none of it enters the
`LatticeGauge` library, the `lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the QA1 matrices
are in English or mixed); they are not translated, normalized or edited. The
constructor's own materials (the construction report `RELATORIO_60-L.md`,
14,107 bytes, SHA-256
`ced9b68d2226bf1fcc40be10e93aa189043898241126916b4c18ad97114a8666`, the
package `STONE60L_evidence.zip`, 308,439 bytes, SHA-256
`a32e7298a40232199c88721c6767a03c26587f791ad34c1df6acbb5a2821faf9`, internal
manifest 42/42, with its bundle, diff, matrices, logs and tests T1–T10 and
T9x, the bundle `stone60_candidate.bundle`, 9,903 bytes, SHA-256
`4dcd00b91ee15c63de2675642668f9b5348dac5458d7e8bb8d5cb581a60f85fe`, and the
feasibility report `RELATORIO_60-A-VIABILIDADE.md`, 13,914 bytes, SHA-256
`f7bf863263f33475d235f99c4f2fb7a96da0a37265c2ea3183d27eadab4ec2d3`, with its
package `STONE60A_evidence.zip`, 205,467 bytes, SHA-256
`194fd29d2384eff5b20de058df2d069da50ab386bb3da7ee198452a5e2dbaf1d`) are
**not** part of this collection: they are the implementer's material, not an
audit; the audit, the review and the publication cite them by hash. The
transport packages prepared by the coordination for the reviewer and for
the auditor are packages of copies and context, not audits, and are not in
the tree.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra / Can (AI model) | different model family from the constructor | tapes (feasibility 60-A, construction 60-L, integration 60-P, this consolidation 60-DOC-P); reading of the module, the reports, the packages and the logs; conference of Git objects and publication metadata; the documentary conference of the 60-A feasibility delivery; the observations that prompted the two Kimi errata; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | feasibility tests (gate 60-A, two elaboration attempts of the chain file, the second clean, plus an expected failure), Lean implementation of the module, local commit and bundle with the constructor's API tests T1–T10 and the negative T9x and a clean rebuild of the 121 modules (gate 60-L), then, after QA1 and the reading, push, pull request, merge and CI follow-up (60-P), and this consolidation, in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction and addendum | Claude (AI model), separate auditing instance, session model id `claude-fable-5-2` as the report declares (the QA1 reports of Stones 52–59 were issued under `claude-fable-5-1`) | **distinct instance and bench; same model family as the constructor** | reproduction by execution (the commit reconstructed from the bundle through a temporary local ref; a fresh container, elan and the v4.15.0 toolchain installed, dependencies materialized from the Mathlib community cache at the nine manifest revisions, 9/9 revisions checked, no `lake update`, not recompiled; no project artifact before the build; 121 modules built, 0 replayed, exit 0; own `#print axioms` of the 50 declarations; own tests Q0–Q7x; the constructor's tests T1–T10 and T9x re-executed in a second pass); preliminary conclusions recorded before opening the constructor's tests, logs, matrices and scripts; one addendum A1 closing its only custody pendency | **not blind** (prior exposure to the earlier stones declared; the tape and the constructor's report read beforehand); not a different model family; not human review |
| Adversarial review and two errata | Kimi (K-ADV), as the documents identify the reviewer | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis of the module in full and of the Stone 59 interfaces consumed, against the frozen v59 base, with own custody checks (hashes of the three files received, `git bundle verify`, the blob of the module recomputed in Python, the root tree recomputed, the diff regenerated and compared byte for byte, the public parent fetched from GitHub); **no Lean execution**; two errata by the same instance, both prompted by the coordination's conference, correcting its own report | **not blind** (the tape disclosed the target; the base read from a frozen package); reading only; the SSH signature of the commit not verified (no public key); did not consult the CI logs, Zenodo or the Release |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions, manual publication of Version 59; in this round, the conference of the feasibility delivery, of the packages and of the reports together with the architect | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model of
the constructing instance, and `claude-fable-5-2` is the session model id
the auditing instance declares for itself. No Lean execution is attributed
to GPT Astra / Can, to Kimi or to the coordination. The historical credits
of "Kimi 3", "Kimi K3" and "Kimi (Moonshot AI)" are preserved as written;
the Stone 60 documents identify the reviewer as "Kimi (K-ADV)" and no build
or version is inferred. The Gemini review of Stone 59 is a record of that
stone; Gemini did not participate in this round and nothing is attributed to
it here.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_60_evidence.zip`](packages/QA1_60_evidence.zip) | `bf966c2f2883e23ba5d22f4026f2d4ef3905482851fb2672f6f6e7399f98d899` | Claude (`claude-fable-5-2`), QA instance | `778e2c7b…` (candidate, reconstructed from the bundle; published as [PR #46](https://github.com/consensusframework/yang-mills-mass-gap/pull/46), merge `58eb3d1b…`) | `PASS NO ESCOPO` (with one non-blocking custody pendency, closed by item 5) | 2026-11-22 (clean build 14:16–14:30 UTC) |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_60-QA1.md`](reports/RELATORIO_60-QA1.md) | `30b0880bc866922eca31c5791efa85043f6419fbe0ee835b2f2acd65da477a18` | Claude (`claude-fable-5-2`), QA instance | `778e2c7b…` | `PASS NO ESCOPO` | 2026-11-22 |
| 3 | QA1 declaration matrix (extracted) | [`reports/60_QA1_DECLARATION_MATRIX.tsv`](reports/60_QA1_DECLARATION_MATRIX.tsv) | `932dc912712c1c1dce7e4acb6f56e96515da6d7cbfc87c694565d27f7cf26004` | Claude (`claude-fable-5-2`), QA instance | `778e2c7b…` | 50 items (42 theorems, 2 `def`, 4 `noncomputable def`, 1 `structure`, 1 `noncomputable instance`), the 50 lines verified in the source, each with the certificate of the auditor's rebuild and of its test Q0 | 2026-11-22 |
| 4 | QA1 test matrix (extracted) | [`reports/60_QA1_TEST_MATRIX.tsv`](reports/60_QA1_TEST_MATRIX.tsv) | `34d0bd08407a2255140d438a1ae61850f66418826ce85162861a2c5a1addcdfc` | Claude (`claude-fable-5-2`), QA instance | `778e2c7b…` | Q0–Q7 positive; Q7x expected application failure; T1–T10 and T9x (constructor's) re-executed | 2026-11-22 |
| 5 | QA1 addendum A1 (custody pendency closed) | [`reports/ADENDO_60-QA1-A1.md`](reports/ADENDO_60-QA1-A1.md) | `2fb1dd09dc2735976b03cfd19fbc1c3d189dd477d1346e3fa47446ca4656c0af` | Claude (`claude-fable-5-2`), QA instance | applies to item 2 (hash `30b0880b…`); the candidate unchanged | custody `PASS`; global `PASS NO ESCOPO` without pendency | 2026-11-22T16:25Z |
| 6 | Adversarial review (Kimi) | [`kimi/RELATORIO_60-K-ADV.md`](kimi/RELATORIO_60-K-ADV.md) | `e7f3017956618af438dad11ac735e29c6cc21079d407db84657497a02329ebe3` | Kimi (K-ADV) | `778e2c7b…` (candidate, from the bundle) and `2ef6500d…` (base, via the public Git objects and the frozen v59 package) | `PASS NO ESCOPO` | 2026-11-23 in the reviewer's time zone (UTC+8), that is 2026-11-22 UTC — see item 7 |
| 7 | Errata C1 of the Kimi review | [`kimi/ERRATA_60-K-ADV-C1.md`](kimi/ERRATA_60-K-ADV-C1.md) | `2c38813376bfa4ca2a732de26faddc238564dc3ed801b77310b272f9ea74a841` | Kimi (K-ADV), same instance | applies to item 6 (hash `e7f30179…`); the scientific target unchanged | verdict `PASS NO ESCOPO` maintained; three precisions of the report | 2026-11-22 (UTC) / 2026-11-23 (UTC+8) |
| 8 | Errata C2 of the Kimi review | [`kimi/ERRATA_60-K-ADV-C2.md`](kimi/ERRATA_60-K-ADV-C2.md) | `28b117736e278297e7508253cc54626bdb819202895dd37356cb4af63b1af878` | Kimi (K-ADV), same instance | applies to item 6, §1.3; the scientific target unchanged | verdict `PASS NO ESCOPO` maintained; one identifier of the custody ledger corrected | 2026-11-22 (UTC) / 2026-11-23 (UTC+8) |
| 9 | Publication report (FITA 60-P) | [`publication/RELATORIO_60-P.md`](publication/RELATORIO_60-P.md) | `b39a804b5e1ff43a207d3415269341136c86e690dbea02866d178ebfc3964a57` | Fable 5.1, constructing/publishing instance | `778e2c7b…` → `58eb3d1b…` | n/a (record) | 2026-11-22 |
| 10 | Publication operational package (the two CI logs) | [`packages/STONE60P_evidence.zip`](packages/STONE60P_evidence.zip) | `cba1076e0908c2b30ff0a0121c3a42c51c3c2f31507a70cb82aebadafa4be26d` | Fable 5.1, constructing/publishing instance | runs 519 (checkout `7e1d3e7…`, the provisional merge) and 520 (checkout `58eb3d1b…`) | n/a (record) | 2026-11-22 |

The hashes of items 1, 2, 6 and 8 were supplied as references in the tapes
(the QA1 package and report and the Kimi report in the addendum A1 and the
errata C1 that cite them; the errata C2 in the consolidation tape) and match
the files received; the hashes of items 3 and 4 are those of the internal
manifest of item 1 and match the extracted copies; the hashes of items 5
and 7 were not transcribed in the text of the integration tape and were
recorded by the publishing instance on the files received (see the
precision C60-P1 below); the publication report and its package are the
originals kept on the publisher's bench. SHA-256 of every file of this
directory except the manifest itself: [`SHA256SUMS.txt`](SHA256SUMS.txt)
(relative paths; covers this README, `PROVENANCE.tsv` and the ten
materials: 12 entries; no self-inclusion). Machine-readable provenance:
[`PROVENANCE.tsv`](PROVENANCE.tsv) (12 columns, 10 materials).

## The QA1 package

`packages/QA1_60_evidence.zip` (43 entries: 40 files and 3 directories, the
root `QA1_60_evidence/` and its `tests/` and `builder_tests_rerun/`;
internal manifest `SHA256SUMS_60-QA1.txt`, 39 entries — every file of the
package except the manifest itself). Contents: the report,
`PRELIMINARY_CONCLUSIONS_first_pass.md` (written before the auditor opened
the constructor's tests, matrices, logs and scripts), the two matrices,
`environment.txt` (a **new** cloud container, the previous bench having been
lost; elan 4.2.4 installed in the session; Lean 4.15.0, Lake 5.0.0-1165156;
a fresh clone with the push URL disabled and a detached worktree at the
candidate `778e2c7b…`, reconstructed from the bundle through a temporary
local ref; manifest SHA-256 `c376bbe9…1227` before the dependencies, before
and after the build; the dependencies materialized by `lake exe cache get`
from the Mathlib community cache, 5,826 files, 9/9 revisions checked, not
compiled from source), `deps_cache_get.log` and its instants,
`prebuild_artifacts.txt` (project build artifacts before the build: none),
`build_full_clean.log` (SHA-256
`69302a215a600d8d7554c3bd8548846069c36342b05c81699eb791dbf2f08e38`; single
integral `lake build` with no prior `.lake/build`, 2026-11-22T14:16:15Z →
14:30:02Z, exit 0, 827 s, **121 modules built, 121 distinct names, 0
replayed**, dependencies 0 built / 0 replayed, 0 errors, 411 certificates
all standard, 137 of them printed across lines, 0 `sorryAx`), its `.result`
and instants, the three manifest hashes (identical), `compare_warning_blocks.py`
and `warnings_block_comparison.txt` (the full multi-line warning blocks
against the Stone 59 baseline — the QA1 log of Stone 59 inside
`docs/audits/stone59/packages/QA1_59_evidence.zip`, SHA-256 `42817399…`,
whose external and internal manifests the auditor validated first: 114
blocks of `LatticeGauge/`, identical multiset, 113 distinct file:line pairs,
**0 in `ActivityProfileDampingOptimalGeometry`**), `certs_full_build.tsv`
(the 411 certificates by name), `tests/` (the `.lean` files Q0–Q7 and Q7x
with their logs) and `builder_tests_rerun/` (the logs of the constructor's
`T60L_api_tests.lean` and `T60L_T9x_EXPECT_FAIL.lean` re-executed on the
auditor's bench, with the same results). Logs are not duplicated outside
the package. The QA1 declaration matrix lists the 50 declarations of the
module with lines and names equal to the constructor's matrix, each with
the certificate observed in the auditor's rebuild and in its test Q0. The
log `build_full_clean.log` of this package is the warning baseline used by
the publication (60-P) for the two CI logs.

Key results reported by the auditor (not re-executed here): 411/411
certificates in the clean build and **50/50** in the test Q0, all equal to
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`; the 50 of Q0 are
the auditor's checks and are not added to the 414 outputs of the CI;
`#check` of 40 signatures (G0–G7 and the Stone 59 and 56 interfaces
consumed); reach characterized by the equality of the effective factors on
the polymers that touch no region, and shown to be an equivalence relation,
by the auditor's own proofs, with no cover of all polymers (Q1); a reference
constant `2`, outside `[0, 1]`, with valid members `0` and `1` in the
component with `R = ∅`, and an **empty component** (`m = 0`, a polymer
touching `R`, the reference worth `2` there — no member is presupposed)
(Q1); the symmetry of the **value** and the triangle inequality re-derived
from the Stone 59 interfaces alone (`optimalBudget_admissible`,
`minCost_le_budget`), without the module's `minCost_comm`,
`minCost_triangle`, `admissible_add` or `budget_add`, the sum of two
minimizers shown admissible but **not** optimal on the return path
`a → b → a` (a summed budget with a coordinate `2` against an optimal cost
`0`), the minimizers never identified (Q2); `dist = optimalDist = minCost`
by `rfl`, the change of reference preserving the value, and two members at
distance `0` with equal functional and raw profiles distinct on every
polymer off `R` (Q3); the exact distance `|c − c′|·e^{−n₀/2}` by a global
cover plus the lower bound at the witness polymer, and the triangle
inequality **with equality** (`1/4`, `1/2`, `3/4`) and **strict** (return)
stated on `dist` itself; `m = 0` and `R = ∅` giving `d = 0` for two
different reasons, in separate theorems (Q4); the instance found by
inference equal to the candidate's (`rfl`), the three- and four-point
bounds from Mathlib and the three-point one re-proved from the triangle and
the symmetry, the polygonal inequality for `k = 0, 1, 2` by the candidate's
lemma and in general by the auditor's own induction (Q5); the two Lipschitz
bounds re-obtained from the Stone 59 capstones and `dist = minCost` with
constants written by the auditor and equal to the candidate's by `rfl`,
uniform continuity and continuity, the `Cf = 0` case (constants `0`,
constant functional), the recoveries with exactly the types of the Stone 59
capstones (definitionally, in both directions — equality of types, not of
derivations), and the algebraic route `d = 0 ⇒` equal functional without
the small-β regime (Q6); against the real structure, an effective change on
a polymer that no region touches gives `¬ Reaches`, no admissible budget and
no member with the changed profile, **proved** (Q7), and the attempt to
build such a member fails with exit 1 and exactly one error at `21:4`, the
open goal `⊢ ∃ i, typedTouchesSupport η (r i)` in the field `reach` — an
application failure, not a counterexample (Q7x). The auditor's disposable
tests emitted 32 warnings (Q6: 29, Q5: 2, Q3: 1; unused binders and the
like), separate from the 114 inherited warnings of the project and from the
0 of the new module. The tests **T1–T10 and T9x** belong to the constructor
(delivered in `STONE60L_evidence.zip`, re-executed by QA1 in its second
pass, which does not change their authorship); the tests **Q0–Q7x** belong
to QA1. The geometric tests are parameterized by `typedTouchesSupport`
hypotheses; no concrete lattice instance is constructed.

## Reading the QA1 record together with its addendum A1

`reports/RELATORIO_60-QA1.md` and `reports/ADENDO_60-QA1-A1.md` are **two
documents of one audit** and are to be read together; both are preserved
exactly as received. The report (§0, §2, §7) records one **non-blocking
custody pendency**: the constructor's report `RELATORIO_60-L.md` had reached
the auditor as text pasted in the conversation, not as a file, so its
SHA-256 could not be recomputed there. The addendum A1 (2026-11-22T16:25Z,
by the same instance) closes it: the pasted text, encoded in UTF-8 with LF
line endings and a final newline, reproduces exactly 14,107 bytes and the
SHA-256 `ced9b68d…8666` of the constructor's delivery; the custody axis
passes from "PASS with a non-blocking pendency" to **PASS**, the global
verdict remains `PASS NO ESCOPO`, and execution, mathematics and
documentation are unchanged (no build or test repeated). The addendum states
its modality (a reconstruction from the literal session record, with four
line-ending variants tested, only one of which matches) and does not enter
the QA1 package, whose hashes are unchanged.

The second pass of the audit (§6 of the report) records, on the
**constructor's** materials, that `t3_triangle_eq_and_return_strict` of the
constructor's test file is an arithmetic statement on the values (`3w/4 =
w/4 + w/2`, `0 < w/4 + w/4`) and not a statement on `dist`; the equality and
the strict inequality on `dist` itself are the auditor's own Q4. This is a
limitation of the constructor's test, not a defect of the candidate. The
audit also records the environment difference between the two clean
rebuilds (the constructor's dependencies compiled from source once as a
preparation of its bench, so its log shows 1,332 dependency targets replayed
with 4,599 dependency warning blocks; the auditor's obtained from the cache,
0 / 0), which does not affect the project modules, compiled in full in both
cases. No errata was issued by the auditing instance, and none is attributed
to it.

## Reading the Kimi review together with its errata C1 and C2

`kimi/RELATORIO_60-K-ADV.md`, `kimi/ERRATA_60-K-ADV-C1.md` and
`kimi/ERRATA_60-K-ADV-C2.md` are **three documents of one review** — one
report and two errata — and are to be read together; all are preserved
exactly as received, and no merged or silently corrected version is
produced. **Each errata prevails over the report on its own point.** The
reviewer identifies itself as "Kimi (K-ADV)"; prior exposure is declared and
the review is not blind.

The review records: its custody work — the three files received (the module,
the bundle and the diff) with their sizes and hashes, `git bundle verify`
passed, the public parent `2ef6500d…` fetched from GitHub (`HEAD`, `main` and
the tag `zenodo-v59`), the commit object read (tree `a7295ffe…`, parent,
author, timestamp `2026-11-22T13:06:36Z`, SSH signature present but not
verified), the blob of the module recomputed in Python and equal to
`fbf6452a…`, the upload byte-identical to the blob extracted from the
bundle, the diff regenerated and byte-identical to the one received, the
root tree recomputed and equal to the commit header, exactly two paths
changed, the `Phase3/` tree of the parent `c3157cb9…` equal to the tree of
the Stone 59 tape and byte-identical (120/120 modules) to the frozen v59
snapshot used as the base of interfaces, and the count 361 + 50 = 411;
then the first pass — the module in full (646/646 lines, 50 declarations
and 50 `#print axioms`, no forbidden construction) and the Stone 59 and
Stone 56 interfaces consumed, read in the frozen source and not from
memory, with the reviewer's own re-derivation of the axes G0–G7: reach as
an equivalence without a cover of all polymers and without profile bounds;
the transport and addition of covers, the multiplicities of repeated
regions preserved, `Admissible` carrying **no** upper bound so that the
summed budget is legitimately admissible; the triangle inequality verified
link by link, the sum of the minimizers being a witness and not claimed
optimal; the component whose membership does not depend on `n`, the
distance defined on every pair of the component and nowhere else, the
kernel of the pseudometric as equality of the effective factors (why
*pseudo*), the reference absent from the optimization of a pair; the
instance in the canonical Mathlib form; the three- and four-point bounds
and the polygonal induction with `k = 0`; the two Lipschitz constants from
the two Stone 59 capstones with `0 ≤ Cf` derived and coercions by `rfl`,
uniform continuity and continuity in this pseudometric only, the chains,
and the algebraic route without `hβ`/`hsmall`; the recoveries as transport;
the implicit hypotheses found (all declared), the degenerate cases
(`m = 0`, `R = ∅`, the empty component, a reference outside `[0, 1]`,
repeated regions, coordinates up to `2`, `k = 0`, the dependence on `n`),
and the search for overclaims (none found). It records what the reviewer
did **not** do: **no Lean execution** (no toolchain in its environment; the
compilation claims of the commit message are the constructor's), the
feasibility and test files not audited (not in its package), the SSH
signature not verified. Verdict `PASS NO ESCOPO`; no correction proposed to
the candidate. It also records the positive closure of the Stone 59
limitation L3: the Stone 59 candidate `dcd6e6b1…`, absent from the remote at
the time of that review, is now public as `refs/heads/stone59`.

**The errata C1** (prompted by the coordination's conference, as the errata
itself states, not a finding of the first pass) corrects three points of the
**report** and keeps the verdict. Where it corrects, its wording prevails:

1. **§1.4, the paths of the Stone 59 consolidation.** The parent `2ef6500d…`
   differs from the Stone 59 candidate `dcd6e6b1…` in 20 paths: `README.md`
   and `VERIFICATION_STATUS.md` (omitted in the report), `formalization.yaml`
   and 17 paths under `docs/`. The conclusion of §1.4 — `Phase3/` identical
   between the Stone 59 candidate and the Stone 60 parent — did not depend on
   the list and stands (tree identity and `diff -r`).
2. **§5, the empty component with an explicit witness.** The example
   `m = 0`, `aref ≡ 2` is restated with an explicit polymer touching `R`,
   constructed from the definitions (a link of `R`, an admissible plaquette
   through it in two cases, the singleton polymer, its contact with `R`), the
   reviewer having found no ready lemma of the form "`R ≠ ∅ ⇒` some polymer
   touches `R`" in the base. The conclusion (the component can be empty; the
   theorems hold vacuously) stands.
3. **The date of the review.** `2026-11-23` is the local date of the
   reviewer's environment (UTC+8); it is 2026-11-22 in UTC and in São Paulo,
   consistent with the reception recorded by the coordination and with the
   timestamp of the candidate. Not an error of record; a time zone not
   declared. The reviewer undertakes to declare the time zone from then on.

**The errata C2** (also prompted by the coordination's conference) corrects
one identifier of the custody ledger of the **report** (§1.3) and keeps the
verdict: the `Phase3/` tree of the candidate `778e2c7b…` is
**`ffabe44339920053581a294929ab8a094d329b77`**, not `6f408214…` as the
report recorded. The errata identifies the origin of the wrong value — the
reviewer's own Python recomputation, fed with `git ls-tree 778e2c7b…
Phase3/` whose entries carry the path prefix (`Phase3/LatticeGauge`, …),
whereas Git tree objects store base names only; the malformed tree
reproduces exactly `6f408214…`, and the corrected routine reproduces
`ffabe443…` for the candidate, `c3157cb9…` for the parent and `62c5fc4f…`
for `Phase3/LatticeGauge`, all equal to `git rev-parse`. The root tree
`a7295ffe…` and the parent's `Phase3/` tree were and remain correct in the
report. The two conclusions that weighed — exactly two paths changed
(`git diff --name-status c3157cb9… ffabe443…`: the module added, the
lakefile modified) and the parent's `Phase3/` being the frozen v59 base —
are re-verified in the errata and stand. **The code and the verdict are
intact**; the correction is to the ledger, not to the candidate.

## Publication and the coordination's precision C60-P1

`publication/RELATORIO_60-P.md` and `packages/STONE60P_evidence.zip` are
preserved exactly as received from the publishing instance. The package
(27 entries: 22 files and 5 directories, the root `STONE60P_evidence/` and
its `ci/`, `evidence/`, `inputs/` and `tools/`; internal manifest
`SHA256SUMS_60P.txt`, 21 entries — every file except the manifest itself)
contains the two job logs as obtained through the GitHub tool (the texts
extracted from the tool's JSON, `run519_job137344481922.log`, SHA-256
`225494c96f73b5689593dedb41a9a36887f2192519224f556be2f09c23b80e4d`, and
`run520_job137349341525.log`, SHA-256
`7854908cc97e26710942498bc53d9392538c98a265adcea7640e12b909ea5d1c`; their
versions with the timestamps removed; the nine revisions extracted from
each), the hashes of the five attachments of the integration tape, the
remote snapshots before the push, after the push and after the merge, the
merge commit object, the warning comparisons of both runs against the QA1
baseline of this stone, the certificates of both runs with their summaries
and name lists, the QA1 baseline log itself under `inputs/`, and the two
reading scripts (`certs.py`, `compare_warning_blocks.py`). The report
records the custody of the materials, the Etapa Zero checks (the remote at
the base, no `stone60` ref, no open pull request, `main` protected; the
rulesets not readable with the tools of that session, the required check
observed through the pull-request state), the push of the candidate, PR #46,
run 519 (id 45066737956, job 137344481922; effective checkout `7e1d3e7…`,
the provisional merge "Merge 778e2c7b… into 2ef6500d…"), the merge
`58eb3d1b…` with the expected head locked (parents base + candidate, tree
equal to the candidate's, the diff candidate → merge empty, all branches
and tags preserved), run 520 (id 45068310285, job 137349341525; effective
checkout `58eb3d1b…`), and the inspection of both logs (121/0, manifest
confirmed twice, nine revisions, 114 warning blocks equal to the QA1
baseline and 0 in the new module, 414 outputs for 412 names, 138
multi-line lists, 50/50 of the module, no `sorryAx` in any list, the three
outputs of the separate step identified). The direct download host of the
job logs was denied by the session's network policy; the logs were obtained
through the GitHub tool and are the texts preserved in the package.

One precision, **by the coordination (consolidation tape of 2026-11-22)**,
on the integration tape — not an errata by the publishing instance, the QA1
or Kimi — is recorded here and is to be read with the publication report:

- **C60-P1 — the hashes of A1 and C1.** The integration tape 60-P named the
  five attachments but transcribed in its text only the hashes already
  cited inside the documents (the QA1 report and package in A1, the Kimi
  report in C1). The hashes of the addendum A1 (2,853 bytes,
  `2fb1dd09…6caf`) and of the errata C1 (7,670 bytes, `2c388133…a841`) had
  been communicated by the coordination before the 60-P tape, although they
  were not transcribed in the tape's text; the publishing instance recorded
  them on the files received, as its report says ("sem referência prévia;
  registrado"), which is to be read as "not transcribed in the tape", not
  as "never communicated". The files are the ones received; nothing concerns
  the code.

## Records for the consolidation

- **No documentary record on the module**: neither the QA1 nor the review
  found an imprecision in the candidate or in its docstrings; no reviewer
  requested any change to the candidate, and no code was changed after the
  audits.
- **One auditing addendum and two reviewing errata** — A1 closes a custody
  pendency of the audit's own record; C1 and C2 correct the review's own
  report (three documentary precisions; one ledger identifier). The
  originals are not edited; the corrections are not defects of the code and
  not additional audits; both errata were prompted by the coordination's
  conference after the first pass and are not attributed to discoveries of
  that pass. **One Kimi review with two errata**, each prevailing on its
  point.
- **CI count 414/412.** The runs 519 and 520 emit 414 axiom lists (411 of
  the build + 3 of the workflow step), all standard, for 412 distinct
  names: two workflow outputs repeat names of the build (multiplicity 2)
  and the third, `LatticeGauge.logPartition_eq_tsum_unrooted`, adds a name
  absent from the build's list (not a new theorem); 138 of the 414 lists
  are printed across lines in those runs (137 of the 411 in the QA1 clean
  build and in the constructor's); the parsing recomposes each list up to
  its closing bracket and checks names and multiplicities, not only the
  total. The 50 commands of the module are included. The 50 certificates of
  Q0 and those of the auditor's other tests are the auditor's own and are
  not added to the 414; the 15 certificates of the constructor's test file
  are the constructor's own and are not added either.
- **The textual count and the matrix.** The README's textual method counts
  1,927 declaration lines at `58eb3d1b…`, that is 49 new lines for a module
  of 50 declarations: the regex does not match the line `noncomputable
  instance instPseudoMetricSpace …` (it matches `instance` only at the
  start of a line). The constructor, the QA1 and this consolidation record
  both numbers; the README method is not changed.
- **Reporting precision on dependencies.** "121 built / 0 replayed" refers
  to the project modules in the clean builds of the constructor and of QA1
  and in the CI. The constructor's bench reuses the pinned dependencies
  compiled from source once as a preparation of that bench during Stone 60-A
  (the cache servers being denied by the session's network policy), so its
  clean rebuild records them as 0 built / 1,332 replayed with 4,599
  dependency warning blocks replayed from that preparation, separate from
  the 114 project blocks; the QA1 log records 0 / 0 with no dependency
  diagnostics (a reuse of the cache); on the CI runner (runs 519–520) the
  nine `Built` targets outside `LatticeGauge` are the Mathlib cache tool —
  four Lean modules (`Cache.IO`, `Cache.Hashing`, `Cache.Requests`,
  `Cache.Main`), their four C objects and the executable `cache` — not nine
  rebuilt packages; the nine package revisions are verified against the
  manifest in a separate step, and the remaining dependency artifacts are
  obtained from the cache.
- **Commit identity.** The candidate `778e2c7b…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH signature header present, trailers `Co-Authored-By: Claude Fable 5.1`
  and `Claude-Session`), accepted by the precedent of Stones 52–59; the QA1,
  the review, the publication and this consolidation record the signature
  as present, not as independently authenticated (`git verify-commit` needs
  an `allowedSignersFile` that no bench had; the reviewer had no public
  key); identity and signature were not redone. The merge `58eb3d1b…` was
  created by GitHub.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the ten materials against the reference hashes (the addendum
A1 for the QA1 report and package, the errata C1 for the Kimi report, the
consolidation tape for the errata C2, the internal manifest of the QA1
package for the two matrices; the publication report and its package
against the originals kept on the publisher's bench); the internal
manifests of the QA1 package (39 entries, all verified; 43 entries, 40
files and 3 directories; CRC without errors) and of the publication package
(21 entries, all verified; 27 entries, 22 files and 5 directories); the
byte-identity of the standalone QA1 report and of the two matrices with
their copies inside the package; the correspondence between the candidate
commit, the pull request, the merge commit and the CI runs of `main`
(PR #46; runs 519 and 520, the latter read as `success` through the GitHub
API at consolidation time; parents, root tree and `Phase3/` tree of
`58eb3d1b…`); the Version 59 Release read through the GitHub API (tag
`zenodo-v59` → `2ef6500d…`, `draft = false`, published 2026-10-31T19:04:26Z,
one asset `V59_QUATRO_ARQUIVOS_PARA_UPLOAD.zip`, 2,201,008 bytes, digest
`a7ba421d…62e5` as reported by the API; the body of the Release states the
DOI 10.5281/zenodo.23697327); the absence of any `zenodo-v60` tag or
Release; the identity of the `Phase3/` tree of this documentary commit with
that of `58eb3d1b…` (`ffabe443…`); and the historical manifests of
`docs/audits/stone52/` to `stone59/` (20, 9, 8, 9, 9, 12, 9 and 14 entries,
all verified, no self-inclusion). The Zenodo record of Version 59 was not
consulted from the consolidating session (the host is unreachable from it);
its publication is recorded as confirmed by the coordinator and as stated
in the Release body.

Reported by the auditor, the reviewer and the publisher and **not**
re-executed here: the build, the `#print axioms` runs, the tests and the
mathematical readings; no Lean was executed in this consolidation. Internal
manifest integrity is not by itself proof of authorship or of the execution
of those builds; the primary machine evidence for the integrated code is the
CI history of `main` (runs 519 and 520, see `RESULTS.md`).
