# Stone 55 — independent evidence: QA1 reproduction, adversarial review with errata, and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 55 candidate `0c50b6d5e23915f13d6f36d560a58ba6f24ae97b` (see
[`docs/stone55/RESULTS.md`](../../stone55/RESULTS.md)), integrated on `main` at
`d6ce3d7232f08b5f975dfa8c6f43ec5031937e10` (PR #33): the audit evidence package
of the QA1 reproduction with its report and two matrices, the adversarial
review by Kimi 3 with its errata, and the publication report of the
constructing/publishing instance. It follows the organization of
[`docs/audits/stone54/`](../stone54/README.md) and
[`docs/audits/stone53/`](../stone53/README.md): one package, one review (this
time with one errata, as for Stone 53), one publication record. The package
is the primary record of the audit; the report and the matrices are extracted
here only for reading convenience and are byte-identical to the copies inside
the package. Nothing in this directory is a Lean module: the package contains
the auditor's own disposable test files (including one test that is *expected
to fail*), build logs and matrices, and none of it enters the `LatticeGauge`
library, the `lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are in
English); they are not translated, normalized or edited. The constructor's own
evidence package (`STONE55L_evidence.zip`, with its bundle, logs and tests
V1–V4) is **not** part of this collection: it is the implementer's material,
not an audit, and it is not incorporated as independent evidence.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra (AI model) | different model family from the constructor | tapes (feasibility 55-A, construction 55-L, publication 55-P, this consolidation); reading of the modules and of the reports, checks of the evidence, Git objects and publication metadata; the observation that originated the errata C1; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | Lean implementation of the two modules, local commit and bundle with the constructor's tests V1–V4, then, after QA1, push, pull request, merge and CI follow-up in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (dependencies from the committed manifest, no `lake update`; `.lake/build` deleted; 116 modules built, 0 replayed, exit 0; own `#print axioms`; own tests W0–W5x); preliminary conclusions recorded before opening the constructor's logs and tests | **not blind** (prior exposure declared); not a different model family; not human review |
| Adversarial review | Luan / Kimi 3 (AI model), as identified in the review | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis (both modules read in full at the fixed SHA before any QA or constructor material, own derivations, hygiene and dependency checks, custody via the public GitHub API and codeload at the fixed SHA); **no Lean execution**; QA1 and the constructor's package opened only after the reviewer's own analysis | **not blind** (prior exposure to Stones 49–54 declared); reading only |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model. No
Lean execution is attributed to GPT Astra or to Kimi 3.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_55_evidence.zip`](packages/QA1_55_evidence.zip) | `f21e2f65e1e8efcbca66311f866cf22db10476271d51eb3a67d822aa3de6f021` | Fable 5.1, QA instance | `0c50b6d5…` (candidate; published as [PR #33](https://github.com/consensusframework/yang-mills-mass-gap/pull/33), merge `d6ce3d72…`) | `PASS NO ESCOPO, com observações documentais` | 2026-09-17 |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_55-QA1.md`](reports/RELATORIO_55-QA1.md) | `911dc9bafd323f0443fc21435c11c778e1708d91cbf80a088273aa07a695ddf1` | Fable 5.1, QA instance | `0c50b6d5…` | `PASS NO ESCOPO, com observações documentais` | 2026-09-17 |
| 3 | QA1 declaration matrix (extracted) | [`reports/55_QA1_DECLARATION_MATRIX.tsv`](reports/55_QA1_DECLARATION_MATRIX.tsv) | `4834fd115ebe2f26de08d0cdd87cb79d4699e5aaf847f5cb86774d6616f95dca` | Fable 5.1, QA instance | `0c50b6d5…` | 78 rows (68 theorems, 10 definitions), 78 PASS | 2026-09-17 |
| 4 | QA1 test matrix (extracted) | [`reports/55_QA1_TEST_MATRIX.tsv`](reports/55_QA1_TEST_MATRIX.tsv) | `22572da8bcdb7b642b1e3451553aa81b2ecaf36e600942e2617a2bca52c26ffc` | Fable 5.1, QA instance | `0c50b6d5…` | W0–W4 positive; W5x expected application failure | 2026-09-17 |
| 5 | Adversarial review | [`kimi/RELATORIO_55-K-ADV.md`](kimi/RELATORIO_55-K-ADV.md) | `fe396514aa285dd340167b35013ed31210e2fdc4bd01af0dbd9de8aa0a4ebb77` | Luan / Kimi 3 | `0c50b6d5…` (sources) and `d6ce3d72…` (scientific merge) | `PASS NO ESCOPO` | 2026-09-19 |
| 6 | Errata C1 to the adversarial review | [`kimi/ERRATA_55-K-ADV-C1.md`](kimi/ERRATA_55-K-ADV-C1.md) | `65f6c004ae318693da74ef2b8fffeba1a9e4cb718e4079a909f722bdea8285f9` | Luan / Kimi 3 | (corrects the attribution of the tests in document 5) | verdict unchanged: `PASS NO ESCOPO` | 2026-09-19 |
| 7 | Publication report (FITA 55-P) | [`publication/RELATORIO_55-P.md`](publication/RELATORIO_55-P.md) | `9eb79e92147372e1ab9e1451654203f34c95dca5d66d2c8979c8c6c9c0b62597` (observed at consolidation; no prior reference hash) | Fable 5.1, constructing/publishing instance | `0c50b6d5…` → `d6ce3d72…` | n/a (record) | 2026-09-17 |

SHA-256 of every file of this directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv`, the package, the three extracted files, the review, the
errata and the publication report; no self-inclusion). Machine-readable
provenance: [`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_55_evidence.zip` (`out/`, 31 entries; internal manifest
`out/SHA256SUMS_55-QA1.txt`, 28 entries — every file of the package except the
manifest itself). Contents: the report, `PRELIMINARY_CONCLUSIONS_first_pass.md`
(written before the auditor opened the constructor's logs and tests), the two
matrices, `environment.txt` (2026-09-17T18:15:57Z; Lean 4.15.0 commit
`11651562caae`, Lake 5.0.0-1165156, `lean-toolchain` `leanprover/lean4:v4.15.0`,
candidate `0c50b6d5…`, manifest SHA-256 `c376bbe9…1227`, `lake update: NOT
run`), `build_directed.log/.result` (`lake build
LatticeGauge.ActivityProfileDampingStability`, exit 0, 343 s),
`build_full_clean.log/.result` (`rm -rf .lake/build && lake build`, exit 0,
644 s, **116 modules built, 0 replayed** — neither of `LatticeGauge` nor of
the dependencies —, 0 errors, 114 inherited warnings all in `LatticeGauge/`
with the same full text as the Stone 54 baseline, 0 in the new modules, 0
`sorryAx`, 247 certificates), `clean_build_start_utc.txt`, the pre/post
manifests of the bench (identical), `hygiene.txt` (lexical checks and the map
of the 104 identifiers consumed, with their defining modules),
`warnings_candidate.txt` (empty), `warnings_file_line_QA1.txt`, and `tests/`
(six `.lean` files W0–W5x, their logs and one preserved first-attempt log of
the auditor's own slip in W4f, resolved autonomously). Logs are not duplicated
outside the package.

Key results reported by the auditor (not re-executed here): 68/68 own
`#print axioms` certificates equal to `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`; `#check` of the capstone, of the two-term form and
of the Stone 54 capstone, no `DependsOnlyOn`, no `δ ≤ 1` (W0); non-constant
family and tuple weights with repetitions counted by position, the
telescoping lemma with an own two-factor proof, the empty product, a zero
factor and a proved counterexample outside `[0, 1]` (W1); the two-profile
ledger re-derived from the exponential form of both sides without the
candidate's ledger lemma, plus sign on the bridges, correction vanishing on
the allowed cores (W2); the series identity, the κ = 2 control re-derived from
the Stone 54 scalar lemma, the budgets (1/2, 2) and (7/8, 1) admissible and
(7/8, 2) not, the closure re-derived by the columns without the two final
theorems, the erosion with `m_T > n` (W3); the applications — δ = 0 by
effective application, profiles equal on the touching polymers and different
elsewhere, δ = 7, the scalar recovery of Stone 54 by an own specialization,
the zero profile without `DependsOnlyOn`, the unit profile with it, the empty
region for non-constant real profiles outside `[0, 1]` (W4); the expected
application failure for a profile of value 2 (W5x), classified as such and not
as a counterexample. The second pass over the constructor's material found
no divergence beyond the documentary precisions already recorded.

## Reading the two Kimi files together

`kimi/RELATORIO_55-K-ADV.md` and `kimi/ERRATA_55-K-ADV-C1.md` are **one review
with one errata, not two approvals**. Read them together; **C1 prevails on
the attribution of the tests**: the opening and section 4 of the review
attribute the tests V1–V4 to QA1; in fact V1–V4 (`V1_profiles_tuples`,
`V2_ledger_signs`, `V3_capstone_applications`, `V4_erosion_columns`) are the
**constructor's** tests, delivered in the constructor's package and checked
by QA1 only in its second pass, while the auditor's own tests are **W0–W5x**,
delivered in the QA1 package and classified in its test matrix. W5x is a
negative test expected to fail (a profile of value 2): an application failure
by a missing hypothesis, not evidence of falsity nor of indispensability, and
not a positive example. The clean reconstruction of the 116 modules, the W0
certificates and the tests W1–W5x belong to QA1; no Lean execution — of the
constructor or of QA1 — is the reviewer's own. The errata originated in an
observation of GPT Astra relayed by the coordination and was verified by the
reviewer against the evidence packages before being accepted. The verdict
`PASS NO ESCOPO` is maintained; the correction concerns the record of
authorship of the tests and not the proofs, the hypotheses, the custody or the
mathematics reviewed. The two Kimi files are preserved exactly as received;
these notes are not applied to them.

## Records D1 / D2 / D3 / D4 / D5 / I1

Recorded by QA1, confirmed by the review and consolidated here without
editing the code (the scientific modules are not edited by the documentary
consolidation; docstrings and headers are left as committed):

- **D1.** `profile_bound_self` (55-B) only simplifies the right-hand side of
  the capstone at δ = 0; the effective application of the capstone with δ = 0
  is proved by the constructor's test V3 and the auditor's tests W4a/W4b.
- **D2.** "KP as OUTPUT" (header of 55-A and docstring of
  `profilePolymerGas_pos`) is to be read as follows: the KP criterion is
  **established** (`abstractKP_of_beta_le_one_div_40000`) and **transported**
  (`abstractKP_profileDampedActivity`), it feeds the exponential
  representation of the gas, and the positivity of the gas is a consequence of
  that representation. The proof is not affected.
- **D3.** The header of 55-A calls the constant-profile specializations
  "definitional identities" in bloc; `profileDampedActivity_const`,
  `profilePolymerGas_const` and `profileCoreExponent_const` are `rfl`, while
  `profileWeight_const`, `tupleProfileWeight_const`, `profileMarkedGas_const`
  and `profileExpectation_const` are theorems by rewriting. The constructor's
  declaration table already distinguishes the cases.
- **D4.** The constructor's test V3 records a `rfl` between
  `…_le_local_exp_decay_of_profile` and the Stone 54 capstone as proof
  irrelevance, not as equality of derivations; it is annotated as such in the
  test and is not used as evidence of anything else.
- **D5.** The zero profile recovers the Stone 51 restricted functional with no
  hypothesis (`profileExpectation_zero`); the comparison with the Gibbs
  expectation requires `DependsOnlyOn f s` (`profileExpectation_one`,
  `abs_profileExpectation_sub_gibbsExpectation_le`). The asymmetry is real and
  necessary.
- **I1.** `import LatticeGauge.CovarianceDecay` is inherited from Stone 54 for
  the one-line wrapper `sum_halfTilt_two_le`; already observed in the Stone 54
  audit; nothing new.
- **Reporting precision.** The constructor's report describes its clean build
  as "0 Replayed" with reference to the project modules; its clean log also
  shows replays and warnings from a Mathlib compiled from source on the
  constructor's bench, which QA1 separated by filter. QA1 and the CI report
  the two populations separately (QA1: 0 replays of `LatticeGauge` and of the
  dependencies; CI: 116 built / 0 replayed of `LatticeGauge`, 9 built / 0
  replayed of dependencies).
- **Commit identity.** The candidate `0c50b6d5…` carries the identity
  configured in the publishing environment, accepted by the precedent of
  Stones 52–54; identity and signature were not redone.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the package, of the standalone QA1 report, of the review and
of the errata against the hashes supplied by the coordinator, and the hash of
the publication report observed and checked against the Git objects and the
PR/CI records; the internal manifest of the package (28 entries, all
verified; no absolute paths, path traversal or links in the archive; 31
entries under `out/`); the byte-identity of the standalone QA1 report with
its copy inside the package, and of the extracted report and matrices with
their copies inside the package; the correspondence between the candidate
commit, the pull request, the merge commit and the CI runs of `main` (PR #33;
runs 493 and 494; parents, root tree and `Phase3/` tree of `d6ce3d72…`); the
identity of the `Phase3/` tree of this documentary commit with that of
`d6ce3d72…` (`20ffea86…`).

Reported by the auditor and the reviewer and **not** re-executed here: the
builds, the `#print axioms` runs, the tests and the mathematical readings.
Internal manifest integrity is not by itself proof of authorship or of the
execution of those builds; the primary machine evidence for the integrated code
is the CI history of `main` (runs 493 and 494, see `RESULTS.md`).
