# Stone 54 — independent evidence: QA1 reproduction, adversarial review and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 54 candidate `410bde8146e8f14b698a03387da395a79f81f9eb` (see
[`docs/stone54/RESULTS.md`](../../stone54/RESULTS.md)), integrated on `main` at
`9c0f6fdecee5c8628a2434d032e421edc78bb722` (PR #30): the audit evidence package
of the QA1 reproduction with its report and two matrices, the adversarial
review by Kimi 3, and the publication report of the constructing/publishing
instance. It follows the organization of
[`docs/audits/stone53/`](../stone53/README.md): one package, one review (this
time without errata), one publication record. The package is the primary record
of the audit; the report and the matrices are extracted here only for reading
convenience and are byte-identical to the copies inside the package. Nothing in
this directory is a Lean module: the package contains the auditor's own
disposable test files (including one test that is *expected to fail*), build
logs and matrices, and none of it enters the `LatticeGauge` library, the
`lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are in
English); they are not translated, normalized or edited. The constructor's own
evidence package (`stone54-L_candidate_410bde8.zip`, with its bundle, logs and
tests) is **not** part of this collection: it is the implementer's material,
not an audit.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra (AI model) | different model family from the constructor | tapes (construction 54-L, publication 54-P, this consolidation); reading of the module and of the reports, checks of the evidence, Git objects and publication metadata; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | Lean implementation of the module, local commit and bundle, then, after QA1, push, pull request, merge and CI follow-up in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (`.lake/build` deleted; 114 modules built, 0 replayed, exit 0; own `#print axioms`; own tests V0–V5); preliminary conclusions recorded before opening the constructor's material | **not blind**; not a different model family; not human review |
| Adversarial review | Luan / Kimi 3 (AI model), as identified in the review | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis (module read in full at the fixed SHA, own derivations, hygiene greps, custody via the public GitHub API); **no Lean execution**; QA1 and 54-P opened only after the reviewer's own analysis | **not blind** (prior exposure declared); reading only |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, publication decisions | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_54_evidence.zip`](packages/QA1_54_evidence.zip) | `6698ff0c6f42a03bd443fd043635233324346efc835a95718498fdcb42ac15ba` | Fable 5.1, QA instance | `410bde81…` (candidate; published as [PR #30](https://github.com/consensusframework/yang-mills-mass-gap/pull/30), merge `9c0f6fde…`) | `PASS com observação documental` | 2026-09-14 |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_54-QA1.md`](reports/RELATORIO_54-QA1.md) | `333b9ee90650915111de56ba51ecd923ddeaa4c289cbaae40844cabc2db25e4b` | Fable 5.1, QA instance | `410bde81…` | `PASS com observação documental` | 2026-09-14 |
| 3 | QA1 declaration matrix (extracted) | [`reports/54_QA1_DECLARATION_MATRIX.tsv`](reports/54_QA1_DECLARATION_MATRIX.tsv) | `69eadc93e34d209720018f2653c8ea620b56458c7c0e1c90a1dc36eb18cad990` | Fable 5.1, QA instance | `410bde81…` | 13 rows, 13 PASS | 2026-09-14 |
| 4 | QA1 test matrix (extracted) | [`reports/54_QA1_TEST_MATRIX.tsv`](reports/54_QA1_TEST_MATRIX.tsv) | `cf3b7c112b37ad07fab702b2f28f8c2b538d5f56e0d0c1808e4d66939156aba9` | Fable 5.1, QA instance | `410bde81…` | V0–V4 positive; V5x expected application failure | 2026-09-14 |
| 5 | Adversarial review | [`kimi/RELATORIO_54-K-ADV.md`](kimi/RELATORIO_54-K-ADV.md) | `53e6517d6a469bcb1d6a289e468e0fd506936bfd544425aac30e0a2fd420d626` | Luan / Kimi 3 | `410bde81…` (sources) and `9c0f6fde…` (scientific merge) | `PASS NO ESCOPO` | 2026-09-14 |
| 6 | Publication report (FITA 54-P) | [`publication/RELATORIO_54-P.md`](publication/RELATORIO_54-P.md) | `febf6d868bc00f6de655555e7d87a8197617f2f3c4603f64fe42dcbd15927819` (observed at consolidation; no prior reference hash) | Fable 5.1, constructing/publishing instance | `410bde81…` → `9c0f6fde…` | n/a (record) | 2026-09-14 |

SHA-256 of every file of this directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv`, the package, the three extracted files, the review and the
publication report; no self-inclusion). Machine-readable provenance:
[`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_54_evidence.zip` (`out/`, 30 files; internal manifest
`out/SHA256SUMS_54-QA1.txt`, 29 entries — every file of the package except the
manifest itself). Contents: the report, `PRELIMINARY_CONCLUSIONS_first_pass.md`
(written before the auditor opened the constructor's logs and tests), the two
matrices, `environment.txt` (Lean 4.15.0 commit `11651562caae`, Lake
5.0.0-1165156, Mathlib `9837ca9d…`, `lean-toolchain` `leanprover/lean4:v4.15.0`,
candidate `410bde81…`), `build_directed.log/.result` (`lake build
LatticeGauge.ActivityDampingLipschitzRefined`, exit 0, 252 s),
`build_full_clean.log/.result` (`rm -rf .lake/build && lake build`, exit 0,
550 s, **114 modules built, 0 replayed**, 0 errors, 114 inherited warnings with
the same full text as the Stone 53 baseline, 0 in the new module, 0 `sorryAx`,
179 certificates), `clean_build_start_utc.txt`, the pre/post manifests of the
bench, `hygiene.txt`, `warnings_candidate.txt` (empty),
`warnings_file_line_QA1.txt`, and `tests/` (six `.lean` files, their logs and
two preserved first-attempt logs of the auditor's own slips, resolved
autonomously). Logs are not duplicated outside the package.

Key results reported by the auditor (not re-executed here): 13/13 own
`#print axioms` certificates equal to `[propext, Classical.choice,
Quot.sound]`, no `sorryAx`; `#check` of the refined capstone and of the Stone
53 capstone side by side, same hypotheses, no `DependsOnlyOn`; the scalar bound
re-derived from `Real.add_one_le_exp` alone, valid for negative exponents and
`q = 0`, false without the upper bound (V1); the κ = 2 accounting and the
erosion with `m_T > n` (V2); the budget (1/2, 2) re-instantiated from the
generic `coreLocalBudget` and the closure re-derived without the two final
theorems (V3); the endpoints and the comparison of constants (V4, including
the effective application of the refined capstone at θ = θ′ and the proof
that equality of the complete constants forces `Cf = 0 ∨ D_s = 0`); the
expected application failure at θ = 2 (V5x), classified as such and not as a
counterexample.

## Reading the review together with the editorial precisions (GPT Astra)

`kimi/RELATORIO_54-K-ADV.md` is one adversarial review with no errata; it is
preserved exactly as received. The following two precisions, attributed to
the architectural review of GPT Astra, are recorded here for the joint
reading; they do not change the verdict and do not constitute another audit:

1. `CovarianceDecay.lean` belongs to Stone 50, gate 50-A19c, per the header
   of that source. The reference to "51-E" in item I1 of the review is
   misplaced.
2. "Scalar mean value" in section B of the review denotes the scalar bound of
   the exponential `|e^x − e^y| ≤ e^q·|x − y|`; the formal derivation uses
   `Real.add_one_le_exp`, not the mean-value theorem — as section A of the
   review itself states.

## Records D1 / D2 / I1

- **D1.** The docstring of `refined_constant_le_published_constant` says the
  constants "agree exactly when `D_s = 0`" and omits `Cf = 0`. The theorem
  states `≤` and is correct. Under `Cf ≥ 0`, equality of the complete constants
  occurs when `Cf = 0` or `D_s = 0`; a strict improvement requires `Cf > 0` and
  `D_s > 0`. In the complete right-hand sides, θ = θ′ also produces equality at
  zero. This compares bounds, not a decrease of the actual deviation. The
  docstring is left as committed; this record, with reference to the original
  declaration, is the correction.
- **D2.** The constructor's strict test compares only the exponentials
  `exp(6·D/113) < exp(8·D/113)` for `D > 0`; the QA1 test covers the complete
  prefactor. The two coverages are distinct.
- **I1.** `import LatticeGauge.CovarianceDecay` serves only the one-line
  wrapper `sum_halfTilt_two_le`; avoidable, legitimate and preserved.
- **Commit identity.** The candidate `410bde81…` carries the identity
  configured in the publishing environment, accepted by the precedent of Stone
  53; identity and signature were not redone.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the package and of the review against the hashes supplied by
the coordinator, and the hash of the publication report observed and checked
against the Git objects and the PR/CI records; the internal manifest of the
package (29 entries, all verified; no absolute paths, path traversal or links
in the archive); the byte-identity of the extracted report and matrices with
their copies inside the package; the correspondence between the candidate
commit, the pull request, the merge commit and the CI runs of `main` (PR #30;
runs 487 and 488); the identity of the `Phase3/` tree of this documentary
commit with that of `9c0f6fde…`.

Reported by the auditor and the reviewer and **not** re-executed here: the
builds, the `#print axioms` runs, the tests and the mathematical readings.
Internal manifest integrity is not by itself proof of authorship or of the
execution of those builds; the primary machine evidence for the integrated code
is the CI history of `main` (runs 487 and 488, see `RESULTS.md`).
