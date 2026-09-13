# Stone 52 — stage audits (52-A0 … 52-E) and final adversarial review

This directory preserves, byte for byte, the seven audit evidence packages
produced for the six gates of Stone 52 (see
[`docs/stone52/RESULTS.md`](../../stone52/RESULTS.md)), together with the
audit reports extracted from them, and, under [`kimi/`](kimi/), the final
adversarial review of the integrated Stone 52 by Kimi 3 with its two
corrective addenda (see "Final adversarial review" below). The packages are the primary record; the
reports are extracted here only for reading convenience and are byte-identical
to the copies inside the packages. Nothing in this directory is a Lean module:
the packages contain the auditors' own disposable test files (including tests
that are *expected to fail*), build logs and matrices, and none of it enters
the `LatticeGauge` library, the `lakefile.toml` globs or the CI build.

All reports are in Portuguese, as written by the auditors; they are not
translated, normalized or edited.

## Who audited, and how independent it is

Every audit was performed by a **separate instance of Claude Fable 5.1** on its
own pinned bench (Lean 4.15.0, Mathlib `9837ca9d…`, resolved manifest
`c376bbe9…1227`), working from the git bundle, the base commit and the code,
with its own tests, in read-only mode. "Independent" here means: a distinct
instance, bench and test set from the implementing instance. It does **not**
mean a different model family (implementer and auditor are both Claude Fable
5.1), and it does not mean human review. The auditing instance was the same
across the seven reports and declares its prior exposure in each report:

| Report | Blindness declared by the auditor |
|---|---|
| 52-A0 QA1, 52-A QA1 | blind: no builder report, diff, matrix, test or log read; everything reconstructed from the bundle |
| 52-A/C1 QA2 | delta audit of the repair `0f86ea8… → 4f40443…` by the same instance that wrote 52-A QA1; the 56 declarations approved in QA1 were checked unchanged, not re-audited |
| 52-B, 52-C, 52-D QA1 | prior exposure declared (the earlier gates); two-pass protocol — first pass with bundle and base only, preliminary conclusions recorded in `PRELIMINARY_CONCLUSIONS_first_pass.md` before any builder material was opened, second pass compares with the builder's package |
| 52-E QA1 | explicitly **not blind** (the auditor had audited every previous gate and written the 52-C preparatory note); same two-pass protocol |

These are seven stage-audit opinions with continuity of the auditing
instance. They are not seven independent reviewers, not a consensus of seven
models, and not a human peer review.

## Index

| # | Gate | Round | Package (canonical name) | Report | Candidate audited | Scope of the audit | Literal verdict | Date |
|---|---|---|---|---|---|---|---|---|
| 1 | 52-A0 | QA1 | [`packages/QA1_52A0_evidence.zip`](packages/QA1_52A0_evidence.zip) | [`reports/RELATORIO_52-A0-QA1.md`](reports/RELATORIO_52-A0-QA1.md) | `76e10feb40a064e5813828fc1feae7c0949d3ec6` (published as [PR #20](https://github.com/consensusframework/yang-mills-mass-gap/pull/20), merge `d62f50d2…`) | `ActivityDampingBudgets.lean`: 35 declarations read, 11 certificates, 5 own tests | `QA1 PASS WITH RESERVATIONS` | 2026-09-06 |
| 2 | 52-A | QA1 | [`packages/QA1_52A_evidence.zip`](packages/QA1_52A_evidence.zip) | [`reports/RELATORIO_52-A-QA1.md`](reports/RELATORIO_52-A-QA1.md) | `0f86ea8dad722ea2cec4ceb6bd624b7eb2709ef8` — **superseded**, never published | `ActivityDampedObservableGas.lean` (56 declarations), 7 own tests | `52-A QA1 PASS WITH RESERVATIONS` | 2026-09-07 |
| 3 | 52-A (C1) | QA2 | [`packages/QA2_52A_C1_evidence.zip`](packages/QA2_52A_C1_evidence.zip) | [`reports/RELATORIO_52-A-QA2.md`](reports/RELATORIO_52-A-QA2.md) | `4f4044333193fb734a7103ea01f6c472ed464563` (published as [PR #21](https://github.com/consensusframework/yang-mills-mass-gap/pull/21), merge `d4fb2937…`) | delta `0f86ea8… → 4f40443…` only: 10 new declarations, unchanged 56, provenance; not a new full audit | `52-A QA2 PASS — C1 READY FOR PUBLICATION` | 2026-09-07 |
| 4 | 52-B | QA1 | [`packages/QA1_52B_evidence.zip`](packages/QA1_52B_evidence.zip) | [`reports/RELATORIO_52-B-QA1.md`](reports/RELATORIO_52-B-QA1.md) + [`reports/ERRATA_52-B-QA1.md`](reports/ERRATA_52-B-QA1.md) | `322f29c331e13f2e257da15c7f6e17fc1efe0e19` ([PR #22](https://github.com/consensusframework/yang-mills-mass-gap/pull/22), merge `eb3051fd…`) | `ActivityDampingLedger.lean`: exact ledger, 15 public declarations certified, 9 own tests | `52-B QA1 PASS` | 2026-09-10 (errata 2026-09-11) |
| 5 | 52-C | QA1 | [`packages/QA1_52C_evidence.zip`](packages/QA1_52C_evidence.zip) | [`reports/RELATORIO_52-C-QA1.md`](reports/RELATORIO_52-C-QA1.md) | `6502ca9f51754d7e084106e8fa1022ca0fa2427a` ([PR #23](https://github.com/consensusframework/yang-mills-mass-gap/pull/23), merge `2708eb9f…`) | `ActivityDampingConnector.lean`: 19 declarations, 12 own tests | `PASS` | 2026-09-11 |
| 6 | 52-D | QA1 | [`packages/QA1_52D_evidence.zip`](packages/QA1_52D_evidence.zip) | [`reports/RELATORIO_52-D-QA1.md`](reports/RELATORIO_52-D-QA1.md) | `6168e2336495a968e4c74005b61d7e33e5f1cb76` ([PR #24](https://github.com/consensusframework/yang-mills-mass-gap/pull/24), merge `2a391941…`) | `ActivityDampingColumnBounds.lean`: the two column bounds, 15 declarations (14 in-file certificates), 11 own tests | `PASS` | 2026-09-11 |
| 7 | 52-E | QA1 | [`packages/QA1_52E_evidence.zip`](packages/QA1_52E_evidence.zip) | [`reports/RELATORIO_52-E-QA1.md`](reports/RELATORIO_52-E-QA1.md) | `8b638c94a7db54eb8b5780f962e0e79d522db6ad` ([PR #25](https://github.com/consensusframework/yang-mills-mass-gap/pull/25), merge `6231d5cb…`) | `ActivityDampingStability.lean`: the capstone, 7 declarations, 11 own tests | `PASS` | 2026-09-12 |

Dependencies between reports: QA2 (#3) presupposes QA1 of 52-A (#2) and
audits only the delta; 52-B, 52-C, 52-D and 52-E each audit one leaf module
over the previously integrated `main`, so each presupposes the integration of
the earlier gates without re-auditing them. 52-D does not certify the
combination of the two columns; 52-E certifies exactly that combination.

SHA-256 of every package, report, review file and index file: [`SHA256SUMS.txt`](SHA256SUMS.txt).
Machine-readable provenance of the seven packages: [`PROVENANCE.tsv`](PROVENANCE.tsv).

## Final adversarial review (Kimi 3)

After the six gates and their seven stage audits, the integrated Stone 52 was
reviewed adversarially by **Kimi 3 (AI model)**, identified in the review as
"Luan", a model of a different family from the implementer and the stage
auditor. This is **one review with two corrective addenda**, not three
approvals and not a new audit of the code.

| File | SHA-256 | Content |
|---|---|---|
| [`kimi/RELATORIO_52-K-ADV.md`](kimi/RELATORIO_52-K-ADV.md) | `668dccd744ebdc1fdceda2feb44308313948132e4805dccb43618c586fda9992` | the review, 2026-09-13 |
| [`kimi/ERRATA_52-K-ADV-C1.md`](kimi/ERRATA_52-K-ADV-C1.md) | `6c2d7fc39bf041cfd16e5b4a2ce780e5c820453d866d91abf283437dab805bf2` | errata C1: six precisions to the review's own wording, counts and method statements |
| [`kimi/ADENDO_52-K-ADV-C2.md`](kimi/ADENDO_52-K-ADV-C2.md) | `f8a6ba344e499ba8644c31ee52b5f2e9ceec51c07f39c7f4055549929e2bc058` | addendum C2: one further precision on `touchCount` in errata C1 |

**Read the review, errata C1 and addendum C2 together; C1 and C2 prevail on
the points they correct.** The three files are preserved exactly as
received; nothing in them was edited or merged.

- **Verdict:** `PASS NO ESCOPO` ("pass within scope"), maintained after C1
  and C2. The reviewer's own formulation: no defect found within the scope and
  the verifications described; absence of findings is not a guarantee of
  infallibility.
- **Reviewed SHA:** the integrated state `00600e03e36f5fdfdfda1983a17929c3efa6b44f`
  (merge of [PR #26](https://github.com/consensusframework/yang-mills-mass-gap/pull/26)),
  tree `d8cba4e4…`, whose `Phase3/` tree `bf2fae8c…` is that of the audited
  52-E candidate `8b638c94…`. The review applies to that state only, not to
  any later scientific change.
- **Modality:** adversarial mathematical and code review by reading (all six
  Stone 52 modules read in full, independent derivations, hygiene greps,
  independent recount of certificates, declarations and lines; CI status read
  from the public API). **No Lean execution or reproduction by the
  reviewer.** Prior exposure declared (the reviewer had audited Stones 49–51);
  the six modules and the stage audits were read only after the reviewer's
  own analysis. This is not a blind audit.
- **What the addenda correct:** only the review's own text — a wrong file
  path, two line counts given without execution, two explanatory glosses on
  the damping mechanism and on `touchCount` (the theorems in the code are
  stated correct), an inequality written as an equality, an over-general
  remark on where `8/(3e)` occurs, and the clarification that the described
  proof steps were reconstructed by reading, not executed. They change no
  conclusion and correct nothing in the scientific code.
- **What it adds to the chain:** a reading by a different model family. The
  clean reproduction of the 111 modules remains the one performed by the
  stage-auditing Claude Fable 5.1 instance in the 52-E audit (`rm -rf
  .lake/build && lake build`, 111 built, 0 replayed); no reproduction by a
  different model family, and no human review, exists.

Distinguish therefore: seven stage audits by the Fable auditing instance
(with builds); one final adversarial review by Kimi 3 with two addenda
(without builds); one clean reproduction of the 111 modules already
performed in the 52-E stage audit.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of each package against the hashes supplied by the coordinator;
the internal `SHA256SUMS*.txt` manifest of each package (27, 31, 29, 37, 41,
37 and 39 entries; 241 in total; all entries verified); the absence of
duplicate names, absolute paths, path traversal and links in the archives;
the byte-identity of the extracted reports with their copies inside the
packages; and the correspondence between the candidate commits named in the
reports and the pull requests, merge commits and CI runs of `main`.

Reported by the auditors and **not** re-executed here: the builds, the
`#print axioms` runs, the tests and the mathematical readings. Internal
manifest integrity is not by itself proof of authorship or of the execution of
those builds; the primary machine evidence for the integrated code is the CI
history of `main` (runs 467–478, see `RESULTS.md`).

The builder's own evidence packages (`STONE52-*-L_evidence.tgz`) are **not**
part of this collection; they are the implementer's material, not audits.

## Evolution of the findings

- **52-A0 QA1 — `PASS WITH RESERVATIONS`.** R1 (cosmetic): one hypothesis
  (`θ ≤ 1`) of `one_sub_dampedPow_le_nat_mul_one_sub` is superfluous; no
  action required. R2 (medium, prospective): the auditor anticipated that
  reaching the exact target constant would require a general mean-value lemma
  `|e^a − e^b| ≤ |a − b|·e^{max(|a|,|b|)}`, absent from the base. The route
  actually taken by 52-C and 52-D reached the constant differently — through
  the factorization `e^{E(1)} − e^{E(θ)} = e^{E(1)}·(1 − e^{C})` and the
  existing exponential control — so that lemma was never needed and was never
  added. The 52-B report records R2 as still open at that time; the 52-C
  report records it as dispensed. The old report is preserved as written.
- **52-A QA1 — `PASS WITH RESERVATIONS`** on the candidate `0f86ea8…`, which
  was **superseded**: the published commit `4f40443…` (C1) is a replacement
  over the same base, not a descendant stacked on `0f86ea8…`. R1 (coefficient
  bridges `kpSignedUnrootedCoeff_dampedActivity` /
  `kpConnectorUnrootedCoeff_dampedActivity`) and R2 (concatenation and
  empty-region interfaces) were resolved by C1, as QA2 verifies; R4
  (author/committer identity of `0f86ea8…` differed from the chain pattern)
  was resolved by C1, which restores the chain identity; R3 (a slightly strong
  hypothesis, `0 ≤ θ ≤ 1` where `|θ| ≤ 1` would do) is cosmetic and remains
  as recorded. QA1 and QA2 must be read together.
- **52-A/C1 QA2 — `PASS — C1 READY FOR PUBLICATION`.** Ten new declarations
  verified; the 56 earlier ones unchanged; no content reservation.
- **52-B QA1 — `PASS`.** No defect. I1 (informative): `ledger_weight_allowed`
  restates an existing lemma. I2 (informative, about the builder's package):
  the builder's build log has two segments and lists each inherited warning
  twice; there are 114 inherited warnings, not 228. F1 (future): the R2 lemma
  of 52-A0, then still open. The **errata** of 2026-09-11 corrects only the
  sign in §6.1 of the report (the orientation of `E_T(1) − E_T(θ)` in the
  interface note for 52-C); it changes nothing in the code, the candidate or
  the verdict.
- **52-C QA1 — `PASS`.** No defect. One inherited interface limitation
  (`summable_kpDampedConnectorUnrootedCoeff` takes the separation hypothesis
  in barrier-region form). Three documentary observations on the builder's
  package (D1–D3), none on the code.
- **52-D QA1 — `PASS`.** No defect. I1: `hCf0 : 0 ≤ Cf` is redundant
  (derivable from `hCf`), kept for uniformity with Stone 51 signatures. D1:
  the module's in-file `#print axioms` list has 14 entries while the auditor
  certified all 15 declarations (the missing one is
  `sevenEighthsBudgetTerm_nonneg`); the module was not modified to extend the
  list. D2: the builder's test matrix labelled two application failures as
  proof that a hypothesis is "genuinely required"; a failed application does
  not prove indispensability, and for `hCf0` the claim is inexact. 52-D does
  not certify the combination of the columns (that is 52-E). A corrected
  builder package for 52-D exists; it is the implementer's material and is
  not part of this collection.
- **52-E QA1 — `PASS`.** No mathematical defect. D1: the module header says
  "the bound at r = ∅ is also stated", but there is no separate declaration —
  only the identity `…_empty_region_eq_zero` and its immediate consequence;
  the module was not edited for this. D2: the recovery of the Stone 51
  capstone at `θ = 0` is a comparison, not a formal dependency (the Stone 51
  capstone module is not imported). D3: a counting label in the builder's
  report. I1: the `hCf0` asymmetry with Stone 51 (derived here, explicit
  there).

## Layout

```
docs/audits/stone52/
  README.md            this index
  PROVENANCE.tsv       one line per package
  SHA256SUMS.txt       SHA-256 of packages, reports and index files (relative paths)
  packages/            the seven audit packages, byte-identical to the files received
  reports/             the audit reports (and the 52-B errata), extracted byte for byte
  kimi/                the Kimi 3 adversarial review, errata C1 and addendum C2, byte-identical
```
