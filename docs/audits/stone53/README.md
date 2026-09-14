# Stone 53 — independent evidence: QA1 reproduction, final adversarial review and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 53 candidate `abad16674ab9b713c7ef9d0344c8f5cc02b09739` (see
[`docs/stone53/RESULTS.md`](../../stone53/RESULTS.md)), integrated on `main` at
`a7ae1c0cb81aa8829c056482afc74f9629485fd6` (PR #28): the audit evidence package
of the QA1 reproduction with its report and two matrices, the final
adversarial review by Kimi 3 with its errata C1, and the publication report of
the constructing/publishing instance. Following the organization of
[`docs/audits/stone52/`](../stone52/README.md), adapted to the actual amount of
evidence: Stone 53 was built as two modules under one construction tape and
audited once, so there is one package, one review with one errata, and one
publication record. The package is the primary record of the audit; the
report and the matrices are extracted here only for reading convenience and
are byte-identical to the copies inside the package. Nothing in this
directory is a Lean module: the package contains the auditor's own disposable
test files (including two tests that are *expected to fail*), build logs and
matrices, and none of it enters the `LatticeGauge` library, the
`lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are
in English); they are not translated, normalized or edited. The constructor's
own evidence package (`stone53-L_candidate_abad166.zip`) is **not** part of
this collection: it is the implementer's material, not an audit.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra (AI model) | different model family from the constructor | tapes (feasibility 53-A, construction 53-L, publication 53-P, this consolidation); review of sources, Git objects and evidence, without a Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench (Mathlib pinned, compiled from source) | Lean implementation of both modules, local commit and bundle, then, after QA1, push, pull request, merge and CI follow-up in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (`.lake/build` deleted; 113 modules built, 0 replayed; own `#print axioms`; own tests U0–U5); preliminary conclusions recorded before opening the constructor's material | **not blind** (the auditor had audited the Stone 52 stages and read the constructor's report before rebuilding); not a different model family; not human review |
| Final adversarial review | Kimi 3 (AI model; "Luan" in the review) | **different model family** from the constructor, the QA instance and the architect | mathematical and code review by reading (both modules read in full, own derivations, hygiene greps, CI metadata via the public API); **no Lean execution or reproduction by the reviewer**; the QA and publication material opened only after the reviewer's own analysis | **not blind** (prior exposure to Stones 49–52 declared); reading only |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, publication decisions | no human review of the mathematics has taken place |

Distinguish therefore: one clean reproduction by execution (QA1, same model
family as the implementer), one adversarial reading by a different model
family (Kimi 3, without builds), one publication record. Claude Code is the
execution environment; Claude Fable 5.1 is the model.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_53_evidence.zip`](packages/QA1_53_evidence.zip) | `96d03db9daf6bbfa09f5faf896bec33ab5f556687a78a729fadc0b621ca3b3c1` | Fable 5.1, QA instance | `abad1667…` (candidate; published as [PR #28](https://github.com/consensusframework/yang-mills-mass-gap/pull/28), merge `a7ae1c0c…`) | `PASS NO ESCOPO` | 2026-09-13 |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_53-QA1.md`](reports/RELATORIO_53-QA1.md) | `bc416ed70a85038849464bd1e190bdd5ae264f63b546dafd681a8f9fef09e545` | Fable 5.1, QA instance | `abad1667…` | `PASS NO ESCOPO` | 2026-09-13 |
| 3 | QA1 declaration matrix (extracted) | [`reports/53_QA1_DECLARATION_MATRIX.tsv`](reports/53_QA1_DECLARATION_MATRIX.tsv) | `99e012f27a89795b300d6a2300e7c1b4796fad365309573dcb05d7651a01f451` | Fable 5.1, QA instance | `abad1667…` | 29 rows, 29 PASS | 2026-09-13 |
| 4 | QA1 test matrix (extracted) | [`reports/53_QA1_TEST_MATRIX.tsv`](reports/53_QA1_TEST_MATRIX.tsv) | `9ed4cb000ea03a91f974d57c486370670adab509ad7fca644cd5519756cd8e1e` | Fable 5.1, QA instance | `abad1667…` | U0–U4 positive; U5x, U5y expected application failures | 2026-09-13 |
| 5 | Adversarial review | [`kimi/RELATORIO_53-K-ADV.md`](kimi/RELATORIO_53-K-ADV.md) | `fe884aed62427b663ab8cc14c34a527be5be1f75fefbeae1efced9c3b81f4a77` | Kimi 3 | `abad1667…` (sources) and `a7ae1c0c…` (merge) | `PASS NO ESCOPO` | 2026-09-13 |
| 6 | Errata C1 to the review | [`kimi/ERRATA_53-K-ADV-C1.md`](kimi/ERRATA_53-K-ADV-C1.md) | `87827fa296305e33b68108f126ca40edc322982c09fa518d26e5e26f00d37ca4` | Kimi 3 (same reviewing instance) | `abad1667…` | `PASS NO ESCOPO` maintained | 2026-09-13 |
| 7 | Publication report (FITA 53-P) | [`publication/RELATORIO_53-P.md`](publication/RELATORIO_53-P.md) | `f8fad9a21bb6607f3f5f529e0798d54d2381e5c2fe1088b5a77400a7640f2d92` | Fable 5.1, constructing/publishing instance | `abad1667…` → `a7ae1c0c…` | n/a (record) | 2026-09-13 |

SHA-256 of every file of this directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv`, the package, the three extracted files, the two Kimi files
and the publication report; no self-inclusion). Machine-readable provenance:
[`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_53_evidence.zip` (`out/`, 32 files; internal manifest
`out/SHA256SUMS_53-QA1.txt`, 31 entries — every file of the package except the
manifest itself). Contents: the report, `PRELIMINARY_CONCLUSIONS_first_pass.md`
(written before the auditor opened the constructor's logs and tests), the two
matrices, `environment.txt` (Lean 4.15.0 commit `11651562caae`, Lake
5.0.0-1165156, Mathlib `9837ca9d…`, `lean-toolchain` `leanprover/lean4:v4.15.0`,
candidate `abad1667…`), `build_directed.log/.result` (`lake build
LatticeGauge.ActivityDampingLipschitz`, exit 0, 280 s),
`build_full_clean.log/.result` (`rm -rf .lake/build && lake build`, exit 0,
523 s, 113 `LatticeGauge` modules built, 0 replayed, 0 errors, 114 inherited
warnings on the same file:line pairs as the Stone 52 baseline, 0 warnings in
the new modules, 0 `sorryAx`), `clean_build_start_utc.txt`, the pre/post
manifests of the bench, `hygiene.txt` (lexical greps and the map of the 79
identifiers actually consumed), `warnings_candidate.txt` (empty),
`warnings_file_line_QA1.txt`, and `tests/` (seven `.lean` files, their logs,
and two preserved first-attempt logs of the auditor's own slips, resolved
autonomously). Logs are not duplicated outside the package.

Key results reported by the auditor (not re-executed here): 29/29 own
`#print axioms` certificates equal to `[propext, Classical.choice,
Quot.sound]`; the `#check` of the elaborated capstone with no
`DependsOnlyOn`; the ledger re-derived from the 52-B representation without
invoking any Stone 53 theorem (U1); the ingredients (U2, including a
counterexample to the power inequality outside `[−1, 1]` and the
inadmissibility of the budget `(7/8, 2)`); the closure re-derived without the
two final theorems (U3); the endpoints (U4), among them the **effective
application of the capstone at θ = θ′ (U4a)** — the constructor's own test
for θ = θ′ used `sub_self`, and `lipschitz_bound_self` in the module is the
algebra of the right-hand side only, so U4a is the test that exercises the
theorem there; and the two expected failures U5x (θ = 2) and U5y (θ′ = 1
without `DependsOnlyOn`), classified by the auditor as application failures,
not as evidence of falsity outside `[0, 1]` or of indispensability.

## Reading the two Kimi files together

`kimi/RELATORIO_53-K-ADV.md` and `kimi/ERRATA_53-K-ADV-C1.md` are **one review
with one errata, not two approvals**. Read them together; **C1 prevails on
the four points it corrects**: (1) the model families — the constructor and
the QA instance are two instances of Claude Fable 5.1, the architect of Stone
53 is GPT Astra (a different family), and the review adds Kimi 3 as a third
family; human coordination exists in the chain, what does not exist is
specialized human mathematical review of the proofs; (2) the hypotheses per
declaration — the ledger dispenses with `Measurable f`, the majorant and the
separation as well as with `DependsOnlyOn f s`; `mf`, `hCf` and `hsep` enter
only the two-term form and the capstone; (3) the domain of the scalar
inequality `|θ^j − θ′^j| ≤ j·|θ − θ′|` — `[0, 1]` is sufficient, not
necessary; (4) the custody item on the commit identity — settled before
publication, no rewrite pending. The verdict `PASS NO ESCOPO` is maintained;
none of the four corrections concerns the code or the formalized mathematics.

Precision on point (3), for the record of this consolidation: Mathlib's
`abs_pow_sub_pow_le` gives `|a^j − b^j| ≤ |a − b|·j·max(|a|, |b|)^(j−1)` with
no hypothesis on `a`, `b`; the condition `max(|a|, |b|) ≤ 1` is imposed by the
Stone 53 lemma, not by the Mathlib lemma, and from it the linear bound
follows, on `[−1, 1]` as well as on `[0, 1]`. This observation does not
enlarge the domain of the capstone, which is stated and proved for
`θ, θ′ ∈ [0, 1]` only. The two Kimi files are preserved exactly as received;
these notes are not applied to them.

## Records for the consolidation

- **Commit identity.** The candidate `abad1667…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH-signed, with the `Co-Authored-By: Claude Fable 5.1` and `Claude-Session`
  trailers), which differs from the identity used in the Stones 51–52 chain.
  The QA1 report raised this as a custody observation (C1). The identity was
  **accepted before publication** (FITA 53-P, following the precedent of the
  Stone 52 documentary consolidation) and the candidate was preserved as
  audited; no amend, rebase, cherry-pick or rewrite is pending.
- **Examples.** The constructor's positive test file contains nine `example`
  declarations (the constructor's report said eight; counted by the auditor,
  D1).
- **`lipschitz_bound_self`** simplifies only the right-hand side of the bound
  at θ = θ′; the effective application of the capstone at θ = θ′ is the
  auditor's test U4a.
- **`rfl` between proofs.** The constructor's test showing that the Stone 52
  capstone and its Stone 53 re-derivation are definitionally equal is proof
  irrelevance for two proofs of one statement; it certifies nothing about the
  equality of the two derivations (D3).
- **Constructor's bench.** The constructor compiled the pinned Mathlib from
  source (the build cache being unreachable from its environment); the QA
  reproduction used the pinned Mathlib already verified in the Stone 52 audits
  (same commit and manifest) (D4).
- **Stone 52 publication.** The Version 52 deposit (DOI
  [10.5281/zenodo.22738731](https://doi.org/10.5281/zenodo.22738731), tag
  `zenodo-v52`, a simple tag pointing to `f4015c5c…`, GitHub Release
  `zenodo-v52` with four assets) was published by the coordinator after Stone
  53 had been merged; the frozen Version 52 tree does not contain Stone 53.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the four received files against the hashes supplied by the
coordinator; the internal manifest of the package (31 entries, all verified;
no absolute paths, path traversal or links in the archive); the byte-identity
of the extracted report and matrices with their copies inside the package;
the correspondence between the candidate commit, the pull request, the merge
commit and the CI runs of `main` (PR #28; runs 483 and 484); the identity of
the `Phase3/` tree of this documentary commit with that of `a7ae1c0c…`.

Reported by the auditor and the reviewer and **not** re-executed here: the
builds, the `#print axioms` runs, the tests and the mathematical readings.
Internal manifest integrity is not by itself proof of authorship or of the
execution of those builds; the primary machine evidence for the integrated
code is the CI history of `main` (runs 483 and 484, see `RESULTS.md`).
