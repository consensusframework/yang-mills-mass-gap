# Stone 56 — independent evidence: QA1 reproduction with its errata, adversarial review and publication record

This directory preserves, byte for byte, the evidence produced around the
Stone 56 candidate `a2fcf8e9050c470b83c7b95cc45d9512b38fcfc1` (see
[`docs/stone56/RESULTS.md`](../../stone56/RESULTS.md)), integrated on `main` at
`ead481456bc8637b2b7c22e867cc49f99f4ab375` (PR #37): the audit evidence package
of the QA1 reproduction with its report, its two matrices and its errata C1,
the adversarial review by Kimi 3, and the publication report of the
constructing/publishing instance. It follows the organization of
[`docs/audits/stone55/`](../stone55/README.md): one package, one review, one
publication record — this time the errata belongs to the QA1 audit, not to
the review. The package is the primary record of the audit; the report and the
matrices are extracted here only for reading convenience and are
byte-identical to the copies inside the package; the errata is a separate
file received after the package and does not regenerate it. Nothing in this
directory is a Lean module: the package contains the auditor's own disposable
test files (including one test that is *expected to fail*), build logs and
matrices, and none of it enters the `LatticeGauge` library, the
`lakefile.toml` globs or the CI build.

The reports are in Portuguese, as written by their authors (the matrices are
in English or mixed); they are not translated, normalized or edited. The
constructor's own evidence package (`STONE56L_evidence.zip`, with its bundle,
logs and tests V1–V4x) and the feasibility materials of 56-A are **not** part
of this collection: they are the implementer's material, not an audit.

## Who did what, and how independent it is

| Role | Who | Instance / family | Method | Independence |
|---|---|---|---|---|
| Scientific architecture and review | GPT Astra (AI model) | different model family from the constructor | tapes (feasibility 56-A, construction 56-L, publication 56-P, this consolidation); reading of the module and of the reports, checks of the evidence, Git objects and publication metadata; no Lean build of its own | architect; not an auditor |
| Construction and publication | Claude Fable 5.1 (AI model) in Claude Code | one instance with an executable Lean bench | feasibility tests (56-A), Lean implementation of the module, local commit and bundle with the constructor's tests V1–V4x and a clean rebuild of the 117 modules, then, after QA1, push, pull request, merge and CI follow-up in the same instance | the constructor; its publication report is a custody record, not an audit |
| QA1 reproduction, with errata | Claude Fable 5.1 (AI model), separate auditing instance | **distinct instance and bench; same model as the constructor** | reproduction by execution (dependencies from the committed manifest, no `lake update`; `.lake/build` deleted; 117 modules built, 0 replayed, exit 0; own `#print axioms`; own tests W0–W7x; the constructor's tests V1–V4x re-executed in a second pass); preliminary conclusions recorded before opening the constructor's material; one errata C1 by the same instance correcting the audit's own record, without a new build | **not blind** (prior exposure declared); not a different model family; not human review |
| Adversarial review | Luan / Kimi 3 (AI model), as identified in the review | **different model family** from the constructor, the QA instance and the architect | review by reading and mathematical analysis (module read in full at the fixed SHA before any QA or constructor material, own re-derivations, custody via the public GitHub API and codeload at the fixed SHA, hashes recalculated); **no Lean execution**; the QA1 package, the errata and the publication report opened only after the reviewer's own analysis | **not blind** (prior exposure to Stones 49–55 declared); reading only; did not receive the constructor's package or construction report; CI conclusions checked through the API without the checkout logs |
| Human coordination | Jucelha Carvalho | — | coordination, custody of credentials, relay of the materials, publication decisions, manual publication | human coordination is not specialized human mathematical review of the proofs, which is not documented at this stage |

Claude Code is the execution environment; Claude Fable 5.1 is the model. No
Lean execution is attributed to GPT Astra or to Kimi 3.

## Index

| # | Document | Path | SHA-256 | Producer | SHA examined | Literal verdict | Date |
|---|---|---|---|---|---|---|---|
| 1 | QA1 evidence package | [`packages/QA1_56_evidence.zip`](packages/QA1_56_evidence.zip) | `53399f1a3c4a3887cb6c88daeba209ed48739918c9b7b1a5822d8758c27f483d` | Fable 5.1, QA instance | `a2fcf8e9…` (candidate; published as [PR #37](https://github.com/consensusframework/yang-mills-mass-gap/pull/37), merge `ead48145…`) | `PASS NO ESCOPO` (sem observações de mérito) | 2026-09-24 |
| 2 | QA1 report (extracted) | [`reports/RELATORIO_56-QA1.md`](reports/RELATORIO_56-QA1.md) | `2481ab1eaab57481d73868cdc79a6dd6e5506bebddc5b5b9c1c43797ab6e2599` | Fable 5.1, QA instance | `a2fcf8e9…` | `PASS NO ESCOPO` | 2026-09-24 |
| 3 | QA1 declaration matrix (extracted) | [`reports/56_QA1_DECLARATION_MATRIX.tsv`](reports/56_QA1_DECLARATION_MATRIX.tsv) | `5419a12027a78d4a5a45f669fd80f871bcad0e8447e76262031bf510bba3827e` | Fable 5.1, QA instance | `a2fcf8e9…` | 24 rows (22 theorems, 2 definitions), all PASS; to be read with the errata C1 | 2026-09-24 |
| 4 | QA1 test matrix (extracted) | [`reports/56_QA1_TEST_MATRIX.tsv`](reports/56_QA1_TEST_MATRIX.tsv) | `3d9ad36ba31825b6e6d53b7b06e56208af9c9d1bd754412c89ec0482efaa94d9` | Fable 5.1, QA instance | `a2fcf8e9…` | W0–W7 positive; W7x expected application failure; V1–V4x (constructor's) re-executed | 2026-09-24 |
| 5 | Errata C1 to the QA1 record | [`reports/ERRATA_56-QA1-C1.md`](reports/ERRATA_56-QA1-C1.md) | `5ab78cf4fd6305f4e3a7b08903b4fd5d3bb91777528588b3cacce20e1dd4ce10` | Fable 5.1, QA instance (the same that issued the report) | `a2fcf8e9…` (no new build) | verdict unchanged: `PASS NO ESCOPO` | 2026-09-24 |
| 6 | Adversarial review | [`kimi/RELATORIO_56-K-ADV.md`](kimi/RELATORIO_56-K-ADV.md) | `3259f314943416346dfc65cc76ce0f101bba22b67eff2ef11e975c64f12307df` | Luan / Kimi 3 | `a2fcf8e9…` (sources) and `ead48145…` (scientific merge) | `PASS NO ESCOPO` | 2026-09-25 (received 2026-09-29) |
| 7 | Publication report (FITA 56-P) | [`publication/RELATORIO_56-P.md`](publication/RELATORIO_56-P.md) | `7627bbe28d8a4bdbd9961d2c57fad98290c5f790f17828573f7e68344fdaccda` | Fable 5.1, constructing/publishing instance | `a2fcf8e9…` → `ead48145…` | n/a (record) | 2026-09-25 |

The seven hashes were supplied as references by the coordinator in the
consolidation tape and match the files received. SHA-256 of every file of
this directory except the manifest itself:
[`SHA256SUMS.txt`](SHA256SUMS.txt) (relative paths; covers this README,
`PROVENANCE.tsv`, the package, the three extracted files, the errata, the
review and the publication report: 9 entries; no self-inclusion).
Machine-readable provenance: [`PROVENANCE.tsv`](PROVENANCE.tsv).

## The QA1 package

`packages/QA1_56_evidence.zip` (48 entries: 46 files and 2 directories, at the
root of the archive; internal manifest `SHA256SUMS_56-QA1.txt`, 45 entries —
every file of the package except the manifest itself). Contents: the report,
`PRELIMINARY_CONCLUSIONS_first_pass.md` (written before the auditor opened
the constructor's material), the two matrices, `environment.txt`
(2026-09-24T20:41:22Z; Lean 4.15.0 commit `11651562caae`, Lake 5.0.0-1165156,
`lean-toolchain` `leanprover/lean4:v4.15.0`, candidate `a2fcf8e9…`, manifest
SHA-256 `c376bbe9…1227`, dependencies from the bench's cache with the nine
revisions verified, `lake update` not run), `build_directed.log/.result`
(`lake build LatticeGauge.ActivityProfileDampingLocality`, exit 0, 308 s),
`build_full_clean.log/.result` (`rm -rf .lake/build && lake build`, exit 0,
721 s, **117 modules built, 0 replayed**, 0 errors, 269 certificates all
standard, 0 `sorryAx`; the log is at the root of the archive), the start/end
instants and the pre/post manifests of the bench, `warnings_candidate.txt`,
`compare_warning_blocks.py` and `warnings_block_comparison.txt` (comparison
of the full multi-line warning blocks against the Version 55 baseline: 114
blocks of `LatticeGauge/`, identical multiset, 0 in the new module),
`tests/` (eight `.lean` files W0–W7 and W7x, their logs and the preserved
first-attempt logs of the auditor's own slips) and `builder_tests_rerun/`
(the constructor's tests V1–V4x re-executed on the auditor's bench, with the
same results). Logs are not duplicated outside the package.

Key results reported by the auditor (not re-executed here): 269/269 own
`#print axioms` certificates in the clean build and 24 in the test W0 (22
theorems + 2 definitions) equal to `[propext, Classical.choice, Quot.sound]`,
no `sorryAx`; `#check` of the two final theorems, the four interfaces, the
Stone 55 capstone and the 55-B bridge interface; the coefficient identity
re-derived by cases with the orientation checked by antisymmetry (W1); the
ledger re-derived from the exponential form of both sides without the
candidate's lemma (W6a); the closure by the columns without the two final
theorems (W6b); the κ = 2 control re-derived and the two-region bridge with
`R = univ`, `R = ∅` and `R := r` (W5); the effective-factor hypotheses with a
non-unit background, raw profiles differing outside `R`, `δ = 7`, `r = ∅` and
`R = ∅` (W2–W4); the localization cases (W7); the expected application
failure without `hsame` (W7x), classified as such and not as a
counterexample.

## Reading the QA1 record together with its errata C1

`reports/RELATORIO_56-QA1.md`, the two matrices and the archived
`PRELIMINARY_CONCLUSIONS_first_pass.md` are to be read together with
[`reports/ERRATA_56-QA1-C1.md`](reports/ERRATA_56-QA1-C1.md), issued by the
same auditing instance from the materials already available, without a new
build and without editing the originals; **C1 prevails on the points it
corrects**. None of them concerns the candidate, its hypotheses, proofs,
compilation results or the comparison of warnings; the verdict `PASS NO
ESCOPO` is maintained. The corrected record reads:

1. **Declaration lines.** 1,780 at the candidate by the documented method
   (the nine keywords followed by a space, applied to the Git objects),
   1,756 at the base plus 24 new lines: 22 `theorem` and 2 `noncomputable
   def`. The 1,790 of the original report came from a pattern with eleven
   alternatives (adding `noncomputable abbrev` and `noncomputable instance`);
   1,745 was another metric (four types). Textual metric, not a count of
   theorems.
2. **The constructor's clean rebuild** (in `STONE56L_evidence.zip`,
   `logs/clean_build.log`): project 117 built / 0 replayed; dependencies
   **0 built / 1,332 replayed**, with 4,599 dependency warnings re-emitted
   from the cache — not a compilation of the dependencies from source, as the
   original report said. That log does not establish the historical origin of
   the cache (the constructor's `environment.txt` states an earlier
   compilation from source on its bench; the audit does not attribute it).
3. **Warnings in the auditor's disposable tests**: 38 (W1: 2, W3: 6, W4: 26,
   W7: 4; unused variables, `beta_reduce` doing nothing, `<;>` where `;`
   suffices), all in the auditor's own files outside the tree, not edited so
   that the executed evidence is preserved — separate from the 114 inherited
   warnings of the project (blocks identical to the baseline) and from the
   0 warnings of the new module.
4. **Certificates.** 22 theorem certificates comparable with the
   constructor's (clean builds of both benches and W0), plus 2 additional
   checks by the auditor for the definitions `kpLocalizedDiffCoeff` and
   `localizedConnectorDiff`, in W0 only; the 269 outputs of the project build
   do not include the definitions, and the constructor's matrix lists them as
   "— (definition)". Column 9 of the QA1 declaration matrix ("certificate
   (#print axioms, own W0 + directed + clean)") is to be read accordingly.
5. **Matrix references and paths.** Four numeric references of the QA1
   declaration matrix are corrected by full names:
   `abs_tupleProfileWeight_sub_le_k_localized` is used in
   `abs_kpLocalizedDiffCoeff_le`; `abs_profileWeight_sub_le_card_localized`
   in `abs_sum_localizedBridgeColumn_le`; `abs_kpLocalizedDiffCoeff_le` in
   `abs_localizedConnectorDiff_le_eroded`; and `0 ≤ Cf` is a hypothesis of
   `abs_sum_localizedConnectorColumn_le`,
   `nat_card_mul_abs_profileNormalizedTerm_le_bridge_two_regions` and
   `abs_sum_localizedBridgeColumn_le`, derived by
   `nonneg_of_abs_le_of_config hCf` in the two-term estimate and in the
   capstone. The package was generated from the auditor's `out/` directory:
   `build_full_clean.log`, `tests/` and `builder_tests_rerun/` are at the root
   of the archive, without the `out/` prefix used in the report.

The tests **V1–V4x** belong to the constructor (delivered in the constructor's
package and re-executed by QA1 in its second pass, which does not change their
authorship); the tests **W0–W7x** belong to QA1. V4x and W7x are expected
application failures for want of `hsame` (V4x on the cancellation lemma, W7x
on the capstone): a missing hypothesis, not a counterexample to the theorem.
The matrices are preserved as received; they are not edited to apply the
corrections.

## Reading the Kimi 3 review, with its declared limits

`kimi/RELATORIO_56-K-ADV.md` is one review with no errata; it is preserved
exactly as received. It records a full reading of the module and of the
imported interfaces, its own re-derivations (attacks A–G), custody through
the codeload tarball and the public API with hashes recalculated by the
reviewer, and the integrity of the QA1 package (45/45). It also records what
the reviewer did **not** have: neither `STONE56L_evidence.zip` nor
`RELATORIO_56-L.md` were received, so the constructor's material reached the
reviewer only indirectly, through the citations of the QA1 report, the errata
C1 and the publication report; the CI runs 501 and 502 were checked for their
conclusions through the API, without inspecting the checkout logs. Where the
review's section 5 discusses the constructor's data contained in the errata,
the provenance remains indirect, as the review itself declares in its
section 1. The custody of the integration checkouts (the provisional merge
`8831358` of run 501 and the definitive `ead48145…` of run 502) is in
`publication/RELATORIO_56-P.md` and in the CI logs, read by the publishing
instance. The review found no mathematical and no new documentary finding;
the pre-existing observation without merit of the QA1 report (the two-region
bridge first moment re-proves the route of the 55-B interface, which ties both
regions to one and is not editable, rather than deriving from it — the
strategy actually adopted with the module frozen) is confirmed, not
re-presented as a finding.

## Records for the consolidation

- **No documentary record on the module**: neither the QA1 nor the review
  found an imprecision in the candidate or in its docstrings. The precisions
  E1–E5 of the construction tape were incorporated in the docstrings of the
  integrated module before the audit.
- **Errata C1** — the five corrections of the QA1 record listed above;
  consolidated here without editing the QA1 files.
- **Reporting precision** (from the publication report): the constructor's
  "0 Replayed" refers to the project modules; QA1 and the CI report the two
  populations separately (QA1: 117/0 with no dependency diagnostics emitted;
  CI: 117 built / 0 replayed of `LatticeGauge`, 9 built / 0 replayed of
  dependencies).
- **Commit identity.** The candidate `a2fcf8e9…` carries the identity
  configured in the publishing environment (`Claude <noreply@anthropic.com>`,
  SSH signature header present, trailers `Co-Authored-By: Claude Fable 5.1`
  and `Claude-Session`), accepted by the precedent of Stones 52–55; the QA1
  and the review record the signature as present, not as independently
  authenticated; identity and signature were not redone.

## What was verified in this consolidation, and what is reported

Verified in this repository at consolidation time (documentary, read-only):
the SHA-256 of the seven materials against the reference hashes supplied by
the coordinator in the consolidation tape; the internal manifest of the
package (45 entries, all verified; no absolute paths, path traversal or
duplicates in the archive; 48 entries); the byte-identity of the standalone
QA1 report with its copy inside the package, and of the extracted report and
matrices with their copies inside the package; the correspondence between the
candidate commit, the pull request, the merge commit and the CI runs of
`main` (PR #37; runs 501 and 502; parents, root tree and `Phase3/` tree of
`ead48145…`); the identity of the `Phase3/` tree of this documentary commit
with that of `ead48145…` (`f387f26d…`); the historical manifests of
`docs/audits/stone52/`, `stone53/`, `stone54/` and `stone55/` (20, 9, 8 and 9
entries, all verified, no self-inclusion).

Reported by the auditor and the reviewer and **not** re-executed here: the
builds, the `#print axioms` runs, the tests and the mathematical readings.
Internal manifest integrity is not by itself proof of authorship or of the
execution of those builds; the primary machine evidence for the integrated
code is the CI history of `main` (runs 501 and 502, see `RESULTS.md`).
