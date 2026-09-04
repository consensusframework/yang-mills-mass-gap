# Release v51 — Exponential Stability Under Remote Polymer-Activity Restriction (Stone 51)

Version 51 DOI: https://doi.org/10.5281/zenodo.22305341
Previous version: Version 50 — https://doi.org/10.5281/zenodo.22162464

## Summary

Stone 51 proves, in Lean 4 and without any project-level axiom, that a local lattice observable is exponentially insensitive to a *remote hard restriction of polymer activities*. Take the Gibbs expectation ⟨f⟩ of a bounded observable f supported on a set of links s, and compare it with the **normalized polymer functional** obtained by suppressing the activities of every polymer touching a remote region r. If s and r are walk-barrier-separated at scale n in the plaquette graph, the two numbers differ by at most

```
|gibbsExpectation f − activityRestrictedExpectation f s r|
    ≤ 2 · Cf · exp(8 · D_s / 113) · exp(−n / 2)
```

with `D_s = card(supportLinkFinset s)` the number of links in the support of f and `Cf` a bound on |f|. This holds in finite volume, in the **small-β (strong-coupling) regime** `0 ≤ β ≤ 1/40000`. The constant 2, the rate 1/2 and the prefactor exp(8 D_s/113) are explicit; the right-hand side depends neither on the lattice size nor on the size of r, with the local support size and the walk-separation scale controlled.

Main theorem: `LatticeGauge.abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay` (`Phase3/LatticeGauge/ActivityRestrictionStability.lean`), kernel certificate `[propext, Classical.choice, Quot.sound]`.

## The five gates (five new modules, 1,579 new Lean lines)

| Gate | Module | Content | Certified declarations |
|---|---|---|---|
| 51-A | `ActivityRestrictedObservableGas.lean` | The whole-family restriction: `regionAllowed r`, the r-restricted polymer gas, the marked gas restricted at the level of whole families, the normalized functional `activityRestrictedExpectation`, true normalization at f = 1 / s = ∅ with positivity of the denominator as an output of KP, and the filtered regrouping by touching cores | `activityRestrictedExpectation_one_empty`, `activityRestrictedMarkedGas_eq_sum_core_mul_restricted` (and primed form) |
| 51-B | `ActivityRestrictionLedger.lean` | Exact partition of the touching cores into region-allowed and bridge cores; composition law for nested restrictions; two transparent cluster exponents; the exact two-column ledger for the difference | `restrictedActivity_comp`, `activityRestrictedExpectation_eq_sum_core_mul_exp`, `gibbsExpectation_sub_activityRestrictedExpectation_eq_two_column_ledger` |
| 51-C | `ActivityRestrictionConnectorGeometry.lean` | The oriented exponent difference identified exactly with a connector cluster sum (`E^r_T − E_T = C_{T,r}`); the factorization `e^{E_T} − e^{E^r_T} = e^{E_T}(1 − e^{C})`; the geometric witness of bridge cores and the mass toll `n ≤ familyTotalCard T`; the connector + bridge ledger | `regionActivityCoreExponent_sub_full_eq_activityRestrictionConnector`, `activityBridgeCore_familyTotalCard_ge`, `gibbsExpectation_sub_activityRestrictedExpectation_eq_connector_bridge_ledger` |
| 51-D | `ActivityRestrictionColumnBounds.lean` | Unilateral connector tail and erosion (only the s-side barrier is charged), exponential control without assuming |C| ≤ 1, the bridge to Stone 50's normalized term, pointwise bounds of both columns (κ = 3 and κ = 1), and the two column sums with prefactors exp(8 D_s/113) and exp(4 D_s/113) | `abs_one_sub_exp_activityRestrictionConnector_le_eroded`, `abs_activityAllowedColumn_sum_le`, `abs_activityBridgeColumn_sum_le` |
| 51-E | `ActivityRestrictionStability.lean` | Ledger + triangle inequality + the two column bounds; the bridge prefactor is dominated by the allowed one; constant 2 | `abs_gibbsExpectation_sub_activityRestrictedExpectation_le_local_exp_decay` |

Phase 3 grows to 105 modules and more than 30,000 Lean source lines. No pre-existing scientific module was modified.

## Verification

- Toolchain: Lean `4.15.0`, Mathlib `9837ca9d65d9de6fad1ef4381750ca688774e608` (manifest SHA-256 `c376bbe93b56fd85fde0a790889f721c578e2a710c300de77b9de8a0c8dc1227`).
- Each gate: local commit + verifiable git bundle → reproduction on a pinned bench (directed build and clean full Phase 3 build, `#print axioms`) → publication on `pedra51-sol` → official CI by `workflow_dispatch` (runs 448 → 452).
- Integration: PR #13, merge commit `807900449c70b2130fb18544a628c118b8f9fb1c` (parents `97a737851…`, `ebc52fdfbdea8e314f0be68abf6d4724dda0c5ed`; tree identical to the audited branch head); CI on `main`: run 33794800321, three phases green.
- All 13 `#print axioms` certificates in the five modules: `[propext, Classical.choice, Quot.sound]`.
- Hygiene in the five modules: 0 `sorry`, 0 `admit`, 0 scientific `axiom`, 0 `native_decide`, 0 `maxHeartbeats`, 0 `set_option`, 0 attributable warnings (114 inherited warnings, unchanged since v50).
- Reproductions: Manus AI 1.6 — Stone 51-A experiments and reproduction (D1-R, D2); a second Claude Fable 5.1 instance — 51-B through 51-E (same model as the executor; a reproduction, not an independent audit).
- Adversarial mathematical review: Kimi 3 — no mathematical, logical or semantic defect found (three caveats: no recompilation by the reviewer; public wording of the functional; the bridge column admits a sharper bound than the common majorant used).
- Independent custody, reproduction and reading audit: Codex v2 — GREEN WITH CAVEATS (Windows reproduction of the 105 modules; certificate; non-vacuity witnesses; raw CI logs not public; semantic scope). Independent of the executor; same developer family as the architect.
- Post-v50 documentation: terminology corrected to "small-β (strong-coupling) regime" (PR #14, merge `624af23a…`, CI run 33873967291 green).

## Limits

Finite-volume lattice statement. `n` is walk separation in the plaquette graph, not Euclidean distance. Volume-independence of the bound holds with the local support size D_s and the walk-separation scale n controlled; the region r does not enter the right-hand side but remains in the geometric hypothesis `WalkBarrierSeparated s r n`. `activityRestrictedExpectation` is a normalized polymer functional obtained by suppressing activities — not a second Gibbs measure, a modified physical action, a boundary condition, or a spatial-mixing statement. Nothing here constructs a thermodynamic or continuum limit, proves a mass gap, or proves any continuum statement required by the Clay Millennium Problem.

## Relation to Stones 49 and 50

Stone 49 established the finite-volume, small-β cluster-expansion identity for the log-partition function. Stone 50 turned it into exponential covariance decay of two local observables. Stone 51 reuses Stone 50's quantitative capital (unilateral A12 tail, bridge mass, A17 budgets, normalized columns) in a new direction: one observable and one remote hard restriction of activities. The connector identification (51-C) and the unilateral erosion (51-D) are new in Version 51 (new relative to Version 50); the constants belong to the same family (2/113 per link, rate 1/2, β ≤ 1/40000).

## Authorship and provenance

Version 51 is a human–AI collaborative work. Human author, coordinator and responsible party: Jucelha Carvalho (Smart Tour Brasil; ORCID 0009-0004-6047-2306). All AI models that contributed to the project are coauthors, identified as AI models; developer companies are not authors, participants or affiliations.

Coauthors (cumulative): Jucelha Carvalho (Smart Tour Brasil); GPT-5.6 "Sol" (AI model); Claude Fable 5 (AI model); Claude Fable 5.1 (AI model); Kimi 3 (AI model); Manus AI 1.6 (AI model); Codex v2 (AI model); Claude Opus 4.5 / 4.6 / 4.7 (AI model); Claude Opus 5 (AI model); GPT-5.2 (AI model); Gemini 3 Pro (AI model); Grok 4.5 (AI model); Grok 4.6 (AI model).

Direct participation in Stone 51: GPT-5.6 "Sol" — architecture and formal specification of the five gates; Claude Fable 5.1 — Lean implementation of 51-A (final) through 51-E, publication and integration; Claude Fable 5 — initial 51-A and iterations; Kimi 3 — adversarial review; Manus AI 1.6 — 51-A experiments and reproduction (D1-R, D2); a second Claude Fable 5.1 instance — bench reproduction of 51-B through 51-E (not an independent audit); Codex v2 — custody, reproduction and reading audit; Jucelha Carvalho — coordination, custody, integration and release. Formal verification: Lean 4 kernel and GitHub Actions (verification instances, not authors). Scientific coauthorship and legal copyright ownership are distinct records.

## License

Code and configuration: Apache License 2.0 (`LICENSE`). Documentation and textual materials: Creative Commons Attribution 4.0 International (`LICENSE-DOCUMENTATION`). Version 50 remains licensed as published (CC BY 4.0).

## Citation

Carvalho, Jucelha (Smart Tour Brasil, ORCID 0009-0004-6047-2306); GPT-5.6 "Sol" (AI model); Claude Fable 5 (AI model); Claude Fable 5.1 (AI model); Kimi 3 (AI model); Manus AI 1.6 (AI model); Codex v2 (AI model); Claude Opus 4.5 / 4.6 / 4.7 (AI model); Claude Opus 5 (AI model); GPT-5.2 (AI model); Gemini 3 Pro (AI model); Grok 4.5 (AI model); Grok 4.6 (AI model) (2026). *Finite-Volume Lattice Gauge Theory in Lean 4 — Version 51: Exponential Stability Under Remote Polymer-Activity Restriction.* Zenodo. https://doi.org/10.5281/zenodo.22305341
