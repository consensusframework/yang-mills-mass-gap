# Release v48 — Absolute Convergence of the Concrete Signed Rooted Ursell Series

**Frozen mathematical core:** commit `c9dda043da48ec8127250197132522857695f314` (branch `pedra48-sol`, CI run 31886396666, green). Documentation/hygiene closure applied on top with no mathematical change.

**The central result.** *For 0 ≤ β ≤ 1/40000, the concrete signed **rooted** Ursell series is absolutely convergent, with Σₙ |Cₙ(w_{β,χ}, γ₀)| ≤ exp(card γ₀)* (`polymer_tsum_abs_signedUrsell_le_exp_card`), together with the summability of the signed series itself and the root-activity corollary.

**The chain (all kernel-checked, Lean 4 + Mathlib v4.15.0):** Stone 46 (|w_β| satisfies the concrete Kotecký–Preiss smallness hypothesis, threshold 1/40000) ⟹ Stone 47 (uniform finite bound S_M ≤ exp|γ₀|) ⟹ 48A (order→series bridge, consumed from the pinned library, nothing duplicated) ⟹ 48B (tree-majorant series: Summable, tsum ≤ exp) ⟹ 48C-α (absolute rooted Ursell series) ⟹ 48C-β (the SIGNED rooted coefficient `kpSignedUrsellCoeff` is born; domination |Cₙ(z)| ≤ Aₙ(|z|); absolute convergence) ⟹ 48D (z literally the signed `polymerWeight`).

**Honest scope boundary.** NOT claimed: any log-Z identification, realZ ≠ 0, any "cluster expansion = log Z" representation, thermodynamic or continuum limits, exponential clustering, or any mass-gap statement. Stone 49 (unrooting → unrooted summability → exp/log identification) is mapped and NOT started.

**Scoreboard:** 63 Phase-3 source files, approximately 740 verified theorem/lemma declarations, 0 scientific axioms, 0 `sorry`.

**Verification and review credits:**
- External adversarial mathematical review — Kimi 3 (Moonshot AI): APPROVED (first stone of the program with no substantive correction).
- External reproducibility and release review — Manus AI 1.6: APPROVED FOR DOCUMENTATION CLOSURE AND MERGE (independent clone build).
- GitHub Actions CI verification (Lean 4 + Mathlib pinned at v4.15.0).
- Architecture and review: GPT-5.6 "Sol" (OpenAI). Lean 4 implementation: Claude Fable 5 (Anthropic). Coordination: Jucelha Carvalho.
