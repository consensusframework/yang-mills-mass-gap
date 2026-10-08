/-
# Stone 57 — Stability of the profile-damped functional under localized
# changes in SEVERAL regions (finite composition of Stone 56)

Scientific architecture: GPT Astra / Can (feasibility tape 57-A, construction
tape 57-L). Construction: Claude Fable 5.1 (Claude Code), promoted from the
feasibility file `T57A_multiregion_tests.lean` (gate 57-A), whose chain
elaborated unchanged.

## The statement

Objects of Stones 55–56 are kept: the damping region `R` stays in the
definition of the functional, the weights, the activities and the exponents,

  F_R(a) = profileExpectation μm β χ f s R a,
  b(η)   = touchFactor R a η,   b′(η) = touchFactor R a′ η,
  D_s    = card (supportLinkFinset s).

A FINITE family of change regions, indexed by `i : Fin m` (`m = 0` included):

  r : Fin m → Set (Link N),   n : Fin m → ℕ,   δ : Fin m → ℝ,
  hδ0    : ∀ i, 0 ≤ δ i,
  hsep   : ∀ i, WalkBarrierSeparated s (r i) (n i),
  hcover : ∀ η, b(η) ≠ b′(η) →
             ∃ i, typedTouchesSupport η (r i) ∧ |b(η) − b′(η)| ≤ δ i.

`hcover` is a cover of the EFFECTIVE CHANGES BY POLYMERS: every polymer whose
effective factor changes is assigned at least one region that localizes it and
pays its intensity. It is not an inclusion of regions of links; the regions
may overlap. With `B = ∑ i : Fin m, δ i · exp(−(n i)/2)`, for profiles
`a, a′` with values in [0, 1], in the regime `0 ≤ β ≤ 1/40000`:

  |F_R(a) − F_R(a′)| ≤ Cf · [e^{6 D_s/113} + e^{4 D_s/113}] · B      (two terms)
                     ≤ (2 Cf) · e^{6 D_s/113} · B.                     (capstone)

Not required: any separation of `s` from `R`; `r i ⊆ R`; disjointness of the
regions; a unit background outside the regions; `δ i ≤ 1`; a sign condition
on activities or exponents; `DependsOnlyOn f s`. `0 ≤ Cf` is derived. No
factor of volume, of `card R`, of `card (r i)` or of `m` enters outside the
sum: the number of regions participates only through the finite sum `B`. The
bound is uniform in the admissible background; the functional is not
independent of it.

## The route (composition derived from Stone 56)

The Stone 56 two-term estimate (`…_le_two_terms_localized`) is consumed at
every step; nothing of its cluster, erosion or budget chain is reopened.

1. An explicit OWNER `owner : Polymer N → Option (Fin m)` assigns to each
   polymer at most one index: `none` only where `b = b′`; `some i` only on
   polymers touching `r i`, with `|b − b′| ≤ δ i` there. Overlapping regions
   are allowed; a polymer touching several regions is owned by one of them.
2. Intermediate profiles by COORDINATE SUBSTITUTION: `p_k` is the second
   profile on the coordinates owned by an index `< k`, the first profile
   elsewhere. `p_0 = a` as profiles; each `p_k` stays in [0, 1]; the effective
   factor of `p_k` selects, by the same condition, `b′` or `b`.
3. At step `i` the Stone 56 hypotheses hold with the region `r i`: outside
   `r i` the effective factors of `p_i` and `p_(i+1)` agree (a coordinate
   switches only at the step of its owner, even if it touches other regions);
   on `r i` they differ by at most `δ i`.
4. `p_m` has the effective factors of `a′` (equality of EFFECTIVE factors,
   not of raw profiles: values never read outside `R` may differ), hence
   `F_R(p_m) = F_R(a′)` by the Stone 56 identity
   `profileExpectation_eq_of_touchFactor_eq`.
5. Finite telescoping, the two-term estimate of Stone 56 at each step with
   `r i, n i, δ i`, and the reorganization of the sum give the two-term form;
   `0 ≤ Cf`, `B ≥ 0` and `e^{4 D_s/113} ≤ e^{6 D_s/113}` give the capstone.
6. The owner is BUILT from `hcover` by classical choice: the public capstones
   take `hcover` and no owner.

The selection and endpoint identities (steps 1, 2, 4) carry no interval, no
regime, no separation and no bound on `f`; the interval and the regime enter
the bounds (steps 3, 5) through the Stone 56 theorem.

## Interfaces

`m = 1` recovers the Stone 56 capstone by application (a compatibility test,
not an independent proof of Stone 56); `m = 0` under `hcover` gives the exact
equality `F_R(a) = F_R(a′)` with no analytic hypothesis.

## Limits

Finite volume, small β. No universal improvement over a single control is
claimed (two equal regions give two equal terms); no new decay exponent, no
optimal constant, no bibliographic priority; no infinite family, summability,
thermodynamic or continuum limit, new Gibbs measure, modified action or mass
gap.
-/

import Mathlib
import LatticeGauge.ActivityProfileDampingLocality

open MeasureTheory
open scoped Classical BigOperators

namespace LatticeGauge

namespace ActivityProfileMultiRegion

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## 57-L.1 — coordinate substitution with a unique owner -/

/-- `moved owner k η`: the polymer η is owned by an index `i` with `i.val < k`,
    i.e. its coordinate has already been switched to the second profile at
    stage `k`. -/
def moved {m : ℕ} (owner : Polymer N → Option (Fin m)) (k : ℕ) (η : Polymer N) : Prop :=
  ∃ i : Fin m, owner η = some i ∧ i.val < k

/-- The intermediate profile `p_k`: the second profile on the coordinates
    owned by an index `< k`, the first profile elsewhere. -/
noncomputable def stepProfile {m : ℕ} (owner : Polymer N → Option (Fin m))
    (a a' : Polymer N → ℝ) (k : ℕ) (η : Polymer N) : ℝ :=
  if moved owner k η then a' η else a η

theorem not_moved_zero {m : ℕ} (owner : Polymer N → Option (Fin m)) (η : Polymer N) :
    ¬ moved owner 0 η := by
  rintro ⟨i, _, hi⟩
  exact Nat.not_lt_zero _ hi

/-- `p_0 = a`, as an identity of profiles. -/
theorem stepProfile_zero {m : ℕ} (owner : Polymer N → Option (Fin m))
    (a a' : Polymer N → ℝ) : stepProfile owner a a' 0 = a := by
  funext η
  unfold stepProfile
  rw [if_neg (not_moved_zero owner η)]

/-- Each `p_k` stays in `[0,1]`: it selects one of the two input values. -/
theorem stepProfile_mem {m : ℕ} (owner : Polymer N → Option (Fin m))
    {a a' : Polymer N → ℝ} (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1)
    (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1) (k : ℕ) (η : Polymer N) :
    0 ≤ stepProfile owner a a' k η ∧ stepProfile owner a a' k η ≤ 1 := by
  unfold stepProfile
  split_ifs
  · exact ⟨h0' η, h1' η⟩
  · exact ⟨h0 η, h1 η⟩

/-- The effective factor of `p_k` selects, by the same condition, `b′(η)` or
    `b(η)` — with the damping region `R` kept. An identity of definitions. -/
theorem touchFactor_stepProfile {m : ℕ} (owner : Polymer N → Option (Fin m))
    (R : Set (Link N)) (a a' : Polymer N → ℝ) (k : ℕ) (η : Polymer N) :
    touchFactor R (stepProfile owner a a' k) η
      = if moved owner k η then touchFactor R a' η else touchFactor R a η := by
  unfold touchFactor stepProfile
  split_ifs <;> rfl

/-- Monotonicity of "already switched" in the stage. -/
theorem moved_mono {m : ℕ} (owner : Polymer N → Option (Fin m)) {k : ℕ} {η : Polymer N}
    (h : moved owner k η) : moved owner (k + 1) η := by
  obtain ⟨i, hi, hk⟩ := h
  exact ⟨i, hi, Nat.lt_succ_of_lt hk⟩

/-- A coordinate that switches exactly at stage `i.val` is owned by `i`. -/
theorem owner_eq_of_moved_succ {m : ℕ} (owner : Polymer N → Option (Fin m)) (i : Fin m)
    {η : Polymer N} (hm : ¬ moved owner i.val η) (hm' : moved owner (i.val + 1) η) :
    owner η = some i := by
  obtain ⟨i', hi', hlt⟩ := hm'
  have hnot : ¬ i'.val < i.val := fun h => hm ⟨i', hi', h⟩
  have hval : i'.val = i.val := by omega
  have : i' = i := Fin.ext hval
  subst this
  exact hi'

/-! ## 57-L.2 — the Stone 56 hypotheses at every step -/

/-- **Step `i`, `hsame`**: outside `r i` the effective factors of `p_i` and
    `p_(i+1)` agree. A coordinate switches only at the step of its owner, even
    when it touches other regions. Uses only `howner_touch`. -/
theorem step_same {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (owner : Polymer N → Option (Fin m)) (a a' : Polymer N → ℝ)
    (howner_touch : ∀ η i, owner η = some i → typedTouchesSupport (N := N) η (r i))
    (i : Fin m) :
    ∀ η, ¬ typedTouchesSupport (N := N) η (r i) →
      touchFactor R (stepProfile owner a a' i.val) η
        = touchFactor R (stepProfile owner a a' (i.val + 1)) η := by
  intro η hη
  rw [touchFactor_stepProfile, touchFactor_stepProfile]
  by_cases hm : moved owner i.val η
  · rw [if_pos hm, if_pos (moved_mono owner hm)]
  · by_cases hm' : moved owner (i.val + 1) η
    · exact absurd (howner_touch η i (owner_eq_of_moved_succ owner i hm hm')) hη
    · rw [if_neg hm, if_neg hm']

/-- **Step `i`, `hδ`**: on `r i` the effective factors of `p_i` and `p_(i+1)`
    differ by at most `δ i`: `howner_bound` on the coordinates owned by `i`,
    a zero difference and `0 ≤ δ i` elsewhere (overlapping regions are never
    charged twice). -/
theorem step_bound {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (owner : Polymer N → Option (Fin m)) (a a' : Polymer N → ℝ) (δ : Fin m → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i)
    (howner_bound : ∀ η i, owner η = some i →
      |touchFactor R a η - touchFactor R a' η| ≤ δ i)
    (i : Fin m) :
    ∀ η, typedTouchesSupport (N := N) η (r i) →
      |touchFactor R (stepProfile owner a a' i.val) η
        - touchFactor R (stepProfile owner a a' (i.val + 1)) η| ≤ δ i := by
  intro η _
  rw [touchFactor_stepProfile, touchFactor_stepProfile]
  by_cases hm : moved owner i.val η
  · rw [if_pos hm, if_pos (moved_mono owner hm), sub_self, abs_zero]
    exact hδ0 i
  · by_cases hm' : moved owner (i.val + 1) η
    · rw [if_neg hm, if_pos hm']
      exact howner_bound η i (owner_eq_of_moved_succ owner i hm hm')
    · rw [if_neg hm, if_neg hm', sub_self, abs_zero]
      exact hδ0 i

/-- **The last profile**: `p_m` has the effective factors of `a′` — equality of
    EFFECTIVE factors, not of raw profiles (values never read outside `R` may
    still differ). Uses only `howner_none`. -/
theorem touchFactor_stepProfile_last {m : ℕ} (R : Set (Link N))
    (owner : Polymer N → Option (Fin m)) (a a' : Polymer N → ℝ)
    (howner_none : ∀ η, owner η = none → touchFactor R a η = touchFactor R a' η)
    (η : Polymer N) :
    touchFactor R (stepProfile owner a a' m) η = touchFactor R a' η := by
  rw [touchFactor_stepProfile]
  by_cases hm : moved owner m η
  · rw [if_pos hm]
  · rw [if_neg hm]
    rcases ho : owner η with _ | i
    · exact howner_none η ho
    · exact absurd ⟨i, ho, i.isLt⟩ hm

/-! ## 57-L.3 — finite telescoping -/

/-- `|g 0 − g k| ≤ ∑_{j<k} |g j − g (j+1)|`, by induction. -/
theorem abs_telescope (g : ℕ → ℝ) (k : ℕ) :
    |g 0 - g k| ≤ ∑ j ∈ Finset.range k, |g j - g (j + 1)| := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    calc |g 0 - g (k + 1)| ≤ |g 0 - g k| + |g k - g (k + 1)| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add_right ih _

/-- `B = ∑ i, δ i · e^{−n i/2} ≥ 0`. -/
theorem budget_nonneg {m : ℕ} (n : Fin m → ℕ) (δ : Fin m → ℝ)
    (hδ0 : ∀ i, 0 ≤ δ i) :
    0 ≤ ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hδ0 i) (Real.exp_pos _).le)

/-! ## 57-L.4 — composition of the Stone 56 two-term estimate along the chain -/

variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **Multi-region estimate with an explicit owner**: the Stone 56 two-term
    estimate at every step (with `r i, n i, δ i` and the two intermediate
    profiles), finite telescoping, and the reorganization of the sum. The
    conclusion is written in the native form of the Stone 56 statement
    (`3·D_s·(2/113)` and `2·D_s·(2/113)`). `R` is kept in every profile and
    functional; the regions `r i` may overlap. -/
theorem abs_profileExpectation_sub_le_of_owner
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (owner : Polymer N → Option (Fin m))
    (howner_none : ∀ η, owner η = none → touchFactor R a η = touchFactor R a' η)
    (howner_touch : ∀ η i, owner η = some i → typedTouchesSupport (N := N) η (r i))
    (howner_bound : ∀ η i, owner η = some i →
      |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
              + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113)))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  set g : ℕ → ℝ := fun k => profileExpectation μm β χ f s R (stepProfile owner a a' k) with hg
  have hg0 : g 0 = profileExpectation μm β χ f s R a := by
    simp only [hg, stepProfile_zero]
  have hgm : g m = profileExpectation μm β χ f s R a' :=
    profileExpectation_eq_of_touchFactor_eq μm β χ f s R
      (touchFactor_stepProfile_last R owner a a' howner_none)
  have hstep : ∀ i : Fin m,
      |g i.val - g (i.val + 1)|
        ≤ δ i * Cf * Real.exp (-((n i : ℕ) : ℝ) / 2)
            * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
                + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) := by
    intro i
    exact abs_profileExpectation_sub_profileExpectation_le_two_terms_localized
      μm hβ mχ hχabs hsmall R mf hCf (hsep i) (hδ0 i)
      (fun η => (stepProfile_mem owner h0 h1 h0' h1' i.val η).1)
      (fun η => (stepProfile_mem owner h0 h1 h0' h1' i.val η).2)
      (fun η => (stepProfile_mem owner h0 h1 h0' h1' (i.val + 1) η).1)
      (fun η => (stepProfile_mem owner h0 h1 h0' h1' (i.val + 1) η).2)
      (step_same R r owner a a' howner_touch i)
      (step_bound R r owner a a' δ hδ0 howner_bound i)
  calc |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      = |g 0 - g m| := by rw [hg0, hgm]
    _ ≤ ∑ j ∈ Finset.range m, |g j - g (j + 1)| := abs_telescope g m
    _ = ∑ i : Fin m, |g i.val - g (i.val + 1)| := Finset.sum_range (fun j => |g j - g (j + 1)|)
    _ ≤ ∑ i : Fin m, δ i * Cf * Real.exp (-((n i : ℕ) : ℝ) / 2)
            * (Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
                + Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))) :=
        Finset.sum_le_sum (fun i _ => hstep i)
    _ = _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-! ## 57-L.5 — the owner built from the cover hypothesis -/

/-- The owner chosen from `hcover` by classical choice: `none` where the
    effective factors agree, an index given by `hcover` where they differ.
    The user of the capstones never supplies an owner. -/
noncomputable def coverOwner {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    Polymer N → Option (Fin m) :=
  fun η => if h : touchFactor R a η ≠ touchFactor R a' η
    then some (Classical.choose (hcover η h)) else none

theorem coverOwner_none {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    ∀ η, coverOwner R r δ a a' hcover η = none → touchFactor R a η = touchFactor R a' η := by
  intro η h
  unfold coverOwner at h
  split_ifs at h with hne
  exact of_not_not hne

theorem coverOwner_touch {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    ∀ η i, coverOwner R r δ a a' hcover η = some i → typedTouchesSupport (N := N) η (r i) := by
  intro η i h
  unfold coverOwner at h
  split_ifs at h with hne
  · have hi := Option.some.inj h
    subst hi
    exact (Classical.choose_spec (hcover η hne)).1

theorem coverOwner_bound {m : ℕ} (R : Set (Link N)) (r : Fin m → Set (Link N))
    (δ : Fin m → ℝ) (a a' : Polymer N → ℝ)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    ∀ η i, coverOwner R r δ a a' hcover η = some i →
      |touchFactor R a η - touchFactor R a' η| ≤ δ i := by
  intro η i h
  unfold coverOwner at h
  split_ifs at h with hne
  · have hi := Option.some.inj h
    subst hi
    exact (Classical.choose_spec (hcover η hne)).2

end ActivityProfileMultiRegion

/-! ## 57-L.6 — the public statements -/

open ActivityProfileMultiRegion

variable {N : ℕ} [NeZero N] [Fintype (Site N)]
variable {G : Type*} [Group G]
variable [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
variable (μm : Measure G) [SigmaFinite μm] [IsProbabilityMeasure μm]

/-- **TWO-TERM ESTIMATE, SEVERAL REGIONS**: under the cover hypothesis,
      |F_R(a) − F_R(a′)| ≤ Cf·[e^{6 D_s/113} + e^{4 D_s/113}]·∑ i, δ i·e^{−n i/2}.
    The owner is built from `hcover` by classical choice; `m = 0` is admitted;
    the regions may overlap; `R` is arbitrary; no separation of `s` from `R`,
    no `r i ⊆ R`, no unit background, no `δ i ≤ 1`, no `DependsOnlyOn f s`;
    nothing divided by any amplitude or factor; no factor of `m` outside the
    sum. The exponents are the Stone 56 ones, rewritten `6 D_s/113`, `4 D_s/113`. -/
theorem abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  have h := abs_profileExpectation_sub_le_of_owner μm hβ mχ hχabs hsmall R mf hCf
    hδ0 hsep h0 h1 h0' h1' (coverOwner R r δ a a' hcover)
    (coverOwner_none R r δ a a' hcover) (coverOwner_touch R r δ a a' hcover)
    (coverOwner_bound R r δ a a' hcover)
  have e1 : Real.exp (3 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      = Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    congr 1; ring
  have e2 : Real.exp (2 * ((supportLinkFinset (N := N) s).card : ℝ) * (2/113))
      = Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) := by
    congr 1; ring
  rw [e1, e2] at h
  exact h

/-- **CAPSTONE 57 — STABILITY OF THE PROFILE-DAMPED FUNCTIONAL UNDER LOCALIZED
    CHANGES IN SEVERAL REGIONS**: under the cover hypothesis,
      |F_R(a) − F_R(a′)| ≤ (2 Cf)·e^{6 D_s/113}·∑ i, δ i·e^{−n i/2},
    the Stone 54–56 constant and regime, the single cost `δ·e^{−n/2}` of Stone
    56 replaced by the finite sum of the individual costs of the regions. From
    the two-term estimate, `0 ≤ Cf` (derived), `B ≥ 0` and
    `e^{4 D_s/113} ≤ e^{6 D_s/113}` (`D_s ≥ 0`). A composition derived from
    Stone 56; no universal improvement over a single control is claimed. -/
theorem abs_profileExpectation_sub_profileExpectation_le_multiregion
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {m : ℕ} {r : Fin m → Set (Link N)} {n : Fin m → ℕ} {δ : Fin m → ℝ}
    (hδ0 : ∀ i, 0 ≤ δ i)
    (hsep : ∀ i, WalkBarrierSeparated (N := N) s (r i) (n i))
    {a a' : Polymer N → ℝ}
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin m, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ (2 * Cf) * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
  have hCf0 : 0 ≤ Cf := nonneg_of_abs_le_of_config hCf
  have hB := budget_nonneg n δ hδ0
  have h2 := abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms
    μm hβ mχ hχabs hsmall R mf hCf hδ0 hsep h0 h1 h0' h1' hcover
  have hD : (0:ℝ) ≤ ((supportLinkFinset (N := N) s).card : ℝ) := Nat.cast_nonneg _
  have hmono : Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
      ≤ Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113) :=
    Real.exp_le_exp.mpr (by nlinarith)
  refine le_trans h2 ?_
  calc Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (4 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2)
      ≤ Cf * (Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
              + Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113))
          * ∑ i : Fin m, δ i * Real.exp (-((n i : ℕ) : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_right _ hB
        apply mul_le_mul_of_nonneg_left _ hCf0
        exact add_le_add_left hmono _
    _ = _ := by ring

/-- **One region recovers Stone 56**: the Stone 56 hypotheses (`hsame`, `hδ`
    for one region `r`) give the cover hypothesis with `m = 1` (`hsame` by
    contraposition gives the touch of `r`), and the capstone of Stone 57
    returns the Stone 56 bound, the sum over `Fin 1` on its right-hand side
    reducing to `δ·e^{−n/2}`. A compatibility test of the composition, not an
    independent proof of Stone 56 (whose theorem is consumed by the chain). -/
theorem abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_multiregion
    {β : ℝ} (hβ : 0 ≤ β) {χ : G → ℝ} (mχ : Measurable χ)
    (hχabs : ∀ g : G, |χ g| ≤ 1) (hsmall : β ≤ (1 : ℝ) / 40000)
    {s r : Set (Link N)} (R : Set (Link N))
    {f : Config N G → ℝ} (mf : Measurable f) {Cf : ℝ} (hCf : ∀ U, |f U| ≤ Cf)
    {n : ℕ} (hsep : WalkBarrierSeparated (N := N) s r n)
    {a a' : Polymer N → ℝ} {δ : ℝ} (hδ0 : 0 ≤ δ)
    (h0 : ∀ η, 0 ≤ a η) (h1 : ∀ η, a η ≤ 1) (h0' : ∀ η, 0 ≤ a' η) (h1' : ∀ η, a' η ≤ 1)
    (hsame : ∀ η, ¬ typedTouchesSupport (N := N) η r → touchFactor R a η = touchFactor R a' η)
    (hδ : ∀ η, typedTouchesSupport (N := N) η r → |touchFactor R a η - touchFactor R a' η| ≤ δ) :
    |profileExpectation μm β χ f s R a - profileExpectation μm β χ f s R a'|
      ≤ δ * (2 * Cf)
          * Real.exp (6 * ((supportLinkFinset (N := N) s).card : ℝ) / 113)
          * Real.exp (-(n : ℝ) / 2) := by
  have hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin 1, typedTouchesSupport (N := N) η ((fun _ => r) i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ (fun _ => δ) i := by
    intro η hne
    have ht : typedTouchesSupport (N := N) η r := by
      by_contra hnt
      exact hne (hsame η hnt)
    exact ⟨0, ht, hδ η ht⟩
  have h := abs_profileExpectation_sub_profileExpectation_le_multiregion μm hβ mχ hχabs hsmall
    R mf hCf (m := 1) (r := fun _ => r) (n := fun _ => n) (δ := fun _ => δ)
    (fun _ => hδ0) (fun _ => hsep) h0 h1 h0' h1' hcover
  rw [Fin.sum_univ_one] at h
  calc _ ≤ _ := h
    _ = _ := by ring

omit [MeasurableMul₂ G] [MeasurableInv G] [SigmaFinite μm] [IsProbabilityMeasure μm] in
/-- **No region**: with `m = 0` the cover hypothesis forces the equality of all
    effective factors (there is no index), hence `F_R(a) = F_R(a′)` EXACTLY,
    with no analytic hypothesis (no regime, no separation, no bound on `f`).
    The analytic capstone also accepts `m = 0`, with cost `B = 0`. -/
theorem profileExpectation_eq_of_cover_empty_family (β : ℝ) (χ : G → ℝ) (f : Config N G → ℝ)
    (s R : Set (Link N)) {r : Fin 0 → Set (Link N)} {δ : Fin 0 → ℝ}
    {a a' : Polymer N → ℝ}
    (hcover : ∀ η, touchFactor R a η ≠ touchFactor R a' η →
      ∃ i : Fin 0, typedTouchesSupport (N := N) η (r i)
        ∧ |touchFactor R a η - touchFactor R a' η| ≤ δ i) :
    profileExpectation μm β χ f s R a = profileExpectation μm β χ f s R a' := by
  apply profileExpectation_eq_of_touchFactor_eq μm β χ f s R
  intro η
  by_contra hne
  obtain ⟨i, _, _⟩ := hcover η hne
  exact i.elim0

/-! ## 57-L.7 — kernel certificates -/

#print axioms ActivityProfileMultiRegion.not_moved_zero
#print axioms ActivityProfileMultiRegion.stepProfile_zero
#print axioms ActivityProfileMultiRegion.stepProfile_mem
#print axioms ActivityProfileMultiRegion.touchFactor_stepProfile
#print axioms ActivityProfileMultiRegion.moved_mono
#print axioms ActivityProfileMultiRegion.owner_eq_of_moved_succ
#print axioms ActivityProfileMultiRegion.step_same
#print axioms ActivityProfileMultiRegion.step_bound
#print axioms ActivityProfileMultiRegion.touchFactor_stepProfile_last
#print axioms ActivityProfileMultiRegion.abs_telescope
#print axioms ActivityProfileMultiRegion.budget_nonneg
#print axioms ActivityProfileMultiRegion.abs_profileExpectation_sub_le_of_owner
#print axioms ActivityProfileMultiRegion.coverOwner_none
#print axioms ActivityProfileMultiRegion.coverOwner_touch
#print axioms ActivityProfileMultiRegion.coverOwner_bound
#print axioms abs_profileExpectation_sub_profileExpectation_le_multiregion_two_terms
#print axioms abs_profileExpectation_sub_profileExpectation_le_multiregion
#print axioms abs_profileExpectation_sub_profileExpectation_le_local_exp_decay_of_multiregion
#print axioms profileExpectation_eq_of_cover_empty_family
#print axioms ActivityProfileMultiRegion.moved
#print axioms ActivityProfileMultiRegion.stepProfile
#print axioms ActivityProfileMultiRegion.coverOwner

end LatticeGauge
