/-
LatticeGauge/Basic.lean — Phase 3 (realistic target), first stone.

UNLIKE Phases 1-2, this file contains NO physical axioms. Everything here
is CONSTRUCTED and every lemma is PROVED (Box 1 of VERIFICATION_STATUS.md).

Scope: finite 4D periodic lattice, gauge configurations valued in an
abstract group G, plaquette holonomy, Wilson action w.r.t. a normalized
real character. Long-term goal (see PHASE3_ROADMAP.md): strong-coupling
mass gap for lattice Yang-Mills (Osterwalder–Seiler 1978).
-/
import Mathlib

namespace LatticeGauge

/-- A site of the 4-dimensional periodic lattice of extent `N`. -/
abbrev Site (N : ℕ) := Fin N × Fin N × Fin N × Fin N

/-- Lattice directions. -/
abbrev Dir := Fin 4

/-- A link is a site together with a positive direction. -/
abbrev Link (N : ℕ) := Site N × Dir

/-- A gauge configuration assigns a group element to every link. -/
abbrev Config (N : ℕ) (G : Type*) := Link N → G

variable {N : ℕ} {G : Type*} [Group G]

/-- Shift a site by one unit in direction `μ` (periodic boundary). -/
def shift (x : Site N) (μ : Dir) [NeZero N] : Site N :=
  match μ with
  | ⟨0, _⟩ => (x.1 + 1, x.2.1, x.2.2.1, x.2.2.2)
  | ⟨1, _⟩ => (x.1, x.2.1 + 1, x.2.2.1, x.2.2.2)
  | ⟨2, _⟩ => (x.1, x.2.1, x.2.2.1 + 1, x.2.2.2)
  | ⟨3, _⟩ => (x.1, x.2.1, x.2.2.1, x.2.2.2 + 1)

/-- Holonomy around the plaquette at `x` in the (μ,ν) plane:
    U_μ(x) · U_ν(x+μ) · U_μ(x+ν)⁻¹ · U_ν(x)⁻¹. -/
def plaquette [NeZero N] (U : Config N G) (x : Site N) (μ ν : Dir) : G :=
  U (x, μ) * U (shift x μ, ν) * (U (shift x ν, μ))⁻¹ * (U (x, ν))⁻¹

/-- The constant-identity configuration. -/
def trivialConfig (N : ℕ) (G : Type*) [Group G] : Config N G := fun _ => 1

@[simp] lemma trivialConfig_apply (ℓ : Link N) : trivialConfig N G ℓ = 1 := rfl

/-- **Proved:** every plaquette of the trivial configuration is 1. -/
@[simp] theorem plaquette_trivial [NeZero N] (x : Site N) (μ ν : Dir) :
    plaquette (trivialConfig N G) x μ ν = 1 := by
  simp [plaquette]

section WilsonAction

variable (χ : G → ℝ)

/-- Wilson action w.r.t. a normalized real character `χ`
    (think `χ g = (1/n) · Re (tr g)` on SU(n)):
    S(U) = Σ_{x, μ<ν} (1 - χ(plaquette)). -/
def wilsonAction [NeZero N] [Fintype (Site N)] (U : Config N G) : ℝ :=
  ∑ x : Site N, ∑ μ : Dir, ∑ ν : Dir,
    if μ.val < ν.val then 1 - χ (plaquette U x μ ν) else 0

/-- **Proved:** if `χ ≤ 1` pointwise, the Wilson action is nonnegative. -/
theorem wilsonAction_nonneg [NeZero N] [Fintype (Site N)]
    (hχ : ∀ g : G, χ g ≤ 1) (U : Config N G) :
    0 ≤ wilsonAction χ U := by
  unfold wilsonAction
  refine Finset.sum_nonneg fun x _ => ?_
  refine Finset.sum_nonneg fun μ _ => ?_
  refine Finset.sum_nonneg fun ν _ => ?_
  by_cases h : μ.val < ν.val
  · simp only [h, if_true]
    linarith [hχ (plaquette U x μ ν)]
  · simp [h]

/-- **Proved:** if `χ 1 = 1`, the trivial configuration has zero action —
    the classical vacuum. -/
theorem wilsonAction_trivial [NeZero N] [Fintype (Site N)]
    (hχ1 : χ 1 = 1) :
    wilsonAction χ (trivialConfig N G) = 0 := by
  unfold wilsonAction
  refine Finset.sum_eq_zero fun x _ => ?_
  refine Finset.sum_eq_zero fun μ _ => ?_
  refine Finset.sum_eq_zero fun ν _ => ?_
  by_cases h : μ.val < ν.val
  · simp [h, hχ1]
  · simp [h]

end WilsonAction

end LatticeGauge
