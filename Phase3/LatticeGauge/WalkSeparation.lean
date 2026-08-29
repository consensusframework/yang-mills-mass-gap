/-
LatticeGauge/WalkSeparation.lean — PEDRA 50, Gate 50-A7: WALK
SEPARATION AND THE ADDITIVE MASS OF THE TUPLE (architecture:
Sol/GPT-5.6, new instance; execution: Fable).

ARCHITECTURAL CORRECTION (the new architect's first ruling,
honoured): SimpleGraph.dist stays in FULL HARD HOLD — not even
under Reachable. Separation is phrased by quantifying over ALL
walks of the ambient plaquetteGraph crossing the barriers:
  every walk from a plaquette touching R₁ to a plaquette
  touching R₂ has length + 1 ≥ n.
For unreachable pairs the statement is correctly VACUOUS — no
artificial value anywhere.

The chain of this gate:
  walk separation ⟹ BarrierSeparation ⟹
  n ≤ card(tuplePlaquetteUnion δ) ⟹ n ≤ Σ i, card((δ i).val)
— the geometric bridge of A6 converted into the ADDITIVE MASS
that the future weighted tail will see. No weights, no series,
no estimates here.

HARD HOLD: no SimpleGraph.dist/edist, no cdist/confinedLengths,
no 64^d, no 16·64^(2m), no q^d, no geometric series, no
exponential tail, no weighted/tilted KP, no covariance, no
changes to A0–A6 files, no clustering/thermodynamic/continuum/
mass-gap/Clay claims. Stone 45 untouched; single polymers do not
impersonate clusters.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.Basic
import LatticeGauge.BarrierBridge

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A7.1 — touching a region (exact abbreviation) -/

def plaquetteTouchesRegion (p : Site N × Dir × Dir)
    (R : Set (Link N)) : Prop :=
  ¬ Disjoint (↑(plaqLinkSet (N := N) p) : Set (Link N)) R

/-! ## A7.2 — separation by walks (ambient graph, vacuous for
    unreachable pairs — no junk value) -/

def WalkBarrierSeparated (R₁ R₂ : Set (Link N)) (n : ℕ) : Prop :=
  ∀ p q : Site N × Dir × Dir,
    plaquetteTouchesRegion (N := N) p R₁ →
    plaquetteTouchesRegion (N := N) q R₂ →
    ∀ w : (plaquetteGraph N).Walk p q, n ≤ w.length + 1

/-! ## A7.3 — walk separation ⟹ BarrierSeparation (the core:
    connectedWithin → induced Reachable → Path in the subtype →
    mapped to the ambient by Embedding.induce → length bounds) -/

theorem walkBarrierSeparated_barrierSeparation
    {R₁ R₂ : Set (Link N)} {n : ℕ}
    (hsep : WalkBarrierSeparated (N := N) R₁ R₂ n) :
    BarrierSeparation (N := N) R₁ R₂ n := by
  intro A hA h₁ h₂
  obtain ⟨p, hpA, hp₁⟩ := h₁
  obtain ⟨q, hqA, hq₂⟩ := h₂
  obtain ⟨hp', hq', hreach⟩ := hA p hpA q hqA
  refine hreach.elim_path (fun path => ?_)
  -- map the induced path to the ambient graph
  have hw := hsep p q hp₁ hq₂
    (path.val.map
      (SimpleGraph.Embedding.induce
        (↑A : Set (Site N × Dir × Dir))).toHom)
  rw [SimpleGraph.Walk.length_map] at hw
  -- a path in the finite subtype has length < card
  have hlt := path.property.length_lt
  have hbridge : Fintype.card
      ↥(↑A : Set (Site N × Dir × Dir)) = A.card := by
    rw [← Fintype.card_coe A]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun x => Finset.mem_coe))
  omega

/-! ## A7.4 — connector ⟹ union card ≥ n (A6 consumed, not
    reproved) -/

theorem connector_tuple_card_ge_of_walkSeparated {k : ℕ}
    {δ : Fin k → Polymer N} {T T' : Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected)
    (hhit : TupleHitsBothForbidden
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s') δ)
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    n ≤ (tuplePlaquetteUnion δ).card :=
  connector_tuple_card_ge hconn hhit
    (walkBarrierSeparated_barrierSeparation hwsep)

/-! ## A7.5 — union ≤ additive mass (overlaps are exactly why
    the direction is ≤; no disjointness hypothesis) -/

noncomputable def tupleTotalCard {k : ℕ}
    (δ : Fin k → Polymer N) : ℕ :=
  ∑ i : Fin k, ((δ i).val).card

theorem card_tuplePlaquetteUnion_le {k : ℕ}
    (δ : Fin k → Polymer N) :
    (tuplePlaquetteUnion δ).card ≤ tupleTotalCard δ := by
  unfold tuplePlaquetteUnion tupleTotalCard
  exact Finset.card_biUnion_le

/-! ## A7.6 — CAPSTONE: the additive mass of a connector -/

/-- **CAPSTONE 50-A7**: a connected connector tuple across two
    walk-separated barriers carries additive mass at least n —
    the visible chain n ≤ card(union) ≤ Σᵢ card(δ i). This is
    the exact output the future tilting will consume. -/
theorem connector_tupleTotalCard_ge {k : ℕ}
    {δ : Fin k → Polymer N} {T T' : Finset (Polymer N)}
    {s s' : Set (Link N)} {n : ℕ}
    (hconn : (polymerIncompatibilityGraph (N := N)
      (fun i => (δ i).val)).Connected)
    (hhit : TupleHitsBothForbidden
      (remoteAllowed (N := N) T s)
      (remoteAllowed (N := N) T' s') δ)
    (hwsep : WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s') n) :
    n ≤ tupleTotalCard δ :=
  le_trans
    (connector_tuple_card_ge_of_walkSeparated hconn hhit hwsep)
    (card_tuplePlaquetteUnion_le δ)

end LatticeGauge
