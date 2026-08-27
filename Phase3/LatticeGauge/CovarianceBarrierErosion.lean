/-
LatticeGauge/CovarianceBarrierErosion.lean — PEDRA 50, Gate
50-A18e: EXACT BARRIER EROSION BY THE CORE MASSES (architecture:
Sol; execution: Fable).

Pure geometry — the missing interface between A18d and A19: the
augmented barriers barrierRegion(T,s), barrierRegion(T',s') keep
a walk separation of at least
  n − (familyTotalCard T + familyTotalCard T').
Every plaquette touching the augmented barrier retreats to the
original support by a SHORT walk inside the responsible polymer
(≤ mass of the side: internal path ≤ card − 1 edges, plus at
most one coupling edge through the shared link — the +1 closes
with no hidden tax, exactly as in the census); the remaining
distance stays available to the connector. In A19 the lost
factor is repurchased by the half-tilt of the cores, preserving
the e^{-n/2} rate. No silent weakening to n − (masses + 1).

NOT here (hard hold): no GoodCorePair, no Disjoint s s', no
β/χ/measure/observable/gas/KP/connector/exponential, no A19
analytics, no SimpleGraph.dist, no new graph, no quotient, no
ordered family, no univ.card, no frozen file touched.
No project-local scientific axioms; 0 sorry.
-/
import Mathlib
import LatticeGauge.CovarianceBadPairMass

open scoped Classical

namespace LatticeGauge

variable {N : ℕ} [NeZero N] [Fintype (Site N)]

/-! ## A18e.1 — the short walk, extracted from the A7 machine
    (the walk is now RETURNED, not consumed) -/

theorem exists_walk_of_connectedWithin
    {A : Finset (Site N × Dir × Dir)}
    {p q : Site N × Dir × Dir}
    (h : connectedWithin (N := N) A p q) :
    ∃ w : (plaquetteGraph N).Walk p q,
      w.length + 1 ≤ A.card := by
  obtain ⟨hp, hq, hreach⟩ := h
  refine hreach.elim_path (fun path => ?_)
  refine ⟨path.val.map
    (SimpleGraph.Embedding.induce
      (↑A : Set (Site N × Dir × Dir))).toHom, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  have hlt := path.property.length_lt
  have hbridge : Fintype.card
      ↥(↑A : Set (Site N × Dir × Dir)) = A.card := by
    rw [← Fintype.card_coe A]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight (fun x => Finset.mem_coe))
  omega

/-! ## A18e.2 — coupling through the shared link -/

theorem plaquetteGraph_adj_of_shared_link
    {p q : Site N × Dir × Dir} {ℓ : Link N}
    (hne : p ≠ q)
    (hp : ℓ ∈ plaqLinkSet (N := N) p)
    (hq : ℓ ∈ plaqLinkSet (N := N) q) :
    (plaquetteGraph N).Adj p q :=
  ⟨hne, ⟨ℓ, Finset.mem_inter.mpr ⟨hp, hq⟩⟩⟩

/-! ## A18e.3 — the one-sided retreat to the support -/

theorem exists_short_walk_to_support_of_touches_barrier
    {T : Finset (Polymer N)} {s : Set (Link N)}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    {p : Site N × Dir × Dir}
    (hp : plaquetteTouchesRegion (N := N) p
      (barrierRegion (N := N) T s)) :
    ∃ q : Site N × Dir × Dir,
      plaquetteTouchesRegion (N := N) q s ∧
      ∃ w : (plaquetteGraph N).Walk p q,
        w.length ≤ familyTotalCard T := by
  have hp' : ¬ Disjoint
      (↑(plaqLinkSet (N := N) p) : Set (Link N))
      (barrierRegion (N := N) T s) := hp
  rw [Set.not_disjoint_iff] at hp'
  obtain ⟨ℓ, hℓp, hℓbar⟩ := hp'
  rcases hℓbar with hℓs | hℓT
  · -- the witness link already lies in s: zero cost
    refine ⟨p, ?_, SimpleGraph.Walk.nil, Nat.zero_le _⟩
    exact Set.not_disjoint_iff.mpr ⟨ℓ, hℓp, hℓs⟩
  · -- the witness link lies in the support of some t ∈ T
    obtain ⟨t, htT, hℓt⟩ := hℓT
    unfold blockLinkSupport familySupport at hℓt
    obtain ⟨p₀, hp₀t, hℓp₀⟩ := hℓt
    have ht : typedTouchesSupport (N := N) t s :=
      (Finset.mem_filter.mp hT).2 t htT
    obtain ⟨q, hqt, hqs⟩ := exists_plaquette_touching ht
    have hconn : connectedWithin (N := N) t.val p₀ q :=
      (isPolymer_of_mem_all t.property).2.2 p₀ hp₀t q hqt
    obtain ⟨w₀, hw₀⟩ := exists_walk_of_connectedWithin hconn
    have hcard : (t.val).card ≤ familyTotalCard T :=
      card_le_familyTotalCard htT
    by_cases hpp : p = p₀
    · subst hpp
      exact ⟨q, hqs, ⟨w₀, by omega⟩⟩
    · have hadj : (plaquetteGraph N).Adj p p₀ :=
        plaquetteGraph_adj_of_shared_link hpp hℓp hℓp₀
      refine ⟨q, hqs, ⟨SimpleGraph.Walk.cons hadj w₀, ?_⟩⟩
      rw [SimpleGraph.Walk.length_cons]
      omega

/-! ## A18e.4 — CAPSTONE: the eroded separation -/

/-- **CAPSTONE 50-A18e**: the augmented barriers keep walk
    separation n − (mass T + mass T') — each side retreats at
    cost at most its mass, the remaining distance belongs to the
    connector. No GoodCorePair, no Disjoint s s'. -/
theorem walkBarrierSeparated_barrierRegions_sub_familyMass
    {T T' : Finset (Polymer N)} {s s' : Set (Link N)} {n : ℕ}
    (hT : T ∈ typedTouchingFamilies (N := N) s)
    (hT' : T' ∈ typedTouchingFamilies (N := N) s')
    (hsep : WalkBarrierSeparated (N := N) s s' n) :
    WalkBarrierSeparated (N := N)
      (barrierRegion (N := N) T s)
      (barrierRegion (N := N) T' s')
      (n - (familyTotalCard T + familyTotalCard T')) := by
  intro p q hp hq w
  obtain ⟨p₁, hp₁s, L, hL⟩ :=
    exists_short_walk_to_support_of_touches_barrier hT hp
  obtain ⟨q₁, hq₁s', R, hR⟩ :=
    exists_short_walk_to_support_of_touches_barrier hT' hq
  have hw := hsep p₁ q₁ hp₁s hq₁s'
    ((L.reverse.append w).append R)
  rw [SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_append,
    SimpleGraph.Walk.length_reverse] at hw
  omega

#print axioms exists_short_walk_to_support_of_touches_barrier
#print axioms walkBarrierSeparated_barrierRegions_sub_familyMass

end LatticeGauge
