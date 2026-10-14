import Kalai5.Polar.Intervals

/-!
# Centrally symmetric polytopes in any dimension; counting through polarity

* `IsCSPolytope d P`: a full-dimensional polytope in `E d`, symmetric about the origin;
* `ncard_faces_polarSet`: a polytope with `0` in its interior and its polar have the same number
  of nonempty faces (`F ↦ F♦` on proper faces, `K ↦ K°`);
* `fvec_polarSet_zero`: the vertices of the polar correspond to the facets.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-- A full-dimensional polytope in `E d`, centrally symmetric about the origin. -/
structure IsCSPolytope (d : ℕ) (P : Set (E d)) : Prop extends IsPolytope P where
  symm : ∀ x ∈ P, -x ∈ P

lemma IsCSPolytope5.toIsCSPolytope {P : Set E5} (hP : IsCSPolytope5 P) : IsCSPolytope 5 P :=
  ⟨hP.toIsPolytope, hP.symm⟩

namespace IsCSPolytope

variable {P : Set (E d)} (hP : IsCSPolytope d P)
include hP

lemma convex : Convex ℝ P := by
  obtain ⟨V, rfl⟩ := hP.polytope; exact convex_convexHull ℝ _

lemma zero_mem_interior : (0 : E d) ∈ interior P := by
  obtain ⟨z, hz⟩ := hP.full
  have hneg : -z ∈ interior P := by
    have hsub : (fun x : E d => -x) ⁻¹' interior P ⊆ P := fun x hx => by
      simpa using hP.symm _ (interior_subset hx)
    have hopen : IsOpen ((fun x : E d => -x) ⁻¹' interior P) :=
      isOpen_interior.preimage continuous_neg
    exact interior_maximal hsub hopen (by simpa using hz)
  have := hP.convex.interior hz hneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simpa [← smul_add] using this

lemma nonempty : P.Nonempty := by
  obtain ⟨z, hz⟩ := hP.full; exact ⟨z, interior_subset hz⟩

end IsCSPolytope

section polar

variable {V : Finset (E d)} (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
include h0

/-- **A polytope with `0` inside and its polar have equally many nonempty faces.** -/
theorem ncard_faces_polarSet :
    (faces (polarSet (convexHull ℝ (V : Set (E d))))).ncard =
      (faces (convexHull ℝ (V : Set (E d)))).ncard := by
  classical
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (polarSet (convexHull ℝ (V : Set (E d)))) =
      convexHull ℝ (V : Set (E d)) :=
    polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  have hne0 : (convexHull ℝ (V : Set (E d))).Nonempty := ⟨0, interior_subset h0⟩
  symm
  refine Set.ncard_congr (fun F _ => if F = convexHull ℝ (V : Set (E d))
    then polarSet (convexHull ℝ (V : Set (E d))) else dualFace (convexHull ℝ (V : Set (E d))) F)
    ?_ ?_ ?_
  · intro F hF
    split_ifs with h
    · exact self_mem_faces ⟨0, zero_mem_polarSet _⟩
    · exact dualFace_mem_faces h0 hF h
  · intro F F' hF hF' heq
    by_cases h1 : F = convexHull ℝ (V : Set (E d)) <;>
      by_cases h2 : F' = convexHull ℝ (V : Set (E d))
    · rw [h1, h2]
    · rw [if_pos h1, if_neg h2] at heq
      exact absurd heq.symm (dualFace_ne_polarSet hF')
    · rw [if_neg h1, if_pos h2] at heq
      exact absurd heq (dualFace_ne_polarSet hF)
    · rw [if_neg h1, if_neg h2] at heq
      rw [eq_of_dualFace h0 hF h1, eq_of_dualFace h0 hF' h2, heq]
  · intro G hG
    by_cases hGQ : G = polarSet (convexHull ℝ (V : Set (E d)))
    · refine ⟨convexHull ℝ (V : Set (E d)), self_mem_faces hne0, ?_⟩
      rw [if_pos rfl, hGQ]
    · have hG' : G ∈ faces (convexHull ℝ (W : Set (E d))) := hW ▸ hG
      have hGQ' : G ≠ convexHull ℝ (W : Set (E d)) := hW ▸ hGQ
      have hFmem := dualFace_mem_faces h0W hG' hGQ'
      have hFne := dualFace_ne_polarSet (V := W) hG'
      have hdd := dualFace_dualFace h0W hG' hGQ'
      rw [← hW, hbip] at hFmem hFne hdd
      refine ⟨dualFace (polarSet (convexHull ℝ (V : Set (E d)))) G, hFmem, ?_⟩
      rw [if_neg hFne]
      exact hdd

/-- **The vertices of the polar correspond to the facets.** -/
theorem fvec_polarSet_zero (hd : 1 ≤ d) :
    fvec (polarSet (convexHull ℝ (V : Set (E d)))) 0 = fvec (convexHull ℝ (V : Set (E d))) (d - 1) := by
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (polarSet (convexHull ℝ (V : Set (E d)))) =
      convexHull ℝ (V : Set (E d)) :=
    polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  apply le_antisymm
  · have h1 := fvec_le_fvec_polarSet h0W 0 (by omega)
    rw [← hW, hbip, Nat.sub_zero] at h1
    exact h1
  · have h2 := fvec_le_fvec_polarSet h0 (d - 1) (by omega)
    rwa [show d - 1 - (d - 1) = 0 by omega] at h2

end polar

end Kalai5
