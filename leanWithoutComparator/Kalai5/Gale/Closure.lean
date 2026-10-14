import Kalai5.Gale.Faces
import Kalai5.Gale.Masks
import Kalai5.Euler.Euler

/-!
# Lower bounds on face numbers from certified face indices

For points `W : Fin n → E k`:

* face indices are closed under intersection (`IsFaceIdx.inter`) and `univ` is one;
* distinct nonempty face indices give distinct faces, so `#faces ≥ #(a family of face indices)`
  (`le_ncard_faces`).

`faces_of_closure` turns a certificate — a list of masks, each the intersection of the certified
facet masks containing it — into a lower bound on the number of faces.
-/

namespace Kalai5.Gale

open Set Module

variable {k n : ℕ} {W : Fin n → E k}

lemma isFaceIdx_univ : IsFaceIdx W Finset.univ :=
  ⟨0, Submodule.zero_mem _, fun _ _ => rfl, fun j hj => absurd (Finset.mem_univ j) hj⟩

lemma IsFaceIdx.nonneg {F : Finset (Fin n)} {a : Fin n → ℝ} (h0 : ∀ j ∈ F, a j = 0)
    (hpos : ∀ j ∉ F, 0 < a j) (j : Fin n) : 0 ≤ a j := by
  by_cases hj : j ∈ F
  · rw [h0 j hj]
  · exact (hpos j hj).le

/-- **Intersections of face indices are face indices.** -/
lemma IsFaceIdx.inter {F G : Finset (Fin n)} (hF : IsFaceIdx W F) (hG : IsFaceIdx W G) :
    IsFaceIdx W (F ∩ G) := by
  classical
  obtain ⟨a, ha, ha0, hapos⟩ := hF
  obtain ⟨b, hb, hb0, hbpos⟩ := hG
  refine ⟨a + b, Submodule.add_mem _ ha hb, fun j hj => ?_, fun j hj => ?_⟩
  · rw [Finset.mem_inter] at hj
    simp [ha0 j hj.1, hb0 j hj.2]
  · rw [Finset.mem_inter, not_and_or] at hj
    have h1 := IsFaceIdx.nonneg ha0 hapos j
    have h2 := IsFaceIdx.nonneg hb0 hbpos j
    simp only [Pi.add_apply]
    rcases hj with hj | hj
    · linarith [hapos j hj]
    · linarith [hbpos j hj]

/-- Intersection of a finite family of face indices. -/
lemma isFaceIdx_inf {ι : Type*} (s : Finset ι) (F : ι → Finset (Fin n))
    (h : ∀ i ∈ s, IsFaceIdx W (F i)) : IsFaceIdx W (s.inf F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isFaceIdx_univ
  | insert i s hi ih =>
    rw [Finset.inf_insert]
    exact (h i (Finset.mem_insert_self i s)).inter (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- **Distinct nonempty face indices give distinct faces.** -/
lemma le_ncard_faces (S : Finset (Finset (Fin n))) (hS : ∀ F ∈ S, F.Nonempty ∧ IsFaceIdx W F) :
    S.card ≤ (faces (convexHull ℝ (range W))).ncard := by
  classical
  have hfin : (faces (convexHull ℝ (range W))).Finite := by
    have := faces_finite_convexHull (Finset.univ.image W)
    rwa [coe_image_univ] at this
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn (fun F => convexHull ℝ (W '' ↑F)) ?_ ?_ hfin
  · intro F hF
    exact (conv_mem_faces (hS F hF).1 (hS F hF).2).1
  · intro F hF G hG hFG
    rw [← (conv_mem_faces (hS F hF).1 (hS F hF).2).2, ← (conv_mem_faces (hS G hG).1 (hS G hG).2).2]
    exact congrArg (idx W) hFG

end Kalai5.Gale
