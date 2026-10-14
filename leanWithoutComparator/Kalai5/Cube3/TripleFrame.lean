import Kalai5.Cube3.SegmentCoordinates
import Kalai5.Cube3.TripleSlab

/-! An exact coordinate map between a three-parallel normal slice and the slab. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma det_ne_of_annihilator {a c b : E 2} (ha : a ≠ 0)
    (h0 : ⟪b,a⟫ = 0) (h1 : ⟪b,c⟫ = 1) : det2 a c ≠ 0 := by
  intro hd
  rw [LemmaB.Eight.inner_E2] at h0 h1
  have he0 : a 0 * (b 0*c 0+b 1*c 1) - c 0*(b 0*a 0+b 1*a 1) = b 1*det2 a c := by
    unfold det2; ring
  have he1 : c 1*(b 0*a 0+b 1*a 1) - a 1*(b 0*c 0+b 1*c 1) = b 0*det2 a c := by
    unfold det2; ring
  rw [h0,h1,hd] at he0 he1
  have ha0 : a 0 = 0 := by linarith
  have ha1 : a 1 = 0 := by linarith
  apply ha
  ext i; fin_cases i <;> assumption

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

structure TripleFrame where
  order : Equiv.Perm (Fin 4)
  normal : E 2
  zero : ∀ i : Fin 3, ⟪normal,S.axis (order i.castSucc)⟫ = 0
  unit : ⟪normal,S.axis (order 3)⟫ = 1

namespace TripleFrame

variable {S} (F : TripleFrame S)

noncomputable def eta : ℝ := S.drift F.normal

lemma normal_ne_zero : F.normal ≠ 0 := by
  intro h
  have hh := F.unit
  rw [h,inner_zero_left] at hh
  norm_num at hh

lemma transverse (i : Fin 3) : det2 (S.axis (F.order i.castSucc)) (S.axis (F.order 3)) ≠ 0 :=
  det_ne_of_annihilator (S.axis_ne_zero _) (F.zero i) F.unit

noncomputable def coords (z : SlabPoint) (j : Fin 4) : ℝ :=
  (![z.1 0,z.1 1,z.1 2,F.eta*z.2 - ∑ i, z.1 i] : Fin 4 → ℝ) (F.order.symm j)

lemma coords_order (z : SlabPoint) (j : Fin 4) :
    F.coords z (F.order j) = (![z.1 0,z.1 1,z.1 2,F.eta*z.2 - ∑ i, z.1 i] : Fin 4 → ℝ) j := by
  simp [coords]

lemma coords_sum (z : SlabPoint) : ∑ j, F.coords z j = S.drift (z.2 • F.normal) := by
  simp only [coords]
  rw [Equiv.sum_comp F.order.symm]
  simp [Fin.sum_univ_four,Fin.sum_univ_three,eta]
  ring

noncomputable def embed (z : SlabPoint) : E5 :=
  pack (S.centeredOffset (F.coords z) (z.2 • F.normal)) (z.2 • F.normal)

lemma planar_embed (z : SlabPoint) : planar (F.embed z) = z.2 • F.normal := planar_pack _ _

lemma centerEval_embed (z : SlabPoint) : S.centerEval (F.embed z) = F.coords z :=
  S.centerEval_pack _ _ (F.coords_sum z)

noncomputable def project : E5 →ₗ[ℝ] SlabPoint where
  toFun p := ((WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![S.centerEval p (F.order 0),S.centerEval p (F.order 1),S.centerEval p (F.order 2)],
    ⟪planar p,S.axis (F.order 3)⟫)
  map_add' := by
    intro p q
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_add]
    · have hp := planarLinear.map_add p q
      change planar (p+q) = planar p + planar q at hp
      simp [hp,inner_add_left]
  map_smul' := by
    intro t p
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_smul]
    · have hp := planarLinear.map_smul t p
      change planar (t • p) = t • planar p at hp
      simp [hp,real_inner_smul_left]

lemma project_first (p : E5) (i : Fin 3) :
    (F.project p).1 i = S.centerEval p (F.order i.castSucc) := by
  fin_cases i <;> rfl

lemma project_last (p : E5) : (F.project p).2 = ⟪planar p,S.axis (F.order 3)⟫ := rfl

lemma project_embed (z : SlabPoint) : F.project (F.embed z) = z := by
  apply Prod.ext
  · ext i
    rw [project_first,centerEval_embed,coords_order]
    fin_cases i <;> rfl
  · rw [project_last,planar_embed,real_inner_smul_left,F.unit,mul_one]

lemma embed_injective : Function.Injective F.embed := by
  intro a b h
  simpa only [F.project_embed] using congrArg F.project h

lemma plane_of_orthogonal (p : E5) (i : Fin 3)
    (hi : ⟪planar p,S.axis (F.order i.castSucc)⟫ = 0) :
    planar p = (F.project p).2 • F.normal := by
  apply sub_eq_zero.1
  apply orthogonal_two_eq_zero (F.transverse i)
  · rw [inner_sub_left,real_inner_smul_left,F.zero,hi,mul_zero,sub_self]
  · rw [inner_sub_left,real_inner_smul_left,F.unit,mul_one,project_last,sub_self]

lemma embed_project {p : E5} (hp : planar p = (F.project p).2 • F.normal) :
    F.embed (F.project p) = p := by
  apply S.centered_ext (by rw [planar_embed]; exact hp.symm)
  rw [centerEval_embed]
  funext j
  obtain ⟨j,rfl⟩ := F.order.surjective j
  rw [coords_order]
  have hsum : ∑ k, S.centerEval p (F.order k) = S.drift (planar p) := by
    rw [Equiv.sum_comp F.order,S.centerEval_sum]
  rw [Fin.sum_univ_four,hp,map_smul,smul_eq_mul] at hsum
  fin_cases j
  · exact F.project_first p 0
  · exact F.project_first p 1
  · exact F.project_first p 2
  · simp only [Matrix.cons_val_three,Fin.sum_univ_three,project_first]
    change F.eta * (F.project p).2 -
      (S.centerEval p (F.order 0) + S.centerEval p (F.order 1) + S.centerEval p (F.order 2)) =
        S.centerEval p (F.order 3)
    change _ = (F.project p).2 * F.eta at hsum
    linarith

lemma mem_embed (z : SlabPoint) : F.embed z ∈ C.polarModel ↔ z ∈ tripleSlab F.eta := by
  rw [S.mem_polar_centered]
  have hzero (i : Fin 3) : ⟪planar (F.embed z),S.axis (F.order i.castSucc)⟫ = 0 := by
    rw [planar_embed,real_inner_smul_left,F.zero,mul_zero]
  have htop : ⟪planar (F.embed z),S.axis (F.order 3)⟫ = z.2 := by
    rw [planar_embed,real_inner_smul_left,F.unit,mul_one]
  constructor
  · intro h
    refine ⟨fun i => ?_,?_⟩
    · have hh := h (F.order i.castSucc)
      rw [centerEval_embed,coords_order,hzero,abs_zero,add_zero] at hh
      fin_cases i <;> exact hh
    · have hh := h (F.order 3)
      rw [centerEval_embed,coords_order,htop] at hh
      exact hh
  · intro h j
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [centerEval_embed,coords_order]
    have hj : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl
    · change |z.1 0| + |⟪planar (F.embed z),S.axis (F.order 0)⟫| ≤ 1
      rw [show ⟪planar (F.embed z),S.axis (F.order 0)⟫ = 0 from hzero 0,abs_zero,add_zero]
      exact h.1 0
    · change |z.1 1| + |⟪planar (F.embed z),S.axis (F.order 1)⟫| ≤ 1
      rw [show ⟪planar (F.embed z),S.axis (F.order 1)⟫ = 0 from hzero 1,abs_zero,add_zero]
      exact h.1 1
    · change |z.1 2| + |⟪planar (F.embed z),S.axis (F.order 2)⟫| ≤ 1
      rw [show ⟪planar (F.embed z),S.axis (F.order 2)⟫ = 0 from hzero 2,abs_zero,add_zero]
      exact h.1 2
    · change |F.eta*z.2-∑ i,z.1 i| + |⟪planar (F.embed z),S.axis (F.order 3)⟫| ≤ 1
      rw [htop]; exact h.2

end TripleFrame
end Kalai5.Cube3
