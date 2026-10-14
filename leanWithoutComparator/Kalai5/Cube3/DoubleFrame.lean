import Kalai5.Cube3.DoubleSlabCount

/-! The exact normal slice for two parallel segment classes. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} {C : Config x} (S : SegmentData C)

structure DoubleFrame where
  order : Equiv.Perm (Fin 4)
  normal : E 2
  zero : ∀ i : Fin 2, ⟪normal,S.axis (order i.castSucc.castSucc)⟫ = 0
  unit : ⟪normal,S.axis (order 3)⟫ = 1
  ratio_pos : 0 < |⟪normal,S.axis (order 2)⟫|
  ratio_le : |⟪normal,S.axis (order 2)⟫| ≤ 1

namespace DoubleFrame

variable {S} (F : DoubleFrame S)

noncomputable def eta : ℝ := S.drift F.normal

noncomputable def ratio : ℝ := |⟪F.normal,S.axis (F.order 2)⟫|

lemma normal_ne_zero : F.normal ≠ 0 := by
  intro h
  have hh := F.unit
  rw [h,inner_zero_left] at hh
  norm_num at hh

lemma transverse (i : Fin 2) : det2 (S.axis (F.order i.castSucc.castSucc)) (S.axis (F.order 3)) ≠ 0 :=
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

lemma plane_of_orthogonal (p : E5) (i : Fin 2)
    (hi : ⟪planar p,S.axis (F.order i.castSucc.castSucc)⟫ = 0) :
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

lemma mem_embed (z : SlabPoint) : F.embed z ∈ C.polarModel ↔ z ∈ doubleSlab F.ratio F.eta := by
  rw [S.mem_polar_centered]
  have hz0 : ⟪planar (F.embed z),S.axis (F.order 0)⟫=0 := by
    rw [planar_embed,real_inner_smul_left,show ⟪F.normal,S.axis (F.order 0)⟫=0 from F.zero 0,mul_zero]
  have hz1 : ⟪planar (F.embed z),S.axis (F.order 1)⟫=0 := by
    rw [planar_embed,real_inner_smul_left,show ⟪F.normal,S.axis (F.order 1)⟫=0 from F.zero 1,mul_zero]
  have hz2 : |⟪planar (F.embed z),S.axis (F.order 2)⟫|=F.ratio*|z.2| := by
    rw [planar_embed,real_inner_smul_left,abs_mul,mul_comm]; rfl
  have hz3 : ⟪planar (F.embed z),S.axis (F.order 3)⟫=z.2 := by
    rw [planar_embed,real_inner_smul_left,F.unit,mul_one]
  constructor
  · intro h
    have h0 := h (F.order 0)
    have h1 := h (F.order 1)
    have h2 := h (F.order 2)
    have h3 := h (F.order 3)
    rw [centerEval_embed,coords_order,hz0,abs_zero,add_zero] at h0
    rw [centerEval_embed,coords_order,hz1,abs_zero,add_zero] at h1
    rw [centerEval_embed,coords_order,hz2] at h2
    rw [centerEval_embed,coords_order,hz3] at h3
    exact ⟨h0,h1,h2,h3⟩
  · intro h j
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [centerEval_embed,coords_order]
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl
    · rw [hz0,abs_zero,add_zero]; exact h.1
    · rw [hz1,abs_zero,add_zero]; exact h.2.1
    · rw [hz2]; exact h.2.2.1
    · rw [hz3]; exact h.2.2.2

end DoubleFrame
end Kalai5.Cube3
