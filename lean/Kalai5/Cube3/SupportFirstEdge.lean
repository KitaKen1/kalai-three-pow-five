import Kalai5.Cube3.SharedQuadrilateral

/-! Exact first-contact construction by a minimum ratio on a finite support set. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem finite_support_first_edge {A : Finset (E 2)} {a b e d z : E 2}
    (ha : a ∈ A) (hb : ∀ u ∈ A,⟪b,u⟫≤⟪b,a⟫)
    (hface : ∀ u ∈ A,⟪b,u⟫=⟪b,a⟫ → ⟪e,u⟫≤⟪e,a⟫)
    (hlower : ∃ v ∈ A,⟪b,v⟫<⟪b,a⟫)
    (hbd : ⟪b,d⟫=0) (hed : ⟪e,d⟫ ≠ 0) (hbz : ⟪b,z⟫=0) (hez : 0 < ⟪e,z⟫) :
    ∃ m q : E 2,q ∈ A ∧ q ≠ a ∧ ⟪m,q⟫=⟪m,a⟫ ∧
      (∀ u ∈ A,⟪m,u⟫≤⟪m,a⟫) ∧ ⟪m,d⟫ ≠ 0 ∧ 0 < ⟪m,z⟫ := by
  classical
  obtain ⟨v,hv,hvlt⟩ := hlower
  let Δ := ⟪b,a⟫-⟪b,v⟫
  have hΔ : 0 < Δ := sub_pos.2 hvlt
  let k := (1+|⟪e,v-a⟫|)/Δ
  have hk : k*Δ=1+|⟪e,v-a⟫| := div_mul_cancel₀ _ hΔ.ne'
  let w := e-k • b
  have hwv : 0 < ⟪w,v-a⟫ := by
    change 0 < ⟪e-k • b,v-a⟫
    rw [inner_sub_left,real_inner_smul_left,inner_sub_right b]
    have h := neg_abs_le ⟪e,v-a⟫
    dsimp only [Δ] at hk
    nlinarith
  let T := A.filter fun u => 0 < ⟪w,u-a⟫
  have hT : T.Nonempty := ⟨v,Finset.mem_filter.2 ⟨hv,hwv⟩⟩
  have hgap (u : E 2) (hu : u ∈ T) : 0 < ⟪b,a⟫-⟪b,u⟫ := by
    obtain ⟨hu,hwu⟩ := Finset.mem_filter.1 hu
    have hle := hb u hu
    apply sub_pos.2
    apply lt_of_le_of_ne hle
    intro heq
    have he := hface u hu heq
    change 0 < ⟪e-k • b,u-a⟫ at hwu
    rw [inner_sub_left,real_inner_smul_left,inner_sub_right e,inner_sub_right b,heq] at hwu
    linarith
  let ratio (u : E 2) := (⟪b,a⟫-⟪b,u⟫)/⟪w,u-a⟫
  obtain ⟨q,hq,hmin⟩ := T.exists_min_image ratio hT
  have hqA : q ∈ A := (Finset.mem_filter.1 hq).1
  have hwq : 0 < ⟪w,q-a⟫ := (Finset.mem_filter.1 hq).2
  let t := ratio q
  have ht : 0 < t := div_pos (hgap q hq) hwq
  have htq : t*⟪w,q-a⟫=⟪b,a⟫-⟪b,q⟫ := div_mul_cancel₀ _ hwq.ne'
  have hbound (u : E 2) (hu : u ∈ A) : t*⟪w,u-a⟫≤⟪b,a⟫-⟪b,u⟫ := by
    by_cases hwu : 0 < ⟪w,u-a⟫
    · exact (le_div_iff₀ hwu).1 (hmin u (Finset.mem_filter.2 ⟨hu,hwu⟩))
    · exact (mul_nonpos_of_nonneg_of_nonpos ht.le (le_of_not_gt hwu)).trans (sub_nonneg.2 (hb u hu))
  let m := b+t • w
  have heval (u : E 2) : ⟪m,u⟫-⟪m,a⟫=⟪b,u⟫-⟪b,a⟫+t*⟪w,u-a⟫ := by
    simp only [m,inner_add_left,real_inner_smul_left,inner_sub_right]; ring
  have hqd : q ≠ a := by intro h; rw [h,sub_self,inner_zero_right] at hwq; exact lt_irrefl _ hwq
  refine ⟨m,q,hqA,hqd,?_,?_,?_,?_⟩
  · have he := heval q; linarith
  · intro u hu
    have he := heval u
    have hb' := hbound u hu
    linarith
  · have hm : ⟪m,d⟫=t*⟪e,d⟫ := by
      simp only [m,w,inner_add_left,inner_sub_left,real_inner_smul_left,hbd,mul_zero,sub_zero,zero_add]
    rw [hm]; exact mul_ne_zero ht.ne' hed
  · have hm : ⟪m,z⟫=t*⟪e,z⟫ := by
      simp only [m,w,inner_add_left,inner_sub_left,real_inner_smul_left,hbz,mul_zero,sub_zero,zero_add]
    rw [hm]; exact mul_pos ht hez

end Kalai5.Cube3
