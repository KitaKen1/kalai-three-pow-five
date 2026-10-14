import Kalai5.Cube3.TriangleMatching

/-! The incidences between triangle normals and two independent segment directions form a matching. -/
namespace Kalai5.Cube3
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma unit_common_orthogonal {n m d : E 2} (hn : ‖n‖=1) (hm : ‖m‖=1)
    (hd : d ≠ 0) (hnd : ⟪n,d⟫=0) (hmd : ⟪m,d⟫=0) : n=m ∨ n= -m := by
  have hnn : ⟪n,n⟫=1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  have he : m=⟪n,m⟫ • n := by
    apply sub_eq_zero.1
    apply orthogonal_two_eq_zero (det_ne_of_annihilator hd hnd hnn)
    · rw [inner_sub_left,real_inner_smul_left,hmd,hnd,mul_zero,sub_self]
    · rw [inner_sub_left,real_inner_smul_left,hnn,mul_one,real_inner_comm n m,sub_self]
  have ht : |⟪n,m⟫|=1 := by
    have hh := congrArg norm he
    rw [hm,norm_smul,hn,mul_one,Real.norm_eq_abs] at hh
    exact hh.symm
  by_cases hpos : 0 ≤ ⟪n,m⟫
  · rw [abs_of_nonneg hpos] at ht
    rw [ht,one_smul] at he
    exact Or.inl he.symm
  · rw [abs_of_neg (lt_of_not_ge hpos)] at ht
    have ht' : ⟪n,m⟫= -1 := by linarith
    rw [ht',neg_one_smul] at he
    exact Or.inr (by rw [he,neg_neg])

structure MixedDirections (T : TriangleData) where
  direction : Fin 2 → E 2
  nonzero : ∀ j,direction j ≠ 0
  transverse : det2 (direction 0) (direction 1) ≠ 0

namespace MixedDirections
variable {T : TriangleData} (D : MixedDirections T)

def Shares (i : Fin 3) (j : Fin 2) : Prop := ⟪T.normal i,D.direction j⟫=0

lemma shared_left_unique {i k : Fin 3} {j : Fin 2} (hi : D.Shares i j) (hk : D.Shares k j) : i=k := by
  rcases unit_common_orthogonal (T.normal_unit i) (T.normal_unit k) (D.nonzero j) hi hk with h | h
  · exact T.normal_injective h
  · exact (T.no_opposite i k h).elim

lemma common_orthogonal_zero {n : E 2} {j k : Fin 2} (hjk : j ≠ k)
    (hj : ⟪n,D.direction j⟫=0) (hk : ⟪n,D.direction k⟫=0) : n=0 := by
  fin_cases j <;> fin_cases k
  · exact (hjk rfl).elim
  · exact orthogonal_two_eq_zero D.transverse hj hk
  · exact orthogonal_two_eq_zero D.transverse hk hj
  · exact (hjk rfl).elim

lemma shared_right_unique {i : Fin 3} {j k : Fin 2} (hj : D.Shares i j) (hk : D.Shares i k) : j=k := by
  by_contra hne
  have hz := D.common_orthogonal_zero hne hj hk
  have hu := T.normal_unit i
  rw [hz,norm_zero] at hu; norm_num at hu

theorem shared_card : Nat.card {i : Fin 3 // ∃ j,D.Shares i j}=
    Nat.card {j : Fin 2 // ∃ i,D.Shares i j} := by
  classical
  let f : {i : Fin 3 // ∃ j,D.Shares i j} → {j : Fin 2 // ∃ i,D.Shares i j} :=
    fun i => ⟨i.property.choose,⟨i.val,i.property.choose_spec⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i k he
      apply Subtype.ext
      have hj := congrArg Subtype.val he
      change i.property.choose=k.property.choose at hj
      have hk := k.property.choose_spec
      rw [← hj] at hk
      exact D.shared_left_unique i.property.choose_spec hk
    · intro j
      obtain ⟨i,hi⟩ := j.property
      refine ⟨⟨i,⟨j.val,hi⟩⟩,?_⟩
      apply Subtype.ext
      exact D.shared_right_unique (Exists.choose_spec (show ∃ k,D.Shares i k from ⟨j.val,hi⟩)) hi
  exact Nat.card_congr (Equiv.ofBijective f hf)

noncomputable def weight (i : Fin 3) : ℕ := by
  classical
  exact 1+(if ∃ j,D.Shares i j then 2 else 0)

theorem weight_sum : (∑ i,D.weight i)+2*Nat.card {j : Fin 2 // ¬∃ i,D.Shares i j}=7 := by
  classical
  have hc := D.shared_card
  have hs := Fintype.card_subtype_compl (fun j : Fin 2 => ∃ i,D.Shares i j)
  have hle := Fintype.card_subtype_le (fun j : Fin 2 => ∃ i,D.Shares i j)
  have hsum : (∑ i,D.weight i)=3+2*Fintype.card {i : Fin 3 // ∃ j,D.Shares i j} := by
    have he (i : Fin 3) : D.weight i=1+2*(if ∃ j,D.Shares i j then 1 else 0) := by
      by_cases hi : ∃ j,D.Shares i j <;> simp [weight,hi]
    simp_rw [he]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    simp [Fintype.card_subtype]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at *
  omega

end MixedDirections
end Kalai5.Cube3
