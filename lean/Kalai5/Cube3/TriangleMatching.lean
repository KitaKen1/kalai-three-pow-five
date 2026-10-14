import Kalai5.Cube3.AlignedTriangle
import Kalai5.Cube3.PositiveSigma

/-! The shared unoriented normals of two triangles form a partial matching. -/

namespace Kalai5.Cube3.TriangleData

def Shares (T U : TriangleData) (i j : Fin 3) : Prop :=
  T.normal i=U.normal j ∨ T.normal i= -U.normal j

lemma Shares.symm {T U : TriangleData} {i j : Fin 3} (h : T.Shares U i j) : U.Shares T j i := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by rw [h,neg_neg])

lemma shares_left_unique {T U : TriangleData} {i k j : Fin 3}
    (h : T.Shares U i j) (g : T.Shares U k j) : i=k := by
  rcases h with h | h <;> rcases g with g | g
  · exact T.normal_injective (h.trans g.symm)
  · exfalso; apply T.no_opposite i k; rw [h,g,neg_neg]
  · exfalso; apply T.no_opposite i k; rw [h,g]
  · exact T.normal_injective (h.trans g.symm)

lemma shares_right_unique {T U : TriangleData} {i j k : Fin 3}
    (h : T.Shares U i j) (g : T.Shares U i k) : j=k :=
  shares_left_unique h.symm g.symm

theorem shared_card (T U : TriangleData) :
    Nat.card {i : Fin 3 // ∃ j,T.Shares U i j} =
      Nat.card {j : Fin 3 // ∃ i,T.Shares U i j} := by
  classical
  let f : {i : Fin 3 // ∃ j,T.Shares U i j} → {j : Fin 3 // ∃ i,T.Shares U i j} :=
    fun i => ⟨i.property.choose,⟨i.val,i.property.choose_spec⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i k he
      apply Subtype.ext
      have hj := congrArg Subtype.val he
      change i.property.choose=k.property.choose at hj
      have hk := k.property.choose_spec
      rw [← hj] at hk
      exact shares_left_unique i.property.choose_spec hk
    · intro j
      obtain ⟨i,hi⟩ := j.property
      refine ⟨⟨i,⟨j.val,hi⟩⟩,?_⟩
      apply Subtype.ext
      exact shares_right_unique (Exists.choose_spec (show ∃ k,T.Shares U i k from ⟨j.val,hi⟩)) hi
  exact Nat.card_congr (Equiv.ofBijective f hf)

noncomputable def sharedWeight (T U : TriangleData) (i : Fin 3) : ℕ := by
  classical
  exact 1+(if ∃ j,T.Shares U i j then 1 else 0)+(if ∃ j,T.normal i= -U.normal j then 1 else 0)

theorem shared_weight_sum (T U : TriangleData) :
    (∑ i,T.sharedWeight U i)+Nat.card {j : Fin 3 // ¬∃ i,T.Shares U i j} =
      6+Nat.card {i : Fin 3 // ∃ j,T.normal i= -U.normal j} := by
  classical
  have hcard := T.shared_card U
  have hsplit := Fintype.card_subtype_compl (fun j : Fin 3 => ∃ i,T.Shares U i j)
  have hle := Fintype.card_subtype_le (fun j : Fin 3 => ∃ i,T.Shares U i j)
  have hsum : (∑ i,T.sharedWeight U i)=3+
      Fintype.card {i : Fin 3 // ∃ j,T.Shares U i j}+
      Fintype.card {i : Fin 3 // ∃ j,T.normal i= -U.normal j} := by
    simp [sharedWeight,Finset.sum_add_distrib,Fintype.card_subtype]
  simp only [Nat.card_eq_fintype_card,Fintype.card_fin] at *
  omega

end Kalai5.Cube3.TriangleData
