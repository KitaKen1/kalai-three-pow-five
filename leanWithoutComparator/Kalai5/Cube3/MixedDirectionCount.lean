import Kalai5.Cube3.MixedDirections

/-! Count triangle directions with weight three at incidences and two for unused segment normals. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {T : TriangleData}
namespace MixedDirections
variable (D : MixedDirections T)

lemma normal_lines_distinct (n : Fin 2 → E 2) (hn : ∀ j,‖n j‖=1)
    (hnd : ∀ j,⟪n j,D.direction j⟫=0) {i j : Fin 2} (hij : i ≠ j) :
    n i ≠ n j ∧ n i ≠ -n j := by
  have hbad (h : ⟪n i,D.direction j⟫=0) : False := by
    have hz := D.common_orthogonal_zero hij (hnd i) h
    have hh := hn i
    rw [hz,norm_zero] at hh; norm_num at hh
  constructor
  · intro he; apply hbad; rw [he]; exact hnd j
  · intro he; apply hbad; rw [he,inner_neg_left,hnd j,neg_zero]

theorem weighted_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (F : ∀ i : Fin 3,PositiveFamily C (Fin (D.weight i)))
    (hF : ∀ i k,(F i).normal k=T.normal i)
    (n : Fin 2 → E 2) (hn : ∀ j,‖n j‖=1) (hnd : ∀ j,⟪n j,D.direction j⟫=0)
    (G : ∀ j : Fin 2,PositiveFamily C (Fin 2)) (hG : ∀ j k,(G j).normal k=n j) :
    20 ≤ fvec P 4 := by
  classical
  let A := PositiveFamily.sigma F
    (fun i j hij a b => by rw [hF,hF]; exact fun h => hij (T.normal_injective h))
    (fun i j a b => by rw [hF,hF]; exact T.no_opposite i j)
  let J := {j : Fin 2 // ¬∃ i,D.Shares i j}
  let B := PositiveFamily.sigma (fun j : J => G j.val)
    (by
      intro i j hij a b
      rw [hG,hG]
      exact (D.normal_lines_distinct n hn hnd (fun h => hij (Subtype.ext h))).1)
    (by
      intro i j a b
      by_cases hij : i=j
      · subst j; exact (G i.val).noOpposite a b
      · rw [hG,hG]
        exact (D.normal_lines_distinct n hn hnd (fun h => hij (Subtype.ext h))).2)
  have hne : ∀ a b,A.normal a ≠ B.normal b := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    change (F i).normal a=(G j.val).normal b at he
    rw [hF,hG] at he
    apply j.property
    refine ⟨i,?_⟩
    change ⟪T.normal i,D.direction j.val⟫=0
    rw [he]; exact hnd j.val
  have hop : ∀ a b,A.normal a ≠ -B.normal b := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    change (F i).normal a= -(G j.val).normal b at he
    rw [hF,hG] at he
    apply j.property
    refine ⟨i,?_⟩
    change ⟪T.normal i,D.direction j.val⟫=0
    rw [he,inner_neg_left,hnd j.val,neg_zero]
  have hh := (A.sum B hne hop).facets hP hrange
  have hc := D.weight_sum
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,
    Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  simp only [Nat.card_eq_fintype_card] at hc
  change (∑ i,D.weight i)+2*Fintype.card J=7 at hc
  omega

end MixedDirections
end Kalai5.Cube3
