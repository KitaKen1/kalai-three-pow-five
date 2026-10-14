import Kalai5.Cube3.SharedTriangleCount

/-! Any extra vertex beyond the matching weights excludes eighteen facets. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.weighted_direction_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) {j k : Fin 4}
    (T : TriangleFibre C j) (U : TriangleFibre C k) (w : Fin 3 → ℕ)
    (F : ∀ i,PositiveFamily C (Fin (w i))) (hF : ∀ i a,(F i).normal a=T.triangle.normal i) :
    6+2*((∑ i,w i)+Nat.card {b : Fin 3 // ¬∃ a,T.triangle.Shares U.triangle a b}) ≤ fvec P 4 := by
  classical
  let A := PositiveFamily.sigma F
    (fun i j hij a b => by rw [hF,hF]; exact fun h => hij (T.triangle.normal_injective h))
    (fun i j a b => by rw [hF,hF]; exact T.triangle.no_opposite i j)
  let J := {j : Fin 3 // ¬∃ i,T.triangle.Shares U.triangle i j}
  have hU : ∀ j : J,∃ F : PositiveFamily C Unit,∀ k,F.normal k=U.triangle.normal j.val :=
    fun j => U.one_positive hP hrange j.val
  choose G hG using hU
  let B := PositiveFamily.sigma G
    (fun i j hij a b => by rw [hG,hG]; exact fun h => hij (Subtype.ext (U.triangle.normal_injective h)))
    (fun i j a b => by rw [hG,hG]; exact U.triangle.no_opposite i.val j.val)
  have hne : ∀ a b,A.normal a ≠ B.normal b := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    change (F i).normal a=(G j).normal b at he
    rw [hF,hG] at he
    exact j.property ⟨i,Or.inl he⟩
  have hop : ∀ a b,A.normal a ≠ -B.normal b := by
    rintro ⟨i,a⟩ ⟨j,b⟩ he
    change (F i).normal a= -(G j).normal b at he
    rw [hF,hG] at he
    exact j.property ⟨i,Or.inr he⟩
  have hh := (A.sum B hne hop).facets hP hrange
  simpa only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,Fintype.card_unit,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one,Nat.card_eq_fintype_card] using hh

theorem TriangleFibre.no_matching_bonus {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i : Fin 3) (G : PositiveFamily C (Fin (T.triangle.sharedWeight U.triangle i+1)))
    (hG : ∀ k,G.normal k=T.triangle.normal i) : False := by
  classical
  let w := fun j => T.triangle.sharedWeight U.triangle j+(if j=i then 1 else 0)
  have hex : ∀ j,∃ F : PositiveFamily C (Fin (w j)),∀ k,F.normal k=T.triangle.normal j := by
    intro j
    by_cases hji : j=i
    · subst j
      let e : Fin (w i) ≃ Fin (T.triangle.sharedWeight U.triangle i+1) :=
        Fintype.equivOfCardEq (by simp [w])
      exact ⟨G.reindex e e.injective,fun k => hG (e k)⟩
    · obtain ⟨F,hF⟩ := TriangleFibre.shared_weight_family hP hrange τ T U h0 h1 hno j
      let e : Fin (w j) ≃ Fin (T.triangle.sharedWeight U.triangle j) :=
        Fintype.equivOfCardEq (by simp [w,hji])
      exact ⟨F.reindex e e.injective,fun k => hF (e k)⟩
  choose F hF using hex
  have hfac := T.weighted_direction_facets hP hrange U w F hF
  have hsum : (∑ j,w j)=(∑ j,T.triangle.sharedWeight U.triangle j)+1 := by
    simp [w,Finset.sum_add_distrib]
  have hcount := T.triangle.shared_weight_sum U.triangle
  rw [hsum] at hfac
  omega

end Kalai5.Cube3
