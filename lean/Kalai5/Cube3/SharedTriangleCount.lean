import Kalai5.Cube3.TriangleMatching

/-! Count each common direction once; every reversed shared edge adds a facet pair. -/

namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.shared_weight_family {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i : Fin 3) :
    ∃ F : PositiveFamily C (Fin (T.triangle.sharedWeight U.triangle i)),
      ∀ k,F.normal k=T.triangle.normal i := by
  classical
  by_cases ho : ∃ j,T.triangle.normal i= -U.triangle.normal j
  · have hs : ∃ j,T.triangle.Shares U.triangle i j := by obtain ⟨j,hj⟩ := ho; exact ⟨j,Or.inr hj⟩
    have hw : T.triangle.sharedWeight U.triangle i=3 := by simp [TriangleData.sharedWeight,ho,hs]
    obtain ⟨j,hj⟩ := ho
    obtain ⟨F,hF⟩ := TriangleFibre.opposed_three τ T U h0 h1 hno i j hj
    let e : Fin (T.triangle.sharedWeight U.triangle i) ≃ Fin 2 ⊕ Unit :=
      Fintype.equivOfCardEq (by simp [hw])
    exact ⟨F.reindex e e.injective,fun k => hF (e k)⟩
  · by_cases hs : ∃ j,T.triangle.Shares U.triangle i j
    · have hw : T.triangle.sharedWeight U.triangle i=2 := by simp [TriangleData.sharedWeight,ho,hs]
      obtain ⟨j,hj | hj⟩ := hs
      · obtain ⟨F,hF⟩ := TriangleFibre.aligned_two τ T U h0 h1 hno i j hj
        let e : Fin (T.triangle.sharedWeight U.triangle i) ≃ Fin 2 := Fintype.equivOfCardEq (by simp [hw])
        exact ⟨F.reindex e e.injective,fun k => hF (e k)⟩
      · exact False.elim (ho ⟨j,hj⟩)
    · have hw : T.triangle.sharedWeight U.triangle i=1 := by simp [TriangleData.sharedWeight,ho,hs]
      obtain ⟨F,hF⟩ := T.one_positive hP hrange i
      let e : Fin (T.triangle.sharedWeight U.triangle i) ≃ Unit := Fintype.equivOfCardEq (by simp [hw])
      exact ⟨F.reindex e e.injective,fun k => hF (e k)⟩

theorem TriangleFibre.shared_direction_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM) :
    18+2*Nat.card {i : Fin 3 // ∃ j,T.triangle.normal i= -U.triangle.normal j} ≤ fvec P 4 := by
  classical
  choose F hF using TriangleFibre.shared_weight_family hP hrange τ T U h0 h1 hno
  let A := PositiveFamily.sigma F
    (fun i j hij a b => by rw [hF,hF]; exact fun h => hij (T.triangle.normal_injective h))
    (fun i j a b => by rw [hF,hF]; exact T.triangle.no_opposite i j)
  let J := {j : Fin 3 // ¬∃ i,T.triangle.Shares U.triangle i j}
  have hU : ∀ j : J,∃ F : PositiveFamily C Unit,∀ k,F.normal k=U.triangle.normal j.val :=
    fun j => U.one_positive hP hrange j.val
  choose G hG using hU
  let B := PositiveFamily.sigma G
    (fun i j hij a b => by
      rw [hG,hG]; exact fun h => hij (Subtype.ext (U.triangle.normal_injective h)))
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
  have hcount := T.triangle.shared_weight_sum U.triangle
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,Fintype.card_unit,
    Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one] at hh
  simp only [Nat.card_eq_fintype_card] at hcount ⊢
  change (∑ i,T.triangle.sharedWeight U.triangle i)+Fintype.card J=
    6+Fintype.card {i : Fin 3 // ∃ j,T.triangle.normal i= -U.triangle.normal j} at hcount
  omega

theorem TriangleFibre.no_opposed_of_eighteen {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM) :
    ∀ i j,T.triangle.normal i ≠ -U.triangle.normal j := by
  classical
  intro i j he
  have hc : 0 < Nat.card {i : Fin 3 // ∃ j,T.triangle.normal i= -U.triangle.normal j} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.2 ⟨⟨i,⟨j,he⟩⟩⟩
  have hb := TriangleFibre.shared_direction_facets hP hrange τ T U h0 h1 hno
  omega

/-- A surviving pair of triangles shares an oriented normal and has no reversed shared normal. -/
def Config.AlignedTriangleDirections (C : Config x) (j k : Fin 4) : Prop :=
  ∀ (T : TriangleFibre C j) (U : TriangleFibre C k),
    (∃ i j,T.triangle.normal i=U.triangle.normal j) ∧
      ∀ i j,T.triangle.normal i ≠ -U.triangle.normal j

theorem Config.aligned_triangle_directions {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.AlignedTriangleDirections (τ 0) (τ 1) := by
  classical
  intro T U
  let σ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hσ0 : σ 0=τ 2 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ1 : σ 1=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ2 : σ 2=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ3 : σ 3=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  let T' : TriangleFibre C (σ 2) := T.reclass hσ2.symm
  let U' : TriangleFibre C (σ 3) := U.reclass hσ3.symm
  have hop : ∀ i j,T.triangle.normal i ≠ -U.triangle.normal j :=
    TriangleFibre.no_opposed_of_eighteen hP hrange hh σ T' U'
      (by rwa [hσ0]) (by rwa [hσ1]) hno
  refine ⟨?_,hop⟩
  by_contra hs
  have he : ∀ i j,T.triangle.normal i ≠ U.triangle.normal j :=
    fun i j hij => hs ⟨i,j,hij⟩
  have hb := T.two_triangles_facets hP hrange τ U h2 h3 he hop
  omega

end Kalai5.Cube3
