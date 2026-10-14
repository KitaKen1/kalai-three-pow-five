import Kalai5.Cube3.AlignedSupportBonus
import Kalai5.Cube3.UnequalAlignedCount
import Kalai5.Cube3.SharedBonusCount

/-! A nonnegative shared support with unequal widths forces an extra polar vertex. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.aligned_three_of_nonnegative_support (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1)
    (i j : Fin 3) (he : T.triangle.normal i=U.triangle.normal j)
    (hne : T.triangle.width i ≠ U.triangle.width j)
    (v w : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1)
    (hS : 0 ≤ T.triangle.height i+U.triangle.height j+
      ⟪T.triangle.normal i,C.signedPoint v+C.signedPoint w⟫) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Unit),∀ k,H.normal k=T.triangle.normal i := by
  classical
  have hn : T.triangle.normal i ≠ 0 := by
    intro hz; have hu := T.triangle.normal_unit i; rw [hz,norm_zero] at hu; norm_num at hu
  obtain ⟨I⟩ := C.projection_intervals (T.triangle.normal i)
  have hz0 := I.radius_zero_singleton h0
  have hz1 := I.radius_zero_singleton h1
  have hp2 := I.radius_positive (show 3 ≤ (C.cls (τ 2)).card by rw [T.card_class]) hn
  have hp3 := I.radius_positive (show 3 ≤ (C.cls (τ 3)).card by rw [U.card_class]) hn
  have hrT := I.triangle_radius T i (by norm_num : (0 : ℝ)<1) (by simp)
  have hrU := I.triangle_radius U j (by norm_num : (0 : ℝ)<1) (by simpa using he)
  simp only [one_mul] at hrT hrU
  by_cases hle : I.radius (τ 2)≤I.radius (τ 3)
  · let F := I.twoWidth τ hz0 hz1 hp2 hp3 hle
    let a := (I.radius (τ 3))⁻¹
    have ha : 0 < a := inv_pos.2 hp3
    have hT : F.normal=a • T.triangle.normal i := rfl
    have hU : F.normal=a • U.triangle.normal j := by rw [hT,he]
    obtain ⟨hr,hu,hη⟩ := F.shared_support_identity T U i j ha hT hU v w hv hw h0 h1
    have hwidth : T.triangle.width i < U.triangle.width j := lt_of_le_of_ne (by linarith) hne
    have hr' : F.ratio < 1 := by nlinarith [mul_pos ha (sub_pos.2 hwidth)]
    have hη' : -1-F.ratio ≤ F.eta := by nlinarith [mul_nonneg ha.le hS]
    obtain ⟨A⟩ := F.triangle_upper_edge T i ha hT
    obtain ⟨B⟩ := F.triangle_upper_edge U j ha hU
    exact F.aligned_three_unequal A B hr' hη' (T.triangle.normal_unit i) ha hT
  · let σ : Equiv.Perm (Fin 4) := (Equiv.swap 2 3).trans τ
    have hσ0 : σ 0=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ1 : σ 1=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
    have hσ2 : σ 2=τ 3 := by simp [σ]
    have hσ3 : σ 3=τ 2 := by simp [σ]
    have hp3' : 0 < I.radius (σ 3) := by rwa [hσ3]
    let F := I.twoWidth σ (by rwa [hσ0]) (by rwa [hσ1]) (by rwa [hσ2]) hp3'
      (by rw [hσ2,hσ3]; exact (lt_of_not_ge hle).le)
    let a := (I.radius (σ 3))⁻¹
    have ha : 0 < a := inv_pos.2 hp3'
    let T' : TriangleFibre C (σ 3) := T.reclass hσ3.symm
    let U' : TriangleFibre C (σ 2) := U.reclass hσ2.symm
    have hT : F.normal=a • T'.triangle.normal i := rfl
    have hU : F.normal=a • U'.triangle.normal j := by
      change a • T.triangle.normal i=a • U.triangle.normal j; rw [he]
    have h0' : (C.cls (F.order 0)).card=1 := by change (C.cls (σ 0)).card=1; rwa [hσ0]
    have h1' : (C.cls (F.order 1)).card=1 := by change (C.cls (σ 1)).card=1; rwa [hσ1]
    obtain ⟨hr,hu,hη⟩ := F.shared_support_identity U' T' j i ha hU hT v w
      (by change C.c v=σ 0; rwa [hσ0]) (by change C.c w=σ 1; rwa [hσ1]) h0' h1'
    change F.ratio=a*U.triangle.width j/2 at hr
    change 1=a*T.triangle.width i/2 at hu
    change F.eta+F.ratio+1=a*(U.triangle.height j+T.triangle.height i+
      ⟪U.triangle.normal j,C.signedPoint v+C.signedPoint w⟫) at hη
    rw [he] at hS
    have hwidth : U.triangle.width j < T.triangle.width i := by linarith
    have hr' : F.ratio < 1 := by nlinarith [mul_pos ha (sub_pos.2 hwidth)]
    have hη' : -1-F.ratio ≤ F.eta := by nlinarith [mul_nonneg ha.le hS]
    obtain ⟨A⟩ := F.triangle_upper_edge U' j ha hU
    obtain ⟨B⟩ := F.triangle_upper_edge T' i ha hT
    exact F.aligned_three_unequal A B hr' hη' (T.triangle.normal_unit i) ha hT

theorem TriangleFibre.unequal_support_neg {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i j : Fin 3) (he : T.triangle.normal i=U.triangle.normal j)
    (hne : T.triangle.width i ≠ U.triangle.width j)
    (v w : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1) :
    T.triangle.height i+U.triangle.height j+⟪T.triangle.normal i,C.signedPoint v+C.signedPoint w⟫ < 0 := by
  classical
  by_contra hS
  obtain ⟨F,hF⟩ := TriangleFibre.aligned_three_of_nonnegative_support τ T U h0 h1 i j he hne v w hv hw (le_of_not_gt hS)
  have hop := TriangleFibre.no_opposed_of_eighteen hP hrange hh τ T U h0 h1 hno
  have hnoopp : ¬∃ j,T.triangle.normal i= -U.triangle.normal j := by rintro ⟨j,hj⟩; exact hop i j hj
  have hs : ∃ j,T.triangle.Shares U.triangle i j := ⟨j,Or.inl he⟩
  have hweight : T.triangle.sharedWeight U.triangle i=2 := by simp [TriangleData.sharedWeight,hs,hnoopp]
  let e : Fin (T.triangle.sharedWeight U.triangle i+1) ≃ Fin 2 ⊕ Unit := Fintype.equivOfCardEq (by simp [hweight])
  exact TriangleFibre.no_matching_bonus hP hrange hh τ T U h0 h1 hno i
    (F.reindex e e.injective) (fun k => hF (e k))

end Kalai5.Cube3
