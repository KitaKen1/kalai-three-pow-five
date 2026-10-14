import Kalai5.Cube3.TriangleSupportIntervals

/-! A common support reaching the smaller width gives four actual polar vertices. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.aligned_four_of_support (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (i j : Fin 3) (he : T.triangle.normal i=U.triangle.normal j)
    (v w : Fin 8) (hv : C.c v=τ 0) (hw : C.c w=τ 1)
    (hS : min (T.triangle.width i) (U.triangle.width j) ≤
      T.triangle.height i+U.triangle.height j+⟪T.triangle.normal i,C.signedPoint v+C.signedPoint w⟫) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Fin 2),∀ k,H.normal k=T.triangle.normal i := by
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
    have hl := F.two_levels_of_triangles T U h0 h1 hT hU
    obtain ⟨hr,hu,hη⟩ := F.shared_support_identity T U i j ha hT hU v w hv hw h0 h1
    rw [min_eq_left (by linarith : T.triangle.width i ≤ U.triangle.width j)] at hS
    have hmul := mul_le_mul_of_nonneg_left hS ha.le
    have hη' : F.ratio-1 ≤ F.eta := by nlinarith [hr,hη,hmul]
    obtain ⟨G,hG⟩ := F.triangle_upper_four_above U j ha hU hl hno hη'
    exact ⟨G,fun k => (hG k).trans he.symm⟩
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
      change a • T.triangle.normal i=a • U.triangle.normal j
      rw [he]
    have h0' : (C.cls (F.order 0)).card=1 := by change (C.cls (σ 0)).card=1; rwa [hσ0]
    have h1' : (C.cls (F.order 1)).card=1 := by change (C.cls (σ 1)).card=1; rwa [hσ1]
    have hl := F.two_levels_of_triangles U' T' h0' h1' hU hT
    obtain ⟨hr,hu,hη⟩ := F.shared_support_identity U' T' j i ha hU hT v w
      (by change C.c v=σ 0; rwa [hσ0]) (by change C.c w=σ 1; rwa [hσ1]) h0' h1'
    change F.ratio=a*U.triangle.width j/2 at hr
    change F.eta+F.ratio+1=a*(U.triangle.height j+T.triangle.height i+
      ⟪U.triangle.normal j,C.signedPoint v+C.signedPoint w⟫) at hη
    rw [min_eq_right (by linarith : U.triangle.width j ≤ T.triangle.width i),he] at hS
    have hmul := mul_le_mul_of_nonneg_left hS ha.le
    have hη' : F.ratio-1 ≤ F.eta := by nlinarith [hr,hη,hmul]
    exact F.triangle_upper_four_above T' i ha hT hl hno hη'

end Kalai5.Cube3
