import Kalai5.Cube3.TriangleNormalizedSupport

/-! Two bounded common supports force positive support at the third triangle edge. -/
namespace Kalai5.Cube3.TriangleData
local notation "⟪" x ", " y "⟫" => inner ℝ x y

theorem third_support_positive_at (T U : TriangleData) (q : E 2)
    (a b c i j : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : T.normal a=U.normal i) (hb : T.normal b=U.normal j)
    (hSa : T.height a+U.height i+⟪T.normal a,q⟫ < U.width i)
    (hSb : T.height b+U.height j+⟪T.normal b,q⟫ < T.width b) :
    0 < T.height c+⟪T.normal c,U.point i+q⟫ := by
  have hij : i ≠ j := by
    intro he; apply hab; apply T.normal_injective; rw [ha,hb,he]
  have hia : T.height a+⟪T.normal a,U.point i+q⟫=
      T.height a+U.height i+⟪T.normal a,q⟫-U.width i := by
    rw [inner_add_right,ha,U.normal_eval,if_pos rfl]; ring
  have hib : T.height b+⟪T.normal b,U.point i+q⟫=
      T.height b+U.height j+⟪T.normal b,q⟫ := by
    rw [inner_add_right,hb,U.normal_eval,if_neg (Ne.symm hij),sub_zero]; ring
  have hA : (T.height a+⟪T.normal a,U.point i+q⟫)/T.width a < 0 := by
    rw [hia]
    exact div_neg_of_neg_of_pos (by linarith) (T.width_positive a)
  have hB : (T.height b+⟪T.normal b,U.point i+q⟫)/T.width b < 1 := by
    rw [hib]
    exact (div_lt_one (T.width_positive b)).2 hSb
  have hsum := T.normalized_support_three (U.point i+q) a b c hab hac hbc
  by_contra hnot
  have hc : (T.height c+⟪T.normal c,U.point i+q⟫)/T.width c ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hnot) (T.width_positive c).le
  linarith

theorem third_support_positive (T U : TriangleData) (q : E 2)
    (a b c i j : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : T.normal a=U.normal i) (hb : T.normal b=U.normal j)
    (hSa : T.height a+U.height i+⟪T.normal a,q⟫ < min (T.width a) (U.width i))
    (hSb : T.height b+U.height j+⟪T.normal b,q⟫ < min (T.width b) (U.width j)) :
    ∃ k : Fin 3,0 < T.height c+⟪T.normal c,U.point k+q⟫ := by
  exact ⟨i,T.third_support_positive_at U q a b c i j hab hac hbc ha hb
    (hSa.trans_le (min_le_right _ _)) (hSb.trans_le (min_le_left _ _))⟩

end Kalai5.Cube3.TriangleData
