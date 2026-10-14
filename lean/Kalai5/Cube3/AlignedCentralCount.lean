import Kalai5.Cube3.AlignedTriangle

/-! A central cap provides four marked vertices even when the drift is negative. -/
namespace Kalai5.Cube3
open Set

lemma doubleSlab_upper_four_central {r η : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hlo : r-1 ≤ η) (hhi : η ≤ 1-r) : Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  have hp := doubleSlab_cap_point hr.le hr1.le (s := 1) (v := η-r) (w := r-1)
    (Or.inl rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inr rfl) (by ring)
  have hq := doubleSlab_cap_point hr.le hr1.le (s := -1) (v := η+r) (w := 1-r)
    (Or.inr rfl) (abs_le.2 ⟨by linarith,by linarith⟩) (Or.inl rfl) (by ring)
  let F := UpperDoubleFamily.swapped _ hp (by norm_num [doublePoint]) (Or.inl rfl)
    (by change 1 ≠ η-r; linarith) (doubleSlab_cap_upper hp.1 rfl)
  let G := UpperDoubleFamily.swapped _ hq (by norm_num [doublePoint]) (Or.inr rfl)
    (by change -1 ≠ η+r; linarith) (doubleSlab_cap_upper hq.1 rfl)
  refine ⟨F.sum G ?_⟩
  intro i j he
  have hh := congrArg (fun p : SlabPoint => p.1 2) he
  rw [UpperDoubleFamily.swapped_third,UpperDoubleFamily.swapped_third] at hh
  change r-1=1-r at hh; linarith

theorem doubleSlab_upper_four_above {r η : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    (hη : r-1 ≤ η) (h0 : ¬(r=1 ∧ η=0)) (h2 : ¬(r=1 ∧ η=2)) :
    Nonempty (UpperDoubleFamily r η (Fin 2 ⊕ Fin 2)) := by
  by_cases hpos : 0 ≤ η
  · exact doubleSlab_upper_four hr hr1 hpos h0 h2
  · exact doubleSlab_upper_four_central hr (by linarith) hη (by linarith)

variable {x : Fin 8 → E5} {C : Config x}

theorem TwoWidthSlice.triangle_upper_four_above (F : TwoWidthSlice C)
    (T : TriangleFibre C (F.order 3)) (i : Fin 3) {a : ℝ} (ha : 0 < a)
    (hn : F.normal=a • T.triangle.normal i) (hlevels : F.intervals.TwoLevels)
    (hno : ¬ C.ExtraPM) (hη : F.ratio-1 ≤ F.eta) :
    ∃ H : PositiveFamily C (Fin 2 ⊕ Fin 2),∀ k,H.normal k=T.triangle.normal i := by
  obtain ⟨h0,h2,_⟩ := F.eta_not_exceptional hlevels hno
  obtain ⟨G⟩ := doubleSlab_upper_four_above F.ratio_pos F.ratio_le hη h0 h2
  exact F.triangle_upper_family G T i ha hn

end Kalai5.Cube3
