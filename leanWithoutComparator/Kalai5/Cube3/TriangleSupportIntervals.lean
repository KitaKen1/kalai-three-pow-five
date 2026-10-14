import Kalai5.Cube3.AlignedCentralCount

/-! Relate the normalized drift to the two triangle supports and actual widths. -/
namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

namespace ProjectionIntervals
variable {n : E 2} (I : ProjectionIntervals C n)

lemma triangle_endpoints {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : n=a • T.triangle.normal i) :
    ⟪n,C.signedPoint (I.hi j)⟫=a*T.triangle.height i ∧
      ⟪n,C.signedPoint (I.lo j)⟫=a*(T.triangle.height i-T.triangle.width i) := by
  have hscale (v : Fin 8) : ⟪n,C.signedPoint v⟫=a*⟪T.triangle.normal i,C.signedPoint v⟫ :=
    (congrArg (fun b : E 2 => ⟪b,C.signedPoint v⟫) hn).trans (real_inner_smul_left _ _ _)
  constructor
  · obtain ⟨k,l,hkl,hik,hil⟩ := TriangleFibre.edge_points i
    rw [← I.triangle_upper_eq T i ha hn k hik,hscale,T.evaluation,if_neg hik,sub_zero]
  · apply le_antisymm
    · have hh := I.lower (T.vertex i)
      rw [T.cls,hscale (T.vertex i),T.evaluation,if_pos rfl] at hh
      exact hh
    · obtain ⟨k,hk⟩ := T.covers (I.lo j) (I.clo j)
      rw [← hk,hscale,T.evaluation]
      by_cases he : i=k
      · rw [if_pos he]
      · rw [if_neg he,sub_zero]
        nlinarith [T.triangle.width_positive i]

lemma triangle_radius {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : n=a • T.triangle.normal i) :
    I.radius j=a*T.triangle.width i/2 := by
  obtain ⟨hi,lo⟩ := I.triangle_endpoints T i ha hn
  simp only [radius,axis,inner_smul_right,inner_sub_right]
  rw [hi,lo]; ring

lemma triangle_center {j : Fin 4} (T : TriangleFibre C j) (i : Fin 3)
    {a : ℝ} (ha : 0 < a) (hn : n=a • T.triangle.normal i) :
    ⟪n,I.center j⟫=a*(T.triangle.height i-T.triangle.width i/2) := by
  obtain ⟨hi,lo⟩ := I.triangle_endpoints T i ha hn
  simp only [center,inner_smul_right,inner_add_right]
  rw [hi,lo]; ring

lemma singleton_center {j : Fin 4} (h1 : (C.cls j).card=1) (v : Fin 8) (hv : C.c v=j) :
    I.center j=C.signedPoint v := by
  have hlo := C.eq_of_singleton_class h1 (I.clo j) hv
  have hhi := C.eq_of_singleton_class h1 (I.chi j) hv
  ext k
  simp [center,hlo,hhi]
  ring

end ProjectionIntervals

theorem TwoWidthSlice.shared_support_identity (F : TwoWidthSlice C)
    (T : TriangleFibre C (F.order 2)) (U : TriangleFibre C (F.order 3))
    (i j : Fin 3) {a : ℝ} (ha : 0 < a)
    (hT : F.normal=a • T.triangle.normal i) (hU : F.normal=a • U.triangle.normal j)
    (v w : Fin 8) (hv : C.c v=F.order 0) (hw : C.c w=F.order 1)
    (h0 : (C.cls (F.order 0)).card=1) (h1 : (C.cls (F.order 1)).card=1) :
    F.ratio=a*T.triangle.width i/2 ∧ 1=a*U.triangle.width j/2 ∧
      F.eta+F.ratio+1=a*(T.triangle.height i+U.triangle.height j+
        ⟪T.triangle.normal i,C.signedPoint v+C.signedPoint w⟫) := by
  have hr := F.intervals.triangle_radius T i ha hT
  have hu := F.intervals.triangle_radius U j ha hU
  rw [F.unit] at hu
  refine ⟨hr,hu,?_⟩
  have hc0 : ⟪F.normal,C.signedPoint v⟫=a*⟪T.triangle.normal i,C.signedPoint v⟫ := by rw [hT,real_inner_smul_left]
  have hc1 : ⟪F.normal,C.signedPoint w⟫=a*⟪T.triangle.normal i,C.signedPoint w⟫ := by rw [hT,real_inner_smul_left]
  change (∑ k,⟪F.normal,F.intervals.center k⟫)+F.ratio+1=_
  rw [← Equiv.sum_comp F.order (fun k => ⟪F.normal,F.intervals.center k⟫),Fin.sum_univ_four,
    F.intervals.singleton_center h0 v hv,F.intervals.singleton_center h1 w hw,
    hc0,hc1,F.intervals.triangle_center T i ha hT,F.intervals.triangle_center U j ha hU,
    inner_add_right]
  change F.ratio=a*T.triangle.width i/2 at hr
  nlinarith [hr,hu]

end Kalai5.Cube3
