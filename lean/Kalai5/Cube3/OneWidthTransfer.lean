import Kalai5.Cube3.OneWidthSlice
import Kalai5.Cube3.TwoWidthTransfer

/-! Lift one-width slab vertices using a saturated segment. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

namespace OneWidthSlice
variable (F : OneWidthSlice C)

lemma plane_of_orthogonal {d : E 2} (hd : d ≠ 0) (hnd : ⟪F.normal,d⟫=0)
    {p : E5} (hpd : ⟪planar p,d⟫=0) : planar p=(F.project p).2 • F.normal := by
  have hunit : ⟪F.normal,F.intervals.axis (F.order 3)⟫=1 := F.unit
  have hdet := det_ne_of_annihilator hd hnd hunit
  apply sub_eq_zero.1
  apply orthogonal_two_eq_zero hdet
  · rw [inner_sub_left,real_inner_smul_left,hnd,hpd,mul_zero,sub_self]
  · rw [inner_sub_left,real_inner_smul_left,hunit,mul_one,F.project_last,sub_self]

theorem embed_extreme {z : SlabPoint} (hz : z ∈ (tripleSlab F.eta).extremePoints ℝ)
    (ht : z.2 ≠ 0) {v w : Fin 8} (hc : C.c v=C.c w)
    (hneq : C.signedPoint w ≠ C.signedPoint v) {s : ℝ} (hs : s=1 ∨ s= -1)
    (hv : C.signedValue (F.embed z) v=s) (hw : C.signedValue (F.embed z) w=s) :
    F.embed z ∈ C.polarModel.extremePoints ℝ := by
  have hnd : ⟪F.normal,C.signedPoint w-C.signedPoint v⟫=0 := by
    have hh := C.equal_signedValue_orthogonal hc (hv.trans hw.symm)
    rw [F.planar_embed,real_inner_smul_left] at hh
    exact (mul_eq_zero.1 hh).resolve_left ht
  refine ⟨(F.mem_embed z).2 hz.1,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hpv := C.signed_endpoint_combination hp hq ha hb hab he v hs hv
  have hpw := C.signed_endpoint_combination hp hq ha hb hab he w hs hw
  have hpplane := F.plane_of_orthogonal (sub_ne_zero.2 hneq) hnd
    (C.equal_signedValue_orthogonal hc (hpv.1.trans hpw.1.symm))
  have hqplane := F.plane_of_orthogonal (sub_ne_zero.2 hneq) hnd
    (C.equal_signedValue_orthogonal hc (hpv.2.trans hpw.2.symm))
  have hpp : F.project p ∈ tripleSlab F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hpplane]; exact hp)
  have hqp : F.project q ∈ tripleSlab F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hqplane]; exact hq)
  have hproj : F.project p=z := hz.2 hpp hqp ⟨a,b,ha,hb,hab,by
    have hh := congrArg F.project he
    simpa only [map_add,map_smul,F.project_embed] using hh⟩
  calc p = F.embed (F.project p) := (F.embed_project hpplane).symm
       _ = F.embed z := congrArg F.embed hproj

lemma signed_eq_hi (z : SlabPoint) {j : Fin 4} {v : Fin 8} (hv : C.c v=j)
    (hproj : ⟪F.normal,C.signedPoint v⟫=⟪F.normal,C.signedPoint (F.intervals.hi j)⟫) :
    C.signedValue (F.embed z) v=F.coords z j+z.2*F.intervals.radius j := by
  have he : C.signedValue (F.embed z) v=C.signedValue (F.embed z) (F.intervals.hi j) := by
    rw [Config.signedValue_eq,Config.signedValue_eq,hv,F.intervals.chi,F.planar_embed]
    simp only [real_inner_smul_left,hproj]
  rw [he,F.intervals.signed_hi,F.centerEval_embed,F.planar_embed,real_inner_smul_left]
  rfl

lemma signed_eq_lo (z : SlabPoint) {j : Fin 4} {v : Fin 8} (hv : C.c v=j)
    (hproj : ⟪F.normal,C.signedPoint v⟫=⟪F.normal,C.signedPoint (F.intervals.lo j)⟫) :
    C.signedValue (F.embed z) v=F.coords z j-z.2*F.intervals.radius j := by
  have he : C.signedValue (F.embed z) v=C.signedValue (F.embed z) (F.intervals.lo j) := by
    rw [Config.signedValue_eq,Config.signedValue_eq,hv,F.intervals.clo,F.planar_embed]
    simp only [real_inner_smul_left,hproj]
  rw [he,F.intervals.signed_lo,F.centerEval_embed,F.planar_embed,real_inner_smul_left]
  rfl

lemma zero_value (z : SlabPoint) (i : Fin 3) (v : Fin 8) (hv : C.c v=F.order i.castSucc) :
    C.signedValue (F.embed z) v=z.1 i := by
  have hrad : F.intervals.radius (F.order i.castSucc)=0 := F.zero i
  have hh := F.intervals.projected_bound v
  rw [hv,hrad] at hh
  have he := abs_eq_zero.1 (le_antisymm hh (abs_nonneg _))
  rw [F.intervals.value_centered,F.centerEval_embed,hv,F.coords_order,F.planar_embed,
    real_inner_smul_left,he,mul_zero,add_zero]
  fin_cases i <;> rfl

end OneWidthSlice
end Kalai5.Cube3
