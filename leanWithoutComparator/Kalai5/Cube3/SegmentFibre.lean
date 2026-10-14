import Kalai5.Cube3.TriangleFibre
import Kalai5.Cube3.TwoWidthConstruction

/-! A two-point fibre without assumptions on the other three classes. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

structure SegmentFibre (j : Fin 4) where
  first : Fin 8
  second : Fin 8
  first_class : C.c first=j
  second_class : C.c second=j
  distinct : first ≠ second
  covers : ∀ v,C.c v=j → v=first ∨ v=second

theorem Config.segment_fibre {j : Fin 4} (h2 : (C.cls j).card=2) : Nonempty (SegmentFibre C j) := by
  classical
  obtain ⟨v,w,hvw,hcls⟩ := Finset.card_eq_two.1 h2
  have hv : C.c v=j := by
    have h : v ∈ C.cls j := by rw [hcls]; simp
    simpa [Config.cls] using h
  have hw : C.c w=j := by
    have h : w ∈ C.cls j := by rw [hcls]; simp
    simpa [Config.cls] using h
  refine ⟨⟨v,w,hv,hw,hvw,?_⟩⟩
  intro z hz
  have hh : z ∈ C.cls j := by simp [Config.cls,hz]
  rw [hcls] at hh
  simpa using hh

namespace SegmentFibre
variable {C} {j : Fin 4} (S : SegmentFibre C j)

def reclass {k : Fin 4} (h : j=k) : SegmentFibre C k where
  first := S.first
  second := S.second
  first_class := S.first_class.trans h
  second_class := S.second_class.trans h
  distinct := S.distinct
  covers v hv := S.covers v (hv.trans h.symm)

noncomputable def direction : E 2 := C.signedPoint S.second-C.signedPoint S.first

lemma direction_ne_zero : S.direction ≠ 0 := by
  intro h
  exact S.distinct (C.signedPoint_inj (S.first_class.trans S.second_class.symm) (sub_eq_zero.1 h).symm)

lemma constant {n : E 2} (hn : ⟪n,S.direction⟫=0) (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint S.first⟫ := by
  rcases S.covers v hv with rfl | rfl
  · rfl
  · rw [direction,inner_sub_right] at hn; exact sub_eq_zero.1 hn

include S in
lemma two_levels {n : E 2} (I : ProjectionIntervals C n) (v : Fin 8) (hv : C.c v=j) :
    ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.lo j)⟫ ∨
      ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (I.hi j)⟫ := by
  apply I.two_levels_of_values (β := ⟪n,C.signedPoint S.first⟫)
    (γ := ⟪n,C.signedPoint S.second⟫) _ v hv
  intro w hw
  rcases S.covers w hw with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

lemma radius_zero {n : E 2} (I : ProjectionIntervals C n) (hn : ⟪n,S.direction⟫=0) :
    I.radius j=0 := by
  simp only [ProjectionIntervals.radius,ProjectionIntervals.axis,inner_smul_right,inner_sub_right]
  rw [S.constant hn _ (I.chi j),S.constant hn _ (I.clo j),sub_self,mul_zero]

lemma radius_positive {n : E 2} (I : ProjectionIntervals C n) (hn : ⟪n,S.direction⟫ ≠ 0) :
    0 < I.radius j := by
  by_contra hh
  have hz : I.radius j=0 := le_antisymm (le_of_not_gt hh) (I.radius_nonneg j)
  have hfirst := I.projected_bound S.first
  have hsecond := I.projected_bound S.second
  rw [S.first_class,hz] at hfirst
  rw [S.second_class,hz] at hsecond
  have hf := abs_eq_zero.1 (le_antisymm hfirst (abs_nonneg _))
  have hs := abs_eq_zero.1 (le_antisymm hsecond (abs_nonneg _))
  apply hn
  rw [direction,inner_sub_right]
  rw [inner_sub_right] at hf hs
  linarith

end SegmentFibre
end Kalai5.Cube3
