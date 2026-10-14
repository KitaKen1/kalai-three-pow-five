import Kalai5.Cube3.PolarGeometry

/-! Arbitrary finite sets of saturated signed vertex evaluations give compact extreme faces. -/

namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

def activeFace (T : Finset (Fin 8)) (s : Fin 8 → ℝ) : Set E5 :=
  {p | p ∈ C.polarModel ∧ ∀ v ∈ T,C.value p v=s v}

lemma activeFace_compact {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (T : Finset (Fin 8)) (s : Fin 8 → ℝ) :
    IsCompact (C.activeFace T s) := by
  apply (C.polarModel_compact hP hrange).inter_right
  change IsClosed {p | ∀ v ∈ T,C.value p v=s v}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro _
  exact isClosed_eq (C.value_continuous v) continuous_const

lemma activeFace_extreme (T : Finset (Fin 8)) (s : Fin 8 → ℝ)
    (hs : ∀ v ∈ T,s v=1 ∨ s v= -1) : IsExtreme ℝ C.polarModel (C.activeFace T s) := by
  refine ⟨fun _ hp => hp.1,?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp,fun v hv => ?_⟩
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  apply (endpoint_combination (hp v) (hq v) ha hb hab _ (hs v hv)).1
  have hh := congrFun (congrArg C.evaluation he) v
  simpa [map_add,map_smul,evaluation,hz.2 v hv] using hh

theorem activeFace_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (T : Finset (Fin 8)) (s : Fin 8 → ℝ)
    (hs : ∀ v ∈ T,s v=1 ∨ s v= -1) (n : E 2)
    {q : E5} (hq : q ∈ C.activeFace T s) (hpos : 0 < ⟪n,planar q⟫) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,(∀ v ∈ T,C.value p v=s v) ∧ 0 < ⟪n,planar p⟫ := by
  let L : E5 →L[ℝ] ℝ := (innerSL ℝ n).comp planarLinear.toContinuousLinearMap
  obtain ⟨p,hp,hmax⟩ := compact_extreme_ge (C.activeFace_compact hP hrange T s) L hq
  exact ⟨p,(C.activeFace_extreme T s hs).extremePoints_subset_extremePoints hp,
    hp.1.2,lt_of_lt_of_le hpos hmax⟩

lemma equal_value_orthogonal {p : E5} {v w : Fin 8} (hclass : C.c v=C.c w)
    (hvalue : C.value p v=C.value p w) : ⟪planar p,C.k w-C.k v⟫=0 := by
  simp only [value,hclass] at hvalue
  rw [inner_sub_right]
  linarith

end Config
end Kalai5.Cube3
