import Kalai5.Cube3.PolarGeometry

/-! Six central full vertices shared by every cube-class polar. -/

namespace Kalai5.Cube3

noncomputable def centralVertex (i : Fin 6) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    (![![1,1,1,0,0], ![-1,-1,-1,0,0], ![1,1,-1,0,0],
       ![-1,-1,1,0,0], ![1,-1,1,0,0], ![-1,1,-1,0,0]] i)

lemma centralVertex_planar (i : Fin 6) : planar (centralVertex i) = 0 := by
  ext j; fin_cases i <;> fin_cases j <;> norm_num [centralVertex,planar] <;> dsimp <;> norm_num

lemma centralVertex_signs (i : Fin 6) (j : Fin 4) :
    offsets (centralVertex i) j = 1 ∨ offsets (centralVertex i) j = -1 := by
  fin_cases i <;> fin_cases j <;> norm_num [centralVertex,offsets] <;> dsimp <;> norm_num

lemma centralVertex_injective : Function.Injective centralVertex := by
  intro i j h
  have h0 := congrArg (fun p : E5 => p 0) h
  have h1 := congrArg (fun p : E5 => p 1) h
  have h2 := congrArg (fun p : E5 => p 2) h
  fin_cases i <;> fin_cases j <;> norm_num [centralVertex] at h0 <;>
    norm_num [centralVertex] at h1 <;> norm_num [centralVertex] at h2 <;> rfl

lemma Config.centralVertex_extreme {x : Fin 8 → E5} (C : Config x) (i : Fin 6) :
    centralVertex i ∈ C.polarModel.extremePoints ℝ := by
  apply C.polarModel_extreme_of_signs
  intro v
  simp only [Config.value,centralVertex_planar,inner_zero_left,add_zero]
  exact centralVertex_signs i (C.c v)

end Kalai5.Cube3
