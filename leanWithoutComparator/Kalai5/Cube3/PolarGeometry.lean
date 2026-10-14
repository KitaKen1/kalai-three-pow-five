import Kalai5.Cube3.PolarModel
import Kalai5.Cube3.CubeSections
import Kalai5.Cube3.Relabel
import Mathlib.Analysis.Convex.KreinMilman

/-! Compact extreme faces of the actual polar model. -/

namespace Kalai5.Cube3

open Set FullPrism

-- Register the existing numeral-coordinate equalities on the pinned FC Mathlib.
-- Each is proved by definitional equality; no new mathematical assumption is used.
attribute [simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four

noncomputable def pack (a : Fin 4 → ℝ) (b : E 2) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm ![a 0,a 1,a 2,b 0,b 1]

lemma offsets_pack {a : Fin 4 → ℝ} (ha : Balanced a) (b : E 2) :
    offsets (pack a b) = a := by
  funext j
  change a 0 + a 3 = a 1 + a 2 at ha
  fin_cases j <;> simp [pack,offsets] <;> (try dsimp) <;> linarith

lemma planar_pack (a : Fin 4 → ℝ) (b : E 2) : planar (pack a b) = b := by
  ext i; fin_cases i <;> simp [pack,planar] <;> rfl

lemma planar_add_smul (p q : E5) (t : ℝ) :
    planar (p + t • q) = planar p + t • planar q := by
  ext i; fin_cases i <;> simp [planar]

noncomputable def planarLinear : E5 →ₗ[ℝ] E 2 where
  toFun := planar
  map_add' := by intro p q; ext i; fin_cases i <;> simp [planar]
  map_smul' := by intro t p; ext i; fin_cases i <;> simp [planar]

lemma compact_extreme_ge {d : ℕ} {S : Set (E d)} (hc : IsCompact S)
    (L : E d →L[ℝ] ℝ) {p : E d} (hp : p ∈ S) :
    ∃ q ∈ S.extremePoints ℝ, L p ≤ L q := by
  obtain ⟨z,hz,hmax⟩ := hc.exists_isMaxOn ⟨p,hp⟩ L.continuous.continuousOn
  have hex : IsExposed ℝ S {q ∈ S | ∀ w ∈ S, L w ≤ L q} := fun _ => ⟨L,rfl⟩
  obtain ⟨q,hq⟩ := (hex.isCompact hc).extremePoints_nonempty ⟨z,hz,hmax⟩
  exact ⟨q,hex.isExtreme.extremePoints_subset_extremePoints hq,hq.1.2 p hp⟩

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

lemma value_add_smul (p q : E5) (t : ℝ) (v : Fin 8) :
    C.value (p + t • q) v = C.value p v + t * C.value q v := by
  have h := congrFun (C.evaluation.map_add p (t • q)) v
  simpa [evaluation,LinearMap.map_smul] using h

lemma value_continuous (v : Fin 8) : Continuous (fun p => C.value p v) := by
  exact (continuous_apply v).comp C.evaluation.continuous_of_finiteDimensional

lemma polarModel_compact {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) : IsCompact C.polarModel := by
  obtain ⟨e,he⟩ := C.exists_polar_equiv
  obtain ⟨V,hV⟩ := hP.polytope
  have hconv : convexHull ℝ (range (pm16 x)) = P := by
    rw [hrange,hV]; exact convexHull_extremePoints_eq V
  have hm : C.polarModel = e.symm '' polarSet P := by
    rw [← hconv, ← C.polarModel_image he]
    ext p
    constructor
    · intro hp
      exact ⟨e p,⟨p,hp,rfl⟩,e.symm_apply_apply p⟩
    · rintro ⟨q,⟨r,hr,rfl⟩,heq⟩
      rw [e.symm_apply_apply] at heq
      exact heq ▸ hr
  rw [hm]
  obtain ⟨W,hW⟩ := hP.polar.polytope
  rw [hW]
  exact (W.finite_toSet.isCompact_convexHull ℝ).image e.symm.continuous_of_finiteDimensional

/-- Saturating one whole class at the same sign gives an extreme subset. -/
def classFace (j : Fin 4) (s : ℝ) : Set E5 :=
  {p | p ∈ C.polarModel ∧ ∀ v, C.c v = j → C.value p v = s}

lemma classFace_compact {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (j : Fin 4) (s : ℝ) :
    IsCompact (C.classFace j s) := by
  apply (C.polarModel_compact hP hrange).inter_right
  change IsClosed {p | ∀ v, C.c v = j → C.value p v = s}
  simp only [setOf_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_iInter
  intro _
  exact isClosed_eq (C.value_continuous v) continuous_const

lemma classFace_extreme (j : Fin 4) {s : ℝ} (hs : s = 1 ∨ s = -1) :
    IsExtreme ℝ C.polarModel (C.classFace j s) := by
  refine ⟨fun _ hp => hp.1, ?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp,fun v hv => ?_⟩
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have heval : a * C.value p v + b * C.value q v = s := by
    have h := congrFun (congrArg C.evaluation he) v
    simpa [map_add,map_smul,evaluation,hz.2 v hv] using h
  exact (endpoint_combination (hp v) (hq v) ha hb hab heval hs).1

lemma polarModel_extreme_of_signs {p : E5} (hp : ∀ v, C.value p v = 1 ∨ C.value p v = -1) :
    p ∈ C.polarModel.extremePoints ℝ := by
  have hmem : p ∈ C.polarModel := by
    intro v; rcases hp v with h | h <;> rw [h] <;> norm_num
  refine ⟨hmem,?_⟩
  intro q hq r hr hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  apply C.evaluation_injective
  funext v
  apply (endpoint_combination (hq v) (hr v) ha hb hab _ (hp v)).1
  have h := congrFun (congrArg C.evaluation he) v
  simpa [map_add,map_smul,evaluation] using h

end Config
end Kalai5.Cube3
