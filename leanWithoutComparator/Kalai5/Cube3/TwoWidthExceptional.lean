import Kalai5.Cube3.TwoWidthConstruction

/-! For two-level projections the equal-width transition points create an extra full normal. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

namespace TwoWidthSlice
variable (F : TwoWidthSlice C)

lemma two_levels_of_triangles (T : TriangleFibre C (F.order 2)) (U : TriangleFibre C (F.order 3))
    (h0 : (C.cls (F.order 0)).card=1) (h1 : (C.cls (F.order 1)).card=1)
    {i j : Fin 3} {a b : ℝ} (hnT : F.normal=a • T.triangle.normal i)
    (hnU : F.normal=b • U.triangle.normal j) : F.intervals.TwoLevels := by
  intro v
  obtain ⟨k,hk⟩ := F.order.surjective (C.c v)
  have hcv : C.c v=F.order k := hk.symm
  rw [hcv]
  fin_cases k
  · exact F.intervals.singleton_two_levels h0 v hcv
  · exact F.intervals.singleton_two_levels h1 v hcv
  · exact F.intervals.triangle_two_levels T i hnT v hcv
  · exact F.intervals.triangle_two_levels U j hnU v hcv

lemma extra_of_pair (hlevels : F.intervals.TwoLevels)
    {s v : ℝ} (hs : s=1 ∨ s= -1) (hv : v=1 ∨ v= -1)
    (he : F.eta=s+v) (hr : F.ratio=1) : C.ExtraPM := by
  let z := doublePoint s v 0 1
  let p := F.embed z
  have hp : planar p=F.normal := by rw [F.planar_embed]; simp [z,doublePoint]
  have habs (j : Fin 4) : |F.coords z j-F.intervals.radius j|=1 ∧
      |F.coords z j+F.intervals.radius j|=1 := by
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [F.coords_order]
    have h0 : F.intervals.radius (F.order 0)=0 := F.zero 0
    have h1 : F.intervals.radius (F.order 1)=0 := F.zero 1
    have h2 : F.intervals.radius (F.order 2)=1 := hr
    have h3 : F.intervals.radius (F.order 3)=1 := F.unit
    fin_cases j
    · change |s-F.intervals.radius (F.order 0)|=1 ∧ |s+F.intervals.radius (F.order 0)|=1
      rw [h0]; rcases hs with rfl | rfl <;> norm_num
    · change |v-F.intervals.radius (F.order 1)|=1 ∧ |v+F.intervals.radius (F.order 1)|=1
      rw [h1]; rcases hv with rfl | rfl <;> norm_num
    · change |0-F.intervals.radius (F.order 2)|=1 ∧ |0+F.intervals.radius (F.order 2)|=1
      rw [h2]; norm_num
    · change |F.eta*1-∑ i,cycle3 s v 0 0 i-F.intervals.radius (F.order 3)|=1 ∧
        |F.eta*1-∑ i,cycle3 s v 0 0 i+F.intervals.radius (F.order 3)|=1
      rw [cycle3_sum,he,h3]; norm_num
  have hvalue (w : Fin 8) : |C.value p w|=1 := by
    rw [← C.signedValue_abs]
    rcases hlevels w with hw | hw
    · rw [F.signed_eq_lo z rfl hw]
      change |F.coords z (C.c w)-1*F.intervals.radius (C.c w)|=1
      simpa only [one_mul] using (habs (C.c w)).1
    · rw [F.signed_eq_hi z rfl hw]
      change |F.coords z (C.c w)+1*F.intervals.radius (C.c w)|=1
      simpa only [one_mul] using (habs (C.c w)).2
  refine ⟨offsets p,planar p,offsets_balanced p,by rw [hp]; exact F.normal_ne_zero,?_⟩
  intro w
  change C.value p w=1 ∨ C.value p w= -1
  have hh := hvalue w
  rcases le_total 0 (C.value p w) with h | h
  · exact Or.inl (by rwa [abs_of_nonneg h] at hh)
  · exact Or.inr (by rw [abs_of_nonpos h] at hh; linarith)

lemma eta_not_exceptional (hlevels : F.intervals.TwoLevels) (hno : ¬ C.ExtraPM) :
    ¬(F.ratio=1 ∧ F.eta=0) ∧ ¬(F.ratio=1 ∧ F.eta=2) ∧ ¬(F.ratio=1 ∧ F.eta= -2) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair hlevels (s := 1) (v := -1) (Or.inl rfl) (Or.inr rfl) (by linarith) hr)
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair hlevels (s := 1) (v := 1) (Or.inl rfl) (Or.inl rfl) (by linarith) hr)
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair hlevels (s := -1) (v := -1) (Or.inr rfl) (Or.inr rfl) (by linarith) hr)

end TwoWidthSlice
end Kalai5.Cube3
