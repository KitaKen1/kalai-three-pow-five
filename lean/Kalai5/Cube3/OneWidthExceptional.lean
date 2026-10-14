import Kalai5.Cube3.OneWidthConstruction

/-! The four exceptional offsets create an extra full normal for two-level projections. -/
namespace Kalai5.Cube3
open Set
variable {x : Fin 8 → E5} {C : Config x}
namespace OneWidthSlice
variable (F : OneWidthSlice C)

lemma extra_of_cube_section (hlevels : F.intervals.TwoLevels)
    {u : E 3} (hu : ∀ i,u i=1 ∨ u i= -1) (hsum : ∑ i,u i=F.eta) : C.ExtraPM := by
  let z : SlabPoint := (u,1)
  let p := F.embed z
  have hp : planar p=F.normal := by rw [F.planar_embed]; simp [z]
  have habs (j : Fin 4) : |F.coords z j-F.intervals.radius j|=1 ∧
      |F.coords z j+F.intervals.radius j|=1 := by
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [F.coords_order]
    have h0 : F.intervals.radius (F.order 0)=0 := F.zero 0
    have h1 : F.intervals.radius (F.order 1)=0 := F.zero 1
    have h2 : F.intervals.radius (F.order 2)=0 := F.zero 2
    fin_cases j
    · change |u 0-F.intervals.radius (F.order 0)|=1 ∧ |u 0+F.intervals.radius (F.order 0)|=1
      rw [h0]; rcases hu 0 with h | h <;> rw [h] <;> norm_num
    · change |u 1-F.intervals.radius (F.order 1)|=1 ∧ |u 1+F.intervals.radius (F.order 1)|=1
      rw [h1]; rcases hu 1 with h | h <;> rw [h] <;> norm_num
    · change |u 2-F.intervals.radius (F.order 2)|=1 ∧ |u 2+F.intervals.radius (F.order 2)|=1
      rw [h2]; rcases hu 2 with h | h <;> rw [h] <;> norm_num
    · change |F.eta*1-∑ i,u i-F.intervals.radius (F.order 3)|=1 ∧
        |F.eta*1-∑ i,u i+F.intervals.radius (F.order 3)|=1
      rw [hsum,F.unit]; norm_num
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
    F.eta ≠ 1 ∧ F.eta ≠ -1 ∧ F.eta ≠ 3 ∧ F.eta ≠ -3 := by
  have hcube (a b c : ℝ) (ha : a=1 ∨ a= -1) (hb : b=1 ∨ b= -1)
      (hc : c=1 ∨ c= -1) : F.eta ≠ a+b+c := by
    intro h
    apply hno
    apply F.extra_of_cube_section hlevels (u := cycle3 a b c 0)
    · intro i; fin_cases i <;> assumption
    · rw [cycle3_sum,h]
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hcube 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  · simpa using hcube (-1) (-1) 1 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  · convert hcube 1 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) using 1 <;> norm_num
  · convert hcube (-1) (-1) (-1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) using 1 <;> norm_num

end OneWidthSlice
end Kalai5.Cube3
