import Kalai5.Cube3.SupportPairPoints
import Kalai5.Cube3.TriangleSupportIntervals

/-! Maximize height in two active faces; simultaneous saturation would force height zero. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.support_pair_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (T : TriangleFibre C (τ 0)) (i : Fin 3)
    (I : ProjectionIntervals C (T.triangle.normal i))
    (hz : I.radius (τ 3)=0) (hle : I.radius (τ 2)≤I.radius (τ 1))
    (hp : 0 < I.drift (T.triangle.normal i)+I.radius (τ 0)) :
    ∃ F : PositiveFamily C (Fin 2),∀ k,F.normal k=T.triangle.normal i := by
  classical
  let n := T.triangle.normal i
  obtain ⟨t,ht,q,hq,hplane,hT,hS,hR,hV⟩ := I.support_pair_points τ hz hle hp
  obtain ⟨a,b,hab,hia,hib⟩ := TriangleFibre.edge_points i
  have ha : ⟪n,C.signedPoint (T.vertex a)⟫=⟪n,C.signedPoint (I.hi (τ 0))⟫ :=
    I.triangle_upper_eq T i (a := 1) (by norm_num) (by simp [n]) a hia
  have hb : ⟪n,C.signedPoint (T.vertex b)⟫=⟪n,C.signedPoint (I.hi (τ 0))⟫ :=
    I.triangle_upper_eq T i (a := 1) (by norm_num) (by simp [n]) b hib
  have hqa (k : Fin 2) : C.signedValue (q k) (T.vertex a)=1 :=
    (ProjectionIntervals.equal_value_on_line (hplane k) ((T.cls a).trans (I.chi _).symm) ha).trans (hT k)
  have hqb (k : Fin 2) : C.signedValue (q k) (T.vertex b)=1 :=
    (ProjectionIntervals.equal_value_on_line (hplane k) ((T.cls b).trans (I.chi _).symm) hb).trans (hT k)
  let lower (k : Fin 2) := if k=0 then I.lo (τ 2) else I.lo (τ 3)
  have hlow (k : Fin 2) : C.signedValue (q k) (lower k)= -1 := by
    fin_cases k
    · exact hR
    · exact hV
  let A (k : Fin 2) : Finset (Fin 8) := {T.vertex a,T.vertex b,I.hi (τ 0),I.hi (τ 1),lower k}
  have hs (k : Fin 2) : ∀ v ∈ A k,C.signedValue (q k) v=1 ∨ C.signedValue (q k) v= -1 := by
    intro v hv
    simp only [A,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (hqa k)
    · exact Or.inl (hqb k)
    · exact Or.inl (hT k)
    · exact Or.inl (hS k)
    · exact Or.inr (hlow k)
  have hqpos (k : Fin 2) : 0 < ⟪n,planar (q k)⟫ := by
    rw [hplane,inner_smul_right,real_inner_self_eq_norm_sq,T.triangle.normal_unit]
    simpa using ht
  have hex (k : Fin 2) : ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v ∈ A k,C.signedValue p v=C.signedValue (q k) v) ∧ 0 < ⟪n,planar p⟫ :=
    C.signed_activeFace_ray_vertex hP hrange (A k) (C.signedValue (q k)) (hs k) n
      (hq k) (fun _ _ => rfl) (hqpos k)
  choose f hf hv hpos using hex
  have hfa (k : Fin 2) : C.signedValue (f k) (T.vertex a)=1 :=
    (hv k _ (by simp [A])).trans (hqa k)
  have hfb (k : Fin 2) : C.signedValue (f k) (T.vertex b)=1 :=
    (hv k _ (by simp [A])).trans (hqb k)
  have hline (k : Fin 2) : ∃ s : ℝ,0 < s ∧ planar (f k)=s • n := by
    apply positive_ray_of_orthogonal (T.triangle.normal_unit i)
      (sub_ne_zero.2 (fun h => hab (T.inj (C.signedPoint_inj ((T.cls a).trans (T.cls b).symm) h.symm))))
      (show ⟪n,C.signedPoint (T.vertex b)-C.signedPoint (T.vertex a)⟫=0 from by rw [inner_sub_right,hb,ha,sub_self])
      (C.equal_signedValue_orthogonal ((T.cls a).trans (T.cls b).symm) ((hfa k).trans (hfb k).symm))
      (hpos k)
  have hneq : f 0 ≠ f 1 := by
    intro he
    obtain ⟨s,hs,hplane'⟩ := hline 0
    have h0 := (hv 0 (I.hi (τ 0)) (by simp [A])).trans (hT 0)
    have h1 := (hv 0 (I.hi (τ 1)) (by simp [A])).trans (hS 0)
    have h2 := (hv 0 (I.lo (τ 2)) (by simp [A,lower])).trans hR
    have h3 : C.signedValue (f 0) (I.lo (τ 3))= -1 := by
      rw [he]; exact (hv 1 _ (by simp [A,lower])).trans hV
    rw [I.signed_hi,hplane',real_inner_smul_left] at h0 h1
    rw [I.signed_lo,hplane',real_inner_smul_left] at h2 h3
    change I.centerEval (f 0) (τ 0)+s*I.radius (τ 0)=1 at h0
    change I.centerEval (f 0) (τ 1)+s*I.radius (τ 1)=1 at h1
    change I.centerEval (f 0) (τ 2)-s*I.radius (τ 2)= -1 at h2
    change I.centerEval (f 0) (τ 3)-s*I.radius (τ 3)= -1 at h3
    rw [hz,mul_zero,sub_zero] at h3
    have hsum := I.centerEval_sum (f 0)
    rw [← Equiv.sum_comp τ,Fin.sum_univ_four,hplane',map_smul,smul_eq_mul] at hsum
    have hpositive : 0 < s*(I.drift n+I.radius (τ 0)+I.radius (τ 1)-I.radius (τ 2)) :=
      mul_pos hs (by linarith)
    nlinarith
  have hinj : Function.Injective f := by
    intro k l he; fin_cases k <;> fin_cases l <;> simp_all
  exact ⟨PositiveFamily.onRay n (T.triangle.normal_unit i) f hinj hf hline,fun _ => rfl⟩

end Kalai5.Cube3
