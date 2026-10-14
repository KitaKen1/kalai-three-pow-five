import Kalai5.Cube3.IntervalCoordinates

/-! The four-dimensional normal slice with two zero widths and two positive widths. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

structure TwoWidthSlice where
  normal : E 2
  intervals : ProjectionIntervals C normal
  order : Equiv.Perm (Fin 4)
  zero : ∀ i : Fin 2,intervals.radius (order i.castSucc.castSucc)=0
  unit : intervals.radius (order 3)=1
  ratio_pos : 0 < intervals.radius (order 2)
  ratio_le : intervals.radius (order 2)≤1

namespace TwoWidthSlice
variable {C} (F : TwoWidthSlice C)

noncomputable def ratio : ℝ := F.intervals.radius (F.order 2)
noncomputable def eta : ℝ := F.intervals.drift F.normal

lemma normal_ne_zero : F.normal ≠ 0 := by
  intro hz
  have h := F.unit
  change ⟪F.normal,F.intervals.axis (F.order 3)⟫=1 at h
  have hz' := congrArg (fun n : E 2 => ⟪n,F.intervals.axis (F.order 3)⟫) hz
  rw [h,inner_zero_left] at hz'; norm_num at hz'

noncomputable def coords (z : SlabPoint) (j : Fin 4) : ℝ :=
  (![z.1 0,z.1 1,z.1 2,F.eta*z.2-∑ i,z.1 i] : Fin 4 → ℝ) (F.order.symm j)

lemma coords_order (z : SlabPoint) (j : Fin 4) :
    F.coords z (F.order j)=(![z.1 0,z.1 1,z.1 2,F.eta*z.2-∑ i,z.1 i] : Fin 4 → ℝ) j := by
  simp [coords]

lemma coords_sum (z : SlabPoint) : ∑ j,F.coords z j=F.intervals.drift (z.2 • F.normal) := by
  simp only [coords]
  rw [Equiv.sum_comp F.order.symm]
  simp [Fin.sum_univ_four,Fin.sum_univ_three,eta]; ring

noncomputable def embed (z : SlabPoint) : E5 :=
  pack (F.intervals.centeredOffset (F.coords z) (z.2 • F.normal)) (z.2 • F.normal)

lemma planar_embed (z : SlabPoint) : planar (F.embed z)=z.2 • F.normal := planar_pack _ _

lemma centerEval_embed (z : SlabPoint) : F.intervals.centerEval (F.embed z)=F.coords z :=
  F.intervals.centerEval_pack _ _ (F.coords_sum z)

noncomputable def project : E5 →ₗ[ℝ] SlabPoint where
  toFun p := ((WithLp.equiv 2 (Fin 3 → ℝ)).symm
    ![F.intervals.centerEval p (F.order 0),F.intervals.centerEval p (F.order 1),
      F.intervals.centerEval p (F.order 2)],⟪planar p,F.intervals.axis (F.order 3)⟫)
  map_add' := by
    intro p q
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_add]
    · have hp := planarLinear.map_add p q
      change planar (p+q)=planar p+planar q at hp
      simp [hp,inner_add_left]
  map_smul' := by
    intro t p
    apply Prod.ext
    · ext i; fin_cases i <;> simp [map_smul]
    · have hp := planarLinear.map_smul t p
      change planar (t • p)=t • planar p at hp
      simp [hp,real_inner_smul_left]

lemma project_first (p : E5) (i : Fin 3) :
    (F.project p).1 i=F.intervals.centerEval p (F.order i.castSucc) := by fin_cases i <;> rfl

lemma project_last (p : E5) : (F.project p).2=⟪planar p,F.intervals.axis (F.order 3)⟫ := rfl

lemma project_embed (z : SlabPoint) : F.project (F.embed z)=z := by
  apply Prod.ext
  · ext i
    rw [F.project_first,F.centerEval_embed,F.coords_order]
    fin_cases i <;> rfl
  · rw [F.project_last,F.planar_embed,real_inner_smul_left]
    change z.2*F.intervals.radius (F.order 3)=z.2
    rw [F.unit,mul_one]

lemma embed_injective : Function.Injective F.embed := by
  intro a b h; simpa only [F.project_embed] using congrArg F.project h

lemma embed_project {p : E5} (hp : planar p=(F.project p).2 • F.normal) :
    F.embed (F.project p)=p := by
  apply F.intervals.centered_ext (by rw [F.planar_embed]; exact hp.symm)
  rw [F.centerEval_embed]
  funext j
  obtain ⟨j,rfl⟩ := F.order.surjective j
  rw [F.coords_order]
  have hsum : ∑ k,F.intervals.centerEval p (F.order k)=F.intervals.drift (planar p) := by
    rw [Equiv.sum_comp F.order,F.intervals.centerEval_sum]
  rw [Fin.sum_univ_four,hp,map_smul,smul_eq_mul] at hsum
  fin_cases j
  · exact F.project_first p 0
  · exact F.project_first p 1
  · exact F.project_first p 2
  · simp only [Fin.sum_univ_three,F.project_first]
    change F.eta*(F.project p).2-
      (F.intervals.centerEval p (F.order 0)+F.intervals.centerEval p (F.order 1)+
       F.intervals.centerEval p (F.order 2))=F.intervals.centerEval p (F.order 3)
    change _=(F.project p).2*F.eta at hsum
    linarith

lemma mem_embed (z : SlabPoint) : F.embed z ∈ C.polarModel ↔ z ∈ doubleSlab F.ratio F.eta := by
  rw [F.intervals.mem_polar_on_line (F.planar_embed z)]
  have h0 : F.intervals.radius (F.order 0)=0 := F.zero 0
  have h1 : F.intervals.radius (F.order 1)=0 := F.zero 1
  constructor
  · intro h
    have ha := h (F.order 0)
    have hb := h (F.order 1)
    have hc := h (F.order 2)
    have hd := h (F.order 3)
    rw [F.centerEval_embed,F.coords_order,h0,zero_mul,add_zero] at ha
    rw [F.centerEval_embed,F.coords_order,h1,zero_mul,add_zero] at hb
    rw [F.centerEval_embed,F.coords_order] at hc
    rw [F.centerEval_embed,F.coords_order,F.unit,one_mul] at hd
    exact ⟨ha,hb,hc,hd⟩
  · intro h j
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [F.centerEval_embed,F.coords_order]
    fin_cases j
    · change |z.1 0|+F.intervals.radius (F.order 0)*|z.2|≤1
      rw [h0,zero_mul,add_zero]; exact h.1
    · change |z.1 1|+F.intervals.radius (F.order 1)*|z.2|≤1
      rw [h1,zero_mul,add_zero]; exact h.2.1
    · exact h.2.2.1
    · change |F.eta*z.2-∑ i,z.1 i|+F.intervals.radius (F.order 3)*|z.2|≤1
      rw [F.unit,one_mul]; exact h.2.2.2

end TwoWidthSlice
end Kalai5.Cube3
