import Kalai5.Cube3.TwoClassRays

/-! Two zero-width classes separate two vertices on a positively supported edge ray. -/

namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} (C : Config x)
namespace Config

theorem edge_two_vertices {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ)
    (τ : Equiv.Perm (Fin 4)) (rep : Fin 4 → Fin 8) (hc : ∀ j,C.c (rep j)=τ j)
    (w : Fin 8) (hwc : C.c w=τ 0) (hneq : C.signedPoint w ≠ C.signedPoint (rep 0))
    (n : E 2) (hn : ‖n‖=1)
    (hw : ⟪n,C.signedPoint w⟫=⟪n,C.signedPoint (rep 0)⟫)
    (hupper : ∀ v,C.c v=τ 0 → ⟪n,C.signedPoint v⟫≤⟪n,C.signedPoint (rep 0)⟫)
    (hconstant2 : ∀ v,C.c v=τ 2 → ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (rep 2)⟫)
    (hconstant3 : ∀ v,C.c v=τ 3 → ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (rep 3)⟫)
    (hpositive : 0 < ⟪n,∑ j,C.signedPoint (rep j)⟫) :
    ∃ f : Fin 2 → E5,Function.Injective f ∧
      (∀ i,f i ∈ C.polarModel.extremePoints ℝ) ∧
      ∀ i,∃ t : ℝ,0 < t ∧ planar (f i)=t • n := by
  have hn0 : n ≠ 0 := by intro hz; rw [hz,norm_zero] at hn; norm_num at hn
  have hτ (i j : Fin 4) (hij : i ≠ j) : τ i ≠ τ j := fun h => hij (τ.injective h)
  obtain ⟨p,hp,hp0,hp2,hppos⟩ := C.two_class_ray_vertex hP hrange (τ 0) (τ 2) (τ 1)
    (hτ 0 2 (by decide)) (hτ 1 0 (by decide)) (hτ 1 2 (by decide)) n hn0
    _ _ hupper hconstant2
  obtain ⟨q,hq,hq0,hq3,hqpos⟩ := C.two_class_ray_vertex hP hrange (τ 0) (τ 3) (τ 1)
    (hτ 0 3 (by decide)) (hτ 1 0 (by decide)) (hτ 1 3 (by decide)) n hn0
    _ _ hupper hconstant3
  have hline (z : E5)
      (hz0 : ∀ v,C.c v=τ 0 → ⟪n,C.signedPoint v⟫=⟪n,C.signedPoint (rep 0)⟫ → C.signedValue z v=1)
      (hzpos : 0 < ⟪n,planar z⟫) : ∃ t : ℝ,0 < t ∧ planar z=t • n := by
    have hv := C.equal_signedValue_orthogonal ((hc 0).trans hwc.symm)
      (p := z) (by rw [hz0 (rep 0) (hc 0) rfl,hz0 w hwc hw])
    have hnv : ⟪n,C.signedPoint w-C.signedPoint (rep 0)⟫=0 := by rw [inner_sub_right,hw,sub_self]
    exact positive_ray_of_orthogonal hn (sub_ne_zero.2 hneq) hnv hv hzpos
  obtain ⟨t,ht,hpt⟩ := hline p hp0 hppos
  have hpq : p ≠ q := by
    intro he
    have hv0 : C.signedValue p (rep 0)=1 := hp0 _ (hc 0) rfl
    have hv2 : C.signedValue p (rep 2)= -1 := hp2 _ (hc 2)
    have hv3 : C.signedValue p (rep 3)= -1 := by rw [he]; exact hq3 _ (hc 3)
    have hvsum : ∑ j,C.signedValue p (rep j)=C.signedValue p (rep 1)-1 := by
      rw [Fin.sum_univ_four,hv0,hv2,hv3]; ring
    have hsum := C.signedValue_sum_ordered τ rep hc p
    rw [hvsum,hpt,real_inner_smul_left] at hsum
    have hv1 := (abs_le.1 ((C.mem_polar_signed p).1 hp.1 (rep 1))).2
    have hgt := mul_pos ht hpositive
    linarith
  refine ⟨![p,q],?_,?_,?_⟩
  · intro i j he; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> assumption
  · intro i; fin_cases i
    · exact ⟨t,ht,hpt⟩
    · exact hline q hq0 hqpos

end Config
end Kalai5.Cube3
