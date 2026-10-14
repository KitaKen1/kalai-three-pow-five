import Kalai5.Cube3.SegmentFibre

/-! Each nonzero normal ray of a two-point class contains two actual polar vertices. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x} {j : Fin 4}
namespace SegmentFibre
variable (S : SegmentFibre C j)

noncomputable def normal : E 2 := ‖normal2 S.direction‖⁻¹ • normal2 S.direction

lemma normal_unit : ‖S.normal‖=1 := by
  rw [normal,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 (norm_pos_iff.2 (normal2_ne_zero S.direction_ne_zero))),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 (normal2_ne_zero S.direction_ne_zero))]

lemma normal_orthogonal : ⟪S.normal,S.direction⟫=0 := by
  rw [normal,real_inner_smul_left,normal2_orthogonal,mul_zero]

theorem two_positive {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) {n : E 2} (hn : ‖n‖=1)
    (hnd : ⟪n,S.direction⟫=0) : ∃ F : PositiveFamily C (Fin 2),∀ i,F.normal i=n := by
  have hn0 : n ≠ 0 := by intro he; rw [he,norm_zero] at hn; norm_num at hn
  have hc (v : Fin 8) (hv : C.c v=j) :
      ⟪n,C.k v⟫=balanceSign j*⟪n,C.signedPoint S.first⟫ := by
    have he := S.constant hnd v hv
    rw [Config.signedPoint,hv,inner_smul_right] at he
    calc
      _ = balanceSign j*(balanceSign j*⟪n,C.k v⟫) := by rw [← mul_assoc,balanceSign_sq,one_mul]
      _ = _ := congrArg (fun t => balanceSign j*t) he
  have hex (i : Fin 2) : ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v,C.c v=j → C.value p v=sign2 i) ∧ 0 < ⟪n,planar p⟫ :=
    C.class_ray_vertex hP hrange j (sign2_sign i) n hn0 _ hc
  choose p hp hv hpos using hex
  have hinj : Function.Injective p := by
    intro i k he
    apply sign2_injective
    rw [← hv i S.first S.first_class,he,hv k S.first S.first_class]
  have hline (i : Fin 2) : ∃ t : ℝ,0 < t ∧ planar (p i)=t • n := by
    apply positive_ray_of_orthogonal hn S.direction_ne_zero hnd _ (hpos i)
    have he : C.signedValue (p i) S.first=C.signedValue (p i) S.second := by
      simp only [Config.signedValue,S.first_class,S.second_class,hv i _ S.first_class,hv i _ S.second_class]
    exact C.equal_signedValue_orthogonal (S.first_class.trans S.second_class.symm) he
  exact ⟨PositiveFamily.onRay n hn p hinj hp hline,fun _ => rfl⟩

end SegmentFibre
end Kalai5.Cube3
