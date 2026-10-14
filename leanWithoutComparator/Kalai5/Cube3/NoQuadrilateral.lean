import Kalai5.Cube3.TransverseBonusCount

/-! The two remaining boundary drifts also force twenty facets. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.quadrilateral_boundary_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (hb : C.QuadSegmentBoundary (τ 0) (τ 1)) : 20 ≤ fvec P 4 := by
  obtain ⟨n,hn,hSn⟩ := hb.1.2 S
  let m := balanceSign (τ 0) • n
  have hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (balanceSign (τ 0) • m) := by
    simpa only [m,smul_smul,balanceSign_sq,one_smul] using hn
  have hm0 : m ≠ 0 := fun hz => hm.ne_zero (by rw [hz,smul_zero])
  have hSm : ⟪m,S.direction⟫=0 := by
    change ⟪balanceSign (τ 0) • n,S.direction⟫=0
    rw [real_inner_smul_left,hSn,mul_zero]
  obtain ⟨I⟩ := C.projection_intervals m
  have he := hb.2 S m hm hSm I
  obtain ⟨E⟩ := C.boundary_support_edge τ (by omega) S h2 h3 hm0 hSm I he
  obtain ⟨F,hF⟩ := C.support_edge_two hP hrange τ S h2 h3
    (I.hi (τ 2)) (I.hi (τ 3)) (I.chi _) (I.chi _) E
  exact C.transverse_bonus_facets hP hrange τ h0 S h2 h3 hb.1.1
    (C.signed_support_edge_normal E) E.transverse F hF

theorem Config.no_three_full_configuration {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : False := by
  obtain ⟨τ,h0,h1,h2,h3,hb⟩ := C.quadrilateral_boundary_pattern hP hrange hh hno
  obtain ⟨S⟩ := C.segment_fibre h1
  have hf := C.quadrilateral_boundary_facets hP hrange τ h0 S h2 h3 hb
  omega

end Kalai5.Cube3
