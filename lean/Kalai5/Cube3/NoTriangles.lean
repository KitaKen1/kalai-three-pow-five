import Kalai5.Cube3.TranslatedTriangleCount
import Kalai5.Cube3.NoSegments

/-! Eliminate the entire (3,3,1,1) distribution in the three-full-pair branch. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.no_two_triangles {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=3) (h1 : (C.cls (τ 1)).card=3)
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) : False := by
  classical
  obtain ⟨T⟩ := C.triangle_fibre h0
  obtain ⟨U⟩ := C.triangle_fibre h1
  obtain ⟨σ,hn,hw,d,hd⟩ := C.translated_triangle_fibres hP hrange hh hno τ h2 h3 T U
  let ρ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hρ0 : ρ 0=τ 2 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ1 : ρ 1=τ 3 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ2 : ρ 2=τ 0 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ3 : ρ 3=τ 1 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  obtain ⟨v,hv⟩ := C.surj (ρ 0)
  obtain ⟨w,hw'⟩ := C.surj (ρ 1)
  let F : TranslatedTriangleFrame C := {
    order := ρ
    T := T.reclass hρ2.symm
    U := U.reclass hρ3.symm
    single0 := by rwa [hρ0]
    single1 := by rwa [hρ1]
    v := v
    w := w
    cv := hv
    cw := hw'
    pairing := σ
    normals := hn
    widths := hw
    shift := d
    translated := hd }
  exact F.no_eighteen hP hrange hh hno

theorem Config.two_size_patterns {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),
    ((C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1) ∨
    ((C.cls (τ 0)).card=3 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=2 ∧ (C.cls (τ 3)).card=1) := by
  obtain ⟨τ,h | h | h⟩ := C.three_size_patterns hP hrange hh hno
  · exact ⟨τ,Or.inl h⟩
  · exact (C.no_two_triangles hP hrange hh hno τ h.1 h.2.1 h.2.2.1 h.2.2.2).elim
  · exact ⟨τ,Or.inr h⟩

end Kalai5.Cube3
