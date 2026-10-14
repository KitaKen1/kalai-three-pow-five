import Kalai5.Cube3.UnequalSupportBonus
import Kalai5.Cube3.TriangleHomothety
import Kalai5.Cube3.AllSharedTriangle

/-! At most eighteen facets force two translated copies of the same signed triangle. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.matched_widths_eq {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (σ : Equiv.Perm (Fin 3)) (hn : ∀ i,T.triangle.normal i=U.triangle.normal (σ i)) :
    ∀ i,T.triangle.width i=U.triangle.width (σ i) := by
  intro i
  by_contra hneq
  have hall (k : Fin 3) : T.triangle.width k ≠ U.triangle.width (σ k) := by
    intro hk
    exact hneq (T.triangle.widths_all_or_none U.triangle σ hn hk i)
  obtain ⟨v,hv⟩ := C.surj (τ 0)
  obtain ⟨w,hw⟩ := C.surj (τ 1)
  obtain ⟨k,hpos⟩ := T.triangle.exists_positive_support
    (C.signedPoint (U.vertex (σ 0))+C.signedPoint v+C.signedPoint w)
  have hneg := TriangleFibre.unequal_support_neg hP hrange hh τ T U h0 h1 hno
    k (σ k) (hn k) (hall k) v w hv hw
  have hup := U.upper (σ k) (U.vertex (σ 0)) (U.cls (σ 0))
  rw [← hn] at hup
  rw [inner_add_right,inner_add_right] at hpos
  rw [inner_add_right] at hneg
  linarith

def Config.TranslatedTriangleFibres (C : Config x) (j k : Fin 4) : Prop :=
  ∀ (T : TriangleFibre C j) (U : TriangleFibre C k),
    ∃ σ : Equiv.Perm (Fin 3),(∀ i,T.triangle.normal i=U.triangle.normal (σ i)) ∧
      (∀ i,T.triangle.width i=U.triangle.width (σ i)) ∧
      ∃ d : E 2,∀ i,U.triangle.point (σ i)=T.triangle.point i+d

theorem Config.translated_triangle_fibres {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.TranslatedTriangleFibres (τ 0) (τ 1) := by
  classical
  intro T U
  obtain ⟨σ,hn⟩ := T.triangle.matching_permutation U.triangle
    (C.all_aligned_triangle_directions hP hrange hh hno τ h2 h3 T U)
  let ρ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hρ0 : ρ 0=τ 2 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ1 : ρ 1=τ 3 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ2 : ρ 2=τ 0 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  have hρ3 : ρ 3=τ 1 := by norm_num [ρ,Equiv.swap_apply_def] <;> decide
  let T' : TriangleFibre C (ρ 2) := T.reclass hρ2.symm
  let U' : TriangleFibre C (ρ 3) := U.reclass hρ3.symm
  have hw := TriangleFibre.matched_widths_eq hP hrange hh ρ T' U'
    (by rwa [hρ0]) (by rwa [hρ1]) hno σ hn
  exact ⟨σ,hn,hw,T.triangle.translation_of_widths U.triangle σ hn hw⟩

end Kalai5.Cube3
