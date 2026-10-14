import Kalai5.Cube3.SharedSupportBounds
import Kalai5.Cube3.ThirdTriangleSupport

/-! At most eighteen facets force all three oriented triangle normals to agree. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} {C : Config x}

theorem TriangleFibre.all_aligned_of_two {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (T : TriangleFibre C (τ 2)) (U : TriangleFibre C (τ 3))
    (h0 : (C.cls (τ 0)).card=1) (h1 : (C.cls (τ 1)).card=1) (hno : ¬ C.ExtraPM)
    (a b i j : Fin 3) (hab : a ≠ b)
    (ha : T.triangle.normal a=U.triangle.normal i) (hb : T.triangle.normal b=U.triangle.normal j) :
    ∀ c,∃ k,T.triangle.normal c=U.triangle.normal k := by
  classical
  intro c
  by_cases hac : a=c
  · exact ⟨i,hac ▸ ha⟩
  by_cases hbc : b=c
  · exact ⟨j,hbc ▸ hb⟩
  by_contra hc
  obtain ⟨v,hv⟩ := C.surj (τ 0)
  obtain ⟨w,hw⟩ := C.surj (τ 1)
  have hSa := TriangleFibre.shared_support_lt hP hrange hh τ T U h0 h1 hno a i ha v w hv hw
  have hSb := TriangleFibre.shared_support_lt hP hrange hh τ T U h0 h1 hno b j hb v w hv hw
  obtain ⟨k,hpos⟩ := T.triangle.third_support_positive U.triangle (C.signedPoint v+C.signedPoint w)
    a b c i j hab hac hbc ha hb hSa hSb
  rw [U.point_eq] at hpos
  have hnon := TriangleFibre.unshared_reference_nonpos hP hrange hh τ T U h0 h1 hno c hc
    v w (U.vertex k) hv hw (U.cls k)
  have hpos' : 0 < T.triangle.height c+
      ⟪T.triangle.normal c,C.signedPoint (U.vertex k)+C.signedPoint v+C.signedPoint w⟫ := by
    simpa only [add_assoc] using hpos
  linarith

def Config.AllAlignedTriangleDirections (C : Config x) (j k : Fin 4) : Prop :=
  ∀ (T : TriangleFibre C j) (U : TriangleFibre C k),∀ i,∃ l,T.triangle.normal i=U.triangle.normal l

theorem Config.all_aligned_triangle_directions {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM)
    (τ : Equiv.Perm (Fin 4)) (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1) :
    C.AllAlignedTriangleDirections (τ 0) (τ 1) := by
  classical
  intro T U
  obtain ⟨a,i,b,j,hab,ha,hb⟩ := C.multiple_aligned_triangle_directions hP hrange hh hno τ h2 h3 T U
  let σ : Equiv.Perm (Fin 4) := ((Equiv.swap 0 2).trans (Equiv.swap 1 3)).trans τ
  have hσ0 : σ 0=τ 2 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ1 : σ 1=τ 3 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ2 : σ 2=τ 0 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  have hσ3 : σ 3=τ 1 := by norm_num [σ,Equiv.swap_apply_def] <;> decide
  let T' : TriangleFibre C (σ 2) := T.reclass hσ2.symm
  let U' : TriangleFibre C (σ 3) := U.reclass hσ3.symm
  exact TriangleFibre.all_aligned_of_two hP hrange hh σ T' U'
    (by rwa [hσ0]) (by rwa [hσ1]) hno a b i j hab ha hb

end Kalai5.Cube3
