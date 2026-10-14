import Kalai5.Cube3.SingleSegmentTransfer
import Kalai5.Cube3.PolygonNormalFamilies

/-! Four nonopposite polygon normals disjoint from a segment normal force twenty facets. -/
namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.generic_quadrilateral_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : 3 ≤ (C.cls (τ 0)).card) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (N : Finset (E 2)) (hN : ∀ n ∈ N,LemmaB.IsEdgeNormal (fibre C.c C.k (τ 0)) n)
    (hcard : 4 ≤ N.card) (hop : ∀ n ∈ N,∀ m ∈ N,n ≠ -m)
    (hsep : ∀ n ∈ N,⟪n,S.direction⟫ ≠ 0) : 20 ≤ fvec P 4 := by
  classical
  obtain ⟨F,hF⟩ := C.edge_normals_family hP hrange (τ 0) N hN hop
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 2 := rfl
  have hρ2 : ρ 2=τ 3 := rfl
  have hρ3 : ρ 3=τ 0 := rfl
  obtain ⟨G,hG⟩ := Config.polygon_segment_three ρ (S.reclass hρ0.symm)
    (by rwa [hρ1]) (by rwa [hρ2]) (by rwa [hρ3])
  have hG' : ∀ k,G.normal k=S.normal := hG
  have hne : ∀ a b,F.normal a ≠ G.normal b := by
    intro a b he
    rw [hF,hG'] at he
    apply hsep a.1.val a.1.property
    rw [he]; exact S.normal_orthogonal
  have hopp : ∀ a b,F.normal a ≠ -G.normal b := by
    intro a b he
    rw [hF,hG'] at he
    apply hsep a.1.val a.1.property
    rw [he,inner_neg_left,S.normal_orthogonal,neg_zero]
  have hh := (F.sum G hne hopp).facets hP hrange
  have hbound : 6+2*(N.card+3)≤fvec P 4 := by
    simpa [Fintype.card_sum,Fintype.card_sigma] using hh
  omega

end Kalai5.Cube3
