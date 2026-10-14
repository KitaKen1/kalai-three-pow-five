import Kalai5.Cube3.SingleEdgeWidth
import Kalai5.Cube3.NoOpposedQuadrilateral

/-! A shared edge leaves only the normalized drifts +1 and -1. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.four_on_shared_ray_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) {q s : Fin 4}
    (h4 : (C.cls q).card=4) (S : SegmentFibre C s)
    (hop : ∀ n,IsEdgeNormal (fibre C.c C.k q) n → ¬ IsEdgeNormal (fibre C.c C.k q) (-n))
    {n : E 2} (hSn : ⟪n,S.direction⟫=0)
    (F : PositiveFamily C (Fin 3 ⊕ Unit)) (hF : ∀ i,F.normal i=n) : 20 ≤ fvec P 4 := by
  classical
  obtain ⟨N,hN,hcard⟩ := C.exists_fibre_normals (show 3 ≤ (C.cls q).card by omega)
  have hNop : ∀ m ∈ N,∀ k ∈ N,m ≠ -k := by
    intro m hm k hk he
    apply hop m (hN m hm)
    rw [he,neg_neg]; exact hN k hk
  let M := N.filter (fun m => ⟪m,S.direction⟫ ≠ 0)
  have hM (m : E 2) (hm : m ∈ M) : IsEdgeNormal (fibre C.c C.k q) m :=
    hN m (Finset.mem_filter.1 hm).1
  have hMc : 3 ≤ M.card := by
    have hh := S.transverse_normals_card_of_no_opposite N (fun m hm => (hN m hm).1) hNop
    dsimp only [M]; omega
  obtain ⟨G,hG⟩ := C.edge_normals_family hP hrange q M hM
    (fun m hm k hk => hNop m (Finset.mem_filter.1 hm).1 k (Finset.mem_filter.1 hk).1)
  have hne : ∀ i j,F.normal i ≠ G.normal j := by
    intro i j he
    rw [hF,hG] at he
    exact (Finset.mem_filter.1 j.1.property).2 (by rw [← he]; exact hSn)
  have hopp : ∀ i j,F.normal i ≠ -G.normal j := by
    intro i j he
    rw [hF,hG] at he
    have hh : ⟪j.1.val,S.direction⟫=0 := by
      have hh := hSn
      rw [he,inner_neg_left] at hh
      linarith
    exact (Finset.mem_filter.1 j.1.property).2 hh
  have hh := (F.sum G hne hopp).facets hP hrange
  have hbound : 6+2*(4+M.card)≤fvec P 4 := by
    simpa [Fintype.card_sum,Fintype.card_sigma] using hh
  omega

theorem Config.shared_quadrilateral_exceptional {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (τ : Equiv.Perm (Fin 4)) (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (hop : ∀ n,IsEdgeNormal (fibre C.c C.k (τ 0)) n → ¬ IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) (balanceSign (τ 0) • n))
    (hSn : ⟪n,S.direction⟫=0) (I : ProjectionIntervals C n) :
    I.drift n=I.radius (τ 0) ∨ I.drift n= -I.radius (τ 0) := by
  by_contra hbad
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 2 := rfl
  have hρ2 : ρ 2=τ 3 := rfl
  have hρ3 : ρ 3=τ 0 := rfl
  have hn0 : n ≠ 0 := fun he => hn.ne_zero (by rw [he,smul_zero])
  have hz (i : Fin 3) : I.radius (ρ i.castSucc)=0 := by
    fin_cases i
    · exact S.radius_zero I hSn
    · exact I.radius_zero_singleton h2
    · exact I.radius_zero_singleton h3
  have hp : 0 < I.radius (ρ 3) := I.radius_positive (by rw [hρ3,h0]; omega) hn0
  let F := I.oneWidth ρ hz hp
  have he : F.normal=(I.radius (ρ 3))⁻¹ • n := rfl
  have hη : F.eta=I.drift n/I.radius (τ 0) := by
    change I.drift ((I.radius (τ 0))⁻¹ • n)=_
    rw [map_smul,smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hrad : I.radius (τ 0) ≠ 0 := hp.ne'
  have h1 : F.eta ≠ 1 := by
    intro h1
    apply hbad; left
    have heq := (div_eq_iff hrad).1 (hη.symm.trans h1)
    simpa using heq
  have hm1 : F.eta ≠ -1 := by
    intro hm1
    apply hbad; right
    have heq := (div_eq_iff hrad).1 (hη.symm.trans hm1)
    simpa using heq
  obtain ⟨G,hG⟩ := F.segment_edge_four S hn (inv_pos.2 hp) he h1 hm1
  have hf := C.four_on_shared_ray_facets hP hrange h0 S hop hSn G hG
  omega

def Config.QuadSegmentBoundary (q s : Fin 4) : Prop :=
  C.QuadSegmentNonopposed q s ∧
    ∀ (S : SegmentFibre C s) (n : E 2),
      IsEdgeNormal (fibre C.c C.k q) (balanceSign q • n) → ⟪n,S.direction⟫=0 →
      ∀ I : ProjectionIntervals C n,I.drift n=I.radius q ∨ I.drift n= -I.radius q

theorem Config.quadrilateral_boundary_pattern {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18) (hno : ¬ C.ExtraPM) :
    ∃ τ : Equiv.Perm (Fin 4),(C.cls (τ 0)).card=4 ∧ (C.cls (τ 1)).card=2 ∧
      (C.cls (τ 2)).card=1 ∧ (C.cls (τ 3)).card=1 ∧ C.QuadSegmentBoundary (τ 0) (τ 1) := by
  obtain ⟨τ,h0,h1,h2,h3,hshape⟩ := C.quadrilateral_nonopposed_pattern hP hrange hh hno
  exact ⟨τ,h0,h1,h2,h3,hshape,fun S n hn hSn I =>
    C.shared_quadrilateral_exceptional hP hrange hh τ h0 S h2 h3 hshape.1 hn hSn I⟩

end Kalai5.Cube3
