import Kalai5.Cube3.OneWidthOpposed
import Kalai5.Cube3.TransverseNormals
import Kalai5.Cube3.QuadrilateralAlignment

/-! Five vertices on an opposed-edge normal when the segment is parallel to those edges. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.aligned_quadrilateral_five (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    (hSn : ⟪n,S.direction⟫=0) (hno : ¬ C.ExtraPM) :
    ∃ H : PositiveFamily C (Fin 3 ⊕ Fin 2),∀ i,H.normal i=n := by
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  have hρ0 : ρ 0=τ 1 := rfl
  have hρ1 : ρ 1=τ 2 := rfl
  have hρ2 : ρ 2=τ 3 := rfl
  have hρ3 : ρ 3=τ 0 := rfl
  obtain ⟨I⟩ := C.projection_intervals n
  have hz (i : Fin 3) : I.radius (ρ i.castSucc)=0 := by
    fin_cases i
    · exact S.radius_zero I hSn
    · exact I.radius_zero_singleton h2
    · exact I.radius_zero_singleton h3
  have hp : 0 < I.radius (ρ 3) := I.radius_positive (by rw [hρ3,h0]; omega) hn.ne_zero
  let F := I.oneWidth ρ hz hp
  have he : F.normal=(I.radius (ρ 3))⁻¹ • n := rfl
  have hlevels : F.intervals.TwoLevels := by
    intro v
    obtain ⟨k,hk⟩ := τ.surjective (C.c v)
    have hv : C.c v=τ k := hk.symm
    rw [hv]
    fin_cases k
    · exact F.intervals.opposed_quad_two_levels h0 hn hm he v hv
    · exact S.two_levels F.intervals v hv
    · exact F.intervals.singleton_two_levels h2 v hv
    · exact F.intervals.singleton_two_levels h3 v hv
  exact F.opposed_five hn hm (inv_pos.2 hp) he hlevels hno

theorem Config.aligned_quadrilateral_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) n)
    (hm : IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    (hSn : ⟪n,S.direction⟫=0) (hno : ¬ C.ExtraPM)
    (halign : ∀ m,IsEdgeNormal (fibre C.c C.k (τ 0)) m →
      IsEdgeNormal (fibre C.c C.k (τ 0)) (-m) → ⟪m,S.direction⟫=0) : 20 ≤ fvec P 4 := by
  classical
  obtain ⟨F,hF⟩ := C.aligned_quadrilateral_five τ h0 S h2 h3 hn hm hSn hno
  obtain ⟨N,hN,hcard⟩ := C.exists_fibre_normals (show 3 ≤ (C.cls (τ 0)).card by omega)
  let M := N.filter (fun m => ⟪m,S.direction⟫ ≠ 0)
  have hM (m : E 2) (hm : m ∈ M) : IsEdgeNormal (fibre C.c C.k (τ 0)) m :=
    hN m (Finset.mem_filter.1 hm).1
  have hMc : 2 ≤ M.card := by
    have hh := S.transverse_normals_card N (fun m hm => (hN m hm).1)
    dsimp only [M]
    omega
  have hop : ∀ m ∈ M,∀ k ∈ M,m ≠ -k := by
    intro m hm k hk he
    have hmk : IsEdgeNormal (fibre C.c C.k (τ 0)) (-m) := by
      rw [he,neg_neg]; exact hM k hk
    exact (Finset.mem_filter.1 hm).2 (halign m (hM m hm) hmk)
  obtain ⟨G,hG⟩ := C.edge_normals_family hP hrange (τ 0) M hM hop
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
  have hbound : 6+2*(5+M.card)≤fvec P 4 := by
    simpa [Fintype.card_sum,Fintype.card_sigma] using hh
  omega

end Kalai5.Cube3
