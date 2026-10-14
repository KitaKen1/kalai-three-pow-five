import Kalai5.Cube3.SupportEdgeTransfer

/-! Two vertices on a transverse edge, three on the segment normal, and two other edges. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

theorem Config.transverse_bonus_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (h0 : (C.cls (τ 0)).card=4) (S : SegmentFibre C (τ 1))
    (h2 : (C.cls (τ 2)).card=1) (h3 : (C.cls (τ 3)).card=1)
    (hop : ∀ n,IsEdgeNormal (fibre C.c C.k (τ 0)) n →
      ¬ IsEdgeNormal (fibre C.c C.k (τ 0)) (-n))
    {n : E 2} (hn : IsEdgeNormal (fibre C.c C.k (τ 0)) (balanceSign (τ 0) • n))
    (hSn : ⟪n,S.direction⟫ ≠ 0)
    (F : PositiveFamily C (Fin 2)) (hF : ∀ i,F.normal i=n) : 20 ≤ fvec P 4 := by
  classical
  let σ : Equiv.Perm (Fin 4) :=
    ⟨fun j => ![1,2,3,0] j,fun j => ![3,0,1,2] j,
      by intro j; fin_cases j <;> rfl,by intro j; fin_cases j <;> rfl⟩
  let ρ := σ.trans τ
  obtain ⟨H,hH⟩ := C.polygon_segment_three ρ S h2 h3 (show 3 ≤ (C.cls (ρ 3)).card by
    change 3 ≤ (C.cls (τ 0)).card; omega)
  obtain ⟨N,hN,hcard⟩ := C.exists_fibre_normals (show 3 ≤ (C.cls (τ 0)).card by omega)
  have hNop : ∀ m ∈ N,∀ k ∈ N,m ≠ -k := by
    intro m hm k hk he
    apply hop m (hN m hm)
    rw [he,neg_neg]; exact hN k hk
  let R := N.filter (fun m => ⟪m,S.direction⟫ ≠ 0)
  let u := balanceSign (τ 0) • n
  let M := R.erase u
  have hRc : 3 ≤ R.card := by
    have hh := S.transverse_normals_card_of_no_opposite N (fun m hm => (hN m hm).1) hNop
    dsimp only [R]; omega
  have hMc : 2 ≤ M.card := by
    have hh := Finset.pred_card_le_card_erase (s := R) (a := u)
    change R.card-1 ≤ M.card at hh
    omega
  have hMR (m : E 2) (hm : m ∈ M) : m ∈ R := (Finset.mem_erase.1 hm).2
  have hMN (m : E 2) (hm : m ∈ M) : m ∈ N := (Finset.mem_filter.1 (hMR m hm)).1
  have hM (m : E 2) (hm : m ∈ M) : IsEdgeNormal (fibre C.c C.k (τ 0)) m := hN m (hMN m hm)
  have htrans (m : E 2) (hm : m ∈ M) : ⟪m,S.direction⟫ ≠ 0 :=
    (Finset.mem_filter.1 (hMR m hm)).2
  have havoid (m : E 2) (hm : m ∈ M) : m ≠ n ∧ m ≠ -n := by
    have hnu : m ≠ u := (Finset.mem_erase.1 hm).1
    have hmu : m ≠ -u := by
      intro he
      apply hop u hn
      rw [← he]; exact hM m hm
    rcases balanceSign_sign (τ 0) with hs | hs
    · simpa [u,hs] using And.intro hnu hmu
    · simpa [u,hs] using And.intro hmu hnu
  obtain ⟨G,hG⟩ := C.edge_normals_family hP hrange (τ 0) M hM
    (fun m hm k hk => hNop m (hMN m hm) k (hMN k hk))
  have hFH : ∀ i j,F.normal i ≠ H.normal j := by
    intro i j he
    rw [hF,hH] at he
    exact hSn (by rw [he]; exact S.normal_orthogonal)
  have hFHo : ∀ i j,F.normal i ≠ -H.normal j := by
    intro i j he
    rw [hF,hH] at he
    change n = -S.normal at he
    exact hSn (by rw [he,inner_neg_left,S.normal_orthogonal,neg_zero])
  let K := F.sum H hFH hFHo
  have hKG : ∀ i j,K.normal i ≠ G.normal j := by
    rintro (i | i) j he
    · change F.normal i=G.normal j at he
      rw [hF,hG] at he
      exact (havoid j.1.val j.1.property).1 he.symm
    · change H.normal i=G.normal j at he
      rw [hH,hG] at he
      exact htrans j.1.val j.1.property (by rw [← he]; exact S.normal_orthogonal)
  have hKGo : ∀ i j,K.normal i ≠ -G.normal j := by
    rintro (i | i) j he
    · change F.normal i= -G.normal j at he
      rw [hF,hG] at he
      exact (havoid j.1.val j.1.property).2 (by rw [he,neg_neg])
    · change H.normal i= -G.normal j at he
      rw [hH,hG] at he
      change S.normal = -j.1.val at he
      have hh := S.normal_orthogonal
      rw [he,inner_neg_left] at hh
      exact htrans j.1.val j.1.property (by linarith)
  have hh := (K.sum G hKG hKGo).facets hP hrange
  have hbound : 6+2*(5+M.card)≤fvec P 4 := by
    simpa [Fintype.card_sum,Fintype.card_sigma] using hh
  omega

end Kalai5.Cube3
