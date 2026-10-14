import Kalai5.FullPrism.Comb
import Kalai5.FullPrism.Upper
import Kalai5.Endpoints.Sixteen

/-!
# The combinatorial type of a 4-polytope with row `(8,16,14,6; 32)`

`prism_sides`: a 4-polytope `K = conv VF` (with `VF` its vertex set) whose row is `tRow` has four
facets `S_0, …, S_3` and a labelling `v_0, …, v_7` of its vertices such that `v_j ∉ S_k` exactly
when `j / 2 = k` (the side facets of a prism over a tetrahedron).

The facet counts: every vertex lies in exactly four facets (`J = 32 = 8 · 4`), every facet has
four or six vertices (equality in `2 f₂(G) ≥ 4 + f₀(G)` summed over the facets, by Euler,
`3 f₀ ≤ 2 f₁` and `Σ f₂(G) = 2 · 14`), every vertex has at least four edges, and every edge lies
in at least three facets; then `miss_side_card`.
-/

namespace Kalai5

open Set FullPrism

variable {d : ℕ}

section

open Classical

variable {VF : Finset (E d)}

/-- Vertices of a face of `conv VF` (when `VF` is the vertex set). -/
lemma extremePoints_face_eq {G : Set (E d)}
    (hext : (VF : Set (E d)) = (convexHull ℝ (VF : Set (E d))).extremePoints ℝ)
    (hG : G ∈ faces (convexHull ℝ (VF : Set (E d)))) :
    G.extremePoints ℝ = G ∩ VF := by
  rw [hext]
  exact hG.2.isExtreme.extremePoints_eq

/-- The number of vertices of a face. -/
lemma cnt_zero_face_eq {G : Set (E d)}
    (hext : (VF : Set (E d)) = (convexHull ℝ (VF : Set (E d))).extremePoints ℝ)
    (hG : G ∈ faces (convexHull ℝ (VF : Set (E d)))) :
    cnt (convexHull ℝ (VF : Set (E d))) G 0 = (VF.filter (· ∈ G)).card := by
  rw [cnt_zero_eq hG, ← face_eq_convexHull_filter hG, extremePoints_face_eq hext hG]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x; simp [and_comm]

/-- The vertex faces. -/
lemma kfaces_zero_eq
    (hext : (VF : Set (E d)) = (convexHull ℝ (VF : Set (E d))).extremePoints ℝ) :
    (kfaces_finite_conv VF 0).toFinset = VF.image fun x => ({x} : Set (E d)) := by
  ext v
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Finset.mem_image]
  constructor
  · rintro ⟨hv, hv0⟩
    obtain ⟨x, rfl⟩ := eq_singleton_of_dim_eq_zero hv.1 hv0
    refine ⟨x, ?_, rfl⟩
    have hx : x ∈ (convexHull ℝ (VF : Set (E d))).extremePoints ℝ :=
      isExtreme_singleton.1 hv.2.isExtreme
    rw [← hext] at hx
    exact hx
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ (convexHull ℝ (VF : Set (E d))).extremePoints ℝ := by
      rw [← hext]; exact hx
    exact ⟨singleton_mem_faces_of_extreme hx', dim_singleton x⟩

/-- Facets containing a vertex. -/
lemma upIn_singleton_eq (x : E d) (j : ℕ) :
    upIn (convexHull ℝ (VF : Set (E d))) {x} j =
      ((kfaces_finite_conv VF j).toFinset.filter fun G => x ∈ G).card := by
  rw [upIn, ← Set.ncard_coe_finset]
  congr 1
  ext G
  simp [Set.singleton_subset_iff, and_assoc, and_comm, and_left_comm]

/-- Faces above a face, as a filter. -/
lemma upIn_eq_card_filter (L : Set (E d)) (j : ℕ) :
    upIn (convexHull ℝ (VF : Set (E d))) L j =
      ((kfaces_finite_conv VF j).toFinset.filter fun G => L ⊆ G).card := by
  rw [upIn, ← Set.ncard_coe_finset]
  congr 1
  ext G
  simp [and_assoc, and_comm, and_left_comm]

section prism

variable (hext : (VF : Set (E d)) = (convexHull ℝ (VF : Set (E d))).extremePoints ℝ)
  (h4 : dim (convexHull ℝ (VF : Set (E d))) = 4)
  (hrow : rowOf (convexHull ℝ (VF : Set (E d))) = tRow)
include hext h4 hrow

lemma prism_counts : fvec (convexHull ℝ (VF : Set (E d))) 0 = 8 ∧
    fvec (convexHull ℝ (VF : Set (E d))) 1 = 16 ∧ fvec (convexHull ℝ (VF : Set (E d))) 2 = 14 ∧
    fvec (convexHull ℝ (VF : Set (E d))) 3 = 6 ∧ flag2 (convexHull ℝ (VF : Set (E d))) 0 3 = 32 :=
  ⟨congrArg Row.n hrow, congrArg Row.e hrow, congrArg Row.p hrow, congrArg Row.r hrow,
    congrArg Row.J hrow⟩

lemma prism_card_VF : VF.card = 8 := by
  have h := fvec_zero_eq VF
  rw [← hext, Set.ncard_coe_finset, (prism_counts hext h4 hrow).1] at h
  exact h.symm

/-- **(P1)** Every vertex lies in exactly four facets. -/
lemma prism_r4 : ∀ x ∈ VF, ((kfaces_finite_conv VF 3).toFinset.filter fun G => x ∈ G).card = 4 := by
  have hge : ∀ x ∈ VF, 4 ≤ ((kfaces_finite_conv VF 3).toFinset.filter fun G => x ∈ G).card := by
    intro x hx
    rw [← upIn_singleton_eq]
    have hxext : x ∈ (convexHull ℝ (VF : Set (E d))).extremePoints ℝ := by rw [← hext]; exact hx
    exact vertex_four_le_r rfl h4 (singleton_mem_faces_of_extreme hxext) (dim_singleton x)
  have hsum : ∑ x ∈ VF, ((kfaces_finite_conv VF 3).toFinset.filter fun G => x ∈ G).card = 32 := by
    rw [← (prism_counts hext h4 hrow).2.2.2.2, flag2_eq_sum_upIn_conv, kfaces_zero_eq hext,
      Finset.sum_image (fun x _ y _ h => Set.singleton_injective h)]
    exact Finset.sum_congr rfl fun x _ => (upIn_singleton_eq x 3).symm
  intro x hx
  by_contra hne
  have hlt := lt_of_le_of_ne (hge x hx) (Ne.symm hne)
  have h := Finset.sum_lt_sum hge ⟨x, hx, hlt⟩
  rw [hsum, Finset.sum_const, prism_card_VF hext h4 hrow] at h
  norm_num at h

/-- **(P2)** Every vertex has at least four neighbours. -/
lemma prism_nb : ∀ x ∈ VF, 4 ≤ (VF.filter fun z => z ≠ x ∧
    ∃ L ∈ faces (convexHull ℝ (VF : Set (E d))), dim L = 1 ∧ x ∈ L ∧ z ∈ L).card := by
  intro x hx
  have hxext : x ∈ (convexHull ℝ (VF : Set (E d))).extremePoints ℝ := by rw [← hext]; exact hx
  have hv := singleton_mem_faces_of_extreme hxext
  -- at least four edges through `x`
  have he : 4 ≤ upIn (convexHull ℝ (VF : Set (E d))) {x} 1 := by
    have h1 := vertex_up_dim_four rfl h4 hv (dim_singleton x)
    have h2 := vertex_three_r_le rfl h4 hv (dim_singleton x)
    have h3 : upIn (convexHull ℝ (VF : Set (E d))) {x} 3 = 4 := by
      rw [upIn_singleton_eq]; exact prism_r4 hext h4 hrow x hx
    rw [h3] at h1 h2
    omega
  rw [upIn_singleton_eq] at he
  -- the other endpoint of each edge
  set f : Set (E d) → E d := fun L =>
    if h : ((VF.filter (· ∈ L)).erase x).Nonempty then h.choose else x with hf
  have hedge : ∀ L ∈ (kfaces_finite_conv VF 1).toFinset.filter (fun G => x ∈ G),
      ∃ z, z ≠ x ∧ VF.filter (· ∈ L) = {x, z} := by
    intro L hL
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hL
    have hc := cnt_zero_of_dim_one hL.1.1 hL.1.2
    rw [cnt_zero_face_eq hext hL.1.1] at hc
    have hxL : x ∈ VF.filter (· ∈ L) := Finset.mem_filter.2 ⟨hx, hL.2⟩
    obtain ⟨a, b, hab, hAB⟩ := Finset.card_eq_two.1 hc
    rw [hAB] at hxL
    rcases Finset.mem_insert.1 hxL with rfl | hxb
    · exact ⟨b, hab.symm, hAB⟩
    · rw [Finset.mem_singleton] at hxb
      subst hxb
      exact ⟨a, hab, by rw [hAB, Finset.pair_comm]⟩
  have hfprop : ∀ L ∈ (kfaces_finite_conv VF 1).toFinset.filter (fun G => x ∈ G),
      f L ≠ x ∧ VF.filter (· ∈ L) = {x, f L} := by
    intro L hL
    obtain ⟨z, hzx, hz⟩ := hedge L hL
    have hne : ((VF.filter (· ∈ L)).erase x).Nonempty :=
      ⟨z, by rw [hz]; simp [hzx]⟩
    have hspec := hne.choose_spec
    have hfz : f L = z := by
      simp only [hf, dif_pos hne]
      have h1 := (Finset.mem_erase.1 hspec).1
      have h2 : hne.choose ∈ ({x, z} : Finset (E d)) := by
        rw [← hz]; exact (Finset.mem_erase.1 hspec).2
      rcases Finset.mem_insert.1 h2 with h | h
      · exact absurd h h1
      · exact Finset.mem_singleton.1 h
    rw [hfz]
    exact ⟨hzx, hz⟩
  calc 4 ≤ ((kfaces_finite_conv VF 1).toFinset.filter fun G => x ∈ G).card := he
    _ ≤ _ := by
      apply Finset.card_le_card_of_injOn f
      · intro L hL
        have hL' := hL
        rw [Finset.mem_coe] at hL'
        obtain ⟨hfx, hfL⟩ := hfprop L hL'
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hL'
        have hmem : f L ∈ VF.filter (· ∈ L) := by rw [hfL]; simp
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨(Finset.mem_filter.1 hmem).1, hfx, L, hL'.1.1, hL'.1.2, hL'.2,
          (Finset.mem_filter.1 hmem).2⟩
      · intro L hL L' hL' hLL'
        rw [Finset.mem_coe] at hL hL'
        have h1 := (hfprop L hL).2
        have h2 := (hfprop L' hL').2
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hL hL'
        rw [face_eq_convexHull_filter hL.1.1, face_eq_convexHull_filter hL'.1.1, h1, h2, hLL']

/-- **(P3)** Neighbours share at least three facets. -/
lemma prism_common : ∀ y ∈ VF, ∀ z ∈ VF, z ≠ y →
    (∃ L ∈ faces (convexHull ℝ (VF : Set (E d))), dim L = 1 ∧ y ∈ L ∧ z ∈ L) →
    3 ≤ ((kfaces_finite_conv VF 3).toFinset.filter fun G => y ∈ G ∧ z ∈ G).card := by
  rintro y - z - - ⟨L, hL, hL1, hyL, hzL⟩
  have h := edge_three_le_up rfl h4 hL hL1
  rw [upIn_eq_card_filter] at h
  refine le_trans h (Finset.card_le_card fun G hG => ?_)
  simp only [Finset.mem_filter] at hG ⊢
  exact ⟨hG.1, hG.2 hyL, hG.2 hzL⟩

/-- **(P4)** Every facet has four or six vertices. -/
lemma prism_facet_size : ∀ G ∈ (kfaces_finite_conv VF 3).toFinset,
    (VF.filter (· ∈ G)).card = 4 ∨ (VF.filter (· ∈ G)).card = 6 := by
  set K := convexHull ℝ (VF : Set (E d)) with hK
  set 𝒢 := (kfaces_finite_conv VF 3).toFinset with h𝒢
  obtain ⟨h0, h1, h2, h3, hJ⟩ := prism_counts hext h4 hrow
  have hmem : ∀ G ∈ 𝒢, G ∈ faces K ∧ dim G = 3 := fun G hG => by
    simpa [h𝒢] using hG
  -- Euler and `3 f₀ ≤ 2 f₁` on each facet: `2 f₂ ≥ 4 + f₀`
  have hloc : ∀ G ∈ 𝒢, 4 + (cnt K G 0 : ℤ) ≤ 2 * cnt K G 2 := by
    intro G hG
    obtain ⟨hGf, hG3⟩ := hmem G hG
    have he := euler_face_conv hGf
    rw [hG3] at he
    simp only [Finset.sum_range_succ, Finset.sum_range_zero] at he
    have hc3 : cnt K G 3 = 1 := by have := cnt_self_conv hGf; rwa [hG3] at this
    have h3f := three_fvec_zero_le (VF.filter (· ∈ G))
      (by rw [← face_eq_convexHull_filter hGf]; exact hG3)
    rw [← face_eq_convexHull_filter hGf, fvec_face_eq_cnt hGf, fvec_face_eq_cnt hGf] at h3f
    norm_num at he
    rw [hc3] at he
    push_cast at he
    have : (3 * cnt K G 0 : ℤ) ≤ 2 * cnt K G 1 := by exact_mod_cast h3f
    linarith
  -- the sums: `Σ f₂ = 28`, `Σ f₀ = 32`
  have hs2 : ∑ G ∈ 𝒢, cnt K G 2 = 28 := by
    have e1 := flag2_eq_sum_cnt_conv VF 2 3
    have e2 := flag2_eq_sum_upIn_conv VF 2 3
    rw [e1] at e2
    rw [e2, Finset.sum_congr rfl fun Q hQ => two_face_up_two rfl h4
      ((Set.Finite.mem_toFinset _).1 hQ).1 ((Set.Finite.mem_toFinset _).1 hQ).2,
      Finset.sum_const, smul_eq_mul, card_kfaces_eq_fvec, h2]
  have hs0 : ∑ G ∈ 𝒢, cnt K G 0 = 32 := by
    rw [← hJ, flag2_eq_sum_cnt_conv]
  -- equality in each local inequality
  have heq : ∀ G ∈ 𝒢, 4 + (cnt K G 0 : ℤ) = 2 * cnt K G 2 := by
    have hnn : ∀ G ∈ 𝒢, (0 : ℤ) ≤ 2 * cnt K G 2 - (4 + cnt K G 0) := fun G hG => by
      linarith [hloc G hG]
    have hzero : ∑ G ∈ 𝒢, ((2 * cnt K G 2 : ℤ) - (4 + cnt K G 0)) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const]
      have hc : 𝒢.card = 6 := by rw [h𝒢, card_kfaces_eq_fvec]; exact h3
      have hs2' : (∑ G ∈ 𝒢, (cnt K G 2 : ℤ)) = 28 := by exact_mod_cast hs2
      have hs0' : (∑ G ∈ 𝒢, (cnt K G 0 : ℤ)) = 32 := by exact_mod_cast hs0
      rw [hs2', hs0', hc]
      norm_num
    intro G hG
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hzero G hG
    linarith
  intro G hG
  obtain ⟨hGf, hG3⟩ := hmem G hG
  rw [← cnt_zero_face_eq hext hGf]
  show cnt K G 0 = 4 ∨ cnt K G 0 = 6
  -- `f₀` is even, at least four and at most seven
  have hev := heq G hG
  have hge : 4 ≤ cnt K G 0 := by
    rw [cnt_zero_eq hGf]
    have hne : (VF.filter (· ∈ G)).Nonempty := by
      obtain ⟨g, hg⟩ := hGf.1
      have hGc := face_eq_convexHull_filter hGf
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [hGc, h, Finset.coe_empty, convexHull_empty] at hg
      exact hg
    have := dim_add_one_le_ncard_extremePoints _ hne
    have hd : dim (convexHull ℝ ((VF.filter (· ∈ G) : Finset (E d)) : Set (E d))) = 3 := by
      rw [← face_eq_convexHull_filter hGf]; exact hG3
    rw [hd] at this
    exact this
  have hle : cnt K G 0 ≤ 7 := by
    rw [cnt_zero_face_eq hext hGf]
    by_contra hgt
    push_neg at hgt
    have hall : VF.filter (· ∈ G) = VF := by
      apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
      rw [prism_card_VF hext h4 hrow]; omega
    have hsub : K ⊆ G := by
      rw [hK]
      refine convexHull_min (fun y hy => ?_) (face_convex (convex_convexHull ℝ _) hGf)
      have : y ∈ VF.filter (· ∈ G) := by rw [hall]; exact hy
      exact (Finset.mem_filter.1 this).2
    have hGK : G = K := le_antisymm (face_subset hGf) hsub
    rw [hGK, h4] at hG3
    omega
  have hle' : cnt K G 0 ≤ 7 := hle
  omega

/-- **The prism structure**: four side facets and a labelling of the vertices in which `v_j`
misses exactly the side `S_{j/2}`. -/
theorem prism_sides : ∃ S : Fin 4 → Set (E d),
    (∀ k, S k ∈ faces (convexHull ℝ (VF : Set (E d))) ∧ dim (S k) = 3) ∧
    ∃ v : Fin 8 → E d, Function.Injective v ∧ (∀ j, v j ∈ VF) ∧ (∀ x ∈ VF, ∃ j, x = v j) ∧
      ∀ k j, (v j ∈ S k ↔ j.val / 2 ≠ k.val) := by
  set 𝒢 := (kfaces_finite_conv VF 3).toFinset with h𝒢
  have h𝒢card : 𝒢.card = 6 := by
    rw [h𝒢, card_kfaces_eq_fvec]; exact (prism_counts hext h4 hrow).2.2.2.1
  have hVF := prism_card_VF hext h4 hrow
  have hmiss : ∀ y ∈ VF, (missF 𝒢 (fun x G => x ∈ G) y).card = 2 := by
    intro y hy
    have h := Finset.card_filter_add_card_filter_not (s := 𝒢) (p := fun G => y ∈ G)
    rw [prism_r4 hext h4 hrow y hy, h𝒢card] at h
    simp only [missF]
    omega
  have hout : ∀ G ∈ 𝒢, (outV VF (fun x G => x ∈ G) G).card = 2 ∨
      (outV VF (fun x G => x ∈ G) G).card = 4 := by
    intro G hG
    have h := Finset.card_filter_add_card_filter_not (s := VF) (p := fun x => x ∈ G)
    rw [hVF] at h
    simp only [outV]
    rcases prism_facet_size hext h4 hrow G hG with h4' | h6 <;> omega
  have hside := miss_side_card VF 𝒢 (fun x G => x ∈ G)
    (fun y z => ∃ L ∈ faces (convexHull ℝ (VF : Set (E d))), dim L = 1 ∧ y ∈ L ∧ z ∈ L)
    hmiss (prism_nb hext h4 hrow) (prism_common hext h4 hrow) hout h𝒢card hVF
  -- the four sides
  set 𝒮 := 𝒢.filter fun G => (outV VF (fun x G => x ∈ G) G).card = 2 with h𝒮
  have h𝒮card : 𝒮.card = 4 := by
    have hdc := double_count VF 𝒢
      (fun y G => ¬ y ∈ G ∧ (outV VF (fun x G => x ∈ G) G).card = 2)
    have hl : ∀ y ∈ VF, (𝒢.filter fun G => ¬ y ∈ G ∧
        (outV VF (fun x G => x ∈ G) G).card = 2).card = 1 := by
      intro y hy
      have := hside y hy
      rwa [missF, Finset.filter_filter] at this
    rw [Finset.sum_congr rfl hl, Finset.sum_const, hVF] at hdc
    have hr : ∀ G ∈ 𝒢, (VF.filter fun y => ¬ y ∈ G ∧
        (outV VF (fun x G => x ∈ G) G).card = 2).card =
        if (outV VF (fun x G => x ∈ G) G).card = 2 then 2 else 0 := by
      intro G _
      split_ifs with h
      · simp only [h, and_true]; exact h
      · simp [h]
    rw [Finset.sum_congr rfl hr, ← Finset.sum_filter, ← h𝒮, Finset.sum_const] at hdc
    simp only [smul_eq_mul] at hdc
    omega
  have hS𝒢 : ∀ G ∈ 𝒮, G ∈ 𝒢 := fun G hG => (Finset.mem_filter.1 hG).1
  set e := Finset.equivFinOfCardEq h𝒮card with he
  set S : Fin 4 → Set (E d) := fun k => (e.symm k : Set (E d)) with hS
  have hSmem : ∀ k, S k ∈ 𝒮 := fun k => (e.symm k).2
  have hSinj : Function.Injective S := fun k k' h => e.symm.injective (Subtype.ext h)
  have hSout : ∀ k, (outV VF (fun x G => x ∈ G) (S k)).card = 2 := fun k =>
    (Finset.mem_filter.1 (hSmem k)).2
  -- a vertex misses at most one side
  have huniq : ∀ x ∈ VF, ∀ k k', x ∉ S k → x ∉ S k' → k = k' := by
    intro x hx k k' hk hk'
    have h1 := hside x hx
    rw [Finset.card_eq_one] at h1
    obtain ⟨G, hG⟩ := h1
    have hmk : S k ∈ (missF 𝒢 (fun x G => x ∈ G) x).filter
        (fun G => (outV VF (fun x G => x ∈ G) G).card = 2) :=
      Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hS𝒢 _ (hSmem k), hk⟩, hSout k⟩
    have hmk' : S k' ∈ (missF 𝒢 (fun x G => x ∈ G) x).filter
        (fun G => (outV VF (fun x G => x ∈ G) G).card = 2) :=
      Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hS𝒢 _ (hSmem k'), hk'⟩, hSout k'⟩
    rw [hG, Finset.mem_singleton] at hmk hmk'
    exact hSinj (hmk.trans hmk'.symm)
  -- the two vertices missed by each side
  have hpair : ∀ k, ∃ a b : E d, a ≠ b ∧ outV VF (fun x G => x ∈ G) (S k) = {a, b} :=
    fun k => Finset.card_eq_two.1 (hSout k)
  choose a b hab habS using hpair
  refine ⟨S, fun k => by
      have h := hS𝒢 _ (hSmem k)
      rw [h𝒢, Set.Finite.mem_toFinset] at h
      exact h,
    fun j => if j.val % 2 = 0 then a ⟨j / 2, by omega⟩ else b ⟨j / 2, by omega⟩, ?_⟩
  -- membership of the labelled vertices
  have hvout : ∀ j : Fin 8, (if j.val % 2 = 0 then a ⟨j / 2, by omega⟩ else b ⟨j / 2, by omega⟩)
      ∈ outV VF (fun x G => x ∈ G) (S ⟨j / 2, by omega⟩) := by
    intro j
    rw [habS]
    split_ifs <;> simp
  have hvVF : ∀ j : Fin 8, (if j.val % 2 = 0 then a ⟨j / 2, by omega⟩ else b ⟨j / 2, by omega⟩)
      ∈ VF := fun j => (Finset.mem_filter.1 (hvout j)).1
  have hprop : ∀ (k : Fin 4) (j : Fin 8),
      ((if j.val % 2 = 0 then a ⟨j / 2, by omega⟩ else b ⟨j / 2, by omega⟩) ∈ S k ↔
        j.val / 2 ≠ k.val) := by
    intro k j
    have hnot := (Finset.mem_filter.1 (hvout j)).2
    have hj4 : (j : ℕ) / 2 < 4 := by omega
    constructor
    · intro hin heq
      have hk : (⟨j / 2, hj4⟩ : Fin 4) = k := Fin.ext heq
      rw [← hk] at hin
      exact hnot hin
    · intro hne
      by_contra hin
      exact hne (congrArg Fin.val (huniq _ (hvVF j) k ⟨j / 2, by omega⟩ hin hnot)).symm
  refine ⟨fun j j' h => ?_, hvVF, fun x hx => ?_, hprop⟩
  · -- injectivity
    have hk : j.val / 2 = j'.val / 2 := by
      have h1 := (hprop ⟨j / 2, by omega⟩ j).not.2 (by simp)
      simp only at h
      rw [h] at h1
      have h2 := (hprop ⟨j / 2, by omega⟩ j').not.1 h1
      push_neg at h2
      exact h2.symm
    simp only at h
    ext
    by_cases hj : j.val % 2 = 0 <;> by_cases hj' : j'.val % 2 = 0
    · omega
    · rw [if_pos hj, if_neg hj'] at h
      have : (⟨j / 2, by omega⟩ : Fin 4) = ⟨j' / 2, by omega⟩ := Fin.ext hk
      rw [this] at h
      exact absurd h (hab _)
    · rw [if_neg hj, if_pos hj'] at h
      have : (⟨j / 2, by omega⟩ : Fin 4) = ⟨j' / 2, by omega⟩ := Fin.ext hk
      rw [this] at h
      exact absurd h.symm (hab _)
    · omega
  · -- every vertex is labelled
    have h1 := hside x hx
    rw [Finset.card_eq_one] at h1
    obtain ⟨G, hG⟩ := h1
    have hGm : G ∈ (missF 𝒢 (fun x G => x ∈ G) x).filter
        (fun G => (outV VF (fun x G => x ∈ G) G).card = 2) := by rw [hG]; simp
    have hG𝒮 : G ∈ 𝒮 := Finset.mem_filter.2 ⟨(Finset.mem_filter.1
      (Finset.mem_filter.1 hGm).1).1, (Finset.mem_filter.1 hGm).2⟩
    have hxG : x ∉ G := (Finset.mem_filter.1 (Finset.mem_filter.1 hGm).1).2
    set k := e ⟨G, hG𝒮⟩ with hk
    have hSk : S k = G := by simp [hS, hk]
    have hxout : x ∈ outV VF (fun x G => x ∈ G) (S k) := by
      rw [hSk]; exact Finset.mem_filter.2 ⟨hx, hxG⟩
    rw [habS] at hxout
    rcases Finset.mem_insert.1 hxout with h | h
    · refine ⟨⟨2 * k, by omega⟩, ?_⟩
      simp only
      rw [if_pos (by omega)]
      have : (⟨2 * (k : ℕ) / 2, by omega⟩ : Fin 4) = k := by ext; simp only; omega
      rw [this]; exact h
    · refine ⟨⟨2 * k + 1, by omega⟩, ?_⟩
      simp only
      rw [if_neg (by omega)]
      have : (⟨(2 * (k : ℕ) + 1) / 2, by omega⟩ : Fin 4) = k := by ext; simp only; omega
      rw [this]; exact Finset.mem_singleton.1 h

end prism

end

end Kalai5
