import Kalai5.Polar.Relative
import Kalai5.Endpoints.Fourteen

/-!
# Recognizing a pyramid from its flag row

A 4-polytope with 7 vertices, 6 facets and `f₀₃ = 29` is a pyramid: some facet contains all
vertices but one (`pyramid_of_counts`).  The proof uses polarity instead of Gale diagrams:

* every vertex lies in at least 4 facets (its dual face is a 3-polytope, with ≥ 4 vertices);
* `f₀₃ = 29 = 4·7 + 1`, so one vertex `v` lies in 5 facets and every other vertex in exactly 4;
* exactly one facet `T₀` misses `v`; if another vertex `w` missed `T₀`, every facet through `w`
  would contain `v`, so every vertex of `w♦` lies in `v♦`, hence `w♦ ⊆ v♦`; both are facets of
  the polar, so `w♦ = v♦` and `w = v`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

lemma kfaces_finite_conv (V : Finset (E d)) (k : ℕ) :
    {F | F ∈ faces (convexHull ℝ (V : Set (E d))) ∧ dim F = k}.Finite :=
  (faces_finite_convexHull V).subset fun _ hF => hF.1

/-- `flag2 K i j = Σ_{i-faces G} #{j-faces above G}` for any polytope. -/
lemma flag2_eq_sum_upIn_conv (V : Finset (E d)) (i j : ℕ) :
    flag2 (convexHull ℝ (V : Set (E d))) i j =
      ∑ G ∈ (kfaces_finite_conv V i).toFinset, upIn (convexHull ℝ (V : Set (E d))) G j := by
  classical
  have hfin := faces_finite_convexHull V
  have hS : {FG : Set (E d) × Set (E d) | FG.1 ∈ faces (convexHull ℝ (V : Set (E d))) ∧
      FG.2 ∈ faces (convexHull ℝ (V : Set (E d))) ∧ FG.1 ⊆ FG.2 ∧
      dim FG.1 = i ∧ dim FG.2 = j}.Finite :=
    (hfin.prod hfin).subset fun FG h => ⟨h.1, h.2.1⟩
  rw [flag2, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (kfaces_finite_conv V i).toFinset)
      (fun FG hFG => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFG
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFG.1, hFG.2.2.2.1⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Set.Finite.mem_toFinset] at hG
  have hfinG : {H | H ∈ faces (convexHull ℝ (V : Set (E d))) ∧ G ⊆ H ∧ dim H = j}.Finite :=
    hfin.subset fun H hH => hH.1
  rw [upIn, Set.ncard_eq_toFinset_card _ hfinG]
  refine Finset.card_nbij' Prod.snd (fun H => (G, H)) ?_ ?_ ?_ ?_
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨-, h2, h3, -, h5⟩, h⟩ := hFG
    exact ⟨h2, h ▸ h3, h5⟩
  · intro H hH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hH.1, hH.2.1, hG.2, hH.2.2⟩, rfl⟩
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter] at hFG
    obtain ⟨-, h⟩ := hFG
    ext <;> simp [h]
  · intro H _; rfl

/-- **A 3-face has at least four vertices.** -/
lemma four_le_cnt_zero_of_dim_three {V : Finset (E d)} {F : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (h3 : dim F = 3) :
    4 ≤ cnt (convexHull ℝ (V : Set (E d))) F 0 := by
  classical
  rw [cnt_zero_eq hF]
  have hS : (V.filter (· ∈ F)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := face_eq_convexHull_filter hF
    rw [h, Finset.coe_empty, convexHull_empty] at this
    obtain ⟨x, hx⟩ := hF.1; rw [this] at hx; exact hx
  have := dim_add_one_le_ncard_extremePoints _ hS
  rw [← face_eq_convexHull_filter hF] at this ⊢
  rw [h3] at this
  omega

/-- **A 4-polytope with 7 vertices, 6 facets and `f₀₃ = 29` is a pyramid**: some facet contains
every vertex except one. -/
theorem pyramid_of_counts {k : ℕ} (hk : k = 4) {V : Finset (E k)}
    (h0 : (0 : E k) ∈ interior (convexHull ℝ (V : Set (E k))))
    (hv : fvec (convexHull ℝ (V : Set (E k))) 0 = 7)
    (hf : fvec (convexHull ℝ (V : Set (E k))) 3 = 6)
    (hJ : flag2 (convexHull ℝ (V : Set (E k))) 0 3 = 29) :
    ∃ v T, v ∈ faces (convexHull ℝ (V : Set (E k))) ∧ dim v = 0 ∧
      T ∈ faces (convexHull ℝ (V : Set (E k))) ∧ dim T = 3 ∧ ¬ v ⊆ T ∧
      ∀ w ∈ faces (convexHull ℝ (V : Set (E k))), dim w = 0 → w ≠ v → w ⊆ T := by
  subst hk
  classical
  have hdimK : dim (convexHull ℝ (V : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E 4) ∈ interior (convexHull ℝ (W : Set (E 4))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (polarSet (convexHull ℝ (V : Set (E 4)))) =
      convexHull ℝ (V : Set (E 4)) :=
    polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  have hneK : ∀ G ∈ faces (convexHull ℝ (V : Set (E 4))), dim G ≤ 3 →
      G ≠ convexHull ℝ (V : Set (E 4)) := fun G _ hG h => by
    rw [h, hdimK] at hG; omega
  -- every vertex lies in at least four facets
  have hup4 : ∀ w ∈ faces (convexHull ℝ (V : Set (E 4))), dim w = 0 →
      4 ≤ upIn (convexHull ℝ (V : Set (E 4))) w 3 := by
    intro w hw hw0
    have hne := hneK w hw (by omega)
    rw [upIn_eq_cnt_dualFace h0 hw hne 3 (by norm_num), show 4 - 1 - 3 = 0 by norm_num]
    have hmem := dualFace_mem_faces h0 hw hne
    have hdim := dim_dualFace h0 hw hne
    rw [hW] at hmem ⊢
    exact four_le_cnt_zero_of_dim_three hmem (by omega)
  -- the vertex with five facets
  set S := (kfaces_finite_conv V 0).toFinset with hS
  have hScard : S.card = 7 := by
    rw [← hv, fvec, Set.ncard_eq_toFinset_card _ (kfaces_finite_conv V 0)]
  have hsum : ∑ w ∈ S, upIn (convexHull ℝ (V : Set (E 4))) w 3 = 29 := by
    rw [← hJ, flag2_eq_sum_upIn_conv]
  have hge : ∀ w ∈ S, 4 ≤ upIn (convexHull ℝ (V : Set (E 4))) w 3 := fun w hw => by
    rw [hS, Set.Finite.mem_toFinset] at hw
    exact hup4 w hw.1 hw.2
  have hex : ∃ v ∈ S, 5 ≤ upIn (convexHull ℝ (V : Set (E 4))) v 3 := by
    by_contra hcon
    push_neg at hcon
    have : ∑ w ∈ S, upIn (convexHull ℝ (V : Set (E 4))) w 3 ≤ ∑ _w ∈ S, 4 :=
      Finset.sum_le_sum fun w hw => by have := hcon w hw; omega
    rw [Finset.sum_const, hScard, smul_eq_mul] at this
    omega
  obtain ⟨v, hvS, hv5⟩ := hex
  have hvS' := hvS
  rw [hS, Set.Finite.mem_toFinset] at hvS'
  have hrest : ∀ T ⊆ S, 4 * T.card ≤ ∑ w ∈ T, upIn (convexHull ℝ (V : Set (E 4))) w 3 :=
    fun T hT => by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      exact Finset.sum_le_sum fun w hw => hge w (hT hw)
  have hothers : ∀ w ∈ S, w ≠ v → upIn (convexHull ℝ (V : Set (E 4))) w 3 = 4 := by
    intro w hwS hwv
    have hwS' : w ∈ S.erase v := Finset.mem_erase.2 ⟨hwv, hwS⟩
    have h1 := Finset.add_sum_erase S (fun x => upIn (convexHull ℝ (V : Set (E 4))) x 3) hvS
    have h2 := Finset.add_sum_erase (S.erase v)
      (fun x => upIn (convexHull ℝ (V : Set (E 4))) x 3) hwS'
    have h3 := hrest ((S.erase v).erase w)
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
    have hc1 : (S.erase v).card = 6 := by rw [Finset.card_erase_of_mem hvS, hScard]
    have hc2 : ((S.erase v).erase w).card = 5 := by rw [Finset.card_erase_of_mem hwS', hc1]
    have hw4 := hge w hwS
    omega
  -- facets: one misses `v`
  have hfin3 : {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ dim T = 3}.Finite :=
    kfaces_finite_conv V 3
  have hv5' : upIn (convexHull ℝ (V : Set (E 4))) v 3 = 5 := by
    have h1 := Finset.add_sum_erase S (fun x => upIn (convexHull ℝ (V : Set (E 4))) x 3) hvS
    have h3 := hrest (S.erase v) (Finset.erase_subset _ _)
    have hc1 : (S.erase v).card = 6 := by rw [Finset.card_erase_of_mem hvS, hScard]
    omega
  have hmiss : {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ ¬ v ⊆ T ∧ dim T = 3}.ncard = 1 := by
    have hunion : {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ dim T = 3} =
        {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ v ⊆ T ∧ dim T = 3} ∪
          {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ ¬ v ⊆ T ∧ dim T = 3} := by
      ext T
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_cases h : v ⊆ T <;> simp [h]
    have hdisj : Disjoint
        {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ v ⊆ T ∧ dim T = 3}
        {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ ¬ v ⊆ T ∧ dim T = 3} := by
      rw [Set.disjoint_left]
      rintro T ⟨-, h1, -⟩ ⟨-, h2, -⟩
      exact h2 h1
    have hcount := Set.ncard_union_eq hdisj (hfin3.subset fun T hT => ⟨hT.1, hT.2.2⟩)
      (hfin3.subset fun T hT => ⟨hT.1, hT.2.2⟩)
    rw [← hunion] at hcount
    have hf' : {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ dim T = 3}.ncard = 6 := hf
    have hv5'' : {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ v ⊆ T ∧ dim T = 3}.ncard = 5 :=
      hv5'
    omega
  obtain ⟨T0, hT0⟩ := Set.ncard_eq_one.1 hmiss
  have hT0mem : T0 ∈ {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ ¬ v ⊆ T ∧ dim T = 3} := by
    rw [hT0]; exact Set.mem_singleton _
  obtain ⟨hT0f, hvT0, hT0d⟩ := hT0mem
  refine ⟨v, T0, hvS'.1, hvS'.2, hT0f, hT0d, hvT0, fun w hw hw0 hwv => ?_⟩
  by_contra hwT0
  -- every facet through `w` contains `v`
  have hclaim : ∀ T ∈ faces (convexHull ℝ (V : Set (E 4))), dim T = 3 → w ⊆ T → v ⊆ T := by
    intro T hT hT3 hwT
    by_contra hvT
    have hmem : T ∈ {T | T ∈ faces (convexHull ℝ (V : Set (E 4))) ∧ ¬ v ⊆ T ∧ dim T = 3} :=
      ⟨hT, hvT, hT3⟩
    rw [hT0] at hmem
    rw [Set.mem_singleton_iff.1 hmem] at hwT
    exact hwT0 hwT
  -- dual faces
  have hwne := hneK w hw (by rw [hw0]; norm_num)
  have hvne := hneK v hvS'.1 (by rw [hvS'.2]; norm_num)
  have hwD := dualFace_mem_faces h0 hw hwne
  have hvD := dualFace_mem_faces h0 hvS'.1 hvne
  have hwDdim := dim_dualFace h0 hw hwne
  have hvDdim := dim_dualFace h0 hvS'.1 hvne
  have hwdd := dualFace_dualFace h0 hw hwne
  rw [hW] at hwD hvD hwdd
  -- every extreme point of `w♦` lies in `v♦`
  have hext : ∀ x ∈ (dualFace (convexHull ℝ (V : Set (E 4))) w).extremePoints ℝ,
      x ∈ dualFace (convexHull ℝ (V : Set (E 4))) v := by
    intro x hx
    have hxK : x ∈ (convexHull ℝ (W : Set (E 4))).extremePoints ℝ :=
      (hwD.2.isExtreme).extremePoints_subset_extremePoints hx
    have hxF : ({x} : Set (E 4)) ∈ faces (convexHull ℝ (W : Set (E 4))) :=
      singleton_mem_faces_of_extreme hxK
    have hxdim : dim ({x} : Set (E 4)) = 0 := dim_singleton x
    have hxne : ({x} : Set (E 4)) ≠ convexHull ℝ (W : Set (E 4)) := by
      intro h
      have := dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩
      rw [← h, hxdim] at this
      omega
    have hTmem := dualFace_mem_faces h0W hxF hxne
    have hTdim := dim_dualFace h0W hxF hxne
    have hTdd := dualFace_dualFace h0W hxF hxne
    have hwT : w ⊆ dualFace (convexHull ℝ (W : Set (E 4))) {x} := by
      have hsub : ({x} : Set (E 4)) ⊆ dualFace (convexHull ℝ (V : Set (E 4))) w :=
        Set.singleton_subset_iff.2 hx.1
      have := dualFace_antitone (K := convexHull ℝ (W : Set (E 4))) hsub
      rwa [hwdd] at this
    rw [← hW] at hTmem hTdim hTdd hwT
    rw [hbip] at hTmem hTdd
    have hvT := hclaim _ hTmem (by omega) hwT
    have := dualFace_antitone (K := convexHull ℝ (V : Set (E 4))) hvT
    rw [hTdd] at this
    exact this (Set.mem_singleton x)
  -- hence `w♦ ⊆ v♦`
  have hsubD : dualFace (convexHull ℝ (V : Set (E 4))) w ⊆
      dualFace (convexHull ℝ (V : Set (E 4))) v := by
    have hconv : dualFace (convexHull ℝ (V : Set (E 4))) w =
        convexHull ℝ ((dualFace (convexHull ℝ (V : Set (E 4))) w).extremePoints ℝ) := by
      set SW := W.filter (· ∈ dualFace (convexHull ℝ (V : Set (E 4))) w)
      have h1 := face_eq_convexHull_filter hwD
      rw [h1, convexHull_extremePoints_eq]
    rw [hconv]
    exact convexHull_min hext (face_convex (convex_convexHull ℝ _) hvD)
  -- both are facets of the polar, so they coincide
  have heqD : dualFace (convexHull ℝ (V : Set (E 4))) w =
      dualFace (convexHull ℝ (V : Set (E 4))) v := by
    by_contra hne
    have hface := mem_faces_of_subset (face_subset hvD) hwD hsubD
    have := dim_lt_of_mem_faces_ne hface hne
    omega
  apply hwv
  rw [eq_of_dualFace h0 hw hwne, eq_of_dualFace h0 hvS'.1 hvne, heqD]


/-! ### Transport of face and flag numbers -/

section transportCounts

variable {K : Set (E d)} {p : E d}

lemma fvec_affEmb (hp : p ∈ K) (j : ℕ) : fvec K j = fvec (affEmb K p ⁻¹' K) j := by
  unfold fvec
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hd⟩
    exact ⟨image_mem_faces hp hF, by rw [dim_image_affEmb]; exact hd⟩
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hd⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, ?_⟩,
      Set.image_preimage_eq_of_subset hFr⟩
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
    rw [Set.image_preimage_eq_of_subset hFr] at this
    rw [← this]; exact hd

lemma flag2_affEmb (hp : p ∈ K) (i j : ℕ) : flag2 K i j = flag2 (affEmb K p ⁻¹' K) i j := by
  unfold flag2
  symm
  refine Set.ncard_congr (fun FG _ => (affEmb K p '' FG.1, affEmb K p '' FG.2)) ?_ ?_ ?_
  · rintro ⟨F, G⟩ ⟨hF, hG, hFG, hdF, hdG⟩
    exact ⟨image_mem_faces hp hF, image_mem_faces hp hG, Set.image_mono hFG,
      by rw [dim_image_affEmb]; exact hdF, by rw [dim_image_affEmb]; exact hdG⟩
  · rintro ⟨F, G⟩ ⟨F', G'⟩ _ _ h
    simp only [Prod.mk.injEq] at h
    have hinj := Set.image_injective.2 (affEmb_injective (K := K) p)
    exact Prod.ext (hinj h.1) (hinj h.2)
  · rintro ⟨F, G⟩ ⟨hF, hG, hFG, hdF, hdG⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    have hGr := subset_range_affEmb hp (face_subset hG)
    refine ⟨(affEmb K p ⁻¹' F, affEmb K p ⁻¹' G),
      ⟨preimage_mem_faces hp hF, preimage_mem_faces hp hG, Set.preimage_mono hFG, ?_, ?_⟩, ?_⟩
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
      rw [Set.image_preimage_eq_of_subset hFr] at this
      rw [← this]; exact hdF
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' G)
      rw [Set.image_preimage_eq_of_subset hGr] at this
      rw [← this]; exact hdG
    · simp only [Set.image_preimage_eq_of_subset hFr, Set.image_preimage_eq_of_subset hGr]

end transportCounts

/-- **Pyramid recognition for a 4-dimensional polytope in any `E d`.** -/
theorem pyramid_of_counts' {K : Set (E d)} {V : Finset (E d)}
    (hK : K = convexHull ℝ (V : Set (E d))) (h4 : dim K = 4)
    (hv : fvec K 0 = 7) (hf : fvec K 3 = 6) (hJ : flag2 K 0 3 = 29) :
    ∃ v T, v ∈ faces K ∧ dim v = 0 ∧ T ∈ faces K ∧ dim T = 3 ∧ ¬ v ⊆ T ∧
      ∀ w ∈ faces K, dim w = 0 → w ≠ v → w ⊆ T := by
  have hne : K.Nonempty := by
    have hS : {F | F ∈ faces K ∧ dim F = 0}.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      have h7 := hv
      rw [fvec, h, Set.ncard_empty] at h7
      omega
    obtain ⟨F, hF, -⟩ := hS
    obtain ⟨x, hx⟩ := hF.1
    exact ⟨x, face_subset hF hx⟩
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK hne
  have hv' : fvec (convexHull ℝ (V' : Set (E (dim K)))) 0 = 7 := by
    rw [← hV', ← fvec_affEmb hp]; exact hv
  have hf' : fvec (convexHull ℝ (V' : Set (E (dim K)))) 3 = 6 := by
    rw [← hV', ← fvec_affEmb hp]; exact hf
  have hJ' : flag2 (convexHull ℝ (V' : Set (E (dim K)))) 0 3 = 29 := by
    rw [← hV', ← flag2_affEmb hp]; exact hJ
  obtain ⟨v', T', hv'f, hv'd, hT'f, hT'd, hvT', hall⟩ := pyramid_of_counts h4 h0 hv' hf' hJ'
  rw [← hV'] at hv'f hT'f hall
  refine ⟨affEmb K p '' v', affEmb K p '' T', image_mem_faces hp hv'f,
    by rw [dim_image_affEmb]; exact hv'd, image_mem_faces hp hT'f,
    by rw [dim_image_affEmb]; exact hT'd, ?_, ?_⟩
  · rw [Set.image_subset_image_iff (affEmb_injective p)]
    exact hvT'
  · intro w hw hw0 hwv
    have hwr := subset_range_affEmb hp (face_subset hw)
    have hww : affEmb K p '' (affEmb K p ⁻¹' w) = w := Set.image_preimage_eq_of_subset hwr
    have hw' := preimage_mem_faces hp hw
    have hw'd : dim (affEmb K p ⁻¹' w) = 0 := by
      have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' w)
      rw [hww, hw0] at this
      omega
    have hw'v : affEmb K p ⁻¹' w ≠ v' := fun h => hwv (by rw [← hww, h])
    have := hall _ hw' hw'd hw'v
    rw [← hww]
    exact Set.image_mono this

/-! ### The exceptional facet of a centrally symmetric 5-polytope -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A facet with row `(7,15,14,6; 29)` is a pyramid**: an apex vertex `v` and a 3-face `T`
containing every other vertex of the facet. -/
theorem IsCSPolytope5.pyramid_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = excRow) :
    ∃ v T, v ∈ faces P ∧ dim v = 0 ∧ v ⊆ F ∧ T ∈ faces P ∧ dim T = 3 ∧ T ⊆ F ∧ ¬ v ⊆ T ∧
      ∀ w ∈ faces P, dim w = 0 → w ⊆ F → w ≠ v → w ⊆ T := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hn : cnt P F 0 = 7 := congrArg Row.n hrow
  have hr : cnt P F 3 = 6 := congrArg Row.r hrow
  have hJ : incid P F 0 3 = 29 := congrArg Row.J hrow
  have hv : fvec F 0 = 7 := by rw [fvec_face_eq_cnt hF', ← hV]; exact hn
  have hf : fvec F 3 = 6 := by rw [fvec_face_eq_cnt hF', ← hV]; exact hr
  have hJ' : flag2 F 0 3 = 29 := by rw [flag2_face_eq_incid hF', ← hV]; exact hJ
  obtain ⟨v, T, hvF, hv0, hTF, hT3, hvT, hall⟩ := pyramid_of_counts' hFV h4 hv hf hJ'
  rw [mem_faces_face_iff hF', ← hV] at hvF hTF
  refine ⟨v, T, hvF.1, hv0, hvF.2, hTF.1, hT3, hTF.2, hvT, fun w hw hw0 hwF hwv => ?_⟩
  have hwF' : w ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ hw, hwF⟩
  exact hall w hwF' hw0 hwv

end cs

end Kalai5
