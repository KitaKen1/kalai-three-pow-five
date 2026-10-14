import Kalai5.Gale.ClassifyX
import Kalai5.Rows.Dual
import Kalai5.Polar.Intervals
import Kalai5.Faces.Symmetry

/-!
# Three-faces with six vertices: type facts and ridge parity

* `facetSizeCnt K k`: the number of 3-faces of `K` with `k` vertices; `vertDegCnt K k`: the number
  of vertices of `K` in `k` three-faces.  Polarity exchanges them (`facetSizeCnt_polar`).
* From the extended classification (`smallX_classification`):
  - a facet with row `excRow = (7,15,14,6; 29)` (the pyramid over a triangular prism) has exactly
    one 3-face with six vertices;
  - a facet with row `zRow = (8,19,18,7; 35)` has exactly two (its polar has row
    `(7,18,19,8; 35)` and two vertices in six 3-faces).
* **Ridge parity** (`IsCSPolytope5.four_dvd_sum_six3`): every 3-face lies in exactly two facets and
  the 3-faces with six vertices come in antipodal pairs, so
  `Σ_F #{3-faces of F with six vertices} ≡ 0 (mod 4)`.
-/

namespace Kalai5

open Set

variable {d : ℕ}

/-! ### Counting through a covering profile -/

lemma ncard_filter_of_cover {α β : Type*} [DecidableEq β] {S : Set α} (hS : S.Finite)
    (f : α → β) {L : List β} (hL : L.Nodup)
    (hcov : (L.map fun t => {x | x ∈ S ∧ f x = t}.ncard).sum = S.ncard)
    (π : β → Prop) [DecidablePred π] :
    {x | x ∈ S ∧ π (f x)}.ncard =
      ((L.filter fun t => decide (π t)).map fun t => {x | x ∈ S ∧ f x = t}.ncard).sum := by
  classical
  set s := hS.toFinset with hsdef
  have hfib : ∀ t, {x | x ∈ S ∧ f x = t}.ncard = (s.filter fun x => f x = t).card := by
    intro t
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [s]
  have hsum : ∀ M : List β, M.Nodup →
      (M.map fun t => {x | x ∈ S ∧ f x = t}.ncard).sum = (s.filter fun x => f x ∈ M).card := by
    intro M hM
    rw [← List.sum_toFinset _ hM]
    have h1 := Finset.card_eq_sum_card_fiberwise (f := f) (s := s.filter fun x => f x ∈ M)
      (t := M.toFinset) (fun x hx => by
        rw [Finset.mem_coe, Finset.mem_filter] at hx
        exact List.mem_toFinset.2 hx.2)
    rw [h1]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hfib]
    congr 1
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, rfl⟩
      exact ⟨⟨hx, List.mem_toFinset.1 ht⟩, rfl⟩
    · rintro ⟨⟨hx, -⟩, h⟩
      exact ⟨hx, h⟩
  have hall : ∀ x ∈ s, f x ∈ L := by
    have h := hsum L hL
    have hS' : S.ncard = s.card := Set.ncard_eq_toFinset_card S hS
    have h' : (s.filter fun x => f x ∈ L).card = s.card := by rw [← h, hcov, hS']
    exact Finset.filter_card_eq h'
  rw [hsum _ (hL.filter _)]
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, hπ⟩
    have hxs : x ∈ s := by rw [hsdef, Set.Finite.mem_toFinset]; exact hx
    exact ⟨hxs, hall x hxs, hπ⟩
  · rintro ⟨hxs, -, hπ⟩
    rw [hsdef, Set.Finite.mem_toFinset] at hxs
    exact ⟨hxs, hπ⟩

/-! ### Facet sizes and vertex degrees -/

/-- The number of 3-faces of `K` with exactly `k` vertices. -/
noncomputable def facetSizeCnt (K : Set (E d)) (k : ℕ) : ℕ :=
  {G | G ∈ faces K ∧ dim G = 3 ∧ cnt K G 0 = k}.ncard

/-- The number of vertices of `K` lying in exactly `k` three-faces. -/
noncomputable def vertDegCnt (K : Set (E d)) (k : ℕ) : ℕ :=
  {G | G ∈ faces K ∧ dim G = 0 ∧ upIn K G 3 = k}.ncard

lemma fv7_nodup : fv7.Nodup := by decide

/-- Facet sizes from a covering facet profile. -/
lemma facetSizeCnt_eq_of_cover {K : Set (E d)} (hfin : (faces K).Finite)
    (hcov : (fv7.map (facetCnt K)).sum = fvec K 3) (k : ℕ) :
    facetSizeCnt K k = ((fv7.filter fun t => decide (t.1 = k)).map (facetCnt K)).sum := by
  have hS : {G | G ∈ faces K ∧ dim G = 3}.Finite := hfin.subset fun G hG => hG.1
  have hfibre : ∀ t, {x | x ∈ {G | G ∈ faces K ∧ dim G = 3} ∧ triBelow K x = t}.ncard =
      facetCnt K t := by
    intro t
    unfold facetCnt
    congr 1
    ext G
    simp only [Set.mem_ofPred_eq, and_assoc]
  have h := ncard_filter_of_cover hS (triBelow K) fv7_nodup (by
    simp only [hfibre]
    exact hcov) (fun t => t.1 = k)
  simp only [hfibre] at h
  rw [← h]
  unfold facetSizeCnt
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, and_assoc, triBelow]

/-- Vertex degrees from a covering vertex profile. -/
lemma vertDegCnt_eq_of_cover {K : Set (E d)} (hfin : (faces K).Finite)
    (hcov : (fv7.map (vertCnt K)).sum = fvec K 0) (k : ℕ) :
    vertDegCnt K k = ((fv7.filter fun t => decide (t.2.2 = k)).map (vertCnt K)).sum := by
  have hS : {G | G ∈ faces K ∧ dim G = 0}.Finite := hfin.subset fun G hG => hG.1
  have hfibre : ∀ t, {x | x ∈ {G | G ∈ faces K ∧ dim G = 0} ∧ triAbove K x = t}.ncard =
      vertCnt K t := by
    intro t
    unfold vertCnt
    congr 1
    ext G
    simp only [Set.mem_ofPred_eq, and_assoc]
  have h := ncard_filter_of_cover hS (triAbove K) fv7_nodup (by
    simp only [hfibre]
    exact hcov) (fun t => t.2.2 = k)
  simp only [hfibre] at h
  rw [← h]
  unfold vertDegCnt
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq, and_assoc, triAbove]

/-! ### Transport -/

section transport

variable {K : Set (E d)} {p : E d}

lemma facetSizeCnt_affEmb (hp : p ∈ K) (k : ℕ) :
    facetSizeCnt K k = facetSizeCnt (affEmb K p ⁻¹' K) k := by
  unfold facetSizeCnt
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hd, hk⟩
    refine ⟨image_mem_faces hp hF, by rw [dim_image_affEmb]; exact hd, ?_⟩
    rw [cnt_affEmb hp]
    exact hk
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hd, hk⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    have hFF : affEmb K p '' (affEmb K p ⁻¹' F) = F := Set.image_preimage_eq_of_subset hFr
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, ?_, ?_⟩, hFF⟩
    · have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
      rw [hFF] at this
      rw [← this]; exact hd
    · rw [← hFF, cnt_affEmb hp] at hk
      exact hk

end transport

/-- **Polarity**: the 3-faces with `k` vertices correspond to the vertices of the polar lying in
`k` three-faces. -/
lemma facetSizeCnt_polar {n : ℕ} (hn : n = 4) {V : Finset (E n)}
    (h0 : (0 : E n) ∈ interior (convexHull ℝ (V : Set (E n)))) (k : ℕ) :
    facetSizeCnt (convexHull ℝ (V : Set (E n))) k =
      vertDegCnt (polarSet (convexHull ℝ (V : Set (E n)))) k := by
  subst hn
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E 4) ∈ interior (convexHull ℝ (W : Set (E 4))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (convexHull ℝ (W : Set (E 4))) = convexHull ℝ (V : Set (E 4)) := by
    rw [← hW]
    exact polarSet_polarSet (convex_convexHull ℝ _)
      (Set.Finite.isClosed_convexHull ℝ V.finite_toSet) (interior_subset h0)
  have hdimK : dim (convexHull ℝ (V : Set (E 4))) = 4 := dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hdimW : dim (convexHull ℝ (W : Set (E 4))) = 4 :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩
  unfold facetSizeCnt vertDegCnt
  rw [hW]
  refine Set.ncard_congr (fun G _ => dualFace (convexHull ℝ (V : Set (E 4))) G) ?_ ?_ ?_
  · rintro G ⟨hG, hd, hk⟩
    have hne : G ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd; omega
    have hmem := dualFace_mem_faces h0 hG hne
    have hdd := dim_dualFace h0 hG hne
    rw [hW] at hmem
    have hd0 : dim (dualFace (convexHull ℝ (V : Set (E 4))) G) = 0 := by omega
    have hneH : dualFace (convexHull ℝ (V : Set (E 4))) G ≠ convexHull ℝ (W : Set (E 4)) := fun h => by
      rw [h, hdimW] at hd0; omega
    refine ⟨hmem, hd0, ?_⟩
    have hup := upIn_eq_cnt_dualFace h0W hmem hneH 3 (by norm_num)
    rw [hup, hbip]
    have hGG := dualFace_dualFace h0 hG hne
    rw [hW] at hGG
    rw [hGG]
    exact hk
  · intro G G' hGm hG'm heq
    obtain ⟨hG, hd, -⟩ := hGm
    obtain ⟨hG', hd', -⟩ := hG'm
    have hne : G ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd; omega
    have hne' : G' ≠ convexHull ℝ (V : Set (E 4)) := fun h => by rw [h, hdimK] at hd'; omega
    have e1 := dualFace_dualFace h0 hG hne
    have e2 := dualFace_dualFace h0 hG' hne'
    have heq' : dualFace (convexHull ℝ (V : Set (E 4))) G =
        dualFace (convexHull ℝ (V : Set (E 4))) G' := heq
    rw [heq'] at e1
    exact e1.symm.trans e2
  · rintro H ⟨hH, hd, hk⟩
    have hneH : H ≠ convexHull ℝ (W : Set (E 4)) := fun h => by rw [h, hdimW] at hd; omega
    have hmem := dualFace_mem_faces h0W hH hneH
    have hdd := dim_dualFace h0W hH hneH
    rw [hbip] at hmem
    have hd3 : dim (dualFace (convexHull ℝ (W : Set (E 4))) H) = 3 := by omega
    have hneG : dualFace (convexHull ℝ (W : Set (E 4))) H ≠ convexHull ℝ (V : Set (E 4)) := fun h => by
      rw [h, hdimK] at hd3; omega
    refine ⟨dualFace (convexHull ℝ (W : Set (E 4))) H, ⟨hmem, hd3, ?_⟩, ?_⟩
    · have hup := upIn_eq_cnt_dualFace h0W hH hneH 3 (by norm_num)
      rw [hbip] at hup
      exact hup.symm.trans hk
    · have hHH := dualFace_dualFace h0W hH hneH
      rw [hbip] at hHH
      exact hHH

/-! ### Facets with six-vertex 3-faces -/

/-- Row of the 4-simplex. -/
def sRow : Row := ⟨5, 10, 10, 5, 20⟩

/-- Row `(8,19,18,7; 35)`: the polar of the unique 4-polytope with row `(7,18,19,8; 35)`. -/
def zRow : Row := ⟨8, 19, 18, 7, 35⟩

lemma smallRowsX_cover : ∀ X ∈ smallRowsX, X.2.1.sum = X.1.r ∧ X.2.2.sum = X.1.n := by
  decide

lemma smallRowsX_exc : ∀ X ∈ smallRowsX, X.1 = excRow → X.2.1 = [2, 3, 0, 1, 0, 0, 0] := by
  decide

lemma smallRowsX_zdual :
    ∀ X ∈ smallRowsX, X.1 = ⟨7, 18, 19, 8, 35⟩ → X.2.2 = [2, 2, 0, 1, 2, 0, 0] := by
  decide

lemma fv7_filter_fst_six :
    fv7.filter (fun t => decide (t.1 = 6)) = [(6, 9, 5), (6, 10, 6), (6, 11, 7), (6, 12, 8)] := by
  decide

lemma fv7_filter_thd_six : fv7.filter (fun t => decide (t.2.2 = 6)) = [(5, 9, 6), (6, 10, 6)] := by
  decide

/-- The number of 3-faces of `P` with six vertices inside `F`. -/
noncomputable def six3 (P F : Set E5) : ℕ :=
  {G | G ∈ faces P ∧ dim G = 3 ∧ G ⊆ F ∧ cnt P G 0 = 6}.ncard

/-- The faces below a face `G ⊆ F` are the same in `P` and in the face `F`. -/
lemma cnt_face_eq {V : Finset (E d)} {F G : Set (E d)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E d)))) (hGF : G ⊆ F) (j : ℕ) :
    cnt F G j = cnt (convexHull ℝ (V : Set (E d))) G j := by
  unfold cnt
  congr 1
  ext H
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hH, hHG, hd⟩
    exact ⟨((mem_faces_face_iff hF).1 hH).1, hHG, hd⟩
  · rintro ⟨hH, hHG, hd⟩
    exact ⟨(mem_faces_face_iff hF).2 ⟨hH, hHG.trans hGF⟩, hHG, hd⟩

lemma six3_eq_facetSizeCnt {V : Finset E5} {F : Set E5}
    (hF : F ∈ faces (convexHull ℝ (V : Set E5))) :
    six3 (convexHull ℝ (V : Set E5)) F = facetSizeCnt F 6 := by
  unfold six3 facetSizeCnt
  congr 1
  ext G
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hG, hd, hGF, hc⟩
    exact ⟨(mem_faces_face_iff hF).2 ⟨hG, hGF⟩, hd, by rw [cnt_face_eq hF hGF]; exact hc⟩
  · rintro ⟨hG, hd, hc⟩
    have hG' := (mem_faces_face_iff hF).1 hG
    exact ⟨hG'.1, hd, hG'.2, by rw [← cnt_face_eq hF hG'.2]; exact hc⟩

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A facet with the row of the simplex has no 3-face with six vertices. -/
theorem IsCSPolytope5.six3_sRow {F : Set E5} (hrow : faceRow P F = sRow) : six3 P F = 0 := by
  have hn : cnt P F 0 = 5 := congrArg Row.n hrow
  unfold six3
  rw [Set.ncard_eq_zero (hs := hP.faces_finite.subset fun G hG => hG.1)]
  ext G
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hG, -, hGF, hc⟩
  have hmono : cnt P G 0 ≤ cnt P F 0 := by
    unfold cnt
    refine Set.ncard_le_ncard (fun H hH => ⟨hH.1, hH.2.1.trans hGF, hH.2.2⟩) ?_
    exact hP.faces_finite.subset fun H hH => hH.1
  omega

/-- **A facet with row `(7,15,14,6; 29)` has exactly one 3-face with six vertices**
(the base of the pyramid over a triangular prism). -/
theorem IsCSPolytope5.six3_excRow {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = excRow) : six3 P F = 1 := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hrowF : rowOf F = excRow := by rw [rowOf_face hF', ← hV]; exact hrow
  have hreal : IsRealRowX (rowXOf F) := ⟨5, F, ⟨_, hFS⟩, h4, rfl⟩
  have hmem := smallX_classification _ hreal (by
    show (rowOf F).n ≤ 7
    rw [hrowF]; decide)
  have hprof := smallRowsX_exc _ hmem hrowF
  have hcov := (smallRowsX_cover _ hmem).1
  have hfin : (faces F).Finite := by rw [hFS]; exact faces_finite_convexHull _
  have hcov' : (fv7.map (facetCnt F)).sum = fvec F 3 := by
    have : (rowXOf F).2.1 = fv7.map (facetCnt F) := rfl
    rw [← this, hcov]
    rfl
  rw [hV, six3_eq_facetSizeCnt hF', facetSizeCnt_eq_of_cover hfin hcov' 6, fv7_filter_fst_six]
  have : (rowXOf F).2.1 = fv7.map (facetCnt F) := rfl
  rw [this] at hprof
  simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at hprof
  simp [List.map_cons, List.sum_cons, hprof]

/-- **A facet with row `(8,19,18,7; 35)` has exactly two 3-faces with six vertices**: its polar
has row `(7,18,19,8; 35)` and exactly two vertices in six 3-faces. -/
theorem IsCSPolytope5.six3_zRow {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hrow : faceRow P F = zRow) : six3 P F = 2 := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFS : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hrowF : rowOf F = zRow := by rw [rowOf_face hF', ← hV]; exact hrow
  have hne : F.Nonempty := hF.1
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hFS hne
  -- the polar of the transported facet
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E (dim F)) ∈ interior (convexHull ℝ (W : Set (E (dim F)))) :=
    hW ▸ zero_mem_interior_polarSet V'
  have hdimW : dim (convexHull ℝ (W : Set (E (dim F)))) = 4 := by
    rw [dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0W⟩, h4]
  -- face numbers of the transported facet
  have hfv : ∀ j, fvec (convexHull ℝ (V' : Set (E (dim F)))) j = fvec F j := fun j => by
    rw [← hV', ← fvec_affEmb hp]
  have hfl : flag2 (convexHull ℝ (V' : Set (E (dim F)))) 0 3 = flag2 F 0 3 := by
    rw [← hV', ← flag2_affEmb hp]
  -- the row of the polar
  have hrowW : rowOf (convexHull ℝ (W : Set (E (dim F)))) = ⟨7, 18, 19, 8, 35⟩ := by
    have e0 := fvec_polarSet_eq h0 3 (by omega)
    have e1 := fvec_polarSet_eq h0 2 (by omega)
    have e2 := fvec_polarSet_eq h0 1 (by omega)
    have e3 := fvec_polarSet_eq h0 0 (by omega)
    have eJ := flag2_polarSet_eq h0 0 3 (by omega) (by omega)
    rw [hW] at e0 e1 e2 e3 eJ
    rw [show dim F - 1 - 3 = 0 by omega] at e0 eJ
    rw [show dim F - 1 - 2 = 1 by omega] at e1
    rw [show dim F - 1 - 1 = 2 by omega] at e2
    rw [show dim F - 1 - 0 = 3 by omega] at e3 eJ
    have hz := hrowF
    simp only [rowOf, zRow, Row.mk.injEq] at hz
    simp only [rowOf, e0, e1, e2, e3, eJ, hfv, hfl, hz]
  have hreal : IsRealRowX (rowXOf (convexHull ℝ (W : Set (E (dim F))))) :=
    ⟨dim F, _, ⟨W, rfl⟩, hdimW, rfl⟩
  have hmem := smallX_classification _ hreal (by
    show (rowOf (convexHull ℝ (W : Set (E (dim F))))).n ≤ 7
    rw [hrowW])
  have hprof := smallRowsX_zdual _ hmem hrowW
  have hcov := (smallRowsX_cover _ hmem).2
  have hcov' : (fv7.map (vertCnt (convexHull ℝ (W : Set (E (dim F)))))).sum =
      fvec (convexHull ℝ (W : Set (E (dim F)))) 0 := by
    have : (rowXOf (convexHull ℝ (W : Set (E (dim F))))).2.2 =
        fv7.map (vertCnt (convexHull ℝ (W : Set (E (dim F))))) := rfl
    rw [← this, hcov]
    rfl
  have hdeg := vertDegCnt_eq_of_cover (faces_finite_convexHull W) hcov' 6
  rw [fv7_filter_thd_six] at hdeg
  have : (rowXOf (convexHull ℝ (W : Set (E (dim F))))).2.2 =
      fv7.map (vertCnt (convexHull ℝ (W : Set (E (dim F))))) := rfl
  rw [this] at hprof
  simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at hprof
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hprof] at hdeg
  -- transport back
  have hpolar := facetSizeCnt_polar h4 h0 6
  rw [hW] at hpolar
  rw [hV, six3_eq_facetSizeCnt hF', facetSizeCnt_affEmb hp, hV', hpolar, hdeg]
  norm_num

/-- **Ridge parity**: `Σ_F #{3-faces of F with six vertices} ≡ 0 (mod 4)`. -/
theorem IsCSPolytope5.four_dvd_sum_six3 :
    4 ∣ ∑ F ∈ (hP.kfaces_finite 4).toFinset, six3 P F := by
  classical
  set T3 := (hP.kfaces_finite 3).toFinset with hT3
  set T4 := (hP.kfaces_finite 4).toFinset with hT4
  have hsix : ∀ F, six3 P F = (T3.filter fun G => G ⊆ F ∧ cnt P G 0 = 6).card := by
    intro F
    unfold six3
    rw [← Set.ncard_coe_finset]
    congr 1
    ext G
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT3, Set.Finite.mem_toFinset]
    tauto
  have hup : ∀ G ∈ T3, (T4.filter fun F => G ⊆ F).card = 2 := by
    intro G hG
    rw [hT3, Set.Finite.mem_toFinset] at hG
    rw [← hP.ridge_two hG.1 hG.2, ← Set.ncard_coe_finset]
    congr 1
    ext F
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT4, Set.Finite.mem_toFinset]
    tauto
  have hsum : ∑ F ∈ T4, six3 P F = 2 * (T3.filter fun G => cnt P G 0 = 6).card := by
    simp only [hsix, Finset.card_filter]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun G hG => ?_
    by_cases hc : cnt P G 0 = 6
    · simp only [hc, and_true, if_true, mul_one]
      rw [← hup G hG, Finset.card_filter]
    · simp [hc]
  have heven : Even (T3.filter fun G => cnt P G 0 = 6).card := by
    refine even_card_of_involution _ (fun G => -G) ?_ (fun G _ => neg_neg G) ?_
    · intro G hG
      rw [Finset.mem_filter, hT3, Set.Finite.mem_toFinset] at hG ⊢
      exact ⟨⟨neg_mem_faces hP.symm hG.1.1, by rw [dim_neg]; exact hG.1.2⟩,
        by rw [hP.cnt_neg]; exact hG.2⟩
    · intro G hG hGG
      rw [Finset.mem_filter, hT3, Set.Finite.mem_toFinset] at hG
      have := hP.eq_of_neg_eq hG.1.1 hGG
      have h5 := hP.dim_self
      rw [← this, hG.1.2] at h5
      omega
  obtain ⟨m, hm⟩ := heven
  rw [hsum, hm]
  exact ⟨m, by ring⟩

end cs

end Kalai5
