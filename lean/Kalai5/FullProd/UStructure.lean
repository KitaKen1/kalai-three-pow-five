import Kalai5.Polar.FacetDual
import Kalai5.Gale.ClassifyU
import Kalai5.Rows.Dual
import Kalai5.Faces.Facets

/-!
# The facet `U = (9, 19, 17, 7; 38)`: vertex–facet incidences

`polytope_u_structure`: a 4-polytope with row `(9, 19, 17, 7; 38)` (with `0` in its interior)
has its nine vertices `x i` and seven facets `G j` labelled so that `x i ∈ G j ↔ j ∈ uInc i`.

Proof: its polar has seven vertices and row `(7, 17, 19, 9; 38)`, so its facets are `uSets` up to
relabelling (`Gale.uStar_facets`); the vertices of the polar are the duals of the facets of the
polytope and its facets the duals of the vertices (`Polar.FacetDual`), and the incidence
`x ∈ G ↔ ⟪x, w_G⟫ = 1` is the incidence of the polar read backwards.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The canonical incidences of `U`: vertex `i` lies on the facets `uInc i`. -/
def uInc (i : Fin 9) : Finset (Fin 7) := Gale.ofMask 7 (Gale.uStarFacets.getD i 0)

lemma uInc_mem_uSets : ∀ i, uInc i ∈ Gale.uSets := by
  decide

lemma exists_uInc_of_mem : ∀ F ∈ Gale.uSets, ∃ i, uInc i = F := by
  intro F hF
  simp only [Gale.uSets, List.mem_map] at hF
  obtain ⟨M, hM, rfl⟩ := hF
  simp only [Gale.uStarFacets, List.mem_cons, List.not_mem_nil, or_false] at hM
  rcases hM with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩, ⟨4, rfl⟩, ⟨5, rfl⟩, ⟨6, rfl⟩, ⟨7, rfl⟩, ⟨8, rfl⟩]

lemma uInc_injective : Function.Injective uInc := by
  unfold Function.Injective uInc
  decide

/-- **Vertex–facet incidences of a 4-polytope with row `(9, 19, 17, 7; 38)`.** -/
theorem polytope_u_structure {k : ℕ} (hk : k = 4) {V : Finset (E k)}
    (h0 : (0 : E k) ∈ interior (convexHull ℝ (V : Set (E k))))
    (hrow : rowOf (convexHull ℝ (V : Set (E k))) = ⟨9, 19, 17, 7, 38⟩) :
    ∃ (x : Fin 9 → E k) (G : Fin 7 → Set (E k)),
      Function.Injective x ∧ (∀ i, x i ∈ (convexHull ℝ (V : Set (E k))).extremePoints ℝ) ∧
      (∀ y ∈ (convexHull ℝ (V : Set (E k))).extremePoints ℝ, ∃ i, x i = y) ∧
      (∀ j, G j ∈ faces (convexHull ℝ (V : Set (E k))) ∧ dim (G j) = 3) ∧
      (∀ F ∈ faces (convexHull ℝ (V : Set (E k))), dim F = 3 → ∃ j, G j = F) ∧
      (∀ i j, x i ∈ G j ↔ j ∈ uInc i) := by
  classical
  subst hk
  set K := convexHull ℝ (V : Set (E 4)) with hK
  have hdK : dim K = 4 := dim_conv_of_interior h0
  obtain ⟨W', hW', h0W', hbip⟩ := exists_polar_conv h0
  -- the row of the polar
  have hrowS : rowOf (convexHull ℝ (W' : Set (E 4))) = Gale.uStarRow := by
    have e0 := fvec_polarSet_eq h0 3 (by norm_num)
    have e1 := fvec_polarSet_eq h0 2 (by norm_num)
    have e2 := fvec_polarSet_eq h0 1 (by norm_num)
    have e3 := fvec_polarSet_eq h0 0 (by norm_num)
    have eJ := flag2_polarSet_eq h0 0 3 (by norm_num) (by norm_num)
    rw [hW'] at e0 e1 e2 e3 eJ
    norm_num at e0 e1 e2 e3 eJ
    simp only [rowOf] at hrow ⊢
    rw [e0, e1, e2, e3, eJ]
    simp only [Row.mk.injEq] at hrow
    obtain ⟨h1, h2, h3, h4, h5⟩ := hrow
    rw [h1, h2, h3, h4, h5]
    rfl
  -- the seven vertices of the polar
  set XS := (extremePoints_finite W').toFinset with hXS
  have hXScard : XS.card = 7 := by
    have h1 := fvec_zero_eq W'
    have h2 : fvec (convexHull ℝ (W' : Set (E 4))) 0 = 7 := by
      have := congrArg Row.n hrowS
      simpa [rowOf, Gale.uStarRow] using this
    rw [h2, Set.ncard_eq_toFinset_card _ (extremePoints_finite W')] at h1
    rw [hXS]; omega
  let e : { x // x ∈ XS } ≃ Fin 7 := Finset.equivFinOfCardEq hXScard
  set W : Fin 7 → E 4 := fun j => (e.symm j : E 4) with hWdef
  have hWmem : ∀ j, W j ∈ (convexHull ℝ (W' : Set (E 4))).extremePoints ℝ := fun j =>
    (Set.Finite.mem_toFinset _).1 (e.symm j).2
  have hrangeW : range W = (convexHull ℝ (W' : Set (E 4))).extremePoints ℝ := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact hWmem j
    · intro hy
      have hyX : y ∈ XS := by rw [hXS, Set.Finite.mem_toFinset]; exact hy
      exact ⟨e ⟨y, hyX⟩, by simp [hWdef]⟩
  have hconvW : convexHull ℝ (range W) = convexHull ℝ (W' : Set (E 4)) := by
    rw [hrangeW]; exact convexHull_extremePoints_eq W'
  have hWinj : Function.Injective W := fun a b h => e.symm.injective (Subtype.ext h)
  have hWext : ∀ j, W j ∈ (convexHull ℝ (range W)).extremePoints ℝ := fun j => by
    rw [hconvW]; exact hWmem j
  have hWspan : affineSpan ℝ (range W) = ⊤ := by
    have hint : (interior (convexHull ℝ (range W))).Nonempty := by
      rw [hconvW]; exact ⟨0, h0W'⟩
    rw [← affineSpan_convexHull]
    exact (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.1 hint
  have hWrow : rowOf (convexHull ℝ (range W)) = Gale.uStarRow := by rw [hconvW]; exact hrowS
  obtain ⟨τ, hdir1, hdir2⟩ := Gale.uStar_facets hWinj hWext hWspan hWrow
  -- the polar as `conv (range W)`
  have hpolW : polarSet K = convexHull ℝ (range W) := by rw [hconvW]; exact hW'
  -- facets of `K` from the vertices of the polar
  have hGex : ∀ j : Fin 7, ∃ G ∈ faces K, dim G + 1 = 4 ∧ dualFace K G = {W (τ.symm j)} := by
    intro j
    have hw : W (τ.symm j) ∈ (polarSet K).extremePoints ℝ := by
      rw [hW']; exact hWmem _
    exact exists_facet_of_polar_vertex h0 hw (by norm_num)
  choose G hGface hGdim hGdual using hGex
  -- vertices of `K` from the facets of the polar
  have hxex : ∀ i : Fin 9, ∃ x0 ∈ K.extremePoints ℝ, ∃ Φ ∈ faces (convexHull ℝ (range W)),
      dim Φ = 3 ∧ (Gale.idx W Φ).map τ.toEmbedding = uInc i ∧ Φ = dualFace K {x0} := by
    intro i
    obtain ⟨Φ, hΦ, hΦ3, hΦi⟩ := hdir2 _ (uInc_mem_uSets i)
    have hΦ' : Φ ∈ faces (polarSet K) := by rw [hpolW]; exact hΦ
    obtain ⟨x0, hx0, hΦeq⟩ := exists_vertex_of_polar_facet h0 hΦ' (by omega)
    exact ⟨x0, hx0, Φ, hΦ, hΦ3, hΦi, hΦeq⟩
  choose x hxext Φ hΦface hΦdim hΦinc hΦeq using hxex
  -- incidences
  have hinc : ∀ i j, x i ∈ G j ↔ j ∈ uInc i := by
    intro i j
    have hxK : x i ∈ K := (hxext i).1
    rw [mem_facet_iff_dual h0 (hGface j) (hGdim j) (hGdual j) hxK, ← hΦinc i,
      Finset.mem_map_equiv, Gale.mem_idx, hΦeq i]
    simp only [dualFace, Set.mem_ofPred_eq, Set.mem_singleton_iff, forall_eq]
    have hwpol : W (τ.symm j) ∈ polarSet K := by rw [hW']; exact (hWmem _).1
    constructor
    · intro h; exact ⟨hwpol, h⟩
    · intro h; exact h.2
  -- a vertex is recovered from its dual facet
  have hrec : ∀ y z : E 4, y ∈ K.extremePoints ℝ → z ∈ K.extremePoints ℝ →
      dualFace K {y} = dualFace K {z} → y = z := by
    intro y z hy hz h
    have hFy : ({y} : Set (E 4)) ∈ faces K := singleton_mem_faces_of_extreme hy
    have hFz : ({z} : Set (E 4)) ∈ faces K := singleton_mem_faces_of_extreme hz
    have hney : ({y} : Set (E 4)) ≠ K := by
      intro h'; have := hdK; rw [← h', dim_singleton] at this; omega
    have hnez : ({z} : Set (E 4)) ≠ K := by
      intro h'; have := hdK; rw [← h', dim_singleton] at this; omega
    have h1 := eq_of_dualFace h0 hFy hney
    have h2 := eq_of_dualFace h0 hFz hnez
    rw [h] at h1
    rw [← h2] at h1
    exact Set.singleton_eq_singleton_iff.1 h1
  refine ⟨x, G, ?_, hxext, ?_, fun j => ⟨hGface j, by have := hGdim j; omega⟩, ?_, hinc⟩
  · -- injectivity of the vertex labels
    intro i i' h
    apply uInc_injective
    rw [← hΦinc i, ← hΦinc i', hΦeq i, hΦeq i', h]
  · -- every vertex is labelled
    intro y hy
    obtain ⟨hΦy, hΦy3⟩ := dualFace_vertex h0 hy (by norm_num)
    rw [hpolW] at hΦy
    obtain ⟨i, hi⟩ := exists_uInc_of_mem _ (hdir1 _ hΦy (by omega))
    refine ⟨i, hrec _ _ (hxext i) hy ?_⟩
    rw [← hΦeq i]
    have hidx : Gale.idx W (Φ i) = Gale.idx W (dualFace K {y}) := by
      have := (hΦinc i).trans hi
      exact Finset.map_injective _ this
    rw [Gale.face_eq_conv_idx (hΦface i), Gale.face_eq_conv_idx hΦy, hidx]
  · -- every facet is labelled
    intro F hF hF3
    obtain ⟨w, hw, hwext, -⟩ := dualFace_facet h0 hF (by omega)
    have hwW : w ∈ range W := by
      rw [hrangeW, ← hW']; exact hwext
    obtain ⟨j', rfl⟩ := hwW
    refine ⟨τ j', ?_⟩
    have h1 := hGdual (τ j')
    rw [Equiv.symm_apply_apply] at h1
    have hneG : G (τ j') ≠ K := by
      intro h'; have := hGdim (τ j'); rw [h'] at this; omega
    have hneF : F ≠ K := by
      intro h'; have := hdK; rw [← h'] at this; omega
    rw [eq_of_dualFace h0 (hGface (τ j')) hneG, eq_of_dualFace h0 hF hneF, h1, hw]

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Vertex–facet incidences of a facet `U` of `P` with row `(9, 19, 17, 7; 38)`**: its vertices
`x i` and its facets `G j` (3-faces of `P`) satisfy `x i ∈ G j ↔ j ∈ uInc i`. -/
theorem IsCSPolytope5.u_structure {U : Set E5} (hU : U ∈ faces P) (h4 : dim U = 4)
    (hrow : faceRow P U = ⟨9, 19, 17, 7, 38⟩) :
    ∃ (x : Fin 9 → E5) (G : Fin 7 → Set E5),
      Function.Injective x ∧ (∀ i, x i ∈ U.extremePoints ℝ) ∧
      (∀ y ∈ U.extremePoints ℝ, ∃ i, x i = y) ∧
      (∀ j, G j ∈ faces P ∧ G j ⊆ U ∧ dim (G j) = 3) ∧
      (∀ i j, x i ∈ G j ↔ j ∈ uInc i) := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hU' : U ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hU
  have hUV : U = convexHull ℝ ((V.filter (· ∈ U) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hU'
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hUV hU.1
  have hrow' : rowOf (convexHull ℝ (V' : Set (E (dim U)))) = ⟨9, 19, 17, 7, 38⟩ := by
    rw [← hV']
    have e := rowOf_face hU'
    rw [← hV] at e
    rw [← hrow, ← e]
    simp only [rowOf, ← fvec_affEmb hp, ← flag2_affEmb hp]
  obtain ⟨x', G', hinj', hext', hsurj', hG', -, hinc'⟩ := polytope_u_structure h4 h0 hrow'
  set e := affEmb U p with he
  have heinj : Function.Injective e := affEmb_injective p
  have hfacesK : ∀ S, S ∈ faces (convexHull ℝ (V' : Set (E (dim U)))) ↔
      S ∈ faces (e ⁻¹' U) := by intro S; rw [hV']
  refine ⟨fun i => e (x' i), fun j => e '' G' j, heinj.comp hinj', ?_, ?_, ?_, ?_⟩
  · intro i
    have hS : ({x' i} : Set (E (dim U))) ∈ faces (e ⁻¹' U) :=
      (hfacesK _).1 (singleton_mem_faces_of_extreme (hext' i))
    have := image_mem_faces hp hS
    rw [Set.image_singleton] at this
    exact mem_extremePoints_of_singleton_mem_faces this
  · intro y hy
    have hyU : y ∈ U := hy.1
    obtain ⟨z, hz⟩ := exists_affEmb_eq hp hyU
    have hyface : ({y} : Set E5) ∈ faces U := by
      rw [hUV] at hy ⊢; exact singleton_mem_faces_of_extreme hy
    have hpre := preimage_mem_faces hp hyface
    have hpre' : e ⁻¹' {y} = {z} := by
      ext w; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro h; exact heinj (h.trans hz.symm)
      · intro h; rw [h]; exact hz
    rw [hpre'] at hpre
    have hzext : z ∈ (convexHull ℝ (V' : Set (E (dim U)))).extremePoints ℝ :=
      mem_extremePoints_of_singleton_mem_faces ((hfacesK _).2 hpre)
    obtain ⟨i, hi⟩ := hsurj' z hzext
    exact ⟨i, by simp only; rw [hi, hz]⟩
  · intro j
    have hS : G' j ∈ faces (e ⁻¹' U) := (hfacesK _).1 (hG' j).1
    have himg := image_mem_faces hp hS
    have hP' := faces_trans hU' himg
    rw [← hV] at hP'
    refine ⟨hP', face_subset himg, ?_⟩
    rw [dim_image_affEmb]; exact (hG' j).2
  · intro i j
    rw [heinj.mem_set_image]
    exact hinc' i j

end cs

end Kalai5
