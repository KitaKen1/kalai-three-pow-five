import Kalai5.Euler.Relations

/-!
# Relative polarity: upper intervals inside faces

A polytope `K ⊆ E d` is full-dimensional in its own affine hull.  We transport it isometrically
to `E (dim K)` (`affEmb`), recentre it at an interior point (`exists_good_affEmb`) and apply the
polarity of `Kalai5.Polar` there (`upIn_eq_cnt_dualFace`).  For a 3-dimensional polytope and a
vertex `v` this gives (`vertex_up_dim_three`)

* `#edges ∋ v = #2-faces ∋ v` (the vertex figure is a polygon), and
* `#edges ∋ v ≥ 3`.

For centrally symmetric 5-polytopes, summed over the 3-faces:

* `f₀₂₄ = f₀₂₃ = 2 f₁₃`, hence the `f₀₂₄` identity;
* `B = 2 f₁₃ - 3 f₀₃ ≥ 0`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {d : ℕ}

/-- `#{j-faces of K containing G}`. -/
noncomputable def upIn (K G : Set (E d)) (j : ℕ) : ℕ :=
  {F | F ∈ faces K ∧ G ⊆ F ∧ dim F = j}.ncard

/-! ### Euler relations for faces of an arbitrary polytope -/

lemma cnt_self_conv {V : Finset (E d)} {G : Set (E d)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) :
    cnt (convexHull ℝ (V : Set (E d))) G (dim G) = 1 := by
  rw [cnt, Set.ncard_eq_one]
  refine ⟨G, ?_⟩
  ext H
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hH, hHG, hd⟩
    by_contra hne
    have hH' : H ∈ faces G := (mem_faces_face_iff hG).2 ⟨hH, hHG⟩
    have := dim_lt_of_mem_faces_ne hH' hne
    omega
  · rintro rfl; exact ⟨hG, le_rfl, rfl⟩

lemma euler_face_conv {V : Finset (E d)} {G : Set (E d)}
    (hG : G ∈ faces (convexHull ℝ (V : Set (E d)))) :
    ∑ j ∈ Finset.range (dim G + 1),
      (-1 : ℤ) ^ j * cnt (convexHull ℝ (V : Set (E d))) G j = 1 := by
  classical
  set S := V.filter (· ∈ G)
  have hGS : G = convexHull ℝ (S : Set (E d)) := face_eq_convexHull_filter hG
  have hS : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    obtain ⟨x, hx⟩ := hG.1
    rw [hGS, h, Finset.coe_empty, convexHull_empty] at hx; exact hx
  have hdims : ∀ H ∈ faces (convexHull ℝ (S : Set (E d))), dim H ≤ dim G := by
    intro H hH
    rw [← hGS] at hH
    exact Submodule.finrank_mono (vectorSpan_mono ℝ (face_subset hH))
  have h := euler_fvec hS (dim G) hdims
  rw [← hGS] at h
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  rw [fvec_face_eq_cnt hG]

/-- **A polygon has as many edges as vertices.** -/
lemma cnt_one_eq_cnt_zero {V : Finset (E d)} {X : Set (E d)}
    (hX : X ∈ faces (convexHull ℝ (V : Set (E d)))) (h2 : dim X = 2) :
    cnt (convexHull ℝ (V : Set (E d))) X 1 = cnt (convexHull ℝ (V : Set (E d))) X 0 := by
  have he := euler_face_conv hX
  have hc := cnt_self_conv hX
  rw [h2] at he hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc] at he
  norm_num at he
  omega

/-! ### Upper intervals through polarity -/

section polar

variable {V : Finset (E d)} (h0 : (0 : E d) ∈ interior (convexHull ℝ (V : Set (E d))))
include h0

/-- **Upper intervals through polarity**: for a polytope with `0` in its interior, the faces
containing a proper face `G` correspond to the faces of the polar inside `G♦`. -/
theorem upIn_eq_cnt_dualFace {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hne : G ≠ convexHull ℝ (V : Set (E d))) (j : ℕ) (hj : j + 1 ≤ d) :
    upIn (convexHull ℝ (V : Set (E d))) G j =
      cnt (polarSet (convexHull ℝ (V : Set (E d))))
        (dualFace (convexHull ℝ (V : Set (E d))) G) (d - 1 - j) := by
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have h0W : (0 : E d) ∈ interior (convexHull ℝ (W : Set (E d))) :=
    hW ▸ zero_mem_interior_polarSet V
  have hbip : polarSet (polarSet (convexHull ℝ (V : Set (E d)))) =
      convexHull ℝ (V : Set (E d)) :=
    polarSet_polarSet (convex_convexHull ℝ _) (Set.Finite.isClosed_convexHull ℝ V.finite_toSet)
      (interior_subset h0)
  have hdimK : dim (convexHull ℝ (V : Set (E d))) = d :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hdimQ : dim (polarSet (convexHull ℝ (V : Set (E d)))) = d :=
    dim_eq_of_interior (polarSet_convex _) ⟨0, zero_mem_interior_polarSet V⟩
  have hfinK := faces_finite_convexHull V
  have hfinQ : (faces (polarSet (convexHull ℝ (V : Set (E d))))).Finite :=
    hW ▸ faces_finite_convexHull W
  apply le_antisymm
  · refine Set.ncard_le_ncard_of_injOn (dualFace (convexHull ℝ (V : Set (E d)))) ?_ ?_
      (hfinQ.subset fun H hH => hH.1)
    · rintro F ⟨hF, hGF, hd⟩
      have hneF : F ≠ convexHull ℝ (V : Set (E d)) := fun h => by rw [h] at hd; omega
      have e := dim_dualFace h0 hF hneF
      exact ⟨dualFace_mem_faces h0 hF hneF, dualFace_antitone hGF, by omega⟩
    · rintro F ⟨hF, -, hd⟩ F' ⟨hF', -, hd'⟩ heq
      have hneF : F ≠ convexHull ℝ (V : Set (E d)) := fun h => by rw [h] at hd; omega
      have hneF' : F' ≠ convexHull ℝ (V : Set (E d)) := fun h => by rw [h] at hd'; omega
      rw [eq_of_dualFace h0 hF hneF, eq_of_dualFace h0 hF' hneF', heq]
  · have hGdd := dualFace_dualFace h0 hG hne
    refine Set.ncard_le_ncard_of_injOn (dualFace (polarSet (convexHull ℝ (V : Set (E d))))) ?_ ?_
      (hfinK.subset fun F hF => hF.1)
    · rintro H ⟨hH, hHG, hd⟩
      have hneH : H ≠ polarSet (convexHull ℝ (V : Set (E d))) := fun h => by
        rw [h] at hd; omega
      rw [hW] at hH hneH
      have e := dim_dualFace h0W hH hneH
      have hmem := dualFace_mem_faces h0W hH hneH
      rw [← hW, hbip] at hmem
      rw [← hW] at e
      refine ⟨hmem, ?_, by omega⟩
      calc G = dualFace (polarSet (convexHull ℝ (V : Set (E d))))
            (dualFace (convexHull ℝ (V : Set (E d))) G) := hGdd.symm
        _ ⊆ dualFace (polarSet (convexHull ℝ (V : Set (E d)))) H := dualFace_antitone hHG
    · rintro H ⟨hH, -, hd⟩ H' ⟨hH', -, hd'⟩ heq
      have hneH : H ≠ polarSet (convexHull ℝ (V : Set (E d))) := fun h => by
        rw [h] at hd; omega
      have hneH' : H' ≠ polarSet (convexHull ℝ (V : Set (E d))) := fun h => by
        rw [h] at hd'; omega
      rw [hW] at hH hH' hneH hneH'
      have e1 := eq_of_dualFace h0W hH hneH
      have e2 := eq_of_dualFace h0W hH' hneH'
      rw [← hW] at e1 e2
      rw [heq] at e1
      exact e1.trans e2.symm

/-- At a face of codimension three the upper interval is a polygon: as many faces of dimension
`dim G + 1` as of dimension `dim G + 2`, and at least three of them. -/
theorem upIn_codim_three {G : Set (E d)} (hG : G ∈ faces (convexHull ℝ (V : Set (E d))))
    (hcod : dim G + 3 = d) :
    upIn (convexHull ℝ (V : Set (E d))) G (dim G + 1) =
        upIn (convexHull ℝ (V : Set (E d))) G (dim G + 2) ∧
      3 ≤ upIn (convexHull ℝ (V : Set (E d))) G (dim G + 1) := by
  have hdimK : dim (convexHull ℝ (V : Set (E d))) = d :=
    dim_eq_of_interior (convex_convexHull ℝ _) ⟨0, h0⟩
  have hne : G ≠ convexHull ℝ (V : Set (E d)) := fun h => by
    rw [h, hdimK] at hcod; omega
  obtain ⟨W, hW⟩ := exists_polarSet_eq_convexHull h0
  have hmem := dualFace_mem_faces h0 hG hne
  have hdim := dim_dualFace h0 hG hne
  rw [hW] at hmem
  have hX2 : dim (dualFace (convexHull ℝ (V : Set (E d))) G) = 2 := by omega
  rw [upIn_eq_cnt_dualFace h0 hG hne _ (by omega), upIn_eq_cnt_dualFace h0 hG hne _ (by omega),
    show d - 1 - (dim G + 1) = 1 by omega, show d - 1 - (dim G + 2) = 0 by omega, hW]
  refine ⟨cnt_one_eq_cnt_zero hmem hX2, ?_⟩
  rw [cnt_one_eq_cnt_zero hmem hX2]
  exact three_le_cnt_zero_of_dim_two hmem hX2

end polar

/-! ### Transport of a polytope to its own affine hull -/

section transport

variable (K : Set (E d))

/-- An isometric embedding of `E (dim K)` onto `vectorSpan ℝ K`. -/
noncomputable def embL : E (dim K) →ₗᵢ[ℝ] E d :=
  (vectorSpan ℝ K).subtypeₗᵢ.comp
    (stdOrthonormalBasis ℝ (vectorSpan ℝ K)).repr.symm.toLinearIsometry

lemma embL_apply (z : E (dim K)) :
    embL K z = ((stdOrthonormalBasis ℝ (vectorSpan ℝ K)).repr.symm z : E d) := rfl

lemma exists_embL_eq {u : E d} (hu : u ∈ vectorSpan ℝ K) : ∃ z, embL K z = u :=
  ⟨(stdOrthonormalBasis ℝ (vectorSpan ℝ K)).repr ⟨u, hu⟩,
    congrArg Subtype.val ((stdOrthonormalBasis ℝ (vectorSpan ℝ K)).repr.symm_apply_apply ⟨u, hu⟩)⟩

/-- The affine embedding `z ↦ embL K z + p` of `E (dim K)` onto the affine span of `K`
(for `p ∈ K`). -/
noncomputable def affEmb (p : E d) : E (dim K) →ᵃ[ℝ] E d :=
  (embL K).toLinearMap.toAffineMap + AffineMap.const ℝ (E (dim K)) p

variable {K} (p : E d)

@[simp] lemma affEmb_apply (z : E (dim K)) : affEmb K p z = embL K z + p := rfl

lemma affEmb_linear : (affEmb K p).linear = (embL K).toLinearMap := by
  ext z; simp [affEmb]

lemma affEmb_injective : Function.Injective (affEmb K p) := fun a b h =>
  (embL K).injective (by simpa using h)

lemma dim_image_affEmb (S : Set (E (dim K))) : dim (affEmb K p '' S) = dim S := by
  change Module.finrank ℝ (vectorSpan ℝ (affEmb K p '' S)) =
    Module.finrank ℝ (vectorSpan ℝ S)
  rw [← AffineMap.map_vectorSpan, affEmb_linear]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective _ (embL K).injective (vectorSpan ℝ S))).symm

variable {p}

lemma exists_affEmb_eq (hp : p ∈ K) {x : E d} (hx : x ∈ K) : ∃ z, affEmb K p z = x := by
  obtain ⟨z, hz⟩ := exists_embL_eq K (vsub_mem_vectorSpan ℝ hx hp)
  exact ⟨z, by rw [affEmb_apply, hz, vsub_eq_sub, sub_add_cancel]⟩

lemma subset_range_affEmb (hp : p ∈ K) {F : Set (E d)} (hF : F ⊆ K) :
    F ⊆ Set.range (affEmb K p) := fun _ hx => exists_affEmb_eq hp (hF hx)

/-- Faces of the transported polytope give faces of `K`. -/
lemma image_mem_faces (hp : p ∈ K) {S : Set (E (dim K))} (hS : S ∈ faces (affEmb K p ⁻¹' K)) :
    affEmb K p '' S ∈ faces K := by
  obtain ⟨l', hl'⟩ := exists_functional hS
  set w := (InnerProductSpace.toDual ℝ (E (dim K))).symm l'
  have hw : ∀ z, l' z = ⟪z, w⟫ := fun z => by
    rw [real_inner_comm]; exact (InnerProductSpace.toDual_symm_apply).symm
  have hl : ∀ z, ip (embL K w) (affEmb K p z) = l' z + ⟪p, embL K w⟫ := by
    intro z
    rw [ip_apply, affEmb_apply, inner_add_left, LinearIsometry.inner_map_map, ← hw]
  refine ⟨hS.1.image _, fun _ => ⟨ip (embL K w), ?_⟩⟩
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' := hz
    rw [hl'] at hz'
    refine ⟨hz'.1, fun y hy => ?_⟩
    obtain ⟨u, rfl⟩ := exists_affEmb_eq hp hy
    rw [hl, hl]
    have := hz'.2 u hy
    linarith
  · rintro ⟨hx, hmax⟩
    obtain ⟨z, rfl⟩ := exists_affEmb_eq hp hx
    refine ⟨z, ?_, rfl⟩
    rw [hl']
    refine ⟨hx, fun u hu => ?_⟩
    have := hmax _ hu
    rw [hl, hl] at this
    linarith

/-- Faces of `K` pull back to faces of the transported polytope. -/
lemma preimage_mem_faces (hp : p ∈ K) {F : Set (E d)} (hF : F ∈ faces K) :
    affEmb K p ⁻¹' F ∈ faces (affEmb K p ⁻¹' K) := by
  obtain ⟨l, hl⟩ := exists_functional hF
  have hl' : ∀ z, l (affEmb K p z) = (l.comp (embL K).toContinuousLinearMap) z + l p := by
    intro z; simp
  obtain ⟨f, hf⟩ := hF.1
  obtain ⟨z0, hz0⟩ := exists_affEmb_eq hp (face_subset hF hf)
  refine ⟨⟨z0, by rw [Set.mem_preimage, hz0]; exact hf⟩,
    fun _ => ⟨l.comp (embL K).toContinuousLinearMap, ?_⟩⟩
  ext z
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  conv_lhs => rw [hl]
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, fun u hu => ?_⟩
    have := hmax _ hu
    rw [hl', hl'] at this
    linarith
  · rintro ⟨hz, hmax⟩
    refine ⟨hz, fun y hy => ?_⟩
    obtain ⟨u, rfl⟩ := exists_affEmb_eq hp hy
    have := hmax u hy
    rw [hl', hl']
    linarith

/-- Upper intervals are preserved by the transport. -/
lemma upIn_affEmb (hp : p ∈ K) (G' : Set (E (dim K))) (j : ℕ) :
    upIn K (affEmb K p '' G') j = upIn (affEmb K p ⁻¹' K) G' j := by
  unfold upIn
  symm
  refine Set.ncard_congr (fun F _ => affEmb K p '' F) ?_ ?_ ?_
  · rintro F ⟨hF, hGF, hd⟩
    exact ⟨image_mem_faces hp hF, Set.image_mono hGF, by rw [dim_image_affEmb]; exact hd⟩
  · intro F F' _ _ h
    exact (Set.image_injective.2 (affEmb_injective (K := K) p)) h
  · rintro F ⟨hF, hGF, hd⟩
    have hFr := subset_range_affEmb hp (face_subset hF)
    refine ⟨affEmb K p ⁻¹' F, ⟨preimage_mem_faces hp hF, fun z hz => hGF ⟨z, hz, rfl⟩, ?_⟩,
      Set.image_preimage_eq_of_subset hFr⟩
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' F)
    rw [Set.image_preimage_eq_of_subset hFr] at this
    rw [← this]; exact hd

/-- A polytope is, after transport to its affine hull and recentring, a polytope with `0` in its
interior. -/
theorem exists_good_affEmb {V : Finset (E d)} (hK : K = convexHull ℝ (V : Set (E d)))
    (hne : K.Nonempty) :
    ∃ p ∈ K, ∃ V' : Finset (E (dim K)),
      affEmb K p ⁻¹' K = convexHull ℝ (V' : Set (E (dim K))) ∧
      (0 : E (dim K)) ∈ interior (convexHull ℝ (V' : Set (E (dim K)))) := by
  classical
  obtain ⟨q, hq⟩ := hne
  set K' := affEmb K q ⁻¹' K with hK'
  have hconv : Convex ℝ K' := by
    have : Convex ℝ K := hK ▸ convex_convexHull ℝ _
    exact this.affine_preimage _
  have himg : affEmb K q '' K' = K :=
    Set.image_preimage_eq_of_subset (subset_range_affEmb hq le_rfl)
  have hdim : dim K' = dim K := by rw [← dim_image_affEmb q K', himg]
  have hne' : K'.Nonempty := by
    obtain ⟨z, hz⟩ := exists_affEmb_eq hq hq
    exact ⟨z, by rw [hK', Set.mem_preimage, hz]; exact hq⟩
  have hspan : affineSpan ℝ K' = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (E (dim K)) (E (dim K))
      hne']
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_euclideanSpace_fin]
    exact hdim
  obtain ⟨c, hc⟩ := hconv.interior_nonempty_iff_affineSpan_eq_top.2 hspan
  have hpK : affEmb K q c ∈ K := by
    have h := interior_subset hc
    rw [hK'] at h
    exact h
  refine ⟨affEmb K q c, hpK, ?_⟩
  set p := affEmb K q c
  have hshift : ∀ z, affEmb K p z = affEmb K q (z + c) := by
    intro z; simp only [p, affEmb_apply, map_add]; abel
  have hinj := affEmb_injective (K := K) p
  set V' := V.preimage (affEmb K p) hinj.injOn
  have hV'coe : (V' : Set (E (dim K))) = affEmb K p ⁻¹' (V : Set (E d)) := Finset.coe_preimage _ _
  have hVsub : (V : Set (E d)) ⊆ K := hK ▸ subset_convexHull ℝ _
  have hconvV' : affEmb K p ⁻¹' K = convexHull ℝ (V' : Set (E (dim K))) := by
    have h1 : affEmb K p '' convexHull ℝ (V' : Set (E (dim K))) = K := by
      rw [AffineMap.image_convexHull, hV'coe,
        Set.image_preimage_eq_of_subset (subset_range_affEmb hpK hVsub), hK]
    ext z
    constructor
    · intro hz
      have hz' : affEmb K p z ∈ affEmb K p '' convexHull ℝ (V' : Set (E (dim K))) := by
        rw [h1]; exact hz
      obtain ⟨w, hw, hwz⟩ := hz'
      rwa [← hinj hwz]
    · intro hz
      have := Set.mem_image_of_mem (affEmb K p) hz
      rwa [h1] at this
  refine ⟨V', hconvV', ?_⟩
  rw [← hconvV']
  have hpre : affEmb K p ⁻¹' K = (Homeomorph.addRight c) ⁻¹' K' := by
    ext z; simp only [Set.mem_preimage, hshift, Homeomorph.coe_addRight, hK']
  rw [hpre, ← Homeomorph.preimage_interior]
  simpa using hc

/-- **Vertices of 3-polytopes.**  In a 3-dimensional polytope (in any `E d`) every vertex lies in
as many edges as 2-faces, and in at least three edges. -/
theorem vertex_up_dim_three {V : Finset (E d)} (hK : K = convexHull ℝ (V : Set (E d)))
    (h3 : dim K = 3) {v : Set (E d)} (hv : v ∈ faces K) (hv0 : dim v = 0) :
    upIn K v 1 = upIn K v 2 ∧ 3 ≤ upIn K v 1 := by
  obtain ⟨p, hp, V', hV', h0⟩ := exists_good_affEmb hK (hv.1.mono (face_subset hv))
  have hvr := subset_range_affEmb hp (face_subset hv)
  have hvv : affEmb K p '' (affEmb K p ⁻¹' v) = v := Set.image_preimage_eq_of_subset hvr
  have hv' : affEmb K p ⁻¹' v ∈ faces (convexHull ℝ (V' : Set (E (dim K)))) :=
    hV' ▸ preimage_mem_faces hp hv
  have hdv : dim (affEmb K p ⁻¹' v) = 0 := by
    have := dim_image_affEmb (K := K) p (affEmb K p ⁻¹' v)
    rw [hvv, hv0] at this
    omega
  have key := upIn_codim_three h0 hv' (by omega)
  simp only [hdv, zero_add] at key
  rw [← hvv, upIn_affEmb hp, upIn_affEmb hp, hV']
  exact key

end transport

/-! ### Centrally symmetric 5-polytopes -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- `incid P R i j = Σ_{i-faces G ⊆ R} #{j-faces H with G ⊆ H ⊆ R}`. -/
lemma IsCSPolytope5.incid_eq_sum_first (R : Set E5) (i j : ℕ) :
    incid P R i j = ∑ G ∈ (hP.below_finite R i).toFinset,
      {H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ R ∧ dim H = j}.ncard := by
  classical
  have hS : {GH : Set E5 × Set E5 | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧ GH.1 ⊆ GH.2 ∧
      GH.2 ⊆ R ∧ dim GH.1 = i ∧ dim GH.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun GH h => ⟨h.1, h.2.1⟩
  rw [incid, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := (hP.below_finite R i).toFinset)
      (fun GH hGH => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hGH
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hGH.1, hGH.2.2.1.trans hGH.2.2.2.1, hGH.2.2.2.2.1⟩)]
  refine Finset.sum_congr rfl fun G hG => ?_
  rw [Set.Finite.mem_toFinset] at hG
  have hfin : {H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ R ∧ dim H = j}.Finite :=
    hP.faces_finite.subset fun H hH => hH.1
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine Finset.card_nbij' Prod.snd (fun H => (G, H)) ?_ ?_ ?_ ?_
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hGH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨-, h2, h3, h4, -, h6⟩, h⟩ := hGH
    exact ⟨h2, h ▸ h3, h4, h6⟩
  · intro H hH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hH.1, hH.2.1, hH.2.2.1, hG.2.2, hH.2.2.2⟩, rfl⟩
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter] at hGH
    obtain ⟨-, h⟩ := hGH
    ext <;> simp [h]
  · intro H _; rfl

/-- `incid P R i j = Σ_{j-faces H ⊆ R} #{i-faces in H}`. -/
lemma IsCSPolytope5.incid_eq_sum_second (R : Set E5) (i j : ℕ) :
    incid P R i j = ∑ H ∈ (hP.below_finite R j).toFinset, cnt P H i := by
  classical
  have hS : {GH : Set E5 × Set E5 | GH.1 ∈ faces P ∧ GH.2 ∈ faces P ∧ GH.1 ⊆ GH.2 ∧
      GH.2 ⊆ R ∧ dim GH.1 = i ∧ dim GH.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun GH h => ⟨h.1, h.2.1⟩
  rw [incid, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := (hP.below_finite R j).toFinset)
      (fun GH hGH => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hGH
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hGH.2.1, hGH.2.2.2.1, hGH.2.2.2.2.2⟩)]
  refine Finset.sum_congr rfl fun H hH => ?_
  rw [Set.Finite.mem_toFinset] at hH
  rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite H i)]
  refine Finset.card_nbij' Prod.fst (fun G => (G, H)) ?_ ?_ ?_ ?_
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hGH
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, -, h3, -, h5, -⟩, h⟩ := hGH
    exact ⟨h1, h ▸ h3, h5⟩
  · intro G hG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hH.1, hG.2.1, hH.2.1, hG.2.2, hH.2.2⟩, rfl⟩
  · intro GH hGH
    rw [Finset.mem_coe, Finset.mem_filter] at hGH
    obtain ⟨-, h⟩ := hGH
    ext <;> simp [h]
  · intro G _; rfl

/-- Every edge has two vertices: `#{(v, E) : v ⊆ E ⊆ R} = 2 f₁(R)`. -/
lemma IsCSPolytope5.incid_zero_one (R : Set E5) : incid P R 0 1 = 2 * cnt P R 1 := by
  rw [hP.incid_eq_sum_second R 0 1]
  have hconst : ∀ H ∈ (hP.below_finite R 1).toFinset, cnt P H 0 = 2 := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    obtain ⟨V, hV⟩ := hP.polytope
    have hH' : H ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hH.1
    have := cnt_zero_of_dim_one hH' hH.2.2
    rwa [← hV] at this
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, cnt,
    Set.ncard_eq_toFinset_card _ (hP.below_finite R 1)]
  ring

/-- Vertices of a 3-face `R`: as many edges as 2-faces of `R` contain `v`, and at least three
edges. -/
lemma IsCSPolytope5.vertex_in_threeface {R v : Set E5} (hR : R ∈ faces P) (h3 : dim R = 3)
    (hv : v ∈ faces P) (hvR : v ⊆ R) (hv0 : dim v = 0) :
    {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ R ∧ dim E = 1}.ncard =
        {Q | Q ∈ faces P ∧ v ⊆ Q ∧ Q ⊆ R ∧ dim Q = 2}.ncard ∧
      3 ≤ {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ R ∧ dim E = 1}.ncard := by
  classical
  obtain ⟨V, hV⟩ := hP.polytope
  have hR' : R ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hR
  have hRV : R = convexHull ℝ ((V.filter (· ∈ R) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hR'
  have hvR' : v ∈ faces R := (mem_faces_face_iff hR').2 ⟨hV ▸ hv, hvR⟩
  have key := vertex_up_dim_three hRV h3 hvR' hv0
  have hup : ∀ j, upIn R v j = {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ R ∧ dim E = j}.ncard := by
    intro j
    unfold upIn
    congr 1
    ext E
    simp only [Set.mem_ofPred_eq, mem_faces_face_iff hR', ← hV]
    tauto
  rw [hup, hup] at key
  exact key

/-- Summed over the vertices of a 3-face `R`: `f₀₂(R) = f₀₁(R)` and `3 f₀(R) ≤ f₀₁(R)`. -/
lemma IsCSPolytope5.threeface_vertex_sums {R : Set E5} (hR : R ∈ faces P) (h3 : dim R = 3) :
    incid P R 0 2 = incid P R 0 1 ∧ 3 * cnt P R 0 ≤ incid P R 0 1 := by
  rw [hP.incid_eq_sum_first R 0 2, hP.incid_eq_sum_first R 0 1]
  constructor
  · refine Finset.sum_congr rfl fun v hv => ?_
    rw [Set.Finite.mem_toFinset] at hv
    exact (hP.vertex_in_threeface hR h3 hv.1 hv.2.1 hv.2.2).1.symm
  · rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite R 0), Finset.card_eq_sum_ones,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun v hv => ?_
    rw [Set.Finite.mem_toFinset] at hv
    have := (hP.vertex_in_threeface hR h3 hv.1 hv.2.1 hv.2.2).2
    omega

/-- **`B ≥ 0`**: `B = Σ_{3-faces R} (2 f₁(R) - 3 f₀(R))` and every vertex of a 3-polytope has
degree at least three. -/
theorem IsCSPolytope5.B_nonneg : 0 ≤ (flagDataOf P).B := by
  simp only [FlagData.B, flagDataOf]
  rw [hP.flag2_eq_sum 1 3, hP.flag2_eq_sum 0 3]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_nonneg fun R hR => ?_
  rw [Set.Finite.mem_toFinset] at hR
  have h := (hP.threeface_vertex_sums hR.1 hR.2).2
  rw [hP.incid_zero_one R] at h
  have : (3 : ℤ) * cnt P R 0 ≤ 2 * cnt P R 1 := by exact_mod_cast h
  linarith

/-- `f₀₂₄ = f₀₂₃ = 2 f₁₃`. -/
theorem IsCSPolytope5.flag3_024_eq : flag3 P 0 2 4 = 2 * flag2 P 1 3 := by
  rw [hP.flag3_eq_sum_mid 0 2 4]
  have h1 : ∑ Q ∈ (hP.kfaces_finite 2).toFinset,
        cnt P Q 0 * {H | H ∈ faces P ∧ Q ⊆ H ∧ dim H = 4}.ncard =
      ∑ Q ∈ (hP.kfaces_finite 2).toFinset,
        cnt P Q 0 * {H | H ∈ faces P ∧ Q ⊆ H ∧ dim H = 3}.ncard := by
    refine Finset.sum_congr rfl fun Q hQ => ?_
    rw [Set.Finite.mem_toFinset] at hQ
    have := hP.twoface_identity hQ.1 hQ.2
    unfold up at this
    rw [this]
  rw [h1, ← hP.flag3_eq_sum_mid 0 2 3, hP.flag3_eq_sum_last 0 2 3, hP.flag2_eq_sum 1 3,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun R hR => ?_
  rw [Set.Finite.mem_toFinset] at hR
  rw [(hP.threeface_vertex_sums hR.1 hR.2).1, hP.incid_zero_one R]

/-- **Summed Euler relation in vertex–facet intervals.** -/
theorem IsCSPolytope5.flag024_identity :
    (flag3 P 0 2 4 : ℤ) = 2 * flag2 P 0 4 + 2 * flag2 P 0 2 + 2 * flag2 P 2 4
      - 4 * (fvec P 1 + fvec P 3) := by
  rw [hP.flag3_024_eq]
  push_cast
  rw [hP.flag13_identity]
  ring

end cs

end Kalai5
