import Kalai5.Pyramid.Parity

/-! Generalize the coordinate construction of `exists_bipyramid_model` to
an arbitrary full pyramid facet. No vertex count or exceptional row is assumed. -/
namespace Kalai5
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.full_pyramid_bipyramid_model {F v T : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hfull : 2 * cnt P F 0 = fvec P 0)
    (hv : v ∈ faces P) (hv0 : dim v = 0) (hvF : v ⊆ F)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hTF : T ⊆ F) (hvT : ¬ v ⊆ T)
    (hall : ∀ w ∈ faces P, dim w = 0 → w ⊆ F → w ≠ v → w ⊆ T) :
    ∃ (V' : Finset (E 4)) (L : E 5 →ₗ[ℝ] E5), Function.Injective L ∧
      IsCSPolytope 4 (convexHull ℝ (V' : Set (E 4))) ∧
      L '' convexHull ℝ ((bipyrV V' : Finset (E 5)) : Set (E 5)) = P := by
  classical
  obtain ⟨a, rfl⟩ := eq_singleton_of_dim_eq_zero hv.1 hv0
  have haP : a ∈ P.extremePoints ℝ := isExtreme_singleton.1 hv.2.isExtreme
  have haF : a ∈ F := hvF rfl
  have haT : a ∉ T := fun h => hvT (Set.singleton_subset_iff.2 h)
  obtain ⟨V, hV⟩ := hP.polytope
  have h0V : (0 : E5) ∈ interior (convexHull ℝ (V : Set E5)) := hV ▸ hP.zero_mem_interior
  -- the vertex set
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = fvec P 0 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hXdef, ← h1, ← hV]
  have hPX : P = convexHull ℝ (X : Set E5) := by
    rw [hXcoe, hV, convexHull_extremePoints_eq]
  have hXs : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hvertface : ∀ x ∈ X, ({x} : Set E5) ∈ faces P := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx
    rw [hV] at hx ⊢
    exact singleton_mem_faces_of_extreme hx
  -- the vertices of `F` and of `T`
  set XF := X.filter (· ∈ F) with hXFdef
  set B := X.filter (· ∈ T) with hBdef
  have hXF_eq : XF = insert a B := by
    ext x
    simp only [hXFdef, hBdef, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hxX, hxF⟩
      by_cases hxa : x = a
      · left; exact hxa
      · right
        refine ⟨hxX, ?_⟩
        have := hall {x} (hvertface x hxX) (dim_singleton x) (Set.singleton_subset_iff.2 hxF)
          (fun h => hxa (Set.singleton_injective h))
        exact this rfl
    · rintro (rfl | ⟨hxX, hxT⟩)
      · exact ⟨by rw [← Finset.mem_coe, hXcoe]; exact haP, haF⟩
      · exact ⟨hxX, hTF hxT⟩
  have haB : a ∉ B := fun h => haT (Finset.mem_filter.1 h).2
  have haX : a ∈ X := by rw [← Finset.mem_coe, hXcoe]; exact haP
  -- `F` misses every antipode of its vertices
  have hFanti : ∀ x ∈ F, -x ∉ F := fun x hx hnx => by
    have := hP.eq_of_mem_of_neg_mem hF hx hnx
    rw [this, hP.dim_self] at h4
    omega
  have hXFcard : XF.card = cnt P F 0 := by
    have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
    have hext : (XF : Set E5) = F.extremePoints ℝ := by
      rw [hF.2.isExtreme.extremePoints_eq, hXFdef, Finset.coe_filter, ← hXcoe]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
      tauto
    set SF := V.filter (· ∈ F)
    have hFSF : F = convexHull ℝ (SF : Set E5) := face_eq_convexHull_filter hF'
    have h1 : cnt P F 0 = fvec F 0 := by
      rw [hV]
      exact (fvec_face_eq_cnt hF' 0).symm
    have h2 : fvec F 0 = (F.extremePoints ℝ).ncard := by
      have := fvec_zero_eq SF
      rwa [← hFSF] at this
    rw [h1, h2, ← hext, Set.ncard_coe_finset]
  have hX_eq : X = XF ∪ XF.image (fun x => -x) := by
    have hsub : XF ∪ XF.image (fun x => -x) ⊆ X := by
      intro x hx
      rcases Finset.mem_union.1 hx with hx | hx
      · exact (Finset.mem_filter.1 hx).1
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        exact hXs y (Finset.mem_filter.1 hy).1
    have hdisj : Disjoint XF (XF.image fun x => -x) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx'
      exact hFanti y (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hx).2
    have hcard : (XF ∪ XF.image fun x => -x).card = fvec P 0 := by
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ neg_injective, hXFcard]
      omega
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hXcard, hcard])).symm
  -- the dual vector of `F`
  have hFne : F ≠ convexHull ℝ (V : Set E5) := fun h => by
    have := hP.dim_self
    rw [hV, ← h, h4] at this
    omega
  obtain ⟨c, -, hcF⟩ := exists_dual_vector h0V (hV ▸ hF) hFne
  have hcF' : ∀ x ∈ F, ⟪x, c⟫ = 1 := fun x hx =>
    (hcF x (hV ▸ face_subset hF hx)).1 hx
  have hBF : ∀ b ∈ B, b ∈ F := fun b hb => hTF (Finset.mem_filter.1 hb).2
  have hcB : ∀ b ∈ (B : Set E5), ⟪b, c⟫ = 1 := fun b hb => hcF' b (hBF b hb)
  have hca : ⟪a, c⟫ = 1 := hcF' a haF
  -- `T = conv B`
  have hTB : T = convexHull ℝ (B : Set E5) := by
    have hT' : T ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hT
    set ST := V.filter (· ∈ T)
    have hTST : T = convexHull ℝ (ST : Set E5) := face_eq_convexHull_filter hT'
    have hext : (B : Set E5) = T.extremePoints ℝ := by
      rw [hT.2.isExtreme.extremePoints_eq, hBdef, Finset.coe_filter, ← hXcoe]
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Finset.mem_coe]
      tauto
    rw [hext]
    conv_lhs => rw [hTST]
    rw [← convexHull_extremePoints_eq ST, ← hTST]
  -- the linear span of the base
  have hBne : B.Nonempty := by
    by_contra hn
    have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.1 hn
    rw [he,Finset.coe_empty,convexHull_empty] at hTB
    exact hT.1.ne_empty hTB
  obtain ⟨b0, hb0⟩ := hBne
  have hvsB : Module.finrank ℝ (vectorSpan ℝ (B : Set E5)) = 3 := by
    have h := hT3
    rw [hTB] at h
    change Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (B : Set E5))) = 3 at h
    rwa [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan] at h
  have hb0ne : b0 ≠ 0 := fun h => by
    have := hcB b0 hb0
    rw [h, inner_zero_left] at this
    norm_num at this
  have hb0vs : b0 ∉ vectorSpan ℝ (B : Set E5) := fun h => by
    have := inner_vectorSpan_eq_zero hcB b0 h
    rw [hcB b0 hb0] at this
    norm_num at this
  set W := Submodule.span ℝ (B : Set E5) with hWdef
  have hWeq : W = vectorSpan ℝ (B : Set E5) ⊔ ℝ ∙ b0 := by
    apply le_antisymm
    · rw [hWdef, Submodule.span_le]
      intro b hb
      have e : b = (b -ᵥ b0) + b0 := by rw [vsub_eq_sub, sub_add_cancel]
      rw [e]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (vsub_mem_vectorSpan ℝ hb hb0))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b0))
    · apply sup_le
      · rw [vectorSpan_def, Submodule.span_le]
        rintro _ ⟨x, hx, y, hy, rfl⟩
        exact Submodule.sub_mem _ (Submodule.subset_span hx) (Submodule.subset_span hy)
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact Submodule.subset_span hb0
  have hW4 : Module.finrank ℝ W = 4 := by
    rw [hWeq]
    have hdisj : vectorSpan ℝ (B : Set E5) ⊓ (ℝ ∙ b0) = ⊥ :=
      (Submodule.disjoint_span_singleton.2 fun h => absurd h hb0vs).eq_bot
    have := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ (B : Set E5)) (ℝ ∙ b0)
    rw [hdisj, finrank_bot, hvsB, finrank_span_singleton hb0ne] at this
    omega
  -- the apex is outside the span of the base
  have haW : a ∉ W := by
    intro haW
    rw [hWeq, Submodule.mem_sup] at haW
    obtain ⟨w, hw, u, hu, hwu⟩ := haW
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hu
    have ht : t = 1 := by
      have h1 := congrArg (fun x => ⟪x, c⟫) hwu
      simp only [inner_add_left, real_inner_smul_left] at h1
      rw [inner_vectorSpan_eq_zero hcB w hw, hcB b0 hb0, hca] at h1
      linarith
    rw [ht, one_smul] at hwu
    have hdirA : a -ᵥ b0 ∈ (affineSpan ℝ (B : Set E5)).direction := by
      rw [direction_affineSpan, vsub_eq_sub, ← hwu, add_sub_cancel_right]
      exact hw
    have haA : a ∈ affineSpan ℝ (B : Set E5) := by
      have := AffineSubspace.vadd_mem_of_mem_direction hdirA (subset_affineSpan ℝ _ hb0)
      rwa [vsub_vadd] at this
    have haTA : a ∈ affineSpan ℝ T := by rw [hTB, affineSpan_convexHull]; exact haA
    have hTfF : T ∈ faces F := mem_faces_of_subset (face_subset hF) hT hTF
    exact haT (inter_affineSpan_subset hTfF ⟨haF, haTA⟩)
  -- coordinates on `W`
  set bW := Module.finBasisOfFinrankEq ℝ W hW4
  let ι : E 4 →ₗ[ℝ] E5 := W.subtype ∘ₗ bW.equivFun.symm.toLinearMap ∘ₗ
    (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).toLinearMap
  have hιinj : Function.Injective ι := by
    simp only [ι, LinearMap.coe_comp]
    exact Subtype.val_injective.comp (bW.equivFun.symm.injective.comp
      (WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).injective)
  have hιmem : ∀ y, ι y ∈ W := fun y =>
    (bW.equivFun.symm ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)) y)).2
  have hιrange : ∀ w ∈ W, ∃ y, ι y = w := fun w hw => by
    refine ⟨(WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm (bW.equivFun ⟨w, hw⟩), ?_⟩
    show ((bW.equivFun.symm ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ))
      ((WithLp.linearEquiv 2 ℝ (Fin 4 → ℝ)).symm (bW.equivFun ⟨w, hw⟩))) : W) : E5) = w
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply]
  -- the linear isomorphism `L`
  let L : E 5 →ₗ[ℝ] E5 :=
    { toFun := fun z => ι (fstPart z) + z (Fin.last 4) • a
      map_add' := fun z z' => by
        have := (fstPartLin 4).map_add z z'
        simp only [fstPartLin, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [this, map_add, PiLp.add_apply, add_smul]
        abel
      map_smul' := fun r z => by
        have := (fstPartLin 4).map_smul r z
        simp only [fstPartLin, LinearMap.coe_mk, AddHom.coe_mk] at this
        rw [this, map_smul, PiLp.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, smul_add] }
  have hL : ∀ z, L z = ι (fstPart z) + z (Fin.last 4) • a := fun _ => rfl
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hL] at hz
    have hlast : z (Fin.last 4) = 0 := by
      by_contra hne
      apply haW
      have : a = -(z (Fin.last 4))⁻¹ • ι (fstPart z) := by
        rw [eq_neg_iff_add_eq_zero.2 hz, smul_neg, neg_smul, neg_neg, smul_smul,
          inv_mul_cancel₀ hne, one_smul]
      rw [this]
      exact W.smul_mem _ (hιmem _)
    rw [hlast, zero_smul, add_zero] at hz
    have hfst : fstPart z = 0 := hιinj (by rw [hz, map_zero])
    refine PiLp.ext fun j => ?_
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hlast
    · have := congrArg (fun y : E 4 => y i) hfst
      simpa using this
  -- the base polytope `R'`
  set S := B ∪ B.image (fun x => -x) with hSdef
  have hSW : (S : Set E5) ⊆ Set.range ι := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · exact hιrange x (Submodule.subset_span hx)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      exact hιrange _ (W.neg_mem (Submodule.subset_span hy))
  set V' := S.preimage ι hιinj.injOn with hV'def
  have hV'coe : ι '' (V' : Set (E 4)) = S := by
    rw [hV'def, Finset.coe_preimage]
    exact Set.image_preimage_eq_of_subset hSW
  have hV'symm : ∀ y ∈ V', -y ∈ V' := by
    intro y hy
    rw [hV'def, Finset.mem_preimage] at hy ⊢
    rw [map_neg]
    rcases Finset.mem_union.1 hy with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
    · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.1 h
      rw [← hxe, neg_neg]
      exact Finset.mem_union_left _ hx
  have hR'cs : IsCSPolytope 4 (convexHull ℝ (V' : Set (E 4))) := by
    refine ⟨⟨⟨V', rfl⟩, ?_⟩, ?_⟩
    · -- full-dimensional
      rw [(convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top, affineSpan_convexHull]
      have hne : (V' : Set (E 4)).Nonempty := by
        have hb0S : b0 ∈ (S : Set E5) := Finset.mem_coe.2 (Finset.mem_union_left _ hb0)
        rw [← hV'coe] at hb0S
        obtain ⟨y, hy, -⟩ := hb0S
        exact ⟨y, hy⟩
      rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ (E 4) (E 4) hne]
      have hspan : Submodule.span ℝ (V' : Set (E 4)) = ⊤ := by
        apply Submodule.map_injective_of_injective hιinj
        rw [Submodule.map_span, hV'coe, Submodule.map_top]
        apply le_antisymm
        · rw [Submodule.span_le]
          intro x hx
          obtain ⟨y, rfl⟩ := hSW hx
          exact LinearMap.mem_range_self ι y
        · rintro _ ⟨y, rfl⟩
          have hW' : W ≤ Submodule.span ℝ (S : Set E5) := by
            rw [hWdef]
            apply Submodule.span_mono
            intro x hx
            exact Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 hx))
          exact hW' (hιmem y)
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      intro y hy
      have h2 : y - -y ∈ vectorSpan ℝ (V' : Set (E 4)) :=
        vsub_mem_vectorSpan ℝ hy (hV'symm y (Finset.mem_coe.1 hy))
      have : y = (1 / 2 : ℝ) • (y - -y) := by
        rw [sub_neg_eq_add, smul_add, ← add_smul]; norm_num
      rw [SetLike.mem_coe, this]
      exact Submodule.smul_mem _ _ h2
    · -- symmetric
      intro x hx
      have hneg : -(convexHull ℝ (V' : Set (E 4))) = convexHull ℝ (V' : Set (E 4)) := by
        rw [← convexHull_neg]
        congr 1
        ext y
        simp only [Set.mem_neg, Finset.mem_coe]
        exact ⟨fun h => by simpa using hV'symm _ h, fun h => hV'symm y h⟩
      rw [← hneg]
      simpa using hx
  -- `P` is the image of the bipyramid
  have hLbip : L '' convexHull ℝ ((bipyrV V' : Finset (E 5)) : Set (E 5)) = P := by
    rw [LinearMap.image_convexHull, hPX]
    congr 1
    ext x
    simp only [bipyrV, Finset.coe_union, Finset.coe_image, Finset.coe_insert,
      Finset.coe_singleton, Set.image_union, Set.image_insert_eq, Set.image_singleton,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image, Finset.mem_coe]
    constructor
    · rintro (⟨_, ⟨y, hy, rfl⟩, rfl⟩ | rfl | rfl)
      · rw [hL, fstPart_mkPt, mkPt_last, zero_smul, add_zero]
        have : ι y ∈ (S : Set E5) := by rw [← hV'coe]; exact ⟨y, hy, rfl⟩
        rw [hX_eq, hXF_eq]
        rcases Finset.mem_union.1 (Finset.mem_coe.1 this) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem h)
        · obtain ⟨b, hb, hbe⟩ := Finset.mem_image.1 h
          rw [← hbe]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem hb))
      · rw [hL, fstPart_mkPt, mkPt_last, map_zero, zero_add, one_smul]
        exact haX
      · rw [hL, fstPart_mkPt, mkPt_last, map_zero, zero_add, neg_one_smul]
        exact hXs a haX
    · intro hx
      rw [hX_eq, hXF_eq] at hx
      rcases Finset.mem_union.1 hx with hx | hx
      · rcases Finset.mem_insert.1 hx with rfl | hx
        · right; left
          rw [hL, fstPart_mkPt, mkPt_last, map_zero, zero_add, one_smul]
        · left
          have : x ∈ (S : Set E5) := Finset.mem_coe.2 (Finset.mem_union_left _ hx)
          rw [← hV'coe] at this
          obtain ⟨y, hy, rfl⟩ := this
          exact ⟨mkPt y 0, ⟨y, hy, rfl⟩, by rw [hL, fstPart_mkPt, mkPt_last, zero_smul, add_zero]⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
        rcases Finset.mem_insert.1 hy with rfl | hy
        · right; right
          rw [hL, fstPart_mkPt, mkPt_last, map_zero, zero_add, neg_one_smul]
        · left
          have : -y ∈ (S : Set E5) :=
            Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hy))
          rw [← hV'coe] at this
          obtain ⟨z, hz, hze⟩ := this
          exact ⟨mkPt z 0, ⟨z, hz, rfl⟩, by rw [hL, fstPart_mkPt, mkPt_last, zero_smul, add_zero, hze]⟩
  exact ⟨V', L, hLinj, hR'cs, hLbip⟩

end Kalai5
