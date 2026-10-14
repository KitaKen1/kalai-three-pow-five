import Kalai5.Rigidity.Stress3
import Kalai5.Rigidity.WhiteleyAssembly
import Kalai5.Rigidity.Step

/-!
# Two-facet stress localization `2 (g(H) + g(H')) ≤ G`

For a centrally symmetric 5-polytope and two facets `H, H'` with `H' ≠ ±H`, the stresses of the
Whiteley bars inside `H` and inside `H'` are independent of each other and of their antipodes:

* the Whiteley bars inside a face of dimension at most three carry no stress
  (`IsCSPolytope5.stress_vanish_of_face`: the face lies in a 3-face, whose bars brace it and
  number `3 f₀ - 6`, `stressSpace_eq_bot_of_braces3`);
* a relation between the four stress spaces leaves a stress of `H` supported on the bars of the
  two disjoint faces `H ∩ H'` and `H ∩ -H'`, hence zero;
* antisymmetrization (`two_mul_finrank_le_of_antisymm_inj`) then gives
  `2 (dim stress(B_H) + dim stress(B_H')) ≤ G`, and each dimension is at least the local `g`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section edges

variable {n : ℕ}

/-- **A face of dimension at least one contains an edge.** -/
lemma exists_edge_of_face {V : Finset (E n)} {F : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hd : 1 ≤ dim F) :
    ∃ Ed ∈ faces (convexHull ℝ (V : Set (E n))), dim Ed = 1 ∧ Ed ⊆ F := by
  classical
  set W := vertFinset (V.filter (· ∈ F)) with hW
  have hFW : F = convexHull ℝ (W : Set (E n)) := by
    rw [hW, convexHull_vertFinset]; exact face_eq_convexHull_filter hF
  have hcp : ConvPos W := convPos_vertFinset _
  have h2 : 1 < W.card := by
    by_contra hle
    push_neg at hle
    obtain ⟨x, hx⟩ := Finset.card_le_one_iff_subset_singleton.1 hle
    have hx' : (W : Set (E n)) ⊆ {x} := by
      intro y hy
      have := hx (Finset.mem_coe.1 hy)
      simpa using this
    have hFx : F ⊆ {x} := by
      rw [hFW]; exact convexHull_min hx' (convex_singleton x)
    have h0 : dim F = 0 := by
      unfold dim
      have := vectorSpan_mono ℝ hFx
      rw [vectorSpan_singleton] at this
      rw [le_bot_iff.1 this, finrank_bot]
    omega
  obtain ⟨x, hx, z, hz, hxz⟩ := Finset.one_lt_card.1 h2
  obtain ⟨μ, -, hμ⟩ := nbrs_cone hcp hx hz
  have hne : (nbrs W x).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp, Finset.sum_empty, sub_eq_zero] at hμ
    exact hxz hμ.symm
  obtain ⟨y, hy⟩ := hne
  obtain ⟨-, -, Ed, hEd, hEd1, -, -⟩ := mem_nbrs.1 hy
  rw [← hFW] at hEd
  exact ⟨Ed, faces_trans hF hEd, hEd1, face_subset hEd⟩

end edges

/-! ### Antisymmetrization for an arbitrary space of stresses -/

section antisymm

variable {d : ℕ}

/-- **Antisymmetrization bound** for any space of stresses of a symmetric infinitesimally rigid
framework on which antisymmetrization is injective: `2 · dim W + d |X| ≤ |B| + 2d`. -/
theorem two_mul_finrank_le_of_antisymm_inj {X : Finset (E d)} {B : Finset (Sym2 (E d))}
    (hXs : ∀ x ∈ X, -x ∈ X) (hX0 : (0 : E d) ∉ X)
    (hspan : Submodule.span ℝ (X : Set (E d)) = ⊤)
    (hBs : ∀ b ∈ B, b.map Neg.neg ∈ B) (hBfree : ∀ b ∈ B, b.map Neg.neg ≠ b)
    (hrig : IsInfRigid (X : Set (E d)) (B : Set (Sym2 (E d))))
    {W : Type*} [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (Φ : W →ₗ[ℝ] (Sym2 (E d) → ℝ))
    (hstr : ∀ w (u : E d → E d), ∑ b ∈ B, Φ w b * barVal u b = 0)
    (hinj : ∀ w, (∀ b ∈ B, Φ w b = Φ w (b.map Neg.neg)) → w = 0) :
    2 * Module.finrank ℝ W + d * X.card ≤ B.card + 2 * d := by
  classical
  have hXfree : ∀ x ∈ X, -x ≠ x := fun x hx h => by
    have h2 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← h]
      exact neg_add_cancel x
    have : x = 0 := (smul_eq_zero.1 h2).resolve_left two_ne_zero
    exact hX0 (this ▸ hx)
  have hσσ : ∀ b : Sym2 (E d), (b.map Neg.neg).map Neg.neg = b := fun b => by
    rw [Sym2.map_map]; simp
  obtain ⟨Xp, hXpX, hXcov, hXdis, hXcard⟩ :=
    exists_half_of_involution (fun x : E d => -x) (fun a => neg_neg a) _ X rfl hXs hXfree
  obtain ⟨Bp, hBpB, hBcov, hBdis, hBcard⟩ :=
    exists_half_of_involution (fun b : Sym2 (E d) => b.map Neg.neg) hσσ _ B rfl hBs hBfree
  have hkerle := finrank_ker_evenRigMap_le hXs hspan hXpX hXdis hBcov hrig
  have hrn := LinearMap.finrank_range_add_finrank_ker (evenRigMap Xp Bp)
  have hdom : Module.finrank ℝ (Xp → E d) = Xp.card * d := by
    rw [Module.finrank_pi_fintype]
    simp
  -- the antisymmetrization map
  let T : W →ₗ[ℝ] EuclideanSpace ℝ Bp :=
    { toFun := fun w => WithLp.toLp 2 (fun b => Φ w b.1 - Φ w (b.1.map Neg.neg))
      map_add' := fun w w' => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.toLp_apply, PiLp.add_apply, map_add, Pi.add_apply]
        ring
      map_smul' := fun a w => by
        refine PiLp.ext fun b => ?_
        simp only [PiLp.toLp_apply, PiLp.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        ring }
  have hT : ∀ w (b : Bp), T w b = Φ w b.1 - Φ w (b.1.map Neg.neg) := fun _ _ => rfl
  have hT_inj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    apply hinj
    intro b hb
    rcases hBcov b hb with h | h
    · have := congrArg (fun z : EuclideanSpace ℝ Bp => z ⟨b, h⟩) hw
      simp only [hT, PiLp.zero_apply] at this
      linarith
    · have := congrArg (fun z : EuclideanSpace ℝ Bp => z ⟨_, h⟩) hw
      simp only [hT, PiLp.zero_apply, hσσ] at this
      linarith
  have hT_perp : LinearMap.range T ≤ (LinearMap.range (evenRigMap Xp Bp))ᗮ := by
    rintro _ ⟨w, rfl⟩
    rw [Submodule.mem_orthogonal']
    rintro _ ⟨v, rfl⟩
    rw [inner_euclid]
    set f := barVal (evenExt Xp v) with hf
    have heven : ∀ p, evenExt Xp v (-p) = evenExt Xp v p := evenExt_neg hXdis v
    have hfneg : ∀ b, f (b.map Neg.neg) = -f b := fun b => barVal_neg_of_even heven b
    set Ω := Φ w with hΩ
    have hsum1 : ∑ b : Bp, T w b * evenRigMap Xp Bp v b =
        ∑ b ∈ Bp, (Ω b - Ω (b.map Neg.neg)) * f b := by
      rw [← Finset.sum_coe_sort Bp]
      rfl
    rw [hsum1]
    have hsplit : ∑ b ∈ Bp, (Ω b - Ω (b.map Neg.neg)) * f b =
        ∑ b ∈ Bp, Ω b * f b + ∑ b ∈ Bp, Ω (b.map Neg.neg) * f (b.map Neg.neg) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hfneg]; ring
    have hinjσ : Set.InjOn (fun b : Sym2 (E d) => b.map Neg.neg) (Bp : Set (Sym2 (E d))) :=
      fun a _ b _ hab => by
        have := congrArg (fun z : Sym2 (E d) => z.map Neg.neg) hab
        simpa only [hσσ] using this
    have himg : ∑ b ∈ Bp, Ω (b.map Neg.neg) * f (b.map Neg.neg) =
        ∑ c ∈ Bp.image (fun b => b.map Neg.neg), Ω c * f c :=
      (Finset.sum_image (f := fun c => Ω c * f c) hinjσ).symm
    have hdisj : Disjoint Bp (Bp.image fun b => b.map Neg.neg) := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc'
      exact hBdis b hb hc
    have hunion : Bp ∪ Bp.image (fun b => b.map Neg.neg) = B := by
      ext c
      constructor
      · intro hc
        rcases Finset.mem_union.1 hc with hc | hc
        · exact hBpB hc
        · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
          exact hBs b (hBpB hb)
      · intro hc
        rcases hBcov c hc with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, hσσ c⟩)
    rw [hsplit, himg, ← Finset.sum_union hdisj, hunion]
    exact hstr w (evenExt Xp v)
  -- dimension count
  have h1 : Module.finrank ℝ W = Module.finrank ℝ (LinearMap.range T) :=
    (LinearMap.finrank_range_of_inj hT_inj).symm
  have h2 : Module.finrank ℝ (LinearMap.range T) ≤
      Module.finrank ℝ (LinearMap.range (evenRigMap Xp Bp))ᗮ := Submodule.finrank_mono hT_perp
  have h3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.range (evenRigMap Xp Bp))
  rw [finrank_euclideanSpace, Fintype.card_coe] at h3
  rw [hdom] at hrn
  have hXc : X.card = 2 * Xp.card := hXcard.symm
  have hBc : B.card = 2 * Bp.card := hBcard.symm
  have key : Module.finrank ℝ W + Xp.card * d ≤ Bp.card + d := by omega
  rw [hXc, hBc]
  calc 2 * Module.finrank ℝ W + d * (2 * Xp.card)
      = 2 * (Module.finrank ℝ W + Xp.card * d) := by ring
    _ ≤ 2 * (Bp.card + d) := Nat.mul_le_mul_left 2 key
    _ = 2 * Bp.card + 2 * d := by ring

end antisymm

/-! ### Faces of centrally symmetric 5-polytopes -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Every face of dimension at most three lies in a 3-face.** -/
lemma IsCSPolytope5.exists_three_face_above {G : Set E5} (hG : G ∈ faces P) (hd : dim G ≤ 3) :
    ∃ T ∈ faces P, dim T = 3 ∧ G ⊆ T := by
  classical
  rcases Nat.lt_or_ge (dim G) 3 with hlt | hge
  · have hne : G ≠ P := fun h => by rw [h, hP.dim_self] at hlt; omega
    have hup : up P G 3 = cnt (polarSet P) (dualFace P G) 1 := hP.up_eq_cnt_dual hG hne 3 (by norm_num)
    obtain ⟨hdual, hdd⟩ := hP.dualFace_mem hG hne
    obtain ⟨W, hW⟩ := hP.polar.polytope
    have hdual' : dualFace P G ∈ faces (convexHull ℝ (W : Set E5)) := by rw [← hW]; exact hdual
    obtain ⟨Ed, hEd, hEd1, hEdsub⟩ := exists_edge_of_face hdual' (by omega)
    have hfin : {F | F ∈ faces (polarSet P) ∧ F ⊆ dualFace P G ∧ dim F = 1}.Finite :=
      (faces_finite_convexHull W).subset fun F hF => by rw [← hW]; exact hF.1
    have hpos : 0 < cnt (polarSet P) (dualFace P G) 1 := by
      unfold cnt
      rw [Set.ncard_pos hfin]
      exact ⟨Ed, by rw [hW]; exact hEd, hEdsub, hEd1⟩
    rw [← hup] at hpos
    unfold up at hpos
    have hne0 : {F | F ∈ faces P ∧ G ⊆ F ∧ dim F = 3}.ncard ≠ 0 := by omega
    obtain ⟨T, hT, hGT, hT3⟩ := Set.nonempty_of_ncard_ne_zero hne0
    exact ⟨T, hT, hT3, hGT⟩
  · exact ⟨G, hG, le_antisymm hd hge, subset_rfl⟩

/-- The vertex data of a face of `P`. -/
lemma IsCSPolytope5.face_vertex_data {V : Finset E5} (hV : P = convexHull ℝ (V : Set E5))
    {F : Set E5} (hF : F ∈ faces P) :
    ∃ XF : Finset E5, (XF : Set E5) = F.extremePoints ℝ ∧ XF.card = cnt P F 0 ∧
      ∃ p0 ∈ XF, (∀ p ∈ XF, p - p0 ∈ vectorSpan ℝ F) ∧
        vectorSpan ℝ F ≤ Submodule.span ℝ ((fun p => p - p0) '' (XF : Set E5)) := by
  classical
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  set SF := V.filter (· ∈ F) with hSFdef
  have hFSF : F = convexHull ℝ (SF : Set E5) := face_eq_convexHull_filter hF'
  set XF := (extremePoints_finite SF).toFinset with hXFdef
  have hXFcoe : (XF : Set E5) = F.extremePoints ℝ := by
    rw [hXFdef, Set.Finite.coe_toFinset, ← hFSF]
  refine ⟨XF, hXFcoe, ?_, ?_⟩
  · have h1 : cnt P F 0 = fvec F 0 := by
      rw [hV]
      exact (fvec_face_eq_cnt hF' 0).symm
    have h2 : fvec F 0 = (F.extremePoints ℝ).ncard := by
      have := fvec_zero_eq SF
      rwa [← hFSF] at this
    rw [h1, h2, ← hXFcoe, Set.ncard_coe_finset]
  · have hFne : F.Nonempty := hF.1
    have hFconv : F = convexHull ℝ (F.extremePoints ℝ) := by
      conv_lhs => rw [hFSF]
      rw [← convexHull_extremePoints_eq SF, ← hFSF]
    obtain ⟨p0, hp0⟩ : (F.extremePoints ℝ).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, convexHull_empty] at hFconv
      rw [hFconv] at hFne
      exact Set.not_nonempty_empty hFne
    have hp0XF : p0 ∈ XF := by rw [← Finset.mem_coe, hXFcoe]; exact hp0
    have hXF_F : ∀ p ∈ XF, p ∈ F := fun p hp => by
      rw [← Finset.mem_coe, hXFcoe] at hp; exact hp.1
    refine ⟨p0, hp0XF, fun p hp => vsub_mem_vectorSpan ℝ (hXF_F p hp) (hXF_F p0 hp0XF), ?_⟩
    have e1 : vectorSpan ℝ F = vectorSpan ℝ (F.extremePoints ℝ) := by
      conv_lhs => rw [hFconv]
      rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    rw [e1, vectorSpan_eq_span_vsub_set_right ℝ hp0, hXFcoe]
    rfl

open Classical in
/-- **Stresses of the Whiteley bars inside a face of dimension at most three vanish.** -/
lemma IsCSPolytope5.stress_vanish_of_face {B : Finset (Sym2 E5)}
    (hBX : ∀ b ∈ B, ∀ p ∈ b, p ∈ P.extremePoints ℝ)
    (hB3br : ∀ T ∈ faces P, dim T = 3 →
      Braces ((B.filter fun b => ∀ p ∈ b, p ∈ T : Finset (Sym2 E5)) : Set (Sym2 E5))
        (T.extremePoints ℝ))
    (hB3 : ∀ T ∈ faces P, dim T = 3 → (B.filter fun b => ∀ p ∈ b, p ∈ T).card + 6 = 3 * cnt P T 0)
    {R : Set E5} (hR : R ∈ faces P) (hd : dim R ≤ 3)
    (Ω : Sym2 E5 → ℝ) (hsupp : ∀ b, Ω b ≠ 0 → b ∈ B ∧ ∀ p ∈ b, p ∈ R)
    (hstr : ∀ u : E5 → E5, ∑ b ∈ B, Ω b * barVal u b = 0) :
    ∀ b, Ω b = 0 := by
  classical
  obtain ⟨T, hT, hT3, hRT⟩ := hP.exists_three_face_above hR hd
  obtain ⟨V, hV⟩ := hP.polytope
  obtain ⟨XF, hXFcoe, hXFcard, p0, hp0, hdiff, hspanF⟩ := hP.face_vertex_data hV hT
  have hText : IsExtreme ℝ P T := hT.2.isExtreme
  set BT := B.filter (fun b => ∀ p ∈ b, p ∈ T) with hBTdef
  have hBT : ∀ b ∈ BT, ∀ p ∈ b, p ∈ XF := by
    intro b hb p hp
    rw [hBTdef, Finset.mem_filter] at hb
    rw [← Finset.mem_coe, hXFcoe, hText.extremePoints_eq]
    exact ⟨hb.2 p hp, hBX b hb.1 p hp⟩
  have hbr : Braces (BT : Set (Sym2 E5)) (XF : Set E5) := by
    rw [hXFcoe]; exact hB3br T hT hT3
  have hcard : BT.card + 6 ≤ 3 * XF.card := by
    rw [hXFcard]; exact (hB3 T hT hT3).le
  have hL : Module.finrank ℝ (vectorSpan ℝ T) = 3 := hT3
  have hbot := stressSpace_eq_bot_of_braces3 hL hp0 hdiff hspanF hbr hcard
  -- `Ω` restricted to `BT` is a stress
  have hsub : ∀ b, Ω b ≠ 0 → b ∈ BT := fun b hb => by
    obtain ⟨hbB, hbR⟩ := hsupp b hb
    rw [hBTdef, Finset.mem_filter]
    exact ⟨hbB, fun p hp => hRT (hbR p hp)⟩
  let ω : EuclideanSpace ℝ BT := WithLp.toLp 2 (fun b => Ω b.1)
  have hω : ω ∈ stressSpace BT := by
    intro u
    have h1 : ∑ b : BT, ω b * barVal u b.1 = ∑ b ∈ BT, Ω b * barVal u b := by
      rw [← Finset.sum_coe_sort BT]
    have h2 : ∑ b ∈ BT, Ω b * barVal u b = ∑ b ∈ B, Ω b * barVal u b := by
      refine Finset.sum_subset (Finset.filter_subset _ _) fun b _ hb => ?_
      by_contra hne
      exact hb (hsub b (left_ne_zero_of_mul hne))
    rw [h1, h2]
    exact hstr u
  rw [hbot, Submodule.mem_bot] at hω
  intro b
  by_contra hne
  have hbT := hsub b hne
  have := congrArg (fun z : EuclideanSpace ℝ BT => z ⟨b, hbT⟩) hω
  exact hne this

/-- **Two-facet stress localization**: for facets `H, H'` with `H' ≠ ±H`,
`2 (g(H) + g(H')) ≤ G`. -/
theorem IsCSPolytope5.two_facet_localization (hW : WhiteleyCSLoc P) {H H' : Set E5}
    (hH : H ∈ faces P) (h4 : dim H = 4) (hH' : H' ∈ faces P) (h4' : dim H' = 4)
    (hne : H' ≠ H) (hne' : H' ≠ -H) :
    2 * (faceRow P H).g + 2 * (faceRow P H').g ≤ (flagDataOf P).G := by
  classical
  obtain ⟨B, hBX, hBs, hBcard, hBloc, hrig, -, hB3br, -, hB3⟩ := hW
  obtain ⟨V, hV⟩ := hP.polytope
  -- the vertex set of `P`
  set X := (extremePoints_finite V).toFinset with hXdef
  have hXcoe : (X : Set E5) = P.extremePoints ℝ := by rw [hXdef, Set.Finite.coe_toFinset, hV]
  have hXcard : X.card = fvec P 0 := by
    have h1 := fvec_zero_eq V
    rw [Set.ncard_eq_toFinset_card _ (extremePoints_finite V)] at h1
    rw [hV, hXdef, h1]
  have hXs : ∀ x ∈ X, -x ∈ X := by
    intro x hx
    rw [← Finset.mem_coe, hXcoe] at hx ⊢
    exact neg_mem_extremePoints hP.symm hx
  have hX0 : (0 : E5) ∉ X := by
    rw [← Finset.mem_coe, hXcoe]
    exact hP.zero_not_mem_extremePoints
  have hspan : Submodule.span ℝ (X : Set E5) = ⊤ := by
    rw [hXcoe, hV]
    exact span_extremePoints_eq_top (hV ▸ hP.zero_mem_interior)
  -- no facet contains a point and its antipode
  have hnoanti : ∀ {F : Set E5}, F ∈ faces P → dim F = 4 → ∀ {p : E5}, p ∈ F → -p ∉ F := by
    intro F hF hF4 p hp hnp
    have := hP.eq_of_mem_of_neg_mem hF hp hnp
    rw [this, hP.dim_self] at hF4
    omega
  -- the bars of the two facets
  set BH := B.filter (fun b => ∀ p ∈ b, p ∈ H) with hBHdef
  set BH' := B.filter (fun b => ∀ p ∈ b, p ∈ H') with hBH'def
  have hσmem : ∀ {F : Set E5} (b : Sym2 E5), (∀ p ∈ b.map Neg.neg, p ∈ F) → ∀ p ∈ b, -p ∈ F :=
    fun b h p hp => h (-p) (Sym2.mem_map.2 ⟨p, hp, rfl⟩)
  have hexists : ∀ b : Sym2 E5, ∃ p, p ∈ b := fun b => by
    induction b using Sym2.ind with
    | _ x y => exact ⟨x, Sym2.mem_mk_left x y⟩
  have hσout : ∀ {F : Set E5}, F ∈ faces P → dim F = 4 → ∀ b : Sym2 E5,
      (∀ p ∈ b, p ∈ F) → ¬ ∀ p ∈ b.map Neg.neg, p ∈ F := by
    intro F hF hF4 b hb hσb
    obtain ⟨p, hp⟩ := hexists b
    exact hnoanti hF hF4 (hb p hp) (hσmem b hσb p hp)
  -- the space of pairs of stresses
  let Φ : (stressSpace BH × stressSpace BH') →ₗ[ℝ] (Sym2 E5 → ℝ) :=
    { toFun := fun x c => extZero BH x.1 c + extZero BH' x.2 c
      map_add' := fun x y => by
        funext c
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, extZero_add, Pi.add_apply]
        ring
      map_smul' := fun a x => by
        funext c
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, extZero_smul, Pi.smul_apply,
          smul_eq_mul, RingHom.id_apply]
        ring }
  have hΦ : ∀ x c, Φ x c = extZero BH x.1 c + extZero BH' x.2 c := fun _ _ => rfl
  -- extension by zero of a stress of a sub-framework is a stress
  have hext_str : ∀ (BF : Finset (Sym2 E5)), BF ⊆ B → ∀ ω ∈ stressSpace BF, ∀ u : E5 → E5,
      ∑ b ∈ B, extZero BF ω b * barVal u b = 0 := by
    intro BF hBF ω hω u
    have h1 : ∑ b ∈ B, extZero BF ω b * barVal u b = ∑ b ∈ BF, extZero BF ω b * barVal u b := by
      symm
      refine Finset.sum_subset hBF fun c _ hc => ?_
      unfold extZero
      rw [dif_neg hc, zero_mul]
    rw [h1, ← Finset.sum_coe_sort BF]
    have := hω u
    rw [← this]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold extZero
    rw [dif_pos c.2]
  have hBHsub : BH ⊆ B := Finset.filter_subset _ _
  have hBH'sub : BH' ⊆ B := Finset.filter_subset _ _
  have hstr : ∀ x (u : E5 → E5), ∑ b ∈ B, Φ x b * barVal u b = 0 := by
    intro x u
    simp only [hΦ, add_mul, Finset.sum_add_distrib]
    rw [hext_str BH hBHsub x.1 x.1.2 u, hext_str BH' hBH'sub x.2 x.2.2 u, add_zero]
  -- faces `H ∩ H'` and `H ∩ -H'`
  have hnH' : -H' ∈ faces P := neg_mem_faces hP.symm hH'
  have hdnH' : dim (-H') = 4 := by rw [dim_neg]; exact h4'
  have hsmall : ∀ {K : Set E5}, K ∈ faces P → dim K = 4 → K ≠ H → (H ∩ K).Nonempty →
      H ∩ K ∈ faces P ∧ dim (H ∩ K) ≤ 3 := by
    intro K hK hK4 hKH hnemp
    have hI := inter_mem_faces_of_nonempty hH hK hnemp
    refine ⟨hI, ?_⟩
    have hfacesP : ∀ {F G : Set E5}, F ∈ faces P → (G ∈ faces F ↔ G ∈ faces P ∧ G ⊆ F) := by
      intro F G hF
      rw [hV] at hF ⊢
      exact mem_faces_face_iff hF
    have hIH : H ∩ K ∈ faces H := (hfacesP hH).2 ⟨hI, Set.inter_subset_left⟩
    have hIne : H ∩ K ≠ H := by
      intro heq
      have hHK : H ⊆ K := by rw [← heq]; exact Set.inter_subset_right
      have hHK' : H ∈ faces K := (hfacesP hK).2 ⟨hH, hHK⟩
      have := dim_lt_of_mem_faces_ne hHK' (Ne.symm hKH)
      omega
    have := dim_lt_of_mem_faces_ne hIH hIne
    omega
  have hneH : -H' ≠ H := fun h => hne' (by rw [← h, neg_neg])
  -- the key: antisymmetrization is injective
  have hinj : ∀ x, (∀ b ∈ B, Φ x b = Φ x (b.map Neg.neg)) → x = 0 := by
    intro x hx
    set Ω1 := extZero BH x.1 with hΩ1
    set Ω2 := extZero BH' x.2 with hΩ2
    have hΩ1out : ∀ c, c ∉ BH → Ω1 c = 0 := fun c hc => by
      rw [hΩ1]; unfold extZero; rw [dif_neg hc]
    have hΩ2out : ∀ c, c ∉ BH' → Ω2 c = 0 := fun c hc => by
      rw [hΩ2]; unfold extZero; rw [dif_neg hc]
    have hmemBH : ∀ c, c ∈ BH ↔ c ∈ B ∧ ∀ p ∈ c, p ∈ H := fun c => by
      rw [hBHdef, Finset.mem_filter]
    have hmemBH' : ∀ c, c ∈ BH' ↔ c ∈ B ∧ ∀ p ∈ c, p ∈ H' := fun c => by
      rw [hBH'def, Finset.mem_filter]
    -- `Ω1` is supported on the bars of `H ∩ H'` and of `H ∩ -H'`
    have hsupp1 : ∀ c, Ω1 c ≠ 0 → c ∈ B ∧ ((∀ p ∈ c, p ∈ H ∩ H') ∨ (∀ p ∈ c, p ∈ H ∩ -H')) := by
      intro c hc
      have hcH : c ∈ BH := by by_contra h; exact hc (hΩ1out c h)
      obtain ⟨hcB, hcHp⟩ := (hmemBH c).1 hcH
      refine ⟨hcB, ?_⟩
      by_cases h1 : ∀ p ∈ c, p ∈ H'
      · exact Or.inl fun p hp => ⟨hcHp p hp, h1 p hp⟩
      by_cases h2 : ∀ p ∈ c.map Neg.neg, p ∈ H'
      · exact Or.inr fun p hp => ⟨hcHp p hp, Set.mem_neg.2 (hσmem c h2 p hp)⟩
      exfalso
      have hcσ := hx c hcB
      rw [hΦ, hΦ] at hcσ
      have e1 : Ω2 c = 0 := hΩ2out c fun h => h1 ((hmemBH' c).1 h).2
      have e2 : Ω1 (c.map Neg.neg) = 0 := hΩ1out _ fun h => hσout hH h4 c hcHp ((hmemBH _).1 h).2
      have e3 : Ω2 (c.map Neg.neg) = 0 := hΩ2out _ fun h => h2 ((hmemBH' _).1 h).2
      rw [← hΩ1, ← hΩ2, e1, e2, e3] at hcσ
      exact hc (by linarith)
    -- `Ω1` vanishes: split along the two disjoint faces
    have hstr1 : ∀ u : E5 → E5, ∑ b ∈ B, Ω1 b * barVal u b = 0 :=
      hext_str BH hBHsub x.1 x.1.2
    have hvanish : ∀ {K K' : Set E5}, K ∈ faces P → dim K = 4 → K ≠ H →
        (∀ q, q ∈ K' → q ∉ K) →
        (∀ c, Ω1 c ≠ 0 → (∀ p ∈ c, p ∈ H ∩ K) ∨ (∀ p ∈ c, p ∈ H ∩ K')) →
        ∀ c, (∀ p ∈ c, p ∈ H ∩ K) → Ω1 c = 0 := by
      intro K K' hK hK4 hKH hdisjK hsuppK c hcK
      set Ωa : Sym2 E5 → ℝ := fun b => if ∀ p ∈ b, p ∈ H ∩ K then Ω1 b else 0 with hΩa
      obtain ⟨p, hp⟩ := hexists c
      have hnemp : (H ∩ K).Nonempty := ⟨p, hcK p hp⟩
      obtain ⟨hIK, hdIK⟩ := hsmall hK hK4 hKH hnemp
      have hsuppa : ∀ b, Ωa b ≠ 0 → b ∈ B ∧ ∀ p ∈ b, p ∈ H ∩ K := by
        intro b hb
        by_cases hbK : ∀ p ∈ b, p ∈ H ∩ K
        · have e : Ωa b = Ω1 b := if_pos hbK
          rw [e] at hb
          exact ⟨((hmemBH b).1 (by by_contra h; exact hb (hΩ1out b h))).1, hbK⟩
        · have e : Ωa b = 0 := if_neg hbK
          exact absurd e hb
      have hstra : ∀ u : E5 → E5, ∑ b ∈ B, Ωa b * barVal u b = 0 := by
        intro u
        set uK : E5 → E5 := fun q => if q ∈ H ∩ K then u q else 0 with huK
        rw [← hstr1 uK]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases hbK : ∀ p ∈ b, p ∈ H ∩ K
        · have e : Ωa b = Ω1 b := if_pos hbK
          rw [e]
          congr 1
          induction b using Sym2.ind with
          | _ y z =>
            rw [barVal_mk, barVal_mk]
            have hy := hbK y (Sym2.mem_mk_left y z)
            have hz := hbK z (Sym2.mem_mk_right y z)
            simp only [huK, if_pos hy, if_pos hz]
        · have e : Ωa b = 0 := if_neg hbK
          rw [e, zero_mul]
          by_cases h0 : Ω1 b = 0
          · rw [h0, zero_mul]
          · have hb' := (hsuppK b h0).resolve_left hbK
            have hother : ∀ q ∈ b, q ∉ H ∩ K := fun q hq hqK =>
              hdisjK q (hb' q hq).2 hqK.2
            induction b using Sym2.ind with
            | _ y z =>
              rw [barVal_mk]
              simp only [huK, if_neg (hother y (Sym2.mem_mk_left y z)),
                if_neg (hother z (Sym2.mem_mk_right y z)), sub_self, inner_zero_left, mul_zero]
      have h := hP.stress_vanish_of_face hBX hB3br hB3 hIK hdIK Ωa hsuppa hstra c
      have e : Ωa c = Ω1 c := if_pos hcK
      rw [e] at h
      exact h
    have hdisjA : ∀ q, q ∈ -H' → q ∉ H' := fun q hq hq' =>
      hnoanti hH' h4' hq' (Set.mem_neg.1 hq)
    have hdisjB : ∀ q, q ∈ H' → q ∉ -H' := fun q hq hq' =>
      hnoanti hH' h4' hq (Set.mem_neg.1 hq')
    have hΩ1zero : ∀ c, Ω1 c = 0 := by
      intro c
      by_contra hc
      obtain ⟨-, hor⟩ := hsupp1 c hc
      rcases hor with hor | hor
      · exact hc (hvanish hH' h4' hne hdisjA (fun c hc => (hsupp1 c hc).2) c hor)
      · exact hc (hvanish hnH' hdnH' hneH hdisjB (fun c hc => (hsupp1 c hc).2.symm) c hor)
    -- then `Ω2` vanishes
    have hΩ2zero : ∀ c, Ω2 c = 0 := by
      intro c
      by_contra hc
      have hcH' : c ∈ BH' := by by_contra h; exact hc (hΩ2out c h)
      obtain ⟨hcB, hcHp⟩ := (hmemBH' c).1 hcH'
      have hcσ := hx c hcB
      rw [hΦ, hΦ, ← hΩ1, ← hΩ2, hΩ1zero, hΩ1zero, zero_add, zero_add] at hcσ
      have e3 : Ω2 (c.map Neg.neg) = 0 :=
        hΩ2out _ fun h => hσout hH' h4' c hcHp ((hmemBH' _).1 h).2
      rw [e3] at hcσ
      exact hc hcσ
    -- conclude
    refine Prod.ext (Subtype.ext (PiLp.ext fun c => ?_)) (Subtype.ext (PiLp.ext fun c => ?_))
    · have h := hΩ1zero c.1
      rw [hΩ1] at h
      unfold extZero at h
      rw [dif_pos c.2] at h
      simpa using h
    · have h := hΩ2zero c.1
      rw [hΩ2] at h
      unfold extZero at h
      rw [dif_pos c.2] at h
      simpa using h
  have key := two_mul_finrank_le_of_antisymm_inj hXs hX0 hspan (fun b hb => (hBs b hb).1)
    (fun b hb => (hBs b hb).2) (by rw [hXcoe]; exact hrig) Φ hstr hinj
  rw [Module.finrank_prod] at key
  -- lower bounds from the hyperplanes of the facets
  have hlowF : ∀ {F : Set E5}, F ∈ faces P → dim F = 4 →
      ((B.filter fun b => ∀ p ∈ b, p ∈ F).card : ℤ) + 10 ≤
        Module.finrank ℝ (stressSpace (B.filter fun b => ∀ p ∈ b, p ∈ F)) + 4 * cnt P F 0 := by
    intro F hF hF4
    obtain ⟨XF, hXFcoe, hXFcard, p0, hp0, hdiff, hspanF⟩ := hP.face_vertex_data hV hF
    have hFext : IsExtreme ℝ P F := hF.2.isExtreme
    have hBF : ∀ b ∈ B.filter (fun b => ∀ p ∈ b, p ∈ F), ∀ p ∈ b, p ∈ XF := by
      intro b hb p hp
      rw [Finset.mem_filter] at hb
      rw [← Finset.mem_coe, hXFcoe, hFext.extremePoints_eq]
      exact ⟨hb.2 p hp, hBX b hb.1 p hp⟩
    have h := le_finrank_stress_of_hyperplane (L := vectorSpan ℝ F) hF4 hp0 hdiff hspanF hBF
    rw [hXFcard] at h
    exact_mod_cast h
  have hl1 := hlowF hH h4
  have hl2 := hlowF hH' h4'
  have hloc1 := hBloc H hH h4
  have hloc2 := hBloc H' hH' h4'
  rw [← hBHdef] at hl1 hloc1
  rw [← hBH'def] at hl2 hloc2
  have hg1 := hP.facet_g_eq hH h4
  have hg2 := hP.facet_g_eq hH' h4'
  simp only [FlagData.G, flagDataOf]
  rw [hg1, hg2]
  rw [hXcard] at key
  have key' : (2 : ℤ) * (Module.finrank ℝ (stressSpace BH) + Module.finrank ℝ (stressSpace BH'))
      + 5 * fvec P 0 ≤ B.card + 2 * 5 := by exact_mod_cast key
  rw [hBcard] at key'
  linarith

end cs

end Kalai5
