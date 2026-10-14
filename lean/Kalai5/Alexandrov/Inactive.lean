import Kalai5.Alexandrov.Poly3

/-!
# The inactive bound

For a `3`-polytope `conv V`, a set `D ⊆ V` with `3 ≤ #D` and a vertex `x ∉ D`:

  `Σ_{2-faces G} (#(D ∩ G) - 2)⁺ ≤ 2 #D - 5`   (`inactive_bound`).

Instead of Euler's formula for subgraphs of the boundary (a topological statement) we use Euler's
formula for the auxiliary polytope `Q⁺ = conv (D ∪ {x})`: the faces `G` with `#(D⁺ ∩ G) ≥ 3` give
distinct `2`-faces `Q⁺ ∩ G` of `Q⁺`, and the (at least three) `2`-faces of `Q⁺` at `x` that do not
arise this way pay for the difference.  If `D ∪ {x}` is coplanar, at most one face meets `D` in
three points.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- Three distinct extreme points span a plane. -/
lemma two_le_dim_of_three {K S : Set (E n)} {p q r : E n} (hp : p ∈ K.extremePoints ℝ)
    (hq : q ∈ K.extremePoints ℝ) (hr : r ∈ K.extremePoints ℝ) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hpS : p ∈ S) (hqS : q ∈ S) (hrS : r ∈ S) : 2 ≤ dim S := by
  have hli : LinearIndependent ℝ ![q - p, r - p] := by
    rw [LinearIndependent.pair_iff]
    intro α β hαβ
    by_cases hβ : β = 0
    · rw [hβ, zero_smul, add_zero] at hαβ
      refine ⟨?_, hβ⟩
      rcases smul_eq_zero.1 hαβ with h | h
      · exact h
      · exact absurd (sub_eq_zero.1 h) hpq.symm
    · exfalso
      have hβr : β • (r - p) = -(α • (q - p)) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]; exact hαβ
      have hcol : r - p = (-α / β) • (q - p) := by
        calc r - p = β⁻¹ • (β • (r - p)) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
          _ = β⁻¹ • (-(α • (q - p))) := by rw [hβr]
          _ = (-α / β) • (q - p) := by
            rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring
      exact not_collinear_of_extreme hp hq hr hpq hpr hqr (-α / β) hcol
  have hle : Submodule.span ℝ {q - p, r - p} ≤ vectorSpan ℝ S := by
    rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact vsub_mem_vectorSpan ℝ hqS hpS
    · exact vsub_mem_vectorSpan ℝ hrS hpS
  have h := finrank_span_eq_card hli
  rw [show Set.range ![q - p, r - p] = {q - p, r - p} by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]] at h
  rw [Fintype.card_fin] at h
  have := Submodule.finrank_mono hle
  unfold dim
  omega

/-- A polygon has at least three vertices. -/
lemma three_le_card_polygon {W : Finset (E n)} (hcp : ConvPos W)
    (h2 : dim (convexHull ℝ (W : Set (E n))) = 2) : 3 ≤ W.card := by
  classical
  obtain ⟨x, hx⟩ : W.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    rw [Finset.coe_empty, convexHull_empty] at h2
    unfold dim at h2
    rw [vectorSpan_empty, finrank_bot] at h2
    omega
  have h := card_nbrs hcp h2 hx
  have hsub : insert x (nbrs W x) ⊆ W := by
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx
    · exact (mem_nbrs.1 hy).1
  have hxn : x ∉ nbrs W x := fun h' => (mem_nbrs.1 h').2.1 rfl
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, h] at this
  omega

/-- The vertices of a `2`-face of a polytope with vertices in convex position: at least three. -/
lemma three_le_card_facePts {V : Finset (E n)} (hcp : ConvPos V) {G : Set (E n)}
    (hG : G ∈ twoFinset V) : 3 ≤ (facePts V G).card := by
  obtain ⟨hGf, hG2⟩ := mem_twoFinset.1 hG
  refine three_le_card_polygon (convPos_facePts hcp hGf) ?_
  rw [← facePts_hull hGf]; exact hG2

/-- A point of the polytope on the affine span of a face lies in the face. -/
lemma mem_face_of_vsub_mem {P G : Set (E n)} (hG : G ∈ faces P) {p y : E n} (hp : p ∈ G)
    (hyP : y ∈ P) (hy : y - p ∈ vectorSpan ℝ G) : y ∈ G := by
  obtain ⟨l, hl⟩ := exists_functional hG
  have hconst : ∀ u ∈ vectorSpan ℝ G, l u = 0 := by
    intro u hu
    rw [vectorSpan_def] at hu
    induction hu using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hw
      have ha' := ha; have hb' := hb
      rw [hl] at ha' hb'
      have h1 := ha'.2 b hb'.1
      have h2 := hb'.2 a ha'.1
      show l (a -ᵥ b) = 0
      rw [vsub_eq_sub, map_sub]; linarith
    | zero => simp
    | add u₁ u₂ _ _ h₁ h₂ => rw [map_add, h₁, h₂, add_zero]
    | smul r u _ h => rw [map_smul, h, smul_zero]
  have hp' := hp
  rw [hl] at hp' ⊢
  refine ⟨hyP, fun w hw => ?_⟩
  have := hconst (y - p) hy
  rw [map_sub] at this
  linarith [hp'.2 w hw]

/-- Two `2`-faces containing a common `2`-dimensional set are equal. -/
lemma eq_of_two_le_dim_inter {P G G' : Set (E n)} (hG : G ∈ faces P) (hG' : G' ∈ faces P)
    (hG2 : dim G = 2) (hG'2 : dim G' = 2) {S : Set (E n)} (hSG : S ⊆ G) (hSG' : S ⊆ G')
    (hS : 2 ≤ dim S) (hSne : S.Nonempty) : G = G' := by
  have key : ∀ {G G' : Set (E n)}, G ∈ faces P → G' ∈ faces P → dim G = 2 → S ⊆ G → S ⊆ G' →
      G ⊆ G' := by
    intro G G' hG hG' hG2 hSG hSG'
    obtain ⟨s, hs⟩ := hSne
    have hI := inter_mem_faces_of_nonempty hG hG' ⟨s, hSG hs, hSG' hs⟩
    have hIG : G ∩ G' ∈ faces G :=
      mem_faces_of_subset (face_subset hG) hI Set.inter_subset_left
    by_contra hsub
    have hne : G ∩ G' ≠ G := fun h => hsub (h ▸ Set.inter_subset_right)
    have hlt := dim_lt_of_mem_faces_ne hIG hne
    have hge : dim S ≤ dim (G ∩ G') :=
      Submodule.finrank_mono (vectorSpan_mono ℝ (Set.subset_inter hSG hSG'))
    omega
  exact Subset.antisymm (key hG hG' hG2 hSG hSG') (key hG' hG hG'2 hSG' hSG)

/-- Three distinct extreme points: the two difference vectors are independent. -/
lemma linIndep_of_three {K : Set (E n)} {p q r : E n} (hp : p ∈ K.extremePoints ℝ)
    (hq : q ∈ K.extremePoints ℝ) (hr : r ∈ K.extremePoints ℝ) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) : LinearIndependent ℝ ![q - p, r - p] := by
  rw [LinearIndependent.pair_iff]
  intro α β hαβ
  by_cases hβ : β = 0
  · rw [hβ, zero_smul, add_zero] at hαβ
    refine ⟨?_, hβ⟩
    rcases smul_eq_zero.1 hαβ with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h) hpq.symm
  · exfalso
    have hβr : β • (r - p) = -(α • (q - p)) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hαβ
    have hcol : r - p = (-α / β) • (q - p) := by
      calc r - p = β⁻¹ • (β • (r - p)) := by rw [smul_smul, inv_mul_cancel₀ hβ, one_smul]
        _ = β⁻¹ • (-(α • (q - p))) := by rw [hβr]
        _ = (-α / β) • (q - p) := by
          rw [smul_neg, smul_smul, ← neg_smul]; congr 1; ring
    exact not_collinear_of_extreme hp hq hr hpq hpr hqr (-α / β) hcol

lemma finrank_span_pair {p q r : E n} (hli : LinearIndependent ℝ ![q - p, r - p]) :
    finrank ℝ (Submodule.span ℝ {q - p, r - p}) = 2 := by
  have h := finrank_span_eq_card hli
  rw [show Set.range ![q - p, r - p] = {q - p, r - p} by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]] at h
  rw [h, Fintype.card_fin]

open Classical in
/-- **The inactive bound.** -/
theorem inactive_bound {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) {D : Finset (E n)} (hDV : D ⊆ V)
    (hD3 : 3 ≤ D.card) {x : E n} (hxV : x ∈ V) (hxD : x ∉ D) :
    ∑ G ∈ twoFinset V, ((facePts D G).card - 2) + 5 ≤ 2 * D.card := by
  set R := convexHull ℝ (V : Set (E n)) with hR
  set Dp := insert x D with hDp
  have hDpV : Dp ⊆ V := Finset.insert_subset hxV hDV
  have hconvsub : convexHull ℝ (Dp : Set (E n)) ⊆ R :=
    convexHull_mono (by exact_mod_cast hDpV)
  have hcpDp : ConvPos Dp := fun y hy =>
    inter_extremePoints_subset_extremePoints_of_subset hconvsub
      ⟨subset_convexHull ℝ _ (by exact_mod_cast hy), hcp y (hDpV hy)⟩
  have hextV : ∀ y ∈ Dp, y ∈ R.extremePoints ℝ := fun y hy => hcp y (hDpV hy)
  have hdimle : dim (convexHull ℝ (Dp : Set (E n))) ≤ 3 := by
    rw [← h3]; exact Submodule.finrank_mono (vectorSpan_mono ℝ hconvsub)
  have hcardDp : Dp.card = D.card + 1 := Finset.card_insert_of_notMem hxD
  have hfDsub : ∀ G, facePts D G ⊆ facePts Dp G := fun G y hy => by
    rw [mem_facePts] at hy ⊢; exact ⟨Finset.mem_insert_of_mem hy.1, hy.2⟩
  by_cases hd3 : dim (convexHull ℝ (Dp : Set (E n))) = 3
  · ------------------------------------------------------------------
    -- the faces with three points of `Dp` give faces of `conv Dp`
    set I := (twoFinset V).filter fun G => 3 ≤ (facePts Dp G).card with hI
    set Γ : Set (E n) → Set (E n) := fun G => convexHull ℝ (facePts Dp G : Set (E n)) with hΓ
    have hΓsub : ∀ G ∈ twoFinset V, Γ G ⊆ G := fun G hG =>
      convexHull_min (fun y hy => (mem_facePts.1 (Finset.mem_coe.1 hy)).2)
        (face_convex (convex_convexHull ℝ _) (mem_twoFinset.1 hG).1)
    have hΓdim : ∀ G ∈ I, 2 ≤ dim (Γ G) := by
      intro G hG
      obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
        (Finset.two_lt_card (s := facePts Dp G)).1 (by have := (Finset.mem_filter.1 hG).2; omega)
      exact two_le_dim_of_three (hextV p (mem_facePts.1 hp).1) (hextV q (mem_facePts.1 hq).1)
        (hextV r (mem_facePts.1 hr).1) hpq hpr hqr (subset_convexHull ℝ _ (by exact_mod_cast hp))
        (subset_convexHull ℝ _ (by exact_mod_cast hq)) (subset_convexHull ℝ _ (by exact_mod_cast hr))
    have hΓface : ∀ G ∈ I, Γ G ∈ twoFinset Dp ∧ facePts Dp (Γ G) = facePts Dp G := by
      intro G hG
      obtain ⟨hGt, hG3⟩ := Finset.mem_filter.1 hG
      obtain ⟨hGf, hG2⟩ := mem_twoFinset.1 hGt
      obtain ⟨p₀, hp₀⟩ : (facePts Dp G).Nonempty := Finset.card_pos.1 (by omega)
      obtain ⟨hp₀Dp, hp₀G⟩ := mem_facePts.1 hp₀
      obtain ⟨l, hl⟩ := exists_functional hGf
      have hp₀max : ∀ z ∈ R, l z ≤ l p₀ := by
        have := hp₀G; rw [hl] at this; exact this.2
      -- `conv Dp ∩ G` is an exposed face of `conv Dp`
      have hexp : convexHull ℝ (Dp : Set (E n)) ∩ G =
          {y | y ∈ convexHull ℝ (Dp : Set (E n)) ∧ ∀ z ∈ convexHull ℝ (Dp : Set (E n)), l z ≤ l y} := by
        ext y
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hy, hyG⟩
          rw [hl] at hyG
          exact ⟨hy, fun z hz => hyG.2 z (hconvsub hz)⟩
        · rintro ⟨hy, hmax⟩
          refine ⟨hy, ?_⟩
          rw [hl]
          refine ⟨hconvsub hy, fun z hz => (hp₀max z hz).trans ?_⟩
          exact hmax p₀ (subset_convexHull ℝ _ (by exact_mod_cast hp₀Dp))
      have hface : convexHull ℝ (Dp : Set (E n)) ∩ G ∈ faces (convexHull ℝ (Dp : Set (E n))) :=
        ⟨⟨p₀, subset_convexHull ℝ _ (by exact_mod_cast hp₀Dp), hp₀G⟩, fun _ => ⟨l, hexp⟩⟩
      have hfil : facePts Dp (convexHull ℝ (Dp : Set (E n)) ∩ G) = facePts Dp G := by
        ext y
        rw [mem_facePts, mem_facePts]
        constructor
        · rintro ⟨hy, -, hyG⟩; exact ⟨hy, hyG⟩
        · rintro ⟨hy, hyG⟩; exact ⟨hy, subset_convexHull ℝ _ (by exact_mod_cast hy), hyG⟩
      have heq : convexHull ℝ (Dp : Set (E n)) ∩ G = Γ G := by
        rw [facePts_hull hface, hfil]
      have hdimΓ : dim (Γ G) = 2 := by
        have h1 := hΓdim G hG
        have h2 : dim (Γ G) ≤ dim G := Submodule.finrank_mono (vectorSpan_mono ℝ (hΓsub G hGt))
        omega
      refine ⟨mem_twoFinset.2 ⟨heq ▸ hface, hdimΓ⟩, ?_⟩
      rw [← heq, hfil]
    have hΓinj : Set.InjOn Γ (I : Set (Set (E n))) := by
      intro G hG G' hG' h
      have hGt := (Finset.mem_filter.1 hG).1
      have hGt' := (Finset.mem_filter.1 hG').1
      obtain ⟨p₀, hp₀⟩ : (facePts Dp G).Nonempty :=
        Finset.card_pos.1 (by have := (Finset.mem_filter.1 hG).2; omega)
      exact eq_of_two_le_dim_inter (mem_twoFinset.1 hGt).1 (mem_twoFinset.1 hGt').1
        (mem_twoFinset.1 hGt).2 (mem_twoFinset.1 hGt').2 (hΓsub G hGt)
        (by rw [show Γ G = Γ G' from h]; exact hΓsub G' hGt') (hΓdim G hG)
        ⟨p₀, subset_convexHull ℝ _ (by exact_mod_cast hp₀)⟩
    -- the faces of `conv Dp` at `x`
    set Fx := (twoFinset Dp).filter fun Γ' => x ∈ Γ' with hFx
    have hFx3 : 3 ≤ Fx.card := by
      have hxDp : x ∈ Dp := Finset.mem_insert_self x D
      rw [hFx, card_twoFaces_at hcpDp hd3 hxDp]
      obtain ⟨σ⟩ := exists_vslice (hcpDp x hxDp)
      rw [← σ.card_sW hcpDp]
      exact three_le_card_polygon (σ.convPos_sW hcpDp) (σ.dim_sW hcpDp hd3)
    set Ix := I.filter fun G => x ∈ G with hIx
    -- (S1) the per-face identity
    have hS1 : ∑ G ∈ twoFinset V, ((facePts D G).card - 2) + Ix.card =
        ∑ G ∈ I, ((facePts Dp G).card - 2) := by
      rw [hI, Finset.sum_filter, hIx, Finset.card_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun G _ => ?_
      by_cases hxG : x ∈ G
      · have hc : (facePts Dp G).card = (facePts D G).card + 1 := by
          have : facePts Dp G = insert x (facePts D G) := by
            ext y; simp only [mem_facePts, hDp, Finset.mem_insert]
            constructor
            · rintro ⟨rfl | hy, hyG⟩
              · exact Or.inl rfl
              · exact Or.inr ⟨hy, hyG⟩
            · rintro (rfl | ⟨hy, hyG⟩)
              · exact ⟨Or.inl rfl, hxG⟩
              · exact ⟨Or.inr hy, hyG⟩
          rw [this, Finset.card_insert_of_notMem (fun h => hxD (mem_facePts.1 h).1)]
        rw [hc]
        split_ifs <;> simp_all <;> omega
      · have hc : facePts Dp G = facePts D G := by
          ext y; simp only [mem_facePts, hDp, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hy, hyG⟩
            · exact absurd hyG hxG
            · exact ⟨hy, hyG⟩
          · rintro ⟨hy, hyG⟩; exact ⟨Or.inr hy, hyG⟩
        rw [hc]
        split_ifs <;> simp_all <;> omega
    -- (S2) transport to the faces of `conv Dp`
    have hS2 : ∑ G ∈ I, ((facePts Dp G).card - 2) =
        ∑ Γ' ∈ I.image Γ, ((facePts Dp Γ').card - 2) := by
      rw [Finset.sum_image hΓinj]
      exact Finset.sum_congr rfl fun G hG => by rw [(hΓface G hG).2]
    -- (S3) Euler for `conv Dp`
    have himg_sub : I.image Γ ⊆ twoFinset Dp := fun Γ' hΓ' => by
      obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hΓ'
      exact (hΓface G hG).1
    have hT : ∑ Γ' ∈ twoFinset Dp, ((facePts Dp Γ').card - 2) + 4 = 2 * Dp.card := by
      have hsum := sum_facePts_sub_two hcpDp hd3
      have hge : ∀ Γ' ∈ twoFinset Dp, 3 ≤ (facePts Dp Γ').card :=
        fun Γ' hΓ' => three_le_card_facePts hcpDp hΓ'
      have hnat : ∑ Γ' ∈ twoFinset Dp, ((facePts Dp Γ').card - 2) + 2 * (twoFinset Dp).card =
          ∑ Γ' ∈ twoFinset Dp, (facePts Dp Γ').card := by
        rw [Finset.card_eq_sum_ones, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun Γ' hΓ' => by have := hge Γ' hΓ'; omega
      have hsumN : ((∑ Γ' ∈ twoFinset Dp, (facePts Dp Γ').card : ℕ) : ℤ) =
          2 * (twoFinset Dp).card + 2 * Dp.card - 4 := by
        push_cast; exact hsum
      omega
    have hS3 : ∑ Γ' ∈ I.image Γ, ((facePts Dp Γ').card - 2) + (Fx \ I.image Γ).card ≤
        ∑ Γ' ∈ twoFinset Dp, ((facePts Dp Γ').card - 2) := by
      have hdisj : Disjoint (I.image Γ) (Fx \ I.image Γ) := Finset.disjoint_sdiff
      have hsub : I.image Γ ∪ (Fx \ I.image Γ) ⊆ twoFinset Dp :=
        Finset.union_subset himg_sub (fun Γ' h => (Finset.mem_filter.1 (Finset.mem_sdiff.1 h).1).1)
      calc ∑ Γ' ∈ I.image Γ, ((facePts Dp Γ').card - 2) + (Fx \ I.image Γ).card
          ≤ ∑ Γ' ∈ I.image Γ, ((facePts Dp Γ').card - 2) +
              ∑ Γ' ∈ Fx \ I.image Γ, ((facePts Dp Γ').card - 2) := by
            gcongr
            rw [Finset.card_eq_sum_ones]
            refine Finset.sum_le_sum fun Γ' hΓ' => ?_
            have := three_le_card_facePts hcpDp (Finset.mem_filter.1 (Finset.mem_sdiff.1 hΓ').1).1
            omega
        _ = ∑ Γ' ∈ I.image Γ ∪ (Fx \ I.image Γ), ((facePts Dp Γ').card - 2) :=
            (Finset.sum_union hdisj).symm
        _ ≤ ∑ Γ' ∈ twoFinset Dp, ((facePts Dp Γ').card - 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
    -- (S4) the faces at `x` coming from `I` come from `Ix`
    have hS4 : (Fx ∩ I.image Γ).card ≤ Ix.card := by
      calc (Fx ∩ I.image Γ).card ≤ (Ix.image Γ).card := by
            refine Finset.card_le_card fun Γ' hΓ' => ?_
            obtain ⟨hΓ'x, hΓ'i⟩ := Finset.mem_inter.1 hΓ'
            obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hΓ'i
            have hxΓ := (Finset.mem_filter.1 hΓ'x).2
            have hGt := (Finset.mem_filter.1 hG).1
            exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hG, hΓsub G hGt hxΓ⟩)
        _ ≤ Ix.card := Finset.card_image_le
    have hsplit := Finset.card_sdiff_add_card_inter Fx (I.image Γ)
    omega
  · ------------------------------------------------------------------
    -- the coplanar case: at most one face meets `D` in three points
    have hdim2 : finrank ℝ (vectorSpan ℝ (Dp : Set (E n))) ≤ 2 := by
      have hvs : vectorSpan ℝ (convexHull ℝ (Dp : Set (E n))) = vectorSpan ℝ (Dp : Set (E n)) := by
        rw [← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
      have : dim (convexHull ℝ (Dp : Set (E n))) ≤ 2 := by omega
      unfold dim at this
      rw [hvs] at this
      exact this
    -- a face with three points of `D` contains all of `Dp`
    have hall : ∀ G ∈ twoFinset V, 3 ≤ (facePts D G).card → (Dp : Set (E n)) ⊆ G := by
      intro G hG hG3
      obtain ⟨hGf, hG2⟩ := mem_twoFinset.1 hG
      obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
        (Finset.two_lt_card (s := facePts D G)).1 (by omega)
      obtain ⟨hpD, hpG⟩ := mem_facePts.1 hp
      obtain ⟨hqD, hqG⟩ := mem_facePts.1 hq
      obtain ⟨hrD, hrG⟩ := mem_facePts.1 hr
      have hpDp : p ∈ Dp := Finset.mem_insert_of_mem hpD
      have hqDp : q ∈ Dp := Finset.mem_insert_of_mem hqD
      have hrDp : r ∈ Dp := Finset.mem_insert_of_mem hrD
      have hli := linIndep_of_three (hextV p hpDp) (hextV q hqDp) (hextV r hrDp) hpq hpr hqr
      have hspan_le : Submodule.span ℝ {q - p, r - p} ≤ vectorSpan ℝ (Dp : Set (E n)) := by
        rw [Submodule.span_le]
        rintro _ (rfl | rfl)
        · exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hqDp) (by exact_mod_cast hpDp)
        · exact vsub_mem_vectorSpan ℝ (by exact_mod_cast hrDp) (by exact_mod_cast hpDp)
      have hspan_eq : Submodule.span ℝ {q - p, r - p} = vectorSpan ℝ (Dp : Set (E n)) :=
        Submodule.eq_of_le_of_finrank_le hspan_le (by rw [finrank_span_pair hli]; exact hdim2)
      have hspanG : Submodule.span ℝ {q - p, r - p} ≤ vectorSpan ℝ G := by
        rw [Submodule.span_le]
        rintro _ (rfl | rfl)
        · exact vsub_mem_vectorSpan ℝ hqG hpG
        · exact vsub_mem_vectorSpan ℝ hrG hpG
      intro y hy
      have hyDp : y ∈ Dp := by exact_mod_cast hy
      have hyp : y - p ∈ vectorSpan ℝ G := hspanG (hspan_eq ▸
        vsub_mem_vectorSpan ℝ (by exact_mod_cast hyDp) (by exact_mod_cast hpDp))
      exact mem_face_of_vsub_mem hGf hpG (subset_convexHull ℝ _ (by exact_mod_cast hDpV hyDp)) hyp
    by_cases hex : ∃ G ∈ twoFinset V, 3 ≤ (facePts D G).card
    · obtain ⟨G₀, hG₀, hG₀3⟩ := hex
      have huniq : ∀ G ∈ twoFinset V, 3 ≤ (facePts D G).card → G = G₀ := by
        intro G hG hG3
        obtain ⟨p, hp, q, hq, r, hr, hpq, hpr, hqr⟩ :=
          (Finset.two_lt_card (s := facePts D G)).1 (by omega)
        have hsubG := hall G hG hG3
        have hsubG₀ := hall G₀ hG₀ hG₀3
        have hS : ({p, q, r} : Set (E n)) ⊆ (Dp : Set (E n)) := by
          rintro y (rfl | rfl | rfl)
          · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (mem_facePts.1 hp).1)
          · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (mem_facePts.1 hq).1)
          · exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (mem_facePts.1 hr).1)
        exact eq_of_two_le_dim_inter (mem_twoFinset.1 hG).1 (mem_twoFinset.1 hG₀).1
          (mem_twoFinset.1 hG).2 (mem_twoFinset.1 hG₀).2 (hS.trans hsubG) (hS.trans hsubG₀)
          (two_le_dim_of_three (hextV p (Finset.mem_insert_of_mem (mem_facePts.1 hp).1))
            (hextV q (Finset.mem_insert_of_mem (mem_facePts.1 hq).1))
            (hextV r (Finset.mem_insert_of_mem (mem_facePts.1 hr).1)) hpq hpr hqr
            (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
            (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
          ⟨p, Set.mem_insert _ _⟩
      have hle : ∑ G ∈ twoFinset V, ((facePts D G).card - 2) ≤ (facePts D G₀).card - 2 := by
        rw [← Finset.sum_erase_add _ _ hG₀]
        have h0 : ∑ G ∈ (twoFinset V).erase G₀, ((facePts D G).card - 2) = 0 :=
          Finset.sum_eq_zero fun G hG => by
            obtain ⟨hne, hGt⟩ := Finset.mem_erase.1 hG
            by_contra hpos
            have : 3 ≤ (facePts D G).card := by omega
            exact hne (huniq G hGt this)
        omega
      have hcardle : (facePts D G₀).card ≤ D.card := by
        rw [facePts_eq_filter]; exact Finset.card_filter_le _ _
      omega
    · push_neg at hex
      have h0 : ∑ G ∈ twoFinset V, ((facePts D G).card - 2) = 0 :=
        Finset.sum_eq_zero fun G hG => by have := hex G hG; omega
      omega

end Kalai5
