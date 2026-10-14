import Kalai5.Endpoints.Q55.Core

/-!
# Eight-vertex facets: excluding fake rows

Let `F` be a facet of a cs 5-polytope with eight vertices.  Its 3-faces are 3-polytopes with at most
seven vertices, each 2-face of `F` lies in exactly two of them, and two of them share at most one
2-face (`IsCSPolytope5.inter_three_eq`).

* **Partners** (`IsCSPolytope5.ntri_le`): a 3-face `T` sends each non-triangular 2-face `Q ⊆ T` to the
  other 3-face of `F` through `Q`.  This is injective, and its values have a non-triangular 2-face.
* **Small 3-faces**: a 2-face of a 3-face `T` has at most `f₂(T) - 1` vertices (its edges lie in
  distinct other 2-faces), so a triangular prism `(6,9,5)` has exactly three quadrilaterals and no
  larger polygon, a square pyramid `(5,8,5)` has one quadrilateral, and a 3-face `(7,11,6)` (excess
  four) needs at least two non-triangular 2-faces.
* Hence a prism forces four 3-faces with a non-triangular 2-face, a `(7,11,6)` forces three, and two
  prisms with a pyramid cannot live among four (the pyramid would get two quadrilaterals).

Counting the 3-faces of `F` by their face numbers (`IsCSPolytope5.facet8_counts`) this excludes the
rows `(8,18,18,8;38)`, `(8,18,18,8;39)`, `(8,19,21,10;44)`, `(8,20,23,11;47)`, `(8,20,23,11;48)` and
`(8,19,20,9;42)` (`IsCSPolytope5.facetRows_not_fake8`).
-/

namespace Kalai5

open Set

open scoped Classical

lemma exists_ne_of_ncard_eq_two {α : Type*} {s : Set α} (h : s.ncard = 2) {a : α} (ha : a ∈ s) :
    ∃ b ∈ s, b ≠ a := by
  obtain ⟨x, y, hxy, rfl⟩ := Set.ncard_eq_two.1 h
  rcases (show a = x ∨ a = y by simpa using ha) with rfl | rfl
  · exact ⟨y, by simp, hxy.symm⟩
  · exact ⟨x, by simp, hxy⟩

/-- The face numbers `(f₀, f₁, f₂)` of 3-polytopes with at most seven vertices. -/
def fv8 : List (ℕ × ℕ × ℕ) :=
  [(4, 6, 4), (5, 8, 5), (5, 9, 6), (6, 9, 5), (6, 10, 6), (6, 11, 7), (6, 12, 8),
    (7, 11, 6), (7, 12, 7), (7, 13, 8), (7, 14, 9), (7, 15, 10)]

lemma fv8_nodup : fv8.Nodup := by decide

/-- The non-triangular 2-faces of `P` inside `T`. -/
def ntri (P T : Set E5) : Set (Set E5) :=
  {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ 4 ≤ cnt P Q 0}

/-- The 3-faces of `P` inside `F` with a non-triangular 2-face. -/
def nsimp (P F : Set E5) : Set (Set E5) :=
  {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ (ntri P T).Nonempty}

/-- The number of 3-faces of `P` inside `F` with face numbers `t`. -/
noncomputable def tcnt (P F : Set E5) (t : ℕ × ℕ × ℕ) : ℕ :=
  {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = t}.ncard

/-- The rows excluded for facets with eight vertices. -/
def fake8 : List Row :=
  [⟨8, 18, 18, 8, 38⟩, ⟨8, 18, 18, 8, 39⟩, ⟨8, 19, 21, 10, 44⟩, ⟨8, 20, 23, 11, 47⟩,
    ⟨8, 20, 23, 11, 48⟩, ⟨8, 19, 20, 9, 42⟩]

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-! ### Faces of 3-faces -/

/-- **An edge of a 3-face lies in exactly two of its 2-faces.** -/
theorem IsCSPolytope5.edge_in_threeface {T e : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (he : e ∈ faces P) (heT : e ⊆ T) (h1 : dim e = 1) :
    {Q | Q ∈ faces P ∧ e ⊆ Q ∧ Q ⊆ T ∧ dim Q = 2}.ncard = 2 := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hT' : T ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hT
  have hTV : T = convexHull ℝ ((V.filter (· ∈ T) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hT'
  have heT' : e ∈ faces T := (mem_faces_face_iff hT').2 ⟨hV ▸ he, heT⟩
  have key := face_up_codim_two hTV heT' (by rw [h1, h3])
  rw [h1] at key
  refine Eq.trans ?_ key
  unfold upIn
  congr 1
  ext Q
  simp only [Set.mem_ofPred_eq, mem_faces_face_iff hT', ← hV]
  constructor
  · rintro ⟨h1', h2', h3', h4'⟩; exact ⟨⟨h1', h3'⟩, h2', by omega⟩
  · rintro ⟨⟨h1', h3'⟩, h2', h4'⟩; exact ⟨h1', h2', h3', by omega⟩

/-- Two distinct 2-faces through an edge meet exactly in it. -/
lemma IsCSPolytope5.inter_two_eq {e Q R : Set E5} (he : e ∈ faces P) (h1 : dim e = 1)
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hR : R ∈ faces P) (hR2 : dim R = 2) (hQR : Q ≠ R)
    (heQ : e ⊆ Q) (heR : e ⊆ R) : Q ∩ R = e := by
  have hI : Q ∩ R ∈ faces P :=
    inter_mem_faces_of_nonempty hQ hR (he.1.mono (subset_inter heQ heR))
  have hIQ : Q ∩ R ∈ faces Q := mem_faces_of_subset (face_subset hQ) hI inter_subset_left
  have hne : Q ∩ R ≠ Q := by
    intro h
    have hQR' : Q ⊆ R := by rw [← h]; exact inter_subset_right
    exact hQR (hP.eq_of_subset_of_dim_le hQ hR hQR' (by omega))
  have hlt := dim_lt_of_mem_faces_ne hIQ hne
  exact (hP.eq_of_subset_of_dim_le he hI (subset_inter heQ heR) (by omega)).symm

/-- A polygon has as many edges as vertices. -/
lemma IsCSPolytope5.cnt_one_of_two {Q : Set E5} (hQ : Q ∈ faces P) (h2 : dim Q = 2) :
    cnt P Q 1 = cnt P Q 0 := by
  have he := hP.euler_face hQ
  have hc := hP.cnt_self hQ
  rw [h2] at he hc
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at he
  rw [hc] at he
  norm_num at he
  omega

/-- A proper face has fewer vertices. -/
lemma IsCSPolytope5.cnt_zero_lt {A B : Set E5} (hA : A ∈ faces P) (hB : B ∈ faces P)
    (hAB : A ⊆ B) (hne : A ≠ B) : cnt P A 0 < cnt P B 0 := by
  obtain ⟨W, hW, hcp⟩ := hP.exists_vertFinset
  have hA' : A ∈ faces (convexHull ℝ (W : Set E5)) := hW ▸ hA
  have hB' : B ∈ faces (convexHull ℝ (W : Set E5)) := hW ▸ hB
  rw [hW, cnt_zero_eq_card hcp hA', cnt_zero_eq_card hcp hB']
  have hsub : W.filter (· ∈ A) ⊆ W.filter (· ∈ B) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, hAB hx.2⟩
  refine Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => hne ?_⟩)
  calc A = convexHull ℝ ((W.filter (· ∈ A) : Finset E5) : Set E5) := face_eq_convexHull_filter hA'
    _ = convexHull ℝ ((W.filter (· ∈ B) : Finset E5) : Set E5) := by rw [h]
    _ = B := (face_eq_convexHull_filter hB').symm

/-- **A 2-face `Q` of a 3-face `T` has at most `f₂(T) - 1` vertices**: the other 2-faces of `T`
through the edges of `Q` are distinct. -/
lemma IsCSPolytope5.cnt_zero_add_one_le {T Q : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (hQ : Q ∈ faces P) (hQT : Q ⊆ T) (h2 : dim Q = 2) : cnt P Q 0 + 1 ≤ cnt P T 2 := by
  have hother : ∀ e ∈ {e | e ∈ faces P ∧ e ⊆ Q ∧ dim e = 1},
      ∃ R ∈ {R | R ∈ faces P ∧ e ⊆ R ∧ R ⊆ T ∧ dim R = 2}, R ≠ Q := by
    rintro e ⟨he, heQ, he1⟩
    exact exists_ne_of_ncard_eq_two (hP.edge_in_threeface hT h3 he (heQ.trans hQT) he1)
      ⟨hQ, heQ, hQT, h2⟩
  choose! f hf hfQ using hother
  have hinj : Set.InjOn f {e | e ∈ faces P ∧ e ⊆ Q ∧ dim e = 1} := by
    intro e he e' he' hee
    obtain ⟨hR, heR, -, hR2⟩ := hf e he
    obtain ⟨hR', heR', -, hR2'⟩ := hf e' he'
    have h1 := hP.inter_two_eq he.1 he.2.2 hQ h2 hR hR2 (hfQ e he).symm he.2.1 heR
    have h1' := hP.inter_two_eq he'.1 he'.2.2 hQ h2 hR' hR2' (hfQ e' he').symm he'.2.1 heR'
    calc e = Q ∩ f e := h1.symm
      _ = Q ∩ f e' := by rw [hee]
      _ = e' := h1'
  have hmaps : ∀ e ∈ {e | e ∈ faces P ∧ e ⊆ Q ∧ dim e = 1},
      f e ∈ {R | R ∈ faces P ∧ R ⊆ T ∧ dim R = 2} \ {Q} := by
    intro e he
    obtain ⟨hR, -, hRT, hR2⟩ := hf e he
    exact ⟨⟨hR, hRT, hR2⟩, hfQ e he⟩
  have hle := Set.ncard_le_ncard_of_injOn f hmaps hinj (hP.below_finite T 2).sdiff
  rw [Set.ncard_sdiff_singleton_of_mem (show Q ∈ {R | R ∈ faces P ∧ R ⊆ T ∧ dim R = 2} from
    ⟨hQ, hQT, h2⟩)] at hle
  have hc1 : {e | e ∈ faces P ∧ e ⊆ Q ∧ dim e = 1}.ncard = cnt P Q 0 := hP.cnt_one_of_two hQ h2
  have hpos : 0 < cnt P T 2 := (Set.ncard_pos (hP.below_finite T 2)).2 ⟨Q, hQ, hQT, h2⟩
  rw [hc1] at hle
  change cnt P Q 0 ≤ cnt P T 2 - 1 at hle
  omega

/-- A 3-face with face numbers `(6,9,5)` (a triangular prism) has exactly three quadrilaterals and
no larger polygon. -/
lemma IsCSPolytope5.q4_695 {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (ht : tri3 P T = (6, 9, 5)) : q4 P T = 3 ∧ big2 P T = 0 := by
  simp only [tri3, Prod.mk.injEq] at ht
  obtain ⟨-, ht1, ht2⟩ := ht
  have hb0 : big2 P T = 0 := by
    rw [hP.big2_eq_card, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro Q hQ h5
    rw [Set.Finite.mem_toFinset] at hQ
    have := hP.cnt_zero_add_one_le hT h3 hQ.1 hQ.2.1 hQ.2.2
    omega
  have he := hP.exc_threeface hT h3
  rw [ht1, ht2] at he
  have hq := hP.exc_eq_q4_of_big T hb0
  refine ⟨?_, hb0⟩
  omega

/-! ### Non-triangular 2-faces and their partners -/

lemma IsCSPolytope5.ntri_finite (T : Set E5) : (ntri P T).Finite :=
  hP.faces_finite.subset fun Q hQ => hQ.1

lemma IsCSPolytope5.nsimp_finite (F : Set E5) : (nsimp P F).Finite :=
  hP.faces_finite.subset fun T hT => hT.1

/-- The non-triangular 2-faces are the quadrilaterals and the larger polygons. -/
lemma IsCSPolytope5.ntri_ncard (T : Set E5) : (ntri P T).ncard = q4 P T + big2 P T := by
  have hA : {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hB : {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hU : ntri P T = {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ∪
      {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0} := by
    ext Q
    simp only [ntri, Set.mem_ofPred_eq, Set.mem_union]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      rcases Nat.lt_or_ge (cnt P Q 0) 5 with h | h
      · exact Or.inl ⟨h1, h2, h3, by omega⟩
      · exact Or.inr ⟨h1, h2, h3, h⟩
    · rintro (⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩)
      · exact ⟨h1, h2, h3, by omega⟩
      · exact ⟨h1, h2, h3, by omega⟩
  have hdisj : Disjoint {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}
      {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0} := by
    rw [Set.disjoint_left]
    rintro Q ⟨-, -, -, h4⟩ ⟨-, -, -, h5⟩
    omega
  rw [hU, Set.ncard_union_eq hdisj hA hB]
  rfl

/-- The excess of a 3-face is carried by its non-triangular 2-faces, each with at most
`f₂(T) - 1` vertices. -/
lemma IsCSPolytope5.exc_le_ntri {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3) :
    exc P T ≤ ((cnt P T 2 : ℤ) - 4) * (ntri P T).ncard := by
  have hcard : (ntri P T).ncard =
      ((hP.below_finite T 2).toFinset.filter fun Q => 4 ≤ cnt P Q 0).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext Q
    simp only [ntri, Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    tauto
  rw [hP.exc_eq_sum T, hcard, ← Finset.sum_boole, Finset.mul_sum]
  refine Finset.sum_le_sum fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  have h3Q := hP.three_le_cnt hQ.1 hQ.2.2
  have hle := hP.cnt_zero_add_one_le hT h3 hQ.1 hQ.2.1 hQ.2.2
  split_ifs with h
  · rw [mul_one]; omega
  · rw [mul_zero]; omega

/-- A 3-face has a non-triangular 2-face iff its excess is positive. -/
lemma IsCSPolytope5.ntri_nonempty_iff {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3) :
    (ntri P T).Nonempty ↔ 3 * cnt P T 2 < 2 * cnt P T 1 := by
  have hx := hP.exc_threeface hT h3
  constructor
  · rintro hne
    have h1 : 0 < (ntri P T).ncard := (Set.ncard_pos (hP.ntri_finite T)).2 hne
    have h2 := hP.q4_add_big_le_exc T
    have h3' := hP.ntri_ncard T
    omega
  · intro hlt
    have hle := hP.exc_le_ntri hT h3
    have h0 : (ntri P T).ncard ≠ 0 := by
      intro h
      rw [h] at hle
      push_cast at hle
      omega
    exact Set.nonempty_of_ncard_ne_zero h0

/-- **Partners of non-triangular 2-faces.**  For a 3-face `T` of a facet `F` and a set `X ∋ T` of
3-faces none of which (other than `T`) contains a non-triangular 2-face of `T`, the
non-triangular 2-faces of `T` are at most as many as the 3-faces of `F` outside `X` with a
non-triangular 2-face. -/
lemma IsCSPolytope5.ntri_le {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) (X : Set (Set E5)) (hTX : T ∈ X)
    (hX : ∀ T' ∈ X, T' ≠ T → ∀ Q ∈ ntri P T, ¬ Q ⊆ T') :
    (ntri P T).ncard ≤ (nsimp P F \ X).ncard := by
  have hother : ∀ Q ∈ ntri P T,
      ∃ T' ∈ {T' | T' ∈ faces P ∧ Q ⊆ T' ∧ T' ⊆ F ∧ dim T' = 3}, T' ≠ T := by
    rintro Q ⟨hQ, hQT, hQ2, -⟩
    exact exists_ne_of_ncard_eq_two (hP.twoface_in_facet hF h4 hQ (hQT.trans hTF) hQ2)
      ⟨hT, hQT, hTF, h3⟩
  choose! g hg hgT using hother
  have hfin : (nsimp P F \ X).Finite := (hP.nsimp_finite F).sdiff
  refine Set.ncard_le_ncard_of_injOn g ?_ ?_ hfin
  · intro Q hQ
    obtain ⟨hT', hQT', hT'F, hT'3⟩ := hg Q hQ
    refine ⟨⟨hT', hT'F, hT'3, Q, hQ.1, hQT', hQ.2.2.1, hQ.2.2.2⟩, ?_⟩
    intro hmem
    exact hX _ hmem (hgT Q hQ) Q hQ hQT'
  · intro Q hQ Q' hQ' hgg
    obtain ⟨hT', hQT', -, hT'3⟩ := hg Q hQ
    obtain ⟨hT'', hQT'', -, hT''3⟩ := hg Q' hQ'
    have e1 := hP.inter_three_eq hQ.1 hQ.2.2.1 hT h3 hT' hT'3 (hgT Q hQ).symm hQ.2.1 hQT'
    have e2 := hP.inter_three_eq hQ'.1 hQ'.2.2.1 hT h3 hT'' hT''3 (hgT Q' hQ').symm hQ'.2.1 hQT''
    calc Q = T ∩ g Q := e1.symm
      _ = T ∩ g Q' := by rw [hgg]
      _ = Q' := e2

/-- The partner bound with `X = {T}`. -/
lemma IsCSPolytope5.ntri_le_pred {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) (hne : (ntri P T).Nonempty) :
    (ntri P T).ncard + 1 ≤ (nsimp P F).ncard := by
  have hle := hP.ntri_le hF h4 hT hTF h3 {T} rfl (fun T' hT' hne' => absurd hT' hne')
  have hmem : T ∈ nsimp P F := ⟨hT, hTF, h3, hne⟩
  rw [Set.ncard_sdiff_singleton_of_mem hmem] at hle
  have hpos : 0 < (nsimp P F).ncard := (Set.ncard_pos (hP.nsimp_finite F)).2 ⟨T, hmem⟩
  omega

/-- **(P1)** A triangular prism forces four 3-faces with a non-triangular 2-face. -/
lemma IsCSPolytope5.four_le_nsimp_of_prism {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) (ht : tri3 P T = (6, 9, 5)) :
    4 ≤ (nsimp P F).ncard := by
  obtain ⟨hq, hb⟩ := hP.q4_695 hT h3 ht
  have hn := hP.ntri_ncard T
  rw [hq, hb] at hn
  have hne : (ntri P T).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have := hP.ntri_le_pred hF h4 hT hTF h3 hne
  omega

/-- **(P3)** A 3-face with face numbers `(7,11,6)` forces three 3-faces with a non-triangular
2-face. -/
lemma IsCSPolytope5.three_le_nsimp_of_7116 {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) (ht : tri3 P T = (7, 11, 6)) :
    3 ≤ (nsimp P F).ncard := by
  simp only [tri3, Prod.mk.injEq] at ht
  obtain ⟨-, ht1, ht2⟩ := ht
  have hx := hP.exc_threeface hT h3
  have hle := hP.exc_le_ntri hT h3
  rw [ht1, ht2] at hx
  rw [ht2] at hle
  have h2 : 2 ≤ (ntri P T).ncard := by push_cast at hle; omega
  have hne : (ntri P T).Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have := hP.ntri_le_pred hF h4 hT hTF h3 hne
  omega

/-- **(P2)** Two prisms and a square pyramid do not fit among four 3-faces with a non-triangular
2-face: each prism would share a quadrilateral with the pyramid. -/
lemma IsCSPolytope5.not_two_prism_pyr {F G1 G2 Y : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hG1 : G1 ∈ faces P) (hG1F : G1 ⊆ F) (hG13 : dim G1 = 3) (ht1 : tri3 P G1 = (6, 9, 5))
    (hG2 : G2 ∈ faces P) (hG2F : G2 ⊆ F) (hG23 : dim G2 = 3) (ht2 : tri3 P G2 = (6, 9, 5))
    (h12 : G1 ≠ G2) (hY : Y ∈ faces P) (hYF : Y ⊆ F) (hY3 : dim Y = 3)
    (htY : tri3 P Y = (5, 8, 5)) (hle : (nsimp P F).ncard ≤ 4) : False := by
  have hY1 : Y ≠ G1 := by
    rintro rfl
    rw [ht1] at htY
    simp at htY
  have hY2 : Y ≠ G2 := by
    rintro rfl
    rw [ht2] at htY
    simp at htY
  obtain ⟨hqY, hbY⟩ := hP.q4_585 hY hY3 htY
  have hnY := hP.ntri_ncard Y
  rw [hqY, hbY] at hnY
  have hYmem : Y ∈ nsimp P F := ⟨hY, hYF, hY3, Set.nonempty_of_ncard_ne_zero (by omega)⟩
  -- every prism shares a non-triangular 2-face with the pyramid
  have share : ∀ G, G ∈ faces P → G ⊆ F → dim G = 3 → tri3 P G = (6, 9, 5) → Y ≠ G →
      ∃ Q ∈ ntri P G, Q ⊆ Y := by
    intro G hG hGF hG3 htG hYG
    by_contra hno
    push Not at hno
    obtain ⟨hq, hb⟩ := hP.q4_695 hG hG3 htG
    have hn := hP.ntri_ncard G
    rw [hq, hb] at hn
    have hGmem : G ∈ nsimp P F := ⟨hG, hGF, hG3, Set.nonempty_of_ncard_ne_zero (by omega)⟩
    have hle' := hP.ntri_le hF h4 hG hGF hG3 {G, Y} (by simp) (by
      intro T' hT' hne Q hQ hQT'
      rcases (show T' = G ∨ T' = Y by simpa using hT') with rfl | rfl
      · exact hne rfl
      · exact hno Q hQ hQT')
    have hsub : ({G, Y} : Set (Set E5)) ⊆ nsimp P F := by
      intro T' hT'
      rcases (show T' = G ∨ T' = Y by simpa using hT') with rfl | rfl
      · exact hGmem
      · exact hYmem
    rw [Set.ncard_sdiff hsub, Set.ncard_pair (Ne.symm hYG)] at hle'
    omega
  obtain ⟨Q1, hQ1, hQ1Y⟩ := share G1 hG1 hG1F hG13 ht1 hY1
  obtain ⟨Q2, hQ2, hQ2Y⟩ := share G2 hG2 hG2F hG23 ht2 hY2
  have hQ12 : Q1 ≠ Q2 := by
    rintro rfl
    have htwo := hP.twoface_in_facet hF h4 hQ1.1 (hQ1.2.1.trans hG1F) hQ1.2.2.1
    have hsub : ({G1, G2, Y} : Set (Set E5)) ⊆
        {T | T ∈ faces P ∧ Q1 ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by
      intro T hT
      rcases (show T = G1 ∨ T = G2 ∨ T = Y by simpa using hT) with rfl | rfl | rfl
      · exact ⟨hG1, hQ1.2.1, hG1F, hG13⟩
      · exact ⟨hG2, hQ2.2.1, hG2F, hG23⟩
      · exact ⟨hY, hQ1Y, hYF, hY3⟩
    have h3 : ({G1, G2, Y} : Set (Set E5)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨G1, G2, Y, h12, hY1.symm, hY2.symm, rfl⟩
    have hle3 := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T hT => hT.1)
    rw [h3, htwo] at hle3
    norm_num at hle3
  have hsub : ({Q1, Q2} : Set (Set E5)) ⊆ ntri P Y := by
    intro Q hQ
    rcases (show Q = Q1 ∨ Q = Q2 by simpa using hQ) with rfl | rfl
    · exact ⟨hQ1.1, hQ1Y, hQ1.2.2.1, hQ1.2.2.2⟩
    · exact ⟨hQ2.1, hQ2Y, hQ2.2.2.1, hQ2.2.2.2⟩
  have := Set.ncard_le_ncard hsub (hP.ntri_finite Y)
  rw [Set.ncard_pair hQ12] at this
  omega

end cs

end Kalai5
