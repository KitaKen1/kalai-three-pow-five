import Kalai5.Endpoints.WeightR19

/-!
# A lower bound for `q55w`, and the Q55 weight of `R₃₅ = (8,18,17,7;35)`

A quadrilateral of a facet `F` whose two 3-faces in `F` both have five vertices lies in two square
pyramids (a triangular bipyramid has no quadrilateral), and a square pyramid has a single
quadrilateral, so `2 b₅₅ ≤ #pyramids` (`IsCSPolytope5.two_b55_le`).  With `q55w = q₄ − 3 b₅₅` and
`b₅₅ ≤ q₄` this gives `q55w F ≥ −#pyramids` (`IsCSPolytope5.q55w_ge_pyr`).

The polar of a facet with row `R₃₅` has row `(7,17,18,8;35)`, catalogued with three vertex profiles:
in each, `2 exc F = 8`, no quadrilateral lies between two square pyramids, and `q₄ ≥ 2`, so
`q55w + 2 exc ≥ 10` (`IsCSPolytope5.q55_r35`).  When `F` has a 7-vertex 3-face `T`, each square
pyramid meets `T` in its quadrilateral (`IsCSPolytope5.pyr_quad_sub`).
-/

namespace Kalai5

open Set

open scoped Classical

/-- The row `R₃₅ = (8,18,17,7;35)`. -/
def r35Row : Row := ⟨8, 18, 17, 7, 35⟩

lemma smallRowsX_r35dual :
    ∀ X ∈ smallRowsX, X.1 = ⟨7, 17, 18, 8, 35⟩ →
      X.2.2 = [3, 1, 1, 0, 2, 0, 0] ∨ X.2.2 = [2, 4, 0, 0, 0, 1, 0] ∨
        X.2.2 = [3, 2, 0, 0, 1, 1, 0] := by
  decide

/-- The quadrilaterals of `F` whose 3-faces in `F` all have five vertices. -/
def b55set (P F : Set E5) : Set (Set E5) :=
  {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4 ∧ non5 P F Q = ∅}

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- `q55w = q₄ − 3 b₅₅`. -/
lemma IsCSPolytope5.q55w_eq_b55 (F : Set E5) :
    q55w P F = q4 P F - 3 * (b55set P F).ncard := by
  rw [hP.q55w_eq, hP.q4_eq_card]
  have hb : (b55set P F).ncard = ((hP.below_finite F 2).toFinset.filter
      (fun Q => cnt P Q 0 = 4 ∧ non5 P F Q = ∅)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext Q
    simp only [b55set, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  rw [hb, Finset.card_filter, Finset.card_filter]
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun Q _ => ?_
  by_cases h4 : cnt P Q 0 = 4 <;> by_cases hn : non5 P F Q = ∅ <;> simp [h4, hn]

/-- **Every 3-face through a `b₅₅` quadrilateral is a square pyramid** (a triangular bipyramid has
no quadrilateral). -/
lemma IsCSPolytope5.b55_pyr {F : Set E5} : ∀ Q ∈ b55set P F, ∀ T, T ∈ faces P → Q ⊆ T → T ⊆ F →
    dim T = 3 → tri3 P T = (5, 8, 5) := by
  rintro Q ⟨hQf, -, hQ2, hQ4, hn⟩ T hT hQT hTF hT3
  have h5 : cnt P T 0 = 5 := by
    by_contra hc
    have : T ∈ non5 P F Q := ⟨hT, hTF, hT3, hQT, hc⟩
    rw [hn] at this
    exact this
  have hQn : 0 < q4 P T :=
    (Set.ncard_pos (hP.faces_finite.subset fun Q' hQ' => hQ'.1)).2 ⟨Q, hQf, hQT, hQ2, hQ4⟩
  have hin := hP.tri3_mem_fv8 hT hT3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h
  all_goals first
    | exact h
    | (exfalso; rw [(hP.q4_596 hT hT3 h).1] at hQn; omega)
    | (exfalso; simp only [tri3, Prod.mk.injEq] at h; omega)

/-- **Each quadrilateral between two 5-vertex 3-faces uses two square pyramids**, and a square
pyramid has one quadrilateral: `2 b₅₅ ≤ #pyramids`. -/
lemma IsCSPolytope5.two_b55_le {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    2 * (b55set P F).ncard ≤ tcnt P F (5, 8, 5) := by
  have hfinB : (b55set P F).Finite := hP.faces_finite.subset fun Q hQ => hQ.1
  have hfinY : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 8, 5)}.Finite :=
    hP.faces_finite.subset fun T hT => hT.1
  have hpyr := hP.b55_pyr (F := F)
  -- each `b₅₅` quadrilateral lies in two pyramids
  have hL : ∀ Q ∈ hfinB.toFinset,
      ∑ T ∈ hfinY.toFinset, (if Q ⊆ T then 1 else 0) = 2 := by
    intro Q hQ
    rw [Set.Finite.mem_toFinset] at hQ
    have htwo := hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2.1
    have hfinT : {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3}.Finite :=
      hP.faces_finite.subset fun T hT => hT.1
    have hc : hfinY.toFinset.filter (fun T => Q ⊆ T) = hfinT.toFinset := by
      ext T
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hT, hTF, hT3, -⟩, hQT⟩
        exact ⟨hT, hQT, hTF, hT3⟩
      · rintro ⟨hT, hQT, hTF, hT3⟩
        exact ⟨⟨hT, hTF, hT3, hpyr Q hQ T hT hQT hTF hT3⟩, hQT⟩
    rw [Finset.sum_boole, hc, ← Set.ncard_eq_toFinset_card _ hfinT, htwo]
    rfl
  -- a pyramid contains at most one `b₅₅` quadrilateral
  have hR : ∀ T ∈ hfinY.toFinset,
      ∑ Q ∈ hfinB.toFinset, (if Q ⊆ T then 1 else 0) ≤ 1 := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    rw [Finset.sum_boole]
    have hq := (hP.q4_585 hT.1 hT.2.2.1 hT.2.2.2).1
    rw [hP.q4_eq_card] at hq
    have hle : (hfinB.toFinset.filter (fun Q => Q ⊆ T)).card ≤
        ((hP.below_finite T 2).toFinset.filter fun Q => cnt P Q 0 = 4).card := by
      apply Finset.card_le_card
      intro Q hQ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hQ ⊢
      exact ⟨⟨hQ.1.1, hQ.2, hQ.1.2.2.1⟩, hQ.1.2.2.2.1⟩
    rw [hq] at hle
    exact_mod_cast hle
  have hsum : ∑ Q ∈ hfinB.toFinset, ∑ T ∈ hfinY.toFinset, (if Q ⊆ T then 1 else 0) =
      ∑ T ∈ hfinY.toFinset, ∑ Q ∈ hfinB.toFinset, (if Q ⊆ T then 1 else 0) :=
    Finset.sum_comm
  have h1 : ∑ Q ∈ hfinB.toFinset, ∑ T ∈ hfinY.toFinset, (if Q ⊆ T then 1 else 0) =
      2 * (b55set P F).ncard := by
    rw [Finset.sum_congr rfl hL, Finset.sum_const, smul_eq_mul, mul_comm,
      ← Set.ncard_eq_toFinset_card _ hfinB]
  have h2 : ∑ T ∈ hfinY.toFinset, ∑ Q ∈ hfinB.toFinset, (if Q ⊆ T then 1 else 0) ≤
      tcnt P F (5, 8, 5) := by
    calc _ ≤ ∑ T ∈ hfinY.toFinset, 1 := Finset.sum_le_sum hR
      _ = tcnt P F (5, 8, 5) := by
        rw [Finset.sum_const, smul_eq_mul, mul_one, tcnt, Set.ncard_eq_toFinset_card _ hfinY]
  calc 2 * (b55set P F).ncard = _ := h1.symm
    _ = _ := hsum
    _ ≤ _ := h2

/-- **Lower bound for `q55w`**: `q55w F ≥ −#(square pyramids of F)`. -/
theorem IsCSPolytope5.q55w_ge_pyr {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    -(tcnt P F (5, 8, 5) : ℤ) ≤ q55w P F := by
  have h1 := hP.q55w_eq_b55 F
  have h2 := hP.two_b55_le hF h4
  have h3 : (b55set P F).ncard ≤ q4 P F :=
    Set.ncard_le_ncard (fun Q hQ => ⟨hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1⟩)
      (hP.faces_finite.subset fun Q hQ => hQ.1)
  omega

/-! ### Eight-vertex facets with a 7-vertex 3-face -/

/-- A face of dimension at most one has at most two vertices. -/
lemma IsCSPolytope5.cnt_le_two_of_dim_le_one {G : Set E5} (hG : G ∈ faces P) (hd : dim G ≤ 1) :
    cnt P G 0 ≤ 2 := by
  rcases Nat.lt_or_ge (dim G) 1 with h0 | h1
  · obtain ⟨g, rfl⟩ := eq_singleton_of_dim_eq_zero hG.1 (by omega)
    have hsub : vset P {g} ⊆ {({g} : Set E5)} := fun v hv =>
      (Set.Nonempty.subset_singleton_iff hv.1.1).1 hv.2.1
    have := Set.ncard_le_ncard hsub (Set.finite_singleton _)
    rw [Set.ncard_singleton] at this
    rw [cnt_eq_vset]
    omega
  · obtain ⟨V, hV⟩ := hP.polytope
    have hG' : G ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hG
    have := cnt_zero_of_dim_one hG' (by omega)
    rw [← hV] at this
    omega

/-- **A square pyramid of an eight-vertex facet with a 7-vertex 3-face `T` has its quadrilateral
in `T`**: the pyramid meets `T` in a proper face with at least `5 + 7 - 8 = 4` vertices. -/
lemma IsCSPolytope5.pyr_quad_sub {F T Y : Set E5} (hn : cnt P F 0 = 8)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT7 : cnt P T 0 = 7)
    (hY : Y ∈ faces P) (hYF : Y ⊆ F) (hY3 : dim Y = 3) (hyt : tri3 P Y = (5, 8, 5)) :
    ∃ G ∈ ntri P Y, G ⊆ T := by
  have hY5 : cnt P Y 0 = 5 := by simp only [tri3, Prod.mk.injEq] at hyt; exact hyt.1
  have hvi : vset P (Y ∩ T) = vset P Y ∩ vset P T := by
    ext v
    simp only [vset, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.subset_inter_iff]
    tauto
  have hu : vset P Y ∪ vset P T ⊆ vset P F := by
    rintro v (hv | hv)
    · exact ⟨hv.1, hv.2.1.trans hYF, hv.2.2⟩
    · exact ⟨hv.1, hv.2.1.trans hTF, hv.2.2⟩
  have h1 := Set.ncard_union_add_ncard_inter (vset P Y) (vset P T) (hP.vset_finite Y)
    (hP.vset_finite T)
  have h2 := Set.ncard_le_ncard hu (hP.vset_finite F)
  rw [← cnt_eq_vset, ← cnt_eq_vset, ← hvi, ← cnt_eq_vset] at h1
  rw [← cnt_eq_vset] at h2
  have h4 : 4 ≤ cnt P (Y ∩ T) 0 := by omega
  have hne : (Y ∩ T).Nonempty := by
    have : (vset P (Y ∩ T)).Nonempty :=
      Set.nonempty_of_ncard_ne_zero (by rw [← cnt_eq_vset]; omega)
    obtain ⟨v, hv⟩ := this
    exact hv.1.1.mono hv.2.1
  have hI : Y ∩ T ∈ faces P := inter_mem_faces_of_nonempty hY hT hne
  have hIY : Y ∩ T ∈ faces Y := mem_faces_of_subset (face_subset hY) hI inter_subset_left
  have hIne : Y ∩ T ≠ Y := by
    intro h
    have hYT : Y ⊆ T := by rw [← h]; exact inter_subset_right
    have := hP.eq_of_subset_of_dim_le hY hT hYT (by omega)
    rw [this] at hY5
    omega
  have hlt := dim_lt_of_mem_faces_ne hIY hIne
  have hd2 : dim (Y ∩ T) = 2 := by
    by_contra hd
    have := hP.cnt_le_two_of_dim_le_one hI (by omega)
    omega
  exact ⟨Y ∩ T, ⟨hI, inter_subset_left, hd2, h4⟩, inter_subset_right⟩

/-- **Consequences of a 7-vertex 3-face `T` in an eight-vertex facet**: no quadrilateral lies
between two square pyramids, and `T` has at least as many quadrilaterals as there are square
pyramids (their quadrilaterals lie in `T`, and are distinct). -/
lemma IsCSPolytope5.facet_T7 {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 = 8) (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3)
    (hT7 : cnt P T 0 = 7) :
    (b55set P F).ncard = 0 ∧ tcnt P F (5, 8, 5) ≤ q4 P T := by
  -- the non-triangular 2-face of a pyramid is unique
  have uniq : ∀ Y, Y ∈ faces P → dim Y = 3 → tri3 P Y = (5, 8, 5) →
      ∀ G ∈ ntri P Y, ∀ G' ∈ ntri P Y, G = G' := by
    intro Y hY hY3 hyt G hG G' hG'
    have hn1 : (ntri P Y).ncard = 1 := by
      rw [hP.ntri_ncard Y, (hP.q4_585 hY hY3 hyt).1, (hP.q4_585 hY hY3 hyt).2]
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hn1
    rw [hx, Set.mem_singleton_iff] at hG hG'
    rw [hG, hG']
  -- a 2-face of `F` in two pyramids and in `T` is impossible
  have three : ∀ G Y Y', G ∈ faces P → G ⊆ F → dim G = 2 → G ⊆ T → Y ∈ faces P → G ⊆ Y →
      Y ⊆ F → dim Y = 3 → tri3 P Y = (5, 8, 5) → Y' ∈ faces P → G ⊆ Y' → Y' ⊆ F →
      dim Y' = 3 → tri3 P Y' = (5, 8, 5) → Y ≠ Y' → False := by
    intro G Y Y' hG hGF hG2 hGT hY hGY hYF hY3 hyt hY' hGY' hY'F hY'3 hy't hYY'
    have hY5 : cnt P Y 0 = 5 := by simp only [tri3, Prod.mk.injEq] at hyt; exact hyt.1
    have hY'5 : cnt P Y' 0 = 5 := by simp only [tri3, Prod.mk.injEq] at hy't; exact hy't.1
    have hTY : T ≠ Y := fun h => by rw [h] at hT7; omega
    have hTY' : T ≠ Y' := fun h => by rw [h] at hT7; omega
    have hsub : ({T, Y, Y'} : Set (Set E5)) ⊆
        {T' | T' ∈ faces P ∧ G ⊆ T' ∧ T' ⊆ F ∧ dim T' = 3} := by
      intro T' hT'
      rcases (show T' = T ∨ T' = Y ∨ T' = Y' by simpa using hT') with h | h | h
      · rw [h]; exact ⟨hT, hGT, hTF, hT3⟩
      · rw [h]; exact ⟨hY, hGY, hYF, hY3⟩
      · rw [h]; exact ⟨hY', hGY', hY'F, hY'3⟩
    have h3 : ({T, Y, Y'} : Set (Set E5)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨T, Y, Y', hTY, hTY', hYY', rfl⟩
    have hle := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T' hT' => hT'.1)
    rw [h3, hP.twoface_in_facet hF h4 hG hGF hG2] at hle
    omega
  refine ⟨?_, ?_⟩
  · -- `b₅₅ = 0`
    rw [Set.ncard_eq_zero (hP.faces_finite.subset fun Q hQ => hQ.1)]
    refine Set.eq_empty_of_forall_notMem fun Q hQ => ?_
    have hQ' := hQ
    obtain ⟨hQf, hQF, hQ2, hQ4, -⟩ := hQ'
    have htwo := hP.twoface_in_facet hF h4 hQf hQF hQ2
    obtain ⟨Y1, Y2, h12, hY12⟩ := Set.ncard_eq_two.1 htwo
    have hY1 : Y1 ∈ {T' | T' ∈ faces P ∧ Q ⊆ T' ∧ T' ⊆ F ∧ dim T' = 3} := by rw [hY12]; simp
    have hY2 : Y2 ∈ {T' | T' ∈ faces P ∧ Q ⊆ T' ∧ T' ⊆ F ∧ dim T' = 3} := by rw [hY12]; simp
    obtain ⟨hY1f, hQY1, hY1F, hY13⟩ := hY1
    obtain ⟨hY2f, hQY2, hY2F, hY23⟩ := hY2
    have hy1 := hP.b55_pyr Q hQ Y1 hY1f hQY1 hY1F hY13
    have hy2 := hP.b55_pyr Q hQ Y2 hY2f hQY2 hY2F hY23
    obtain ⟨G, hG, hGT⟩ := hP.pyr_quad_sub hn hT hTF hT3 hT7 hY1f hY1F hY13 hy1
    have hGQ : G = Q := uniq Y1 hY1f hY13 hy1 G hG Q ⟨hQf, hQY1, hQ2, by omega⟩
    rw [hGQ] at hGT
    exact three Q Y1 Y2 hQf hQF hQ2 hGT hY1f hQY1 hY1F hY13 hy1 hY2f hQY2 hY2F hY23 hy2 h12
  · -- the pyramids inject into the quadrilaterals of `T`
    have hex : ∀ Y ∈ {Y | Y ∈ faces P ∧ Y ⊆ F ∧ dim Y = 3 ∧ tri3 P Y = (5, 8, 5)},
        ∃ G, G ∈ ntri P Y ∧ G ⊆ T :=
      fun Y hY => hP.pyr_quad_sub hn hT hTF hT3 hT7 hY.1 hY.2.1 hY.2.2.1 hY.2.2.2
    choose! g hg using hex
    have hinj : Set.InjOn g {Y | Y ∈ faces P ∧ Y ⊆ F ∧ dim Y = 3 ∧ tri3 P Y = (5, 8, 5)} := by
      intro Y hY Y' hY' h
      by_contra hne
      obtain ⟨⟨hGf, hGY, hG2, -⟩, hGT⟩ := hg Y hY
      obtain ⟨⟨-, hGY', -, -⟩, -⟩ := hg Y' hY'
      rw [← h] at hGY'
      exact three (g Y) Y Y' hGf (hGY.trans hY.2.1) hG2 hGT hY.1 hGY hY.2.1 hY.2.2.1 hY.2.2.2
        hY'.1 hGY' hY'.2.1 hY'.2.2.1 hY'.2.2.2 hne
    have hmaps : g '' {Y | Y ∈ faces P ∧ Y ⊆ F ∧ dim Y = 3 ∧ tri3 P Y = (5, 8, 5)} ⊆
        {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
      rintro Q ⟨Y, hY, rfl⟩
      obtain ⟨⟨hGf, hGY, hG2, hG4⟩, hGT⟩ := hg Y hY
      have hle := hP.cnt_zero_add_one_le hY.1 hY.2.2.1 hGf hGY hG2
      have hf2 : cnt P Y 2 = 5 := by
        have := hY.2.2.2
        simp only [tri3, Prod.mk.injEq] at this
        exact this.2.2
      exact ⟨hGf, hGT, hG2, by omega⟩
    have := Set.ncard_le_ncard hmaps (hP.faces_finite.subset fun Q hQ => hQ.1)
    rw [hinj.ncard_image] at this
    exact this

/-- **Lower bound for `2 q₄`** of an eight-vertex facet: pyramids count one, prisms three, and any
further bonus `k T ≤ q₄ T` on the other 3-faces. -/
lemma IsCSPolytope5.two_q4_lb {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 = 8) (k : Set E5 → ℤ)
    (hk : ∀ T ∈ (hP.below_finite F 3).toFinset, tri3 P T ≠ (5, 8, 5) → tri3 P T ≠ (6, 9, 5) →
      k T ≤ q4 P T)
    (hk0 : ∀ T ∈ (hP.below_finite F 3).toFinset, tri3 P T = (5, 8, 5) ∨ tri3 P T = (6, 9, 5) →
      k T = 0) :
    (tcnt P F (5, 8, 5) : ℤ) + 3 * tcnt P F (6, 9, 5) +
      ∑ T ∈ (hP.below_finite F 3).toFinset, k T ≤ 2 * q4 P F := by
  rw [hP.two_q4_facet hF h4]
  have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset,
      (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 9, 5) then 3 else 0)
        (tri3 P T) + k T ≤ (q4 P T : ℤ) := by
    intro T hT
    have hT' := hT
    rw [Set.Finite.mem_toFinset] at hT'
    by_cases h1 : tri3 P T = (5, 8, 5)
    · rw [hk0 T hT (Or.inl h1), h1, (hP.q4_585 hT'.1 hT'.2.2 h1).1]
      simp
    · by_cases h2 : tri3 P T = (6, 9, 5)
      · rw [hk0 T hT (Or.inr h2), h2, (hP.q4_695 hT'.1 hT'.2.2 h2).1]
        simp
      · have := hk T hT h1 h2
        simp only [h1, h2, ite_false]
        linarith
  have hsum := Finset.sum_le_sum hpt
  have h8 := hP.facet8_sum hF h4 hn
    (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 9, 5) then 3 else 0)
  have hval : (fv8.map fun t => (tcnt P F t : ℤ) *
      (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 9, 5) then 3 else 0) t).sum =
      (tcnt P F (5, 8, 5) : ℤ) + 3 * tcnt P F (6, 9, 5) := by
    simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
    try ring
  rw [Finset.sum_add_distrib, h8, hval] at hsum
  exact hsum

/-! ### The row `R₃₅` -/

/-- **The 3-faces of a facet with row `R₃₅`**, by the three catalogued profiles of the polar, and
`2 exc = 8`. -/
lemma IsCSPolytope5.r35_types {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r35Row) :
    2 * exc P F = 8 ∧
      ((tcnt P F (5, 8, 5) = 1 ∧ tcnt P F (6, 9, 5) = 1) ∨
        (tcnt P F (5, 8, 5) = 4 ∧ tcnt P F (7, 11, 6) = 1 ∧ tcnt P F (6, 9, 5) = 0) ∨
        (tcnt P F (5, 8, 5) = 2 ∧ tcnt P F (7, 11, 6) = 1 ∧ tcnt P F (6, 9, 5) = 0)) := by
  have hR' := hR
  simp only [faceRow, r35Row, Row.mk.injEq] at hR'
  obtain ⟨h0, h1, h2, h3, hJ⟩ := hR'
  obtain ⟨X, hX, hX1, hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0, h1, h2, h3, hJ] at hX1
  obtain ⟨e1, -, -, -⟩ := hP.facet8_arith hF h4 h0
  have hE := hP.two_exc_facet hF h4
  have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset,
      exc P T = (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2) (tri3 P T) := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    rw [hP.exc_threeface hT.1 hT.2.2]
    rfl
  have hsum := hP.facet8_sum hF h4 h0 (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2)
  rw [Finset.sum_congr rfl hpt, hsum] at hE
  simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hE
  push_cast at hE
  rcases smallRowsX_r35dual X hX hX1 with hp | hp | hp <;> rw [hp] at hX2 <;>
    simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at hX2 <;> omega

/-- **Q55 weight of `R₃₅`**: `q55w + 2 exc ≥ 10`.  With one pyramid, `b₅₅ = 0` and the pyramid
and prism give `q₄ ≥ 2`; with a 7-vertex 3-face `T`, `b₅₅ = 0` and `q₄(T) ≥ #pyramids`
(`IsCSPolytope5.facet_T7`), so again `q₄ ≥ 2`. -/
theorem IsCSPolytope5.q55_r35 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r35Row) : 10 ≤ q55w P F + 2 * exc P F := by
  have hn : cnt P F 0 = 8 := by
    simp only [faceRow, r35Row, Row.mk.injEq] at hR
    exact hR.1
  obtain ⟨hE, hcase⟩ := hP.r35_types hF h4 hR
  have hq := hP.q55w_eq_b55 F
  have hb := hP.two_b55_le hF h4
  rcases hcase with ⟨c1, c2⟩ | ⟨c1, c2, c3⟩ | ⟨c1, c2, c3⟩
  · -- one pyramid, one prism
    have hlb := hP.two_q4_lb hF h4 hn (fun _ => 0) (fun _ _ _ _ => by positivity)
      (fun _ _ _ => rfl)
    simp only [Finset.sum_const_zero, add_zero] at hlb
    rw [c1, c2] at hlb
    rw [c1] at hb
    push_cast at hlb
    omega
  all_goals
    obtain ⟨T7, hT7f, hT7F, hT73, ht7⟩ := hP.exists_of_tcnt (F := F) (t := (7, 11, 6)) (by omega)
    have hT7 : cnt P T7 0 = 7 := by simp only [tri3, Prod.mk.injEq] at ht7; exact ht7.1
    obtain ⟨hb0, hq7⟩ := hP.facet_T7 hF h4 hn hT7f hT7F hT73 hT7
    have hmem : T7 ∈ (hP.below_finite F 3).toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨hT7f, hT7F, hT73⟩
    have hlb := hP.two_q4_lb hF h4 hn
      (fun T => if T = T7 then (tcnt P F (5, 8, 5) : ℤ) else 0)
      (fun T _ _ _ => by
        by_cases h : T = T7
        · rw [if_pos h, h]; exact_mod_cast hq7
        · rw [if_neg h]; positivity)
      (fun T _ h => by
        rw [if_neg]
        rintro rfl
        rcases h with h | h <;> rw [ht7] at h <;> simp at h)
    rw [Finset.sum_ite_eq', if_pos hmem] at hlb
    rw [c1, c3] at hlb
    push_cast at hlb
    omega

end cs

end Kalai5
