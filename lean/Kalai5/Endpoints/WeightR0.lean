import Kalai5.Endpoints.R7Types
import Kalai5.Endpoints.Q55.Sum

/-!
# The Q55 weight of the row `R₀ = (8,18,17,7;36)`

The polar of a facet with row `R₀` has row `(7,17,18,8;36)`, a single catalogued type, so the 3-faces
are one tetrahedron, four square pyramids and two triangular prisms (`IsCSPolytope5.r0_types`).
The prisms have three quadrilaterals each with distinct partners, so no quadrilateral is shared by
two pyramids (`IsCSPolytope5.not_two_prism_pyr_excl`); hence every quadrilateral counts `+1` in
`q55w`, `q₄ = 5`, the excess is `5`, and `q55w + 2 exc = 15` (`IsCSPolytope5.q55_r0`).
-/

namespace Kalai5

open Set

open scoped Classical

/-- The row `R₀ = (8,18,17,7;36)`. -/
def r0Row : Row := ⟨8, 18, 17, 7, 36⟩

lemma smallRowsX_r0dual :
    ∀ X ∈ smallRowsX, X.1 = ⟨7, 17, 18, 8, 36⟩ → X.2.2 = [1, 4, 2, 0, 0, 0, 0] := by
  decide

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **(P2) with exclusions**: two prisms and a square pyramid `Y`, all outside a set `X` of 3-faces
containing no non-triangular 2-face of the prisms, cannot live among four 3-faces outside `X` with a
non-triangular 2-face. -/
lemma IsCSPolytope5.not_two_prism_pyr_excl {F G1 G2 Y : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4)
    (hG1 : G1 ∈ faces P) (hG1F : G1 ⊆ F) (hG13 : dim G1 = 3) (ht1 : tri3 P G1 = (6, 9, 5))
    (hG2 : G2 ∈ faces P) (hG2F : G2 ⊆ F) (hG23 : dim G2 = 3) (ht2 : tri3 P G2 = (6, 9, 5))
    (h12 : G1 ≠ G2) (hY : Y ∈ faces P) (hYF : Y ⊆ F) (hY3 : dim Y = 3)
    (htY : tri3 P Y = (5, 8, 5)) (X : Set (Set E5)) (hXfin : X.Finite)
    (hG1X : G1 ∉ X) (hG2X : G2 ∉ X) (hYX : Y ∉ X)
    (hX1 : ∀ T ∈ X, ∀ Q ∈ ntri P G1, ¬ Q ⊆ T) (hX2 : ∀ T ∈ X, ∀ Q ∈ ntri P G2, ¬ Q ⊆ T)
    (hle : (nsimp P F \ X).ncard ≤ 4) : False := by
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
  have hYmem : Y ∈ nsimp P F \ X :=
    ⟨⟨hY, hYF, hY3, Set.nonempty_of_ncard_ne_zero (by omega)⟩, hYX⟩
  have share : ∀ G, G ∈ faces P → G ⊆ F → dim G = 3 → tri3 P G = (6, 9, 5) → Y ≠ G → G ∉ X →
      (∀ T ∈ X, ∀ Q ∈ ntri P G, ¬ Q ⊆ T) → ∃ Q ∈ ntri P G, Q ⊆ Y := by
    intro G hG hGF hG3 htG hYG hGX hXG
    by_contra hno
    push Not at hno
    obtain ⟨hq, hb⟩ := hP.q4_695 hG hG3 htG
    have hn := hP.ntri_ncard G
    rw [hq, hb] at hn
    have hGmem : G ∈ nsimp P F \ X :=
      ⟨⟨hG, hGF, hG3, Set.nonempty_of_ncard_ne_zero (by omega)⟩, hGX⟩
    have hle' := hP.ntri_le hF h4 hG hGF hG3 (X ∪ {G, Y}) (by simp) (by
      intro T' hT' hne Q hQ hQT'
      rcases hT' with hT' | hT'
      · exact hXG T' hT' Q hQ hQT'
      · rcases (show T' = G ∨ T' = Y by simpa using hT') with rfl | rfl
        · exact hne rfl
        · exact hno Q hQ hQT')
    have hdiff : nsimp P F \ (X ∪ {G, Y}) = (nsimp P F \ X) \ {G, Y} := by
      exact Set.sdiff_sdiff.symm
    have hsub : ({G, Y} : Set (Set E5)) ⊆ nsimp P F \ X := by
      intro T' hT'
      rcases (show T' = G ∨ T' = Y by simpa using hT') with rfl | rfl
      · exact hGmem
      · exact hYmem
    rw [hdiff, Set.ncard_sdiff hsub, Set.ncard_pair (Ne.symm hYG)] at hle'
    omega
  obtain ⟨Q1, hQ1, hQ1Y⟩ := share G1 hG1 hG1F hG13 ht1 hY1 hG1X hX1
  obtain ⟨Q2, hQ2, hQ2Y⟩ := share G2 hG2 hG2F hG23 ht2 hY2 hG2X hX2
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

/-- **The 3-faces of a facet with row `R₀`**: one tetrahedron, four square pyramids, two prisms. -/
lemma IsCSPolytope5.r0_types {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r0Row) :
    tcnt P F (4, 6, 4) = 1 ∧ tcnt P F (5, 8, 5) = 4 ∧ tcnt P F (6, 9, 5) = 2 ∧
      tcnt P F (5, 9, 6) = 0 ∧ tcnt P F (6, 10, 6) = 0 ∧ tcnt P F (7, 11, 6) = 0 := by
  simp only [faceRow, r0Row, Row.mk.injEq] at hR
  obtain ⟨h0, h1, h2, h3, hJ⟩ := hR
  obtain ⟨X, hX, hX1, hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0, h1, h2, h3, hJ] at hX1
  rw [smallRowsX_r0dual X hX hX1] at hX2
  simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at hX2
  omega

/-- Sums over the 3-faces of an eight-vertex facet, grouped by type. -/
lemma IsCSPolytope5.facet8_sum {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (h8 : cnt P F 0 = 8) (g : ℕ × ℕ × ℕ → ℤ) :
    ∑ T ∈ (hP.below_finite F 3).toFinset, g (tri3 P T) =
      (fv8.map fun t => (tcnt P F t : ℤ) * g t).sum := by
  have hall : ∀ T ∈ (hP.below_finite F 3).toFinset, tri3 P T ∈ fv8 := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    have hne : T ≠ F := by
      rintro rfl
      rw [hT.2.2] at h4
      exact absurd h4 (by norm_num)
    have hlt := hP.cnt_zero_lt hT.1 hF hT.2.1 hne
    exact hP.tri3_mem_fv8 hT.1 hT.2.2 (by omega)
  rw [sum_of_cover _ (tri3 P) fv8_nodup hall g]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  rw [hP.tcnt_eq_card]

lemma IsCSPolytope5.one_le_tcnt {F T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F)
    (h3 : dim T = 3) : 1 ≤ tcnt P F (tri3 P T) := by
  unfold tcnt
  have hfin : {T' | T' ∈ faces P ∧ T' ⊆ F ∧ dim T' = 3 ∧ tri3 P T' = tri3 P T}.Finite :=
    hP.faces_finite.subset fun T' h => h.1
  exact (Set.ncard_pos hfin).2 ⟨T, hT, hTF, h3, rfl⟩

/-- In a facet with row `R₀` every 3-face is a tetrahedron, a square pyramid or a prism. -/
lemma IsCSPolytope5.r0_type_cases {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r0Row) {T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) :
    tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (6, 9, 5) := by
  have hR' := hR
  simp only [faceRow, r0Row, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, -, -, -⟩ := hP.r0_types hF h4 hR
  obtain ⟨e1, -, -, -⟩ := hP.facet8_arith hF h4 hn
  have h1 := hP.one_le_tcnt hT hTF h3
  have hne : T ≠ F := by
    rintro rfl
    rw [h3] at h4
    exact absurd h4 (by norm_num)
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT h3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | (left; rfl) | (right; left; rfl) | (right; right; rfl) | omega

/-- **Q55 weight of `R₀`**: `q55w + 2 exc ≥ 15`. -/
theorem IsCSPolytope5.q55_r0 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = r0Row) : 15 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, r0Row, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r0_types hF h4 hR
  obtain ⟨e1, -, -, e4⟩ := hP.facet8_arith hF h4 hn
  -- the excess
  have hexc : 2 * exc P F = 10 := by
    rw [hP.two_exc_facet hF h4]
    have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset,
        exc P T = (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2) (tri3 P T) := by
      intro T hT
      rw [Set.Finite.mem_toFinset] at hT
      rw [hP.exc_threeface hT.1 hT.2.2]
      rfl
    have hsum := hP.facet8_sum hF h4 hn (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2)
    rw [Finset.sum_congr rfl hpt, hsum]
    simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    omega
  -- the quadrilaterals
  have hq4 : 2 * (q4 P F : ℤ) = 10 := by
    rw [hP.two_q4_facet hF h4]
    have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset, (q4 P T : ℤ) =
        (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 9, 5) then 3 else 0)
          (tri3 P T) := by
      intro T hT
      rw [Set.Finite.mem_toFinset] at hT
      rcases hP.r0_type_cases hF h4 hR hT.1 hT.2.1 hT.2.2 with h | h | h
      · rw [hP.q4_464 hT.1 hT.2.2 h, h]; rfl
      · rw [(hP.q4_585 hT.1 hT.2.2 h).1, h]; rfl
      · rw [(hP.q4_695 hT.1 hT.2.2 h).1, h]; rfl
    have hsum := hP.facet8_sum hF h4 hn
      (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 9, 5) then 3 else 0)
    rw [Finset.sum_congr rfl hpt, hsum]
    simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
    omega
  -- no quadrilateral between two square pyramids
  have hno55 : ∀ Q ∈ (hP.below_finite F 2).toFinset, cnt P Q 0 = 4 → non5 P F Q ≠ ∅ := by
    intro Q hQ h4Q h55
    rw [Set.Finite.mem_toFinset] at hQ
    obtain ⟨hQf, hQF, hQ2⟩ := hQ
    have htwo := hP.twoface_in_facet hF h4 hQf hQF hQ2
    obtain ⟨T1, T2, h12, hT12⟩ := Set.ncard_eq_two.1 htwo
    have hT1 : T1 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    have hT2 : T2 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    obtain ⟨hT1f, hQT1, hT1F, hT13⟩ := hT1
    obtain ⟨hT2f, hQT2, hT2F, hT23⟩ := hT2
    have five : ∀ T, T ∈ faces P → Q ⊆ T → T ⊆ F → dim T = 3 → tri3 P T = (5, 8, 5) := by
      intro T hT hQT hTF hT3
      have h5 : cnt P T 0 = 5 := by
        by_contra hc
        have : T ∈ non5 P F Q := ⟨hT, hTF, hT3, hQT, hc⟩
        rw [h55] at this
        exact this
      rcases hP.r0_type_cases hF h4 hR hT hTF hT3 with h | h | h
      · simp only [tri3, Prod.mk.injEq] at h; omega
      · exact h
      · simp only [tri3, Prod.mk.injEq] at h; omega
    have ht1 := five T1 hT1f hQT1 hT1F hT13
    have ht2 := five T2 hT2f hQT2 hT2F hT23
    -- the unique non-triangular 2-face of a pyramid through `Q` is `Q`
    have uniq : ∀ T, T ∈ faces P → dim T = 3 → tri3 P T = (5, 8, 5) → Q ∈ ntri P T →
        ∀ Q' ∈ ntri P T, Q' = Q := by
      intro T hT hT3 htT hQn Q' hQ'
      have hn1 : (ntri P T).ncard = 1 := by
        rw [hP.ntri_ncard T, (hP.q4_585 hT hT3 htT).1, (hP.q4_585 hT hT3 htT).2]
      obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hn1
      rw [hx, Set.mem_singleton_iff] at hQn hQ'
      rw [hQ', hQn]
    have hQn1 : Q ∈ ntri P T1 := ⟨hQf, hQT1, hQ2, by omega⟩
    have hQn2 : Q ∈ ntri P T2 := ⟨hQf, hQT2, hQ2, by omega⟩
    -- a 3-face other than `T1, T2` contains no non-triangular 2-face of them
    have hX : ∀ G, G ∈ faces P → G ⊆ F → dim G = 3 → G ≠ T1 → G ≠ T2 →
        ∀ T ∈ ({T1, T2} : Set (Set E5)), ∀ Q' ∈ ntri P G, ¬ Q' ⊆ T := by
      intro G hG hGF hG3 hG1' hG2' T hT Q' hQ' hQ'T
      have hQ'eq : Q' = Q := by
        rcases (show T = T1 ∨ T = T2 by simpa using hT) with rfl | rfl
        · exact uniq T hT1f hT13 ht1 hQn1 Q' ⟨hQ'.1, hQ'T, hQ'.2.2.1, hQ'.2.2.2⟩
        · exact uniq T hT2f hT23 ht2 hQn2 Q' ⟨hQ'.1, hQ'T, hQ'.2.2.1, hQ'.2.2.2⟩
      have hQG : Q ⊆ G := hQ'eq ▸ hQ'.2.1
      have hsub : ({G, T1, T2} : Set (Set E5)) ⊆
          {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by
        intro T' hT'
        rcases (show T' = G ∨ T' = T1 ∨ T' = T2 by simpa using hT') with rfl | rfl | rfl
        · exact ⟨hG, hQG, hGF, hG3⟩
        · exact ⟨hT1f, hQT1, hT1F, hT13⟩
        · exact ⟨hT2f, hQT2, hT2F, hT23⟩
      have h3 : ({G, T1, T2} : Set (Set E5)).ncard = 3 :=
        Set.ncard_eq_three.2 ⟨G, T1, T2, hG1', hG2', h12, rfl⟩
      have hle3 := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T hT => hT.1)
      rw [h3, htwo] at hle3
      norm_num at hle3
    -- two prisms, and a pyramid other than `T1, T2`
    obtain ⟨G1, G2, hG12, ⟨hG1, hG1F, hG13, hg1⟩, ⟨hG2, hG2F, hG23, hg2⟩⟩ :=
      hP.exists_two_of_tcnt (F := F) (t := (6, 9, 5)) (by omega)
    have hpyr : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 8, 5)}.ncard = 4 := c2
    obtain ⟨Y, ⟨hY, hYF, hY3, hyt⟩, hYX⟩ :
        ∃ Y ∈ {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 8, 5)},
          Y ∉ ({T1, T2} : Set (Set E5)) := by
      by_contra hall
      push Not at hall
      have hsub : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = (5, 8, 5)} ⊆
          ({T1, T2} : Set (Set E5)) := fun T hT => hall T hT
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair h12, hpyr] at this
      omega
    have notX : ∀ G, tri3 P G = (6, 9, 5) → G ∉ ({T1, T2} : Set (Set E5)) := by
      intro G hgG hG
      rcases (show G = T1 ∨ G = T2 by simpa using hG) with rfl | rfl
      · rw [ht1] at hgG; simp at hgG
      · rw [ht2] at hgG; simp at hgG
    have hG1X := notX G1 hg1
    have hG2X := notX G2 hg2
    have hsubX : ({T1, T2} : Set (Set E5)) ⊆ nsimp P F := by
      intro T hT
      rcases (show T = T1 ∨ T = T2 by simpa using hT) with rfl | rfl
      · exact ⟨hT1f, hT1F, hT13, ⟨Q, hQn1⟩⟩
      · exact ⟨hT2f, hT2F, hT23, ⟨Q, hQn2⟩⟩
    have hle : (nsimp P F \ ({T1, T2} : Set (Set E5))).ncard ≤ 4 := by
      rw [Set.ncard_sdiff hsubX, Set.ncard_pair h12]
      omega
    exact hP.not_two_prism_pyr_excl hF h4 hG1 hG1F hG13 hg1 hG2 hG2F hG23 hg2 hG12 hY hYF hY3
      hyt {T1, T2} (Set.toFinite _) hG1X hG2X hYX
      (hX G1 hG1 hG1F hG13 (fun h => hG1X (h ▸ by simp)) (fun h => hG1X (h ▸ by simp)))
      (hX G2 hG2 hG2F hG23 (fun h => hG2X (h ▸ by simp)) (fun h => hG2X (h ▸ by simp))) hle
  -- every quadrilateral counts `+1`
  have hq55 : q55w P F = q4 P F := by
    rw [hP.q55w_eq F, hP.q4_eq_card, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    by_cases h4Q : cnt P Q 0 = 4
    · rw [if_pos h4Q, if_neg (hno55 Q hQ h4Q), if_pos h4Q]
    · rw [if_neg h4Q, if_neg h4Q]
  rw [hq55]
  omega

end cs

end Kalai5
