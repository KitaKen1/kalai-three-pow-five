import Kalai5.Endpoints.Fake8

/-!
# Eight-vertex facets: the counting and the excluded rows

The 3-faces of a facet `F` with eight vertices have at most seven vertices, so their face numbers lie
in `fv8`; counting them by type gives three linear equations in the twelve counts
(`IsCSPolytope5.facet8_counts`: the number of 3-faces, their vertices `J`, and their 2-faces `2p`)
and the number of 3-faces with a non-triangular 2-face.  Together with the local facts (P1)–(P3) of
`Kalai5.Endpoints.Fake8`, `omega` excludes each row of `fake8`.
-/

namespace Kalai5

open Set

open scoped Classical

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.tcnt_eq_card (F : Set E5) (t : ℕ × ℕ × ℕ) :
    tcnt P F t = ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t).card := by
  rw [← Set.ncard_coe_finset]
  unfold tcnt
  congr 1
  ext T
  simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  tauto

/-- The face numbers of a 3-face with at most seven vertices lie in `fv8`. -/
lemma IsCSPolytope5.tri3_mem_fv8 {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (h7 : cnt P T 0 ≤ 7) : tri3 P T ∈ fv8 := by
  have he := hP.threeface_identity hT h3
  have hv := (hP.threeface_vertex_sums hT h3).2
  rw [hP.incid_zero_one] at hv
  have hx := hP.exc_threeface hT h3
  have hx0 : 0 ≤ exc P T := by
    have := hP.q4_add_big_le_exc T
    have h1 : (0 : ℤ) ≤ q4 P T := by positivity
    have h2 : (0 : ℤ) ≤ big2 P T := by positivity
    linarith
  have hb : cnt P T 1 = cnt P T 0 + cnt P T 2 - 2 := by omega
  have h4 : 4 ≤ cnt P T 0 := by omega
  have hc1 : cnt P T 2 + 4 ≤ 2 * cnt P T 0 := by omega
  have hc2 : cnt P T 0 + 4 ≤ 2 * cnt P T 2 := by omega
  have hcu : cnt P T 2 ≤ 10 := by omega
  unfold tri3
  rw [hb]
  generalize cnt P T 0 = a at *
  generalize cnt P T 2 = c at *
  interval_cases a <;> interval_cases c <;> first | omega | decide

/-- **Counting the 3-faces of an eight-vertex facet** by their face numbers. -/
lemma IsCSPolytope5.facet8_counts {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (h8 : cnt P F 0 = 8) :
    (fv8.map fun t => (tcnt P F t : ℤ)).sum = cnt P F 3 ∧
    (fv8.map fun t => (tcnt P F t : ℤ) * t.1).sum = incid P F 0 3 ∧
    (fv8.map fun t => (tcnt P F t : ℤ) * t.2.2).sum = 2 * cnt P F 2 ∧
    (fv8.map fun t => (tcnt P F t : ℤ) * if 3 * t.2.2 < 2 * t.2.1 then 1 else 0).sum =
      (nsimp P F).ncard := by
  have hall : ∀ T ∈ (hP.below_finite F 3).toFinset, tri3 P T ∈ fv8 := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    have hne : T ≠ F := by
      rintro rfl
      rw [hT.2.2] at h4
      exact absurd h4 (by norm_num)
    have hlt := hP.cnt_zero_lt hT.1 hF hT.2.1 hne
    exact hP.tri3_mem_fv8 hT.1 hT.2.2 (by omega)
  have key : ∀ g : ℕ × ℕ × ℕ → ℤ, ∑ T ∈ (hP.below_finite F 3).toFinset, g (tri3 P T) =
      (fv8.map fun t => (tcnt P F t : ℤ) * g t).sum := by
    intro g
    rw [sum_of_cover _ (tri3 P) fv8_nodup hall g]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    rw [hP.tcnt_eq_card]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := key fun _ => 1
    simp only [mul_one] at h
    rw [← h, Finset.sum_const, nsmul_eq_mul, mul_one, cnt,
      Set.ncard_eq_toFinset_card _ (hP.below_finite F 3)]
  · have h := key fun t => (t.1 : ℤ)
    rw [← h, hP.incid_eq_sum_second F 0 3]
    push_cast
    rfl
  · have h := key fun t => (t.2.2 : ℤ)
    rw [← h]
    have h2 : incid P F 2 3 = 2 * cnt P F 2 := by
      rw [hP.incid_eq_sum_first F 2 3]
      have htwo : ∀ Q ∈ (hP.below_finite F 2).toFinset,
          {H | H ∈ faces P ∧ Q ⊆ H ∧ H ⊆ F ∧ dim H = 3}.ncard = 2 := by
        intro Q hQ
        rw [Set.Finite.mem_toFinset] at hQ
        exact hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2
      rw [Finset.sum_congr rfl htwo, Finset.sum_const, smul_eq_mul, cnt,
        Set.ncard_eq_toFinset_card _ (hP.below_finite F 2)]
      ring
    have h3 := hP.incid_eq_sum_second F 2 3
    rw [h2] at h3
    show ∑ T ∈ (hP.below_finite F 3).toFinset, ((cnt P T 2 : ℕ) : ℤ) = _
    exact_mod_cast h3.symm
  · have h := key fun t => if 3 * t.2.2 < 2 * t.2.1 then (1 : ℤ) else 0
    have hset : ((hP.below_finite F 3).toFinset.filter fun T =>
        3 * (tri3 P T).2.2 < 2 * (tri3 P T).2.1) = (hP.nsimp_finite F).toFinset := by
      ext T
      rw [Finset.mem_filter, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      constructor
      · rintro ⟨⟨hT, hTF, hT3⟩, hlt⟩
        exact ⟨hT, hTF, hT3, (hP.ntri_nonempty_iff hT hT3).2 hlt⟩
      · rintro ⟨hT, hTF, hT3, hne⟩
        exact ⟨⟨hT, hTF, hT3⟩, (hP.ntri_nonempty_iff hT hT3).1 hne⟩
    rw [← h, Finset.sum_boole, hset, ← Set.ncard_eq_toFinset_card _ (hP.nsimp_finite F)]

lemma IsCSPolytope5.exists_of_tcnt {F : Set E5} {t : ℕ × ℕ × ℕ} (h : 1 ≤ tcnt P F t) :
    ∃ T, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = t := by
  have : ({T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = t}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by unfold tcnt at h; omega)
  obtain ⟨T, hT⟩ := this
  exact ⟨T, hT⟩

lemma IsCSPolytope5.exists_two_of_tcnt {F : Set E5} {t : ℕ × ℕ × ℕ} (h : 2 ≤ tcnt P F t) :
    ∃ T₁ T₂, T₁ ≠ T₂ ∧ (T₁ ∈ faces P ∧ T₁ ⊆ F ∧ dim T₁ = 3 ∧ tri3 P T₁ = t) ∧
      (T₂ ∈ faces P ∧ T₂ ⊆ F ∧ dim T₂ = 3 ∧ tri3 P T₂ = t) := by
  have hfin : {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = t}.Finite :=
    hP.faces_finite.subset fun T hT => hT.1
  obtain ⟨T₁, h₁, T₂, h₂, hne⟩ := (Set.one_lt_ncard hfin).1 (by unfold tcnt at h; omega)
  exact ⟨T₁, T₂, hne, h₁, h₂⟩

/-- The twelve counts of an eight-vertex facet, written out. -/
lemma IsCSPolytope5.facet8_arith {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (h8 : cnt P F 0 = 8) :
    tcnt P F (4, 6, 4) + tcnt P F (5, 8, 5) + tcnt P F (5, 9, 6) + tcnt P F (6, 9, 5) +
        tcnt P F (6, 10, 6) + tcnt P F (6, 11, 7) + tcnt P F (6, 12, 8) + tcnt P F (7, 11, 6) +
        tcnt P F (7, 12, 7) + tcnt P F (7, 13, 8) + tcnt P F (7, 14, 9) + tcnt P F (7, 15, 10) =
      cnt P F 3 ∧
    4 * tcnt P F (4, 6, 4) + 5 * tcnt P F (5, 8, 5) + 5 * tcnt P F (5, 9, 6) +
        6 * tcnt P F (6, 9, 5) + 6 * tcnt P F (6, 10, 6) + 6 * tcnt P F (6, 11, 7) +
        6 * tcnt P F (6, 12, 8) + 7 * tcnt P F (7, 11, 6) + 7 * tcnt P F (7, 12, 7) +
        7 * tcnt P F (7, 13, 8) + 7 * tcnt P F (7, 14, 9) + 7 * tcnt P F (7, 15, 10) =
      incid P F 0 3 ∧
    4 * tcnt P F (4, 6, 4) + 5 * tcnt P F (5, 8, 5) + 6 * tcnt P F (5, 9, 6) +
        5 * tcnt P F (6, 9, 5) + 6 * tcnt P F (6, 10, 6) + 7 * tcnt P F (6, 11, 7) +
        8 * tcnt P F (6, 12, 8) + 6 * tcnt P F (7, 11, 6) + 7 * tcnt P F (7, 12, 7) +
        8 * tcnt P F (7, 13, 8) + 9 * tcnt P F (7, 14, 9) + 10 * tcnt P F (7, 15, 10) =
      2 * cnt P F 2 ∧
    tcnt P F (5, 8, 5) + tcnt P F (6, 9, 5) + tcnt P F (6, 10, 6) + tcnt P F (6, 11, 7) +
        tcnt P F (7, 11, 6) + tcnt P F (7, 12, 7) + tcnt P F (7, 13, 8) + tcnt P F (7, 14, 9) =
      (nsimp P F).ncard := by
  obtain ⟨e1, e2, e3, e4⟩ := hP.facet8_counts hF h4 h8
  simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at e1 e2 e3 e4
  norm_num at e1 e2 e3 e4
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The local facts (P1)–(P3) as arithmetic. -/
lemma IsCSPolytope5.facet8_local {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    (1 ≤ tcnt P F (6, 9, 5) → 4 ≤ (nsimp P F).ncard) ∧
    (1 ≤ tcnt P F (7, 11, 6) → 3 ≤ (nsimp P F).ncard) ∧
    (2 ≤ tcnt P F (6, 9, 5) → 1 ≤ tcnt P F (5, 8, 5) → 5 ≤ (nsimp P F).ncard) := by
  refine ⟨fun h => ?_, fun h => ?_, ?_⟩
  · obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt h
    exact hP.four_le_nsimp_of_prism hF h4 hT hTF hT3 ht
  · obtain ⟨T, hT, hTF, hT3, ht⟩ := hP.exists_of_tcnt h
    exact hP.three_le_nsimp_of_7116 hF h4 hT hTF hT3 ht
  · intro h2 h1
    by_contra hlt
    have hle : (nsimp P F).ncard ≤ 4 := by omega
    obtain ⟨G1, G2, h12, ⟨hG1, hG1F, hG13, ht1⟩, ⟨hG2, hG2F, hG23, ht2⟩⟩ :=
      hP.exists_two_of_tcnt h2
    obtain ⟨Y, hY, hYF, hY3, htY⟩ := hP.exists_of_tcnt h1
    exact hP.not_two_prism_pyr hF h4 hG1 hG1F hG13 ht1 hG2 hG2F hG23 ht2 h12 hY hYF hY3 htY hle

set_option maxHeartbeats 4000000 in
/-- **No facet has a row in `fake8`.** -/
theorem IsCSPolytope5.facet_not_fake8 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F ∈ fake8) : False := by
  simp only [fake8, List.mem_cons, List.mem_nil_iff, or_false] at hR
  have hn : cnt P F 0 = 8 := by
    rcases hR with h | h | h | h | h | h <;>
      (simp only [faceRow, Row.mk.injEq] at h; exact h.1)
  obtain ⟨e1, e2, e3, e4⟩ := hP.facet8_arith hF h4 hn
  obtain ⟨ipr, i7, iP2⟩ := hP.facet8_local hF h4
  rcases hR with h | h | h | h | h | h <;>
    (simp only [faceRow, Row.mk.injEq] at h
     obtain ⟨-, -, hp, hr, hJ⟩ := h
     omega)

/-- **No facet row of `P` is in `fake8`.** -/
theorem IsCSPolytope5.facetRows_not_fake8 : ∀ R ∈ facetRows P, R ∉ fake8 := by
  intro R hR hmem
  obtain ⟨F, hF, h4, rfl⟩ := hP.mem_facetRows hR
  exact hP.facet_not_fake8 hF h4 hmem

/-- Each 3-face has at least four vertices: `4 r ≤ J` for the facet rows. -/
theorem IsCSPolytope5.facetRows_four_r_le : ∀ R ∈ facetRows P, 4 * R.r ≤ R.J := by
  intro R hR
  obtain ⟨F, hF, h4, rfl⟩ := hP.mem_facetRows hR
  simp only [faceRow]
  rw [hP.incid_eq_sum_second F 0 3, cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F 3),
    mul_comm, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun T hT => ?_
  rw [Set.Finite.mem_toFinset] at hT
  exact hP.four_le_cnt_three hT.1 hT.2.2

end cs

end Kalai5
