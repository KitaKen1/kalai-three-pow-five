import Kalai5.LemmaB.Blocks

/-!
# Lemma B: the count, type by type

With the classes sorted by size, the fibre sizes are `(5,1,1)`, `(4,2,1)`, `(3,3,1)` or `(3,2,2)`.
In each case a list of label blocks is counted (`sum_card_pats_add_one_le`):

| type | octahedral blocks | equatorial blocks | total `≥` |
|---|---|---|---|
| (5,1,1) | 18 labels `≥ 11` (pentagon) | 9 labels `≥ 5` (exposing directions) | 243 |
| (4,2,1) | `12·11 + 6·9 + 6·3` (rank 3: `x ≥ 5`) | `6·6 + 3·2` (zero-width direction) | 246 |
| (3,3,1) | `12(|N₁∪N₂| + |N₁∪-N₂|) + 98` | `18 c` (common normals, rank 3) | `242 + 6c` |
| (3,2,2) ∥ | 214 (rank 3: no edge of `T` parallel) | 42 (zero-width direction) | 250 |
| (3,2,2) ∦ | 246 if `w_T(α) = w_3(α)` (rank 3), else 222 | else 42 | 246 |
-/

namespace Kalai5.LemmaB

open Set Module Kalai5.LemmaA
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Config

variable {x : Fin 7 → E5} (C : Config x)

lemma not_both_pnrm {l : ELab} (hl : l = lP ∨ l = lN) {N : Finset (E 2)} {a : E 2}
    (h : ¬(a ∈ N ∧ -a ∈ N)) : ¬(a ∈ pnrm l N ∧ -a ∈ pnrm l N) := by
  rcases hl with rfl | rfl
  · exact h
  · rw [pnrm_neg, Finset.mem_neg', Finset.mem_neg', neg_neg]
    exact fun h' => h ⟨h'.2, h'.1⟩

lemma not_both_of_anti {X : Finset (E 2)} (h : ∀ n ∈ X, -n ∉ X) (a : E 2) :
    ¬(a ∈ X ∧ -a ∈ X) := fun h' => h a h'.1 h'.2

lemma pair_normals {j : Fin 3} {a : E 2} (h1 : IsEdgeNormal (C.K j) a)
    (h2 : IsEdgeNormal (C.K j) (-a)) : ∀ n ∈ ({a, -a} : Finset (E 2)), IsEdgeNormal (C.K j) n := by
  intro n hn
  rw [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl
  · exact h1
  · exact h2

/-- Normals of a sign-labelled segment class, as normals of `M_S`. -/
lemma pair_normals_msum {S : Fin 3 → ELab} {j : Fin 3} (hSj : S j = lP ∨ S j = lN) {a : E 2}
    (h1 : IsEdgeNormal (C.K j) a) (h2 : IsEdgeNormal (C.K j) (-a)) :
    ∀ n ∈ ({a, -a} : Finset (E 2)), IsEdgeNormal (C.msum S) n := by
  intro n hn
  rw [← pnrm_pair hSj a] at hn
  exact C.normals_msum (C.pair_normals h1 h2) n hn

/-! ### (5,1,1) -/

theorem count_511 (h0 : (C.cls 0).card = 5) (h1 : (C.cls 1).card = 1)
    (h2 : (C.cls 2).card = 1) : 243 ≤ (faces (convexHull ℝ (range (pm x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  have hsum := C.sum_card_pats_add_one_le (blkU [(sg, o3, o3), ({lB}, o3, o3)])
    (fun S hS => ne_none_of_mem_blkU (by decide) hS)
  rw [sum_blkU [(sg, o3, o3), ({lB}, o3, o3)] (by decide)] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have b1 : ∀ S ∈ Blk.set (sg, o3, o3), 11 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_o3 lB_not_mem_o3
    have hS0 : S 0 = lP ∨ S 0 = lN := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have b2 : ∀ S ∈ Blk.set ({lB}, o3, o3), 5 ≤ (C.pats S).card := by
    intro S hS
    have hS' := onlyB0 hS rfl lB_not_mem_o3 lB_not_mem_o3
    have := C.card_cls_le_pats hS' (fin3_cases (fun h => absurd rfl h)
      (fun _ b => C.wd_eq_zero_of_card_one h1 b) (fun _ b => C.wd_eq_zero_of_card_one h2 b))
      (by omega)
    omega
  have e1 := sum_set_ge b1
  have e2 := sum_set_ge b2
  simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2
  omega

/-! ### (4,2,1) -/

theorem count_421 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 4) (h1 : (C.cls 1).card = 2)
    (h2 : (C.cls 2).card = 1) : 243 ≤ (faces (convexHull ℝ (range (pm x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  obtain ⟨vp, vq, α, hvp, hvq, hne, hcls, hα1, hα⟩ := C.exists_segment h1
  obtain ⟨hn1, hn1', hw1⟩ := C.segment_normal hvp hvq hne hcls hα1 hα
  have hα0 : α ≠ 0 := hn1.ne_zero
  have hW : 0 < C.wd 0 α := C.wd_pos_of_three_le (by omega) hα0
  have hw2 : ∀ b, C.wd 2 b = 0 := C.wd_eq_zero_of_card_one h2
  -- rank three: the quadrilateral has no pair of edges parallel to the segment
  have hrank : ¬(α ∈ N0 ∧ -α ∈ N0) := by
    rintro ⟨ha, hna⟩
    exact hX (C.extraPM_of_classes hα0 hW (fin3_cases
      (Or.inr ⟨rfl, C.two_level_quad h0 (hN0 α ha) (hN0 _ hna)⟩) (Or.inl hw1) (Or.inl (hw2 α))))
  have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
    fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hW)
      (fun _ => by rw [hw2]; exact hW)
  have hsum := C.sum_card_pats_add_one_le
    (blkU [(sg, sg, o3), (sg, {lO}, o3), ({lO}, sg, o3), ({lB}, sg, o3), ({lB}, {lO}, o3)])
    (fun S hS => ne_none_of_mem_blkU (by decide) hS)
  rw [sum_blkU [(sg, sg, o3), (sg, {lO}, o3), ({lO}, sg, o3), ({lB}, sg, o3), ({lB}, {lO}, o3)]
    (by decide)] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have b1 : ∀ S ∈ Blk.set (sg, sg, o3), 11 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_o3
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    have hS0 := mem_sg.1 hs0
    have hS1 := mem_sg.1 hs1
    have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n hn
      · exact C.pair_normals_msum hS1 hn1 hn1' n hn
    have hc := card_union_pair_ge (not_both_pnrm hS0 hrank)
    have hc' := card_pnrm hS0 N0
    have := C.oct_bound hS' hN (by omega)
    omega
  have b2 : ∀ S ∈ Blk.set (sg, {lO}, o3), 9 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_o3
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have b3 : ∀ S ∈ Blk.set ({lO}, sg, o3), 3 ≤ (C.pats S).card := by
    intro S hS
    exact C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_o3)
      (mem_sg.1 (Blk.mem_set.1 hS).2.1) (by omega)
  have b4 : ∀ S ∈ Blk.set ({lB}, sg, o3), 6 ≤ (C.pats S).card := by
    intro S hS
    exact C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_sg lB_not_mem_o3)
      (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
  have b5 : ∀ S ∈ Blk.set ({lB}, {lO}, o3), 2 ≤ (C.pats S).card := by
    intro S hS
    exact C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_o3) hJ
  have e1 := sum_set_ge b1
  have e2 := sum_set_ge b2
  have e3 := sum_set_ge b3
  have e4 := sum_set_ge b4
  have e5 := sum_set_ge b5
  simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5
  omega

/-! ### (3,3,1) -/

theorem count_331 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 3) (h1 : (C.cls 1).card = 3)
    (h2 : (C.cls 2).card = 1) : 243 ≤ (faces (convexHull ℝ (range (pm x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  obtain ⟨N1, hN1, hc1⟩ := C.exists_normals_K (j := 1) (by omega)
  have hd0 := C.dim_K_eq_two (j := 0) (by omega)
  have hd1 := C.dim_K_eq_two (j := 1) (by omega)
  have hK0 : (C.K 0).card = 3 := by rw [C.card_K, h0]
  have hK1 : (C.K 1).card = 3 := by rw [C.card_K, h1]
  have hanti0 : ∀ n ∈ N0, -n ∉ N0 := fun n hn hn' =>
    not_edgeNormal_neg hK0 hd0 (hN0 n hn) (hN0 _ hn')
  have hanti1 : ∀ n ∈ N1, -n ∉ N1 := fun n hn hn' =>
    not_edgeNormal_neg hK1 hd1 (hN1 n hn) (hN1 _ hn')
  have hw2 : ∀ b, C.wd 2 b = 0 := C.wd_eq_zero_of_card_one h2
  -- common normal lines, with both orientations
  set Cm : Finset (E 2) := N0 ∩ (N1 ∪ -N1) with hCm
  set D : Finset (E 2) := Cm ∪ -Cm with hD
  have hDn0 : ∀ b ∈ D, IsEdgeNormal (C.K 0) b ∨ IsEdgeNormal (C.K 0) (-b) := by
    intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · exact Or.inl (hN0 b (Finset.mem_inter.1 hb).1)
    · exact Or.inr (hN0 _ (Finset.mem_inter.1 (Finset.mem_neg'.1 hb)).1)
  have hDn1 : ∀ b ∈ D, IsEdgeNormal (C.K 1) b ∨ IsEdgeNormal (C.K 1) (-b) := by
    intro b hb
    rcases Finset.mem_union.1 hb with hb | hb
    · rcases Finset.mem_union.1 (Finset.mem_inter.1 hb).2 with h | h
      · exact Or.inl (hN1 b h)
      · exact Or.inr (hN1 _ (Finset.mem_neg'.1 h))
    · rcases Finset.mem_union.1 (Finset.mem_inter.1 (Finset.mem_neg'.1 hb)).2 with h | h
      · exact Or.inr (hN1 _ h)
      · have := hN1 _ (Finset.mem_neg'.1 h)
        rw [neg_neg] at this
        exact Or.inl this
  have hD0 : ∀ b ∈ D, b ≠ 0 := by
    intro b hb
    rcases hDn0 b hb with h | h
    · exact h.ne_zero
    · exact fun h0 => h.ne_zero (by rw [h0, neg_zero])
  -- rank three: at a common normal the two triangles have different widths
  have hrank : ∀ b ∈ D, C.wd 0 b ≠ C.wd 1 b := by
    intro b hb heq
    have hb0 := hD0 b hb
    apply hX
    refine C.extraPM_of_classes hb0 (C.wd_pos_of_three_le (j := 0) (by omega) hb0)
      (fin3_cases ?_ ?_ ?_)
    · exact Or.inr ⟨rfl, C.two_level_tri h0 (hDn0 b hb)⟩
    · exact Or.inr ⟨heq.symm, C.two_level_tri h1 (hDn1 b hb)⟩
    · exact Or.inl (hw2 b)
  set D0 := D.filter fun b => C.wd 1 b < C.wd 0 b with hD0def
  set D1 := D.filter fun b => ¬ (C.wd 1 b < C.wd 0 b) with hD1def
  have hD01 : D0.card + D1.card = D.card := Finset.card_filter_add_card_filter_not _
  have hDc : D.card = 2 * Cm.card := by
    have hdisj : Disjoint Cm (-Cm) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      rw [Finset.mem_neg'] at hn'
      exact hanti0 n (Finset.mem_inter.1 hn).1 (Finset.mem_inter.1 hn').1
    rw [hD, Finset.card_union_of_disjoint hdisj, Finset.card_neg]; ring
  have hCc : Cm.card = (N0 ∩ N1).card + (N0 ∩ -N1).card := by
    have hdisj : Disjoint (N0 ∩ N1) (N0 ∩ -N1) := by
      rw [Finset.disjoint_left]
      intro n hn hn'
      exact hanti1 n (Finset.mem_inter.1 hn).2 (Finset.mem_neg'.1 (Finset.mem_inter.1 hn').2)
    rw [hCm, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint hdisj]
  have hJ0 : ∀ b ∈ D0, ∀ i, i ≠ 0 → C.wd i b < C.wd 0 b := by
    intro b hb
    rw [Finset.mem_filter] at hb
    exact fin3_cases (fun h => absurd rfl h) (fun _ => hb.2)
      (fun _ => by rw [hw2]; exact C.wd_pos_of_three_le (by omega) (hD0 b hb.1))
  have hJ1 : ∀ b ∈ D1, ∀ i, i ≠ 1 → C.wd i b < C.wd 1 b := by
    intro b hb
    rw [Finset.mem_filter] at hb
    exact fin3_cases (fun _ => lt_of_le_of_ne (not_lt.1 hb.2) (hrank b hb.1))
      (fun h => absurd rfl h)
      (fun _ => by rw [hw2]; exact C.wd_pos_of_three_le (by omega) (hD0 b hb.1))
  have hinj0 : ∀ b ∈ D0, ∀ b' ∈ D0, amax (C.K 0) b = amax (C.K 0) b' → b = b' :=
    fun b hb b' hb' h => eq_of_amax_eq_triangle hK0 hd0 (hDn0 b (Finset.mem_filter.1 hb).1)
      (hDn0 b' (Finset.mem_filter.1 hb').1) h
  have hinj1 : ∀ b ∈ D1, ∀ b' ∈ D1, amax (C.K 1) b = amax (C.K 1) b' → b = b' :=
    fun b hb b' hb' h => eq_of_amax_eq_triangle hK1 hd1 (hDn1 b (Finset.mem_filter.1 hb).1)
      (hDn1 b' (Finset.mem_filter.1 hb').1) h
  have hsum := C.sum_card_pats_add_one_le
    (blkU [({lP}, {lP}, o3), ({lN}, {lN}, o3), ({lP}, {lN}, o3), ({lN}, {lP}, o3),
      (sg, {lO}, o3), ({lO}, sg, o3), ({lO}, {lO}, sg), ({lB}, o3, o3), (o3, {lB}, o3)])
    (fun S hS => ne_none_of_mem_blkU (by decide) hS)
  rw [sum_blkU [({lP}, {lP}, o3), ({lN}, {lN}, o3), ({lP}, {lN}, o3), ({lN}, {lP}, o3),
      (sg, {lO}, o3), ({lO}, sg, o3), ({lO}, {lO}, sg), ({lB}, o3, o3), (o3, {lB}, o3)]
    (by decide)] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have bPP : ∀ S ∈ Blk.set ({lP}, {lP}, o3), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card := by
    intro S hS
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ N0 ∪ N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    exact C.oct_bound hS' hN
      (le_trans (by omega) (Finset.card_le_card Finset.subset_union_left))
  have bNN : ∀ S ∈ Blk.set ({lN}, {lN}, o3), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card := by
    intro S hS
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ -N0 ∪ -N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    have hc : (-N0 ∪ -N1).card = (N0 ∪ N1).card := by rw [neg_union', Finset.card_neg]
    rw [← hc]
    exact C.oct_bound hS' hN
      (by rw [hc]; exact le_trans (by omega) (Finset.card_le_card Finset.subset_union_left))
  have bPN : ∀ S ∈ Blk.set ({lP}, {lN}, o3), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card := by
    intro S hS
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ N0 ∪ -N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    exact C.oct_bound hS' hN
      (le_trans (by omega) (Finset.card_le_card Finset.subset_union_left))
  have bNP : ∀ S ∈ Blk.set ({lN}, {lP}, o3), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card := by
    intro S hS
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ -N0 ∪ N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    have hc : (-N0 ∪ N1).card = (N0 ∪ -N1).card := by
      rw [show (-N0 ∪ N1 : Finset (E 2)) = -N0 ∪ -(-N1) by rw [neg_neg], neg_union',
        Finset.card_neg]
    rw [← hc]
    exact C.oct_bound hS' hN
      (by rw [hc]; exact le_trans (by omega) (Finset.card_le_card Finset.subset_union_left))
  have b2 : ∀ S ∈ Blk.set (sg, {lO}, o3), 7 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_o3
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have b3 : ∀ S ∈ Blk.set ({lO}, sg, o3), 7 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_o3
    have hS1 := mem_sg.1 (Blk.mem_set.1 hS).2.1
    have hc := card_pnrm hS1 N1
    have := C.oct_bound hS' (C.normals_msum (j := 1) hN1) (by omega)
    omega
  have b4 : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 1 ≤ (C.pats S).card := fun S hS =>
    C.one_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
  have bE0 : ∀ S ∈ Blk.set ({lB}, o3, o3), D0.card ≤ (C.pats S).card := fun S hS =>
    C.card_le_pats_of_dirs (onlyB0 hS rfl lB_not_mem_o3 lB_not_mem_o3) D0 hJ0 hinj0
  have bE1 : ∀ S ∈ Blk.set (o3, {lB}, o3), D1.card ≤ (C.pats S).card := fun S hS =>
    C.card_le_pats_of_dirs (onlyB1 hS lB_not_mem_o3 rfl lB_not_mem_o3) D1 hJ1 hinj1
  have e1 := sum_set_ge bPP
  have e2 := sum_set_ge bNN
  have e3 := sum_set_ge bPN
  have e4 := sum_set_ge bNP
  have e5 := sum_set_ge b2
  have e6 := sum_set_ge b3
  have e7 := sum_set_ge b4
  have e8 := sum_set_ge bE0
  have e9 := sum_set_ge bE1
  simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  have u1 := Finset.card_union_add_card_inter N0 N1
  have u2 := Finset.card_union_add_card_inter N0 (-N1)
  rw [Finset.card_neg] at u2
  omega

/-! ### (3,2,2) -/

theorem count_322 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 3) (h1 : (C.cls 1).card = 2)
    (h2 : (C.cls 2).card = 2) : 243 ≤ (faces (convexHull ℝ (range (pm x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  have hd0 := C.dim_K_eq_two (j := 0) (by omega)
  have hK0 : (C.K 0).card = 3 := by rw [C.card_K, h0]
  have hanti0 : ∀ n ∈ N0, -n ∉ N0 := fun n hn hn' =>
    not_edgeNormal_neg hK0 hd0 (hN0 n hn) (hN0 _ hn')
  obtain ⟨vp, vq, α, hvp, hvq, hne, hcls, hα1, hα⟩ := C.exists_segment h1
  obtain ⟨hn1, hn1', hw1⟩ := C.segment_normal hvp hvq hne hcls hα1 hα
  obtain ⟨wp, wq, γ, hwp, hwq, hne', hcls', hγ1, hγ⟩ := C.exists_segment h2
  obtain ⟨hn2, hn2', -⟩ := C.segment_normal hwp hwq hne' hcls' hγ1 hγ
  have hα0 : α ≠ 0 := hn1.ne_zero
  have hγ0 : γ ≠ 0 := hn2.ne_zero
  have hW : 0 < C.wd 0 α := C.wd_pos_of_three_le (by omega) hα0
  -- blocks common to all cases
  have bD : ∀ S ∈ Blk.set (sg, {lO}, {lO}), 7 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_lO
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have bF1 : ∀ S ∈ Blk.set ({lO}, sg, {lO}), 3 ≤ (C.pats S).card := fun S hS =>
    C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_lO)
      (mem_sg.1 (Blk.mem_set.1 hS).2.1) (by omega)
  have bF2 : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 3 ≤ (C.pats S).card := fun S hS =>
    C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
      (mem_sg.1 (Blk.mem_set.1 hS).2.2) (by omega)
  have eD := sum_set_ge bD
  have eF1 := sum_set_ge bF1
  have eF2 := sum_set_ge bF2
  simp only [card_sg, card_o3, Finset.card_singleton] at eD eF1 eF2
  by_cases hpar : ⟪α, C.k wq⟫ = ⟪α, C.k wp⟫
  · /- parallel segments: `α` is a zero-width direction of both -/
    obtain ⟨hm2, hm2', hw2α⟩ := C.segment_normal hwp hwq hne' hcls' hα1 hpar
    have hrank : α ∉ N0 ∧ -α ∉ N0 := by
      have key : ¬(α ∈ N0 ∨ -α ∈ N0) := by
        intro h
        apply hX
        refine C.extraPM_of_classes hα0 hW (fin3_cases ?_ (Or.inl hw1) (Or.inl hw2α))
        refine Or.inr ⟨rfl, C.two_level_tri h0 ?_⟩
        rcases h with h | h
        · exact Or.inl (hN0 _ h)
        · exact Or.inr (hN0 _ h)
      exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
    have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
      fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hW)
        (fun _ => by rw [hw2α]; exact hW)
    have hsum := C.sum_card_pats_add_one_le
      (blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), (sg, {lO}, {lO}), ({lO}, sg, o3),
        ({lB}, sg, o3), ({lB}, {lO}, o3)])
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), (sg, {lO}, {lO}), ({lO}, sg, o3),
        ({lB}, sg, o3), ({lB}, {lO}, o3)] (by decide)] at hsum
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    -- `T + segment(s)`: the normals of `±T` and `±α`, `|N(T)| + 2 ≥ 5`
    have key : ∀ S : Fin 3 → ELab, (∀ j, S j ≠ some none) → (S 0 = lP ∨ S 0 = lN) →
        (∀ n ∈ ({α, -α} : Finset (E 2)), IsEdgeNormal (C.msum S) n) → 11 ≤ (C.pats S).card := by
      intro S hS' hS0 hαS
      have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
        intro n hn
        rcases Finset.mem_union.1 hn with hn | hn
        · exact C.normals_msum (j := 0) hN0 n hn
        · exact hαS n hn
      have hm := not_mem_pnrm hS0 hrank.1 hrank.2
      have hc := card_union_pair_ge2 hm.1 hm.2 hα0
      have hc' := card_pnrm hS0 N0
      have := C.oct_bound hS' hN (by omega)
      omega
    have bA : ∀ S ∈ Blk.set (sg, sg, sg), 11 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
      exact key S (noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_sg) (mem_sg.1 hs0)
        (C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1')
    have bB : ∀ S ∈ Blk.set (sg, sg, {lO}), 11 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
      exact key S (noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_lO) (mem_sg.1 hs0)
        (C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1')
    have bC : ∀ S ∈ Blk.set (sg, {lO}, sg), 11 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨hs0, -, hs2⟩ := Blk.mem_set.1 hS
      exact key S (noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg) (mem_sg.1 hs0)
        (C.pair_normals_msum (mem_sg.1 hs2) hm2 hm2')
    have bE : ∀ S ∈ Blk.set ({lO}, sg, o3), 3 ≤ (C.pats S).card := fun S hS =>
      C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_o3)
        (mem_sg.1 (Blk.mem_set.1 hS).2.1) (by omega)
    have b6 : ∀ S ∈ Blk.set ({lB}, sg, o3), 6 ≤ (C.pats S).card := fun S hS =>
      C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_sg lB_not_mem_o3)
        (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
    have b7 : ∀ S ∈ Blk.set ({lB}, {lO}, o3), 2 ≤ (C.pats S).card := fun S hS =>
      C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_o3) hJ
    have e1 := sum_set_ge bA
    have e2 := sum_set_ge bB
    have e3 := sum_set_ge bC
    have e4 := sum_set_ge bE
    have e5 := sum_set_ge b6
    have e6 := sum_set_ge b7
    simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6
    omega
  · /- non-parallel segments -/
    have hw2α : 0 < C.wd 2 α := C.wd_pos_of_ne hwq hwp hpar
    have hγα : γ ≠ α ∧ γ ≠ -α := by
      constructor
      · rintro rfl; exact hpar hγ
      · rintro rfl
        apply hpar
        rw [inner_neg_left, inner_neg_left] at hγ
        linarith
    have hanti : ∀ S : Fin 3 → ELab, (S 0 = lP ∨ S 0 = lN) →
        ∀ n ∈ pnrm (S 0) N0, -n ∉ pnrm (S 0) N0 := fun S hS0 => anti_pnrm hS0 hanti0
    have bD' : ∀ S ∈ Blk.set ({lO}, sg, sg), 9 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨-, hs1, hs2⟩ := Blk.mem_set.1 hS
      have hS' := noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_sg
      have hN : ∀ n ∈ ({α, -α} ∪ {γ, -γ} : Finset (E 2)), IsEdgeNormal (C.msum S) n := by
        intro n hn
        rcases Finset.mem_union.1 hn with hn | hn
        · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
        · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
      have hc := card_two_pairs hα0 hγ0 hγα.1 hγα.2
      have := C.oct_bound hS' hN (by omega)
      omega
    have eD' := sum_set_ge bD'
    simp only [card_sg, card_o3, Finset.card_singleton] at eD'
    by_cases hJ2 : C.wd 0 α = C.wd 2 α
    · -- equal widths at `α`: rank three excludes an edge of `T` parallel to the first segment
      have hrank : α ∉ N0 ∧ -α ∉ N0 := by
        have key : ¬(α ∈ N0 ∨ -α ∈ N0) := by
          intro h
          apply hX
          refine C.extraPM_of_classes hα0 hW (fin3_cases ?_ (Or.inl hw1)
            (Or.inr ⟨hJ2.symm, C.two_level_pair h2 α⟩))
          refine Or.inr ⟨rfl, C.two_level_tri h0 ?_⟩
          rcases h with h | h
          · exact Or.inl (hN0 _ h)
          · exact Or.inr (hN0 _ h)
        exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩
      have hsum := C.sum_card_pats_add_one_le
        (blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg), (sg, {lO}, {lO}),
          ({lO}, sg, {lO}), ({lO}, {lO}, sg)])
        (fun S hS => ne_none_of_mem_blkU (by decide) hS)
      rw [sum_blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg), (sg, {lO}, {lO}),
          ({lO}, sg, {lO}), ({lO}, {lO}, sg)] (by decide)] at hsum
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
      have bA : ∀ S ∈ Blk.set (sg, sg, sg), 13 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, hs1, hs2⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_sg
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α} ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · rcases Finset.mem_union.1 hn with hn | hn
            · exact C.normals_msum (j := 0) hN0 n hn
            · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
          · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
        have hm := not_mem_pnrm hS0 hrank.1 hrank.2
        have hc := card_union_two_pairs_ge3 hm.1 hm.2 hα0 (not_both_of_anti (hanti S hS0) γ)
          hγα.1 hγα.2
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have bB : ∀ S ∈ Blk.set (sg, sg, {lO}), 11 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_lO
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · exact C.normals_msum (j := 0) hN0 n hn
          · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
        have hm := not_mem_pnrm hS0 hrank.1 hrank.2
        have hc := card_union_pair_ge2 hm.1 hm.2 hα0
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have bC : ∀ S ∈ Blk.set (sg, {lO}, sg), 9 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, -, hs2⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · exact C.normals_msum (j := 0) hN0 n hn
          · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
        have hc := card_union_pair_ge (not_both_of_anti (hanti S hS0) γ)
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have e1 := sum_set_ge bA
      have e2 := sum_set_ge bB
      have e3 := sum_set_ge bC
      simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3
      omega
    · -- a unique widest class at `α`: the zero-width direction of the first segment
      have bA : ∀ S ∈ Blk.set (sg, sg, sg), 11 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, hs1, hs2⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_sg
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α} ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · rcases Finset.mem_union.1 hn with hn | hn
            · exact C.normals_msum (j := 0) hN0 n hn
            · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
          · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
        have hc := card_union_two_pairs_ge (not_both_of_anti (hanti S hS0) α)
          (not_both_of_anti (hanti S hS0) γ) hγα.1 hγα.2
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have bB : ∀ S ∈ Blk.set (sg, sg, {lO}), 9 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_lO
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · exact C.normals_msum (j := 0) hN0 n hn
          · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
        have hc := card_union_pair_ge (not_both_of_anti (hanti S hS0) α)
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have bC : ∀ S ∈ Blk.set (sg, {lO}, sg), 9 ≤ (C.pats S).card := by
        intro S hS
        obtain ⟨hs0, -, hs2⟩ := Blk.mem_set.1 hS
        have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg
        have hS0 := mem_sg.1 hs0
        have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
          intro n hn
          rcases Finset.mem_union.1 hn with hn | hn
          · exact C.normals_msum (j := 0) hN0 n hn
          · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
        have hc := card_union_pair_ge (not_both_of_anti (hanti S hS0) γ)
        have hc' := card_pnrm hS0 N0
        have := C.oct_bound hS' hN (by omega)
        omega
      have e1 := sum_set_ge bA
      have e2 := sum_set_ge bB
      have e3 := sum_set_ge bC
      simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3
      rcases lt_or_gt_of_ne hJ2 with hlt | hlt
      · -- the second segment is widest
        have hJ : ∀ i, i ≠ 2 → C.wd i α < C.wd 2 α :=
          fin3_cases (fun _ => hlt) (fun _ => by rw [hw1]; exact hw2α) (fun h => absurd rfl h)
        have hsum := C.sum_card_pats_add_one_le
          (blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg), (sg, {lO}, {lO}),
            ({lO}, sg, {lO}), ({lO}, {lO}, sg), (o3, sg, {lB}), (o3, {lO}, {lB})])
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg),
            (sg, {lO}, {lO}), ({lO}, sg, {lO}), ({lO}, {lO}, sg), (o3, sg, {lB}),
            (o3, {lO}, {lB})] (by decide)] at hsum
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have b8 : ∀ S ∈ Blk.set (o3, sg, {lB}), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB2 hS lB_not_mem_o3 lB_not_mem_sg rfl)
            (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
        have b9 : ∀ S ∈ Blk.set (o3, {lO}, {lB}), 2 ≤ (C.pats S).card := fun S hS =>
          C.two_le_card_pats (onlyB2 hS lB_not_mem_o3 lB_not_mem_lO rfl) hJ
        have e8 := sum_set_ge b8
        have e9 := sum_set_ge b9
        simp only [card_sg, card_o3, Finset.card_singleton] at e8 e9
        omega
      · -- the triangle is widest
        have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
          fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hW) (fun _ => hlt)
        have hsum := C.sum_card_pats_add_one_le
          (blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg), (sg, {lO}, {lO}),
            ({lO}, sg, {lO}), ({lO}, {lO}, sg), ({lB}, sg, o3), ({lB}, {lO}, o3)])
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), ({lO}, sg, sg),
            (sg, {lO}, {lO}), ({lO}, sg, {lO}), ({lO}, {lO}, sg), ({lB}, sg, o3),
            ({lB}, {lO}, o3)] (by decide)] at hsum
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have b8 : ∀ S ∈ Blk.set ({lB}, sg, o3), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_sg lB_not_mem_o3)
            (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
        have b9 : ∀ S ∈ Blk.set ({lB}, {lO}, o3), 2 ≤ (C.pats S).card := fun S hS =>
          C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_o3) hJ
        have e8 := sum_set_ge b8
        have e9 := sum_set_ge b9
        simp only [card_sg, card_o3, Finset.card_singleton] at e8 e9
        omega

end Config

end Kalai5.LemmaB
