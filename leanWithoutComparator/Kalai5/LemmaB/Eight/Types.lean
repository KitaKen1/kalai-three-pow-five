import Kalai5.LemmaB.Eight.Blocks

/-!
# Lemma B at sixteen vertices: the count, type by type

With the classes sorted by size, the fibre sizes are `(6,1,1)`, `(5,2,1)`, `(4,3,1)`, `(4,2,2)` or
`(3,3,2)`.  As for seven pairs (`Kalai5.LemmaB.Types`), a list of label blocks is counted
(`sum_card_pats_add_one_le`); with eight points the octahedral blocks are larger, and the
equatorial blocks are only needed in degenerate positions:

| type | octahedral | equatorial | total `≥` |
|---|---|---|---|
| (6,1,1) | 18 labels `≥ 13` (hexagon) + 8 | – | 243 |
| (5,2,1) | `12·11 + 6·11 + 6·3 + 2` | `6·6 + 3·2` (zero-width direction) | 261 |
| (4,3,1) | `12 (x + y) + 110`, `x + y ≥ 11` | – | 243 |
| (4,3,1), parallel pair | `x + y ≥ 10` | `9·2` (rank 3: unequal widths) | 249 |
| (4,2,2), (3,3,2) | see `count_422`, `count_332` | zero-width directions | `≥ 243` |
-/

namespace Kalai5.LemmaB.Eight

open Set Module Kalai5.LemmaA
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Config

variable {x : Fin 8 → E5} (C : Config x)

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

/-! ### (6,1,1) -/

theorem count_611 (h0 : (C.cls 0).card = 6) (h1 : (C.cls 1).card = 1)
    (h2 : (C.cls 2).card = 1) :
    243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  have hsum := C.sum_card_pats_add_one_le (blkU [(sg, o3, o3), ({lO}, sg, o3), ({lO}, {lO}, sg)])
    (fun S hS => ne_none_of_mem_blkU (by decide) hS)
  rw [sum_blkU [(sg, o3, o3), ({lO}, sg, o3), ({lO}, {lO}, sg)] (by decide)] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have b1 : ∀ S ∈ Blk.set (sg, o3, o3), 13 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_o3 lB_not_mem_o3
    have hS0 : S 0 = lP ∨ S 0 = lN := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have b2 : ∀ S ∈ Blk.set ({lO}, sg, o3), 1 ≤ (C.pats S).card := fun S hS =>
    C.one_le_pats (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_o3)
  have b3 : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 1 ≤ (C.pats S).card := fun S hS =>
    C.one_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
  have e1 := sum_set_ge b1
  have e2 := sum_set_ge b2
  have e3 := sum_set_ge b3
  simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3
  omega

/-! ### (5,2,1) -/

theorem count_521 (h0 : (C.cls 0).card = 5) (h1 : (C.cls 1).card = 2)
    (h2 : (C.cls 2).card = 1) :
    243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  obtain ⟨vp, vq, α, hvp, hvq, hne, hcls, hα1, hα⟩ := C.exists_segment h1
  obtain ⟨hn1, -, hw1⟩ := C.segment_normal hvp hvq hne hcls hα1 hα
  have hα0 : α ≠ 0 := hn1.ne_zero
  have hW : 0 < C.wd 0 α := C.wd_pos_of_three_le (by omega) hα0
  have hw2 : ∀ b, C.wd 2 b = 0 := C.wd_eq_zero_of_card_one h2
  have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
    fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hW)
      (fun _ => by rw [hw2]; exact hW)
  have hsum := C.sum_card_pats_add_one_le
    (blkU [(sg, sg, o3), (sg, {lO}, o3), ({lO}, sg, o3), ({lO}, {lO}, sg), ({lB}, sg, o3),
      ({lB}, {lO}, o3)])
    (fun S hS => ne_none_of_mem_blkU (by decide) hS)
  rw [sum_blkU [(sg, sg, o3), (sg, {lO}, o3), ({lO}, sg, o3), ({lO}, {lO}, sg), ({lB}, sg, o3),
      ({lB}, {lO}, o3)] (by decide)] at hsum
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
  have b1 : ∀ S ∈ Blk.set (sg, sg, o3), 11 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_o3
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have b2 : ∀ S ∈ Blk.set (sg, {lO}, o3), 11 ≤ (C.pats S).card := by
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
  have b4 : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 1 ≤ (C.pats S).card := fun S hS =>
    C.one_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
  have b5 : ∀ S ∈ Blk.set ({lB}, sg, o3), 6 ≤ (C.pats S).card := by
    intro S hS
    exact C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_sg lB_not_mem_o3)
      (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
  have b6 : ∀ S ∈ Blk.set ({lB}, {lO}, o3), 2 ≤ (C.pats S).card := by
    intro S hS
    exact C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_o3) hJ
  have e1 := sum_set_ge b1
  have e2 := sum_set_ge b2
  have e3 := sum_set_ge b3
  have e4 := sum_set_ge b4
  have e5 := sum_set_ge b5
  have e6 := sum_set_ge b6
  simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6
  omega

/-! ### (4,3,1) -/

/-- The octahedral blocks of two polygon classes `0, 1` and a point class `2`: the four sign
combinations of the polygons, each polygon alone, and the point alone. -/
def blocks431 : List Blk :=
  [({lP}, {lP}, o3), ({lN}, {lN}, o3), ({lP}, {lN}, o3), ({lN}, {lP}, o3),
    (sg, {lO}, o3), ({lO}, sg, o3), ({lO}, {lO}, sg)]

/-- `blocks431` with the equatorial block of class `0`. -/
def blocks431a : List Blk := blocks431 ++ [({lB}, o3, o3)]

/-- `blocks431` with the equatorial block of class `1`. -/
def blocks431b : List Blk := blocks431 ++ [(o3, {lB}, o3)]

/-- Octahedral bounds for two polygon classes with normal sets `N0`, `N1`. -/
lemma oct431 {N0 N1 : Finset (E 2)} (hN0 : ∀ n ∈ N0, IsEdgeNormal (C.K 0) n)
    (hN1 : ∀ n ∈ N1, IsEdgeNormal (C.K 1) n) (h0 : 3 ≤ N0.card) (h1 : 3 ≤ N1.card) :
    (∀ S ∈ Blk.set ({lP}, {lP}, o3), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card) ∧
    (∀ S ∈ Blk.set ({lN}, {lN}, o3), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card) ∧
    (∀ S ∈ Blk.set ({lP}, {lN}, o3), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card) ∧
    (∀ S ∈ Blk.set ({lN}, {lP}, o3), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card) := by
  refine ⟨fun S hS => ?_, fun S hS => ?_, fun S hS => ?_, fun S hS => ?_⟩
  · obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ N0 ∪ N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    exact C.oct_bound hS' hN (le_trans h0 (Finset.card_le_card Finset.subset_union_left))
  · obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
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
      (by rw [hc]; exact le_trans h0 (Finset.card_le_card Finset.subset_union_left))
  · obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    have hS' := noB hS (by decide) (by decide) lB_not_mem_o3
    have hN : ∀ n ∈ N0 ∪ -N1, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
      · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
    exact C.oct_bound hS' hN (le_trans h0 (Finset.card_le_card Finset.subset_union_left))
  · obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
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
      (by rw [hc]; exact le_trans h0 (Finset.card_le_card Finset.subset_union_left))

theorem count_431 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 4) (h1 : (C.cls 1).card = 3)
    (h2 : (C.cls 2).card = 1) :
    243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  obtain ⟨N1, hN1, hc1⟩ := C.exists_normals_K (j := 1) (by omega)
  have hd1 := C.dim_K_eq_two (j := 1) (by omega)
  have hK1 : (C.K 1).card = 3 := by rw [C.card_K, h1]
  have hanti1 : ∀ n ∈ N1, -n ∉ N1 := fun n hn hn' =>
    not_edgeNormal_neg hK1 hd1 (hN1 n hn) (hN1 _ hn')
  have hw2 : ∀ b, C.wd 2 b = 0 := C.wd_eq_zero_of_card_one h2
  obtain ⟨bPP, bNN, bPN, bNP⟩ := C.oct431 hN0 hN1 (by omega) (by omega)
  have b2 : ∀ S ∈ Blk.set (sg, {lO}, o3), 9 ≤ (C.pats S).card := by
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
  have u1 := Finset.card_union_add_card_inter N0 N1
  have u2 := Finset.card_union_add_card_inter N0 (-N1)
  -- the two intersections are disjoint parts of `N0`
  have hdisj : Disjoint (N0 ∩ N1) (N0 ∩ -N1) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact hanti1 n (Finset.mem_inter.1 hn).2 (Finset.mem_neg'.1 (Finset.mem_inter.1 hn').2)
  have hle0 : (N0 ∩ N1).card + (N0 ∩ -N1).card ≤ N0.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left)
  by_cases hpair : ∃ n ∈ N0, -n ∈ N0 ∧ (n ∈ N1 ∨ -n ∈ N1)
  · -- a pair of parallel edges of the quadrilateral, parallel to an edge of the triangle:
    -- rank three makes the widths different
    obtain ⟨n, hn, hnn, hn1⟩ := hpair
    have hn0 : n ≠ 0 := (hN0 n hn).ne_zero
    have hq := C.two_level_quad h0 (hN0 n hn) (hN0 _ hnn)
    have ht := C.two_level_tri (n := n) h1 (by
      rcases hn1 with h | h
      · exact Or.inl (hN1 n h)
      · exact Or.inr (hN1 _ h))
    have hW0 : 0 < C.wd 0 n := C.wd_pos_of_three_le (j := 0) (by omega) hn0
    have hW1 : 0 < C.wd 1 n := C.wd_pos_of_three_le (j := 1) (by omega) hn0
    have hne : C.wd 0 n ≠ C.wd 1 n := by
      intro heq
      apply hX
      exact C.extraPM_of_classes hn0 hW0
        (fin3_cases (Or.inr ⟨rfl, hq⟩) (Or.inr ⟨heq.symm, ht⟩) (Or.inl (hw2 n)))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · -- class `1` is the widest at `n`
      have hJ : ∀ i, i ≠ 1 → C.wd i n < C.wd 1 n :=
        fin3_cases (fun _ => hlt) (fun h => absurd rfl h) (fun _ => by rw [hw2]; exact hW1)
      have hsum := C.sum_card_pats_add_one_le (blkU blocks431b)
        (fun S hS => ne_none_of_mem_blkU (by decide) hS)
      rw [sum_blkU blocks431b (by decide)] at hsum
      simp only [blocks431b, blocks431, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil] at hsum
      have bE : ∀ S ∈ Blk.set (o3, {lB}, o3), 2 ≤ (C.pats S).card := fun S hS =>
        C.two_le_card_pats (onlyB1 hS lB_not_mem_o3 rfl lB_not_mem_o3) hJ
      have e1 := sum_set_ge bPP
      have e2 := sum_set_ge bNN
      have e3 := sum_set_ge bPN
      have e4 := sum_set_ge bNP
      have e5 := sum_set_ge b2
      have e6 := sum_set_ge b3
      have e7 := sum_set_ge b4
      have e8 := sum_set_ge bE
      simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6 e7 e8
      rw [Finset.card_neg] at u2
      omega
    · -- class `0` is the widest at `n`
      have hJ : ∀ i, i ≠ 0 → C.wd i n < C.wd 0 n :=
        fin3_cases (fun h => absurd rfl h) (fun _ => hgt) (fun _ => by rw [hw2]; exact hW0)
      have hsum := C.sum_card_pats_add_one_le (blkU blocks431a)
        (fun S hS => ne_none_of_mem_blkU (by decide) hS)
      rw [sum_blkU blocks431a (by decide)] at hsum
      simp only [blocks431a, blocks431, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil, List.sum_cons, List.sum_nil] at hsum
      have bE : ∀ S ∈ Blk.set ({lB}, o3, o3), 2 ≤ (C.pats S).card := fun S hS =>
        C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_o3 lB_not_mem_o3) hJ
      have e1 := sum_set_ge bPP
      have e2 := sum_set_ge bNN
      have e3 := sum_set_ge bPN
      have e4 := sum_set_ge bNP
      have e5 := sum_set_ge b2
      have e6 := sum_set_ge b3
      have e7 := sum_set_ge b4
      have e8 := sum_set_ge bE
      simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6 e7 e8
      rw [Finset.card_neg] at u2
      omega
  · -- otherwise the common normal lines inject into `N1`
    push Not at hpair
    have hle1 : (N0 ∩ N1).card + (N0 ∩ -N1).card ≤ N1.card := by
      have hdisj' : Disjoint (N0 ∩ N1) (-(N0 ∩ -N1)) := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        rw [Finset.mem_neg', Finset.mem_inter, Finset.mem_neg', neg_neg] at hn'
        obtain ⟨hn0, hn1⟩ := Finset.mem_inter.1 hn
        exact (hpair n hn0 hn'.1).1 hn1
      rw [← Finset.card_neg (N0 ∩ -N1), ← Finset.card_union_of_disjoint hdisj']
      refine Finset.card_le_card (Finset.union_subset Finset.inter_subset_right ?_)
      intro n hn
      rw [Finset.mem_neg', Finset.mem_inter, Finset.mem_neg', neg_neg] at hn
      exact hn.2
    have hsum := C.sum_card_pats_add_one_le (blkU blocks431)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks431 (by decide)] at hsum
    simp only [blocks431, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have e1 := sum_set_ge bPP
    have e2 := sum_set_ge bNN
    have e3 := sum_set_ge bPN
    have e4 := sum_set_ge bNP
    have e5 := sum_set_ge b2
    have e6 := sum_set_ge b3
    have e7 := sum_set_ge b4
    simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 e5 e6 e7
    rw [Finset.card_neg] at u2
    omega


/-! ### (4,2,2) -/

/-- Octahedral blocks of a polygon class `0` and two segment classes. -/
def blocks422 : List Blk :=
  [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), (sg, {lO}, {lO}), ({lO}, sg, sg),
    ({lO}, sg, {lO}), ({lO}, {lO}, sg)]

def blocks422a : List Blk := blocks422 ++ [({lB}, sg, o3)]
def blocks422b : List Blk := blocks422 ++ [(o3, sg, {lB})]
def blocks422c : List Blk := blocks422 ++ [({lB}, o3, sg)]
def blocks422d : List Blk := blocks422 ++ [(o3, {lB}, sg)]

/-- Parallel segments. -/
def blocks422p : List Blk :=
  [(sg, sg, sg), (sg, sg, {lO}), (sg, {lO}, sg), (sg, {lO}, {lO}), ({lO}, sg, o3),
    ({lO}, {lO}, sg), ({lB}, sg, o3), ({lB}, {lO}, sg), ({lB}, {lO}, {lO})]

theorem count_422 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 4) (h1 : (C.cls 1).card = 2)
    (h2 : (C.cls 2).card = 2) :
    243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
  obtain ⟨N0, hN0, hc0⟩ := C.exists_normals_K (j := 0) (by omega)
  obtain ⟨vp, vq, α, hvp, hvq, hne, hcls, hα1, hα⟩ := C.exists_segment h1
  obtain ⟨hn1, hn1', hw1⟩ := C.segment_normal hvp hvq hne hcls hα1 hα
  obtain ⟨wp, wq, γ, hwp, hwq, hne', hcls', hγ1, hγ⟩ := C.exists_segment h2
  obtain ⟨hn2, hn2', hw2γ⟩ := C.segment_normal hwp hwq hne' hcls' hγ1 hγ
  have hα0 : α ≠ 0 := hn1.ne_zero
  have hγ0 : γ ≠ 0 := hn2.ne_zero
  have hWα : 0 < C.wd 0 α := C.wd_pos_of_three_le (by omega) hα0
  have hWγ : 0 < C.wd 0 γ := C.wd_pos_of_three_le (by omega) hγ0
  -- blocks common to all cases
  have bD : ∀ S ∈ Blk.set (sg, {lO}, {lO}), 9 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_lO
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have bF2 : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 3 ≤ (C.pats S).card := fun S hS =>
    C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
      (mem_sg.1 (Blk.mem_set.1 hS).2.2) (by omega)
  -- the quadrilateral alone, with any segment labels
  have quad9 : ∀ S : Fin 3 → ELab, (∀ j, S j ≠ some none) → (S 0 = lP ∨ S 0 = lN) →
      9 ≤ (C.pats S).card := by
    intro S hS' hS0
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have eD := sum_set_ge bD
  have eF2 := sum_set_ge bF2
  simp only [card_sg, card_o3, Finset.card_singleton] at eD eF2
  by_cases hpar : ⟪α, C.k wq⟫ = ⟪α, C.k wp⟫
  · /- parallel segments: `α` is a zero-width direction of both -/
    obtain ⟨hm2, hm2', hw2α⟩ := C.segment_normal hwp hwq hne' hcls' hα1 hpar
    have hq : ¬(α ∈ N0 ∧ -α ∈ N0) := by
      rintro ⟨ha, hna⟩
      exact hX (C.extraPM_of_classes hα0 hWα (fin3_cases
        (Or.inr ⟨rfl, C.two_level_quad h0 (hN0 α ha) (hN0 _ hna)⟩) (Or.inl hw1) (Or.inl hw2α)))
    have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
      fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hWα)
        (fun _ => by rw [hw2α]; exact hWα)
    have key : ∀ S : Fin 3 → ELab, (∀ j, S j ≠ some none) → (S 0 = lP ∨ S 0 = lN) →
        (∀ n ∈ ({α, -α} : Finset (E 2)), IsEdgeNormal (C.msum S) n) → 11 ≤ (C.pats S).card := by
      intro S hS' hS0 hαS
      have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
        intro n hn
        rcases Finset.mem_union.1 hn with hn | hn
        · exact C.normals_msum (j := 0) hN0 n hn
        · exact hαS n hn
      have hc := card_union_pair_ge (not_both_pnrm hS0 hq)
      have hc' := card_pnrm hS0 N0
      have := C.oct_bound hS' hN (by omega)
      omega
    have hsum := C.sum_card_pats_add_one_le (blkU blocks422p)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks422p (by decide)] at hsum
    simp only [blocks422p, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
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
    have b7 : ∀ S ∈ Blk.set ({lB}, {lO}, sg), 6 ≤ (C.pats S).card := fun S hS =>
      C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_sg)
        (mem_sg.1 (Blk.mem_set.1 hS).2.2) hwp hwq hne' hcls' hpar hJ
    have b8 : ∀ S ∈ Blk.set ({lB}, {lO}, {lO}), 2 ≤ (C.pats S).card := fun S hS =>
      C.two_le_card_pats (onlyB0 hS rfl lB_not_mem_lO lB_not_mem_lO) hJ
    have eA := sum_set_ge bA
    have eB := sum_set_ge bB
    have eC := sum_set_ge bC
    have eE := sum_set_ge bE
    have e6 := sum_set_ge b6
    have e7 := sum_set_ge b7
    have e8 := sum_set_ge b8
    simp only [card_sg, card_o3, Finset.card_singleton] at eA eB eC eE e6 e7 e8
    omega
  · /- non-parallel segments -/
    have hpos2 : 0 < C.wd 2 α := C.wd_pos_of_ne hwp hwq (fun h => hpar h.symm)
    have hγpar : ⟪γ, C.k vq⟫ ≠ ⟪γ, C.k vp⟫ := by
      intro h
      have hv : C.k vq - C.k vp ≠ 0 := sub_ne_zero.2 (fun h' => hne h'.symm)
      have h1' : ⟪C.k vq - C.k vp, α⟫ = 0 := by
        rw [inner_sub_left, real_inner_comm α, real_inner_comm α, hα, sub_self]
      have h2' : ⟪C.k vq - C.k vp, γ⟫ = 0 := by
        rw [inner_sub_left, real_inner_comm γ, real_inner_comm γ, h, sub_self]
      rcases eq_or_eq_neg_of_inner hv hα1 hγ1 h1' h2' with rfl | rfl
      · exact hpar hγ
      · apply hpar
        have := hγ
        simp only [inner_neg_left] at this
        linarith
    have hpos1 : 0 < C.wd 1 γ := C.wd_pos_of_ne hvp hvq (fun h => hγpar h.symm)
    have hγα : γ ≠ α := by rintro rfl; exact hpar hγ
    have hγα' : γ ≠ -α := by
      rintro rfl
      apply hpar
      have := hγ
      simp only [inner_neg_left] at this
      linarith
    have bG : ∀ S ∈ Blk.set ({lO}, sg, sg), 9 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨-, hs1, hs2⟩ := Blk.mem_set.1 hS
      have hS' := noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_sg
      have hN : ∀ n ∈ ({α, -α} : Finset (E 2)) ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
        intro n hn
        rcases Finset.mem_union.1 hn with hn | hn
        · exact C.pair_normals_msum (mem_sg.1 hs1) hn1 hn1' n hn
        · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
      have hc := card_two_pairs hα0 hγ0 hγα hγα'
      have := C.oct_bound hS' hN (by omega)
      omega
    have bF1 : ∀ S ∈ Blk.set ({lO}, sg, {lO}), 3 ≤ (C.pats S).card := fun S hS =>
      C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_lO)
        (mem_sg.1 (Blk.mem_set.1 hS).2.1) (by omega)
    have eG := sum_set_ge bG
    have eF1 := sum_set_ge bF1
    simp only [card_sg, card_o3, Finset.card_singleton] at eG eF1
    -- crude bounds for the blocks with the quadrilateral and a segment
    have cA : ∀ S ∈ Blk.set (sg, sg, sg), 9 ≤ (C.pats S).card := fun S hS =>
      quad9 S (noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_sg) (mem_sg.1 (Blk.mem_set.1 hS).1)
    have cB : ∀ S ∈ Blk.set (sg, sg, {lO}), 9 ≤ (C.pats S).card := fun S hS =>
      quad9 S (noB hS lB_not_mem_sg lB_not_mem_sg lB_not_mem_lO) (mem_sg.1 (Blk.mem_set.1 hS).1)
    have cC : ∀ S ∈ Blk.set (sg, {lO}, sg), 9 ≤ (C.pats S).card := fun S hS =>
      quad9 S (noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg) (mem_sg.1 (Blk.mem_set.1 hS).1)
    by_cases hqα : α ∈ N0 ∧ -α ∈ N0
    · -- rank three: the widths of the quadrilateral and the second segment differ at `α`
      have hne2 : C.wd 2 α ≠ C.wd 0 α := by
        intro heq
        exact hX (C.extraPM_of_classes hα0 hWα (fin3_cases
          (Or.inr ⟨rfl, C.two_level_quad h0 (hN0 α hqα.1) (hN0 _ hqα.2)⟩) (Or.inl hw1)
          (Or.inr ⟨heq, C.two_level_pair h2 α⟩)))
      have eA := sum_set_ge cA
      have eB := sum_set_ge cB
      have eC := sum_set_ge cC
      simp only [card_sg, card_o3, Finset.card_singleton] at eA eB eC
      rcases lt_or_gt_of_ne hne2 with hlt | hgt
      · have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
          fin3_cases (fun h => absurd rfl h) (fun _ => by rw [hw1]; exact hWα) (fun _ => hlt)
        have hsum := C.sum_card_pats_add_one_le (blkU blocks422a)
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU blocks422a (by decide)] at hsum
        simp only [blocks422a, blocks422, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have bE : ∀ S ∈ Blk.set ({lB}, sg, o3), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_sg lB_not_mem_o3)
            (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
        have eE := sum_set_ge bE
        simp only [card_sg, card_o3, Finset.card_singleton] at eE
        omega
      · have hJ : ∀ i, i ≠ 2 → C.wd i α < C.wd 2 α :=
          fin3_cases (fun _ => hgt) (fun _ => by rw [hw1]; exact hpos2) (fun h => absurd rfl h)
        have hsum := C.sum_card_pats_add_one_le (blkU blocks422b)
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU blocks422b (by decide)] at hsum
        simp only [blocks422b, blocks422, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have bE : ∀ S ∈ Blk.set (o3, sg, {lB}), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB2 hS lB_not_mem_o3 lB_not_mem_sg rfl)
            (mem_sg.1 (Blk.mem_set.1 hS).2.1) hvp hvq hne hcls hα hJ
        have eE := sum_set_ge bE
        simp only [card_sg, card_o3, Finset.card_singleton] at eE
        omega
    by_cases hqγ : γ ∈ N0 ∧ -γ ∈ N0
    · -- symmetric: the widths of the quadrilateral and the first segment differ at `γ`
      have hne1 : C.wd 1 γ ≠ C.wd 0 γ := by
        intro heq
        exact hX (C.extraPM_of_classes hγ0 hWγ (fin3_cases
          (Or.inr ⟨rfl, C.two_level_quad h0 (hN0 γ hqγ.1) (hN0 _ hqγ.2)⟩)
          (Or.inr ⟨heq, C.two_level_pair h1 γ⟩) (Or.inl hw2γ)))
      have eA := sum_set_ge cA
      have eB := sum_set_ge cB
      have eC := sum_set_ge cC
      simp only [card_sg, card_o3, Finset.card_singleton] at eA eB eC
      rcases lt_or_gt_of_ne hne1 with hlt | hgt
      · have hJ : ∀ i, i ≠ 0 → C.wd i γ < C.wd 0 γ :=
          fin3_cases (fun h => absurd rfl h) (fun _ => hlt) (fun _ => by rw [hw2γ]; exact hWγ)
        have hsum := C.sum_card_pats_add_one_le (blkU blocks422c)
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU blocks422c (by decide)] at hsum
        simp only [blocks422c, blocks422, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have bE : ∀ S ∈ Blk.set ({lB}, o3, sg), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_o3 lB_not_mem_sg)
            (mem_sg.1 (Blk.mem_set.1 hS).2.2) hwp hwq hne' hcls' hγ hJ
        have eE := sum_set_ge bE
        simp only [card_sg, card_o3, Finset.card_singleton] at eE
        omega
      · have hJ : ∀ i, i ≠ 1 → C.wd i γ < C.wd 1 γ :=
          fin3_cases (fun _ => hgt) (fun h => absurd rfl h) (fun _ => by rw [hw2γ]; exact hpos1)
        have hsum := C.sum_card_pats_add_one_le (blkU blocks422d)
          (fun S hS => ne_none_of_mem_blkU (by decide) hS)
        rw [sum_blkU blocks422d (by decide)] at hsum
        simp only [blocks422d, blocks422, List.cons_append, List.nil_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil] at hsum
        have bE : ∀ S ∈ Blk.set (o3, {lB}, sg), 6 ≤ (C.pats S).card := fun S hS =>
          C.six_le_card_pats (onlyB1 hS lB_not_mem_o3 rfl lB_not_mem_sg)
            (mem_sg.1 (Blk.mem_set.1 hS).2.2) hwp hwq hne' hcls' hγ hJ
        have eE := sum_set_ge bE
        simp only [card_sg, card_o3, Finset.card_singleton] at eE
        omega
    -- generic position: both segments add normals
    have hsum := C.sum_card_pats_add_one_le (blkU blocks422)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks422 (by decide)] at hsum
    simp only [blocks422, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
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
      have hc := card_union_two_pairs_ge (not_both_pnrm hS0 hqα) (not_both_pnrm hS0 hqγ) hγα hγα'
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
      have hc := card_union_pair_ge (not_both_pnrm hS0 hqα)
      have hc' := card_pnrm hS0 N0
      have := C.oct_bound hS' hN (by omega)
      omega
    have bC : ∀ S ∈ Blk.set (sg, {lO}, sg), 11 ≤ (C.pats S).card := by
      intro S hS
      obtain ⟨hs0, -, hs2⟩ := Blk.mem_set.1 hS
      have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg
      have hS0 := mem_sg.1 hs0
      have hN : ∀ n ∈ pnrm (S 0) N0 ∪ {γ, -γ}, IsEdgeNormal (C.msum S) n := by
        intro n hn
        rcases Finset.mem_union.1 hn with hn | hn
        · exact C.normals_msum (j := 0) hN0 n hn
        · exact C.pair_normals_msum (mem_sg.1 hs2) hn2 hn2' n hn
      have hc := card_union_pair_ge (not_both_pnrm hS0 hqγ)
      have hc' := card_pnrm hS0 N0
      have := C.oct_bound hS' hN (by omega)
      omega
    have eA := sum_set_ge bA
    have eB := sum_set_ge bB
    have eC := sum_set_ge bC
    simp only [card_sg, card_o3, Finset.card_singleton] at eA eB eC
    omega


/-! ### (3,3,2) -/

/-- Octahedral blocks of two triangle classes and a segment class. -/
def blocks332 : List Blk :=
  [({lP}, {lP}, sg), ({lN}, {lN}, sg), ({lP}, {lN}, sg), ({lN}, {lP}, sg),
    ({lP}, {lP}, {lO}), ({lN}, {lN}, {lO}), ({lP}, {lN}, {lO}), ({lN}, {lP}, {lO}),
    (sg, {lO}, sg), ({lO}, sg, sg), (sg, {lO}, {lO}), ({lO}, sg, {lO}), ({lO}, {lO}, sg)]

def blocks332a : List Blk := blocks332 ++ [({lB}, o3, sg)]
def blocks332b : List Blk := blocks332 ++ [(o3, {lB}, sg)]

lemma sub_o3 {a b : Finset ELab} {S : Fin 3 → ELab} (hS : S ∈ Blk.set (a, b, {lO})) :
    S ∈ Blk.set (a, b, o3) := by
  obtain ⟨h0, h1, h2⟩ := Blk.mem_set.1 hS
  rw [Finset.mem_singleton] at h2
  exact Blk.mem_set.2 ⟨h0, h1, by rw [h2]; exact (by decide : lO ∈ o3)⟩

theorem count_332 (hX : ¬ C.ExtraPM) (h0 : (C.cls 0).card = 3) (h1 : (C.cls 1).card = 3)
    (h2 : (C.cls 2).card = 2) :
    243 ≤ (faces (convexHull ℝ (range (FullPrism.pm16 x)))).ncard := by
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
  obtain ⟨wp, wq, α, hwp, hwq, hne, hcls, hα1, hα⟩ := C.exists_segment h2
  obtain ⟨hn2, hn2', hw2⟩ := C.segment_normal hwp hwq hne hcls hα1 hα
  have hα0 : α ≠ 0 := hn2.ne_zero
  have hW0 : 0 < C.wd 0 α := C.wd_pos_of_three_le (j := 0) (by omega) hα0
  have hW1 : 0 < C.wd 1 α := C.wd_pos_of_three_le (j := 1) (by omega) hα0
  -- the octahedral bounds
  obtain ⟨bPP, bNN, bPN, bNP⟩ := C.oct431 hN0 hN1 (by omega) (by omega)
  have bPPo : ∀ S ∈ Blk.set ({lP}, {lP}, {lO}), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
    fun S hS => bPP S (sub_o3 hS)
  have bNNo : ∀ S ∈ Blk.set ({lN}, {lN}, {lO}), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
    fun S hS => bNN S (sub_o3 hS)
  have bPNo : ∀ S ∈ Blk.set ({lP}, {lN}, {lO}), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
    fun S hS => bPN S (sub_o3 hS)
  have bNPo : ∀ S ∈ Blk.set ({lN}, {lP}, {lO}), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
    fun S hS => bNP S (sub_o3 hS)
  -- a triangle and the segment: at least four normals
  have tri9 : ∀ S : Fin 3 → ELab, (∀ j, S j ≠ some none) → ∀ (j : Fin 3) (N : Finset (E 2)),
      (∀ n ∈ N, IsEdgeNormal (C.K j) n) → (∀ n ∈ N, -n ∉ N) → 3 ≤ N.card →
      (S j = lP ∨ S j = lN) → (S 2 = lP ∨ S 2 = lN) → 9 ≤ (C.pats S).card := by
    intro S hS' j N hN hanti hN3 hSj hS2
    have hN' : ∀ n ∈ pnrm (S j) N ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact C.normals_msum hN n hn
      · exact C.pair_normals_msum hS2 hn2 hn2' n hn
    have hc := card_union_pair_ge (not_both_pnrm hSj (not_both_of_anti hanti α))
    have hc' := card_pnrm hSj N
    have := C.oct_bound hS' hN' (by omega)
    omega
  have bS0 : ∀ S ∈ Blk.set (sg, {lO}, sg), 9 ≤ (C.pats S).card := fun S hS =>
    tri9 S (noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_sg) 0 N0 hN0 hanti0 (by omega)
      (mem_sg.1 (Blk.mem_set.1 hS).1) (mem_sg.1 (Blk.mem_set.1 hS).2.2)
  have bS1 : ∀ S ∈ Blk.set ({lO}, sg, sg), 9 ≤ (C.pats S).card := fun S hS =>
    tri9 S (noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_sg) 1 N1 hN1 hanti1 (by omega)
      (mem_sg.1 (Blk.mem_set.1 hS).2.1) (mem_sg.1 (Blk.mem_set.1 hS).2.2)
  have bT0 : ∀ S ∈ Blk.set (sg, {lO}, {lO}), 7 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_sg lB_not_mem_lO lB_not_mem_lO
    have hS0 := mem_sg.1 (Blk.mem_set.1 hS).1
    have hc := card_pnrm hS0 N0
    have := C.oct_bound hS' (C.normals_msum (j := 0) hN0) (by omega)
    omega
  have bT1 : ∀ S ∈ Blk.set ({lO}, sg, {lO}), 7 ≤ (C.pats S).card := by
    intro S hS
    have hS' := noB hS lB_not_mem_lO lB_not_mem_sg lB_not_mem_lO
    have hS1 := mem_sg.1 (Blk.mem_set.1 hS).2.1
    have hc := card_pnrm hS1 N1
    have := C.oct_bound hS' (C.normals_msum (j := 1) hN1) (by omega)
    omega
  have bSeg : ∀ S ∈ Blk.set ({lO}, {lO}, sg), 3 ≤ (C.pats S).card := fun S hS =>
    C.three_le_pats (noB hS lB_not_mem_lO lB_not_mem_lO lB_not_mem_sg)
      (mem_sg.1 (Blk.mem_set.1 hS).2.2) (by omega)
  -- all three classes signed: the union of the normals with `±α`
  have allS : ∀ S : Fin 3 → ELab, (∀ j, S j ≠ some none) → (S 2 = lP ∨ S 2 = lN) →
      ∀ X : Finset (E 2), (∀ n ∈ X, IsEdgeNormal (C.msum S) n) → 3 ≤ X.card →
      2 * (X ∪ {α, -α}).card + 1 ≤ (C.pats S).card := by
    intro S hS' hS2 X hX hX3
    have hN : ∀ n ∈ X ∪ {α, -α}, IsEdgeNormal (C.msum S) n := by
      intro n hn
      rcases Finset.mem_union.1 hn with hn | hn
      · exact hX n hn
      · exact C.pair_normals_msum hS2 hn2 hn2' n hn
    exact C.oct_bound hS' hN (le_trans hX3 (Finset.card_le_card Finset.subset_union_left))
  have nPP : ∀ S ∈ Blk.set ({lP}, {lP}, sg), ∀ n ∈ N0 ∪ N1, IsEdgeNormal (C.msum S) n := by
    intro S hS n hn
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    rcases Finset.mem_union.1 hn with hn | hn
    · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
    · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
  have nNN : ∀ S ∈ Blk.set ({lN}, {lN}, sg), ∀ n ∈ -N0 ∪ -N1, IsEdgeNormal (C.msum S) n := by
    intro S hS n hn
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    rcases Finset.mem_union.1 hn with hn | hn
    · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
    · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
  have nPN : ∀ S ∈ Blk.set ({lP}, {lN}, sg), ∀ n ∈ N0 ∪ -N1, IsEdgeNormal (C.msum S) n := by
    intro S hS n hn
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    rcases Finset.mem_union.1 hn with hn | hn
    · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
    · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
  have nNP : ∀ S ∈ Blk.set ({lN}, {lP}, sg), ∀ n ∈ -N0 ∪ N1, IsEdgeNormal (C.msum S) n := by
    intro S hS n hn
    obtain ⟨hs0, hs1, -⟩ := Blk.mem_set.1 hS
    rw [Finset.mem_singleton] at hs0 hs1
    rcases Finset.mem_union.1 hn with hn | hn
    · exact C.normals_msum (j := 0) hN0 n (by rw [hs0]; exact hn)
    · exact C.normals_msum (j := 1) hN1 n (by rw [hs1]; exact hn)
  have cNN : (-N0 ∪ -N1).card = (N0 ∪ N1).card := by rw [neg_union', Finset.card_neg]
  have cNP : (-N0 ∪ N1).card = (N0 ∪ -N1).card := by
    rw [show (-N0 ∪ N1 : Finset (E 2)) = -N0 ∪ -(-N1) by rw [neg_neg], neg_union',
      Finset.card_neg]
  have l3 : 3 ≤ (N0 ∪ N1).card := le_trans (by omega) (Finset.card_le_card Finset.subset_union_left)
  have l3' : 3 ≤ (N0 ∪ -N1).card :=
    le_trans (by omega) (Finset.card_le_card Finset.subset_union_left)
  have sg2 : ∀ {a b : Finset ELab} {S : Fin 3 → ELab}, S ∈ Blk.set (a, b, sg) →
      S 2 = lP ∨ S 2 = lN := fun hS => mem_sg.1 (Blk.mem_set.1 hS).2.2
  -- sizes of the common normal lines
  have u1 := Finset.card_union_add_card_inter N0 N1
  have u2 := Finset.card_union_add_card_inter N0 (-N1)
  rw [Finset.card_neg] at u2
  have hdisj : Disjoint (N0 ∩ N1) (N0 ∩ -N1) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    exact hanti1 n (Finset.mem_inter.1 hn).2 (Finset.mem_neg'.1 (Finset.mem_inter.1 hn').2)
  have hle0 : (N0 ∩ N1).card + (N0 ∩ -N1).card ≤ N0.card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left
      Finset.inter_subset_left)
  have eS0 := sum_set_ge bS0
  have eS1 := sum_set_ge bS1
  have eT0 := sum_set_ge bT0
  have eT1 := sum_set_ge bT1
  have eSeg := sum_set_ge bSeg
  have ePPo := sum_set_ge bPPo
  have eNNo := sum_set_ge bNNo
  have ePNo := sum_set_ge bPNo
  have eNPo := sum_set_ge bNPo
  simp only [card_sg, Finset.card_singleton] at eS0 eS1 eT0 eT1 eSeg ePPo eNNo ePNo eNPo
  rcases lt_trichotomy (C.wd 0 α) (C.wd 1 α) with hlt | heq | hgt
  · -- class `1` is the widest at `α`
    have hJ : ∀ i, i ≠ 1 → C.wd i α < C.wd 1 α :=
      fin3_cases (fun _ => hlt) (fun h => absurd rfl h) (fun _ => by rw [hw2]; exact hW1)
    have hsum := C.sum_card_pats_add_one_le (blkU blocks332b)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks332b (by decide)] at hsum
    simp only [blocks332b, blocks332, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have aPP : ∀ S ∈ Blk.set ({lP}, {lP}, sg), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nPP S hS) l3
    have aNN : ∀ S ∈ Blk.set ({lN}, {lN}, sg), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => by
        have := C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nNN S hS) (by omega)
        omega
    have aPN : ∀ S ∈ Blk.set ({lP}, {lN}, sg), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nPN S hS) l3'
    have aNP : ∀ S ∈ Blk.set ({lN}, {lP}, sg), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => by
        have := C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nNP S hS) (by omega)
        omega
    have bE : ∀ S ∈ Blk.set (o3, {lB}, sg), 6 ≤ (C.pats S).card := fun S hS =>
      C.six_le_card_pats (onlyB1 hS lB_not_mem_o3 rfl lB_not_mem_sg)
        (mem_sg.1 (Blk.mem_set.1 hS).2.2) hwp hwq hne hcls hα hJ
    have e1 := sum_set_ge aPP
    have e2 := sum_set_ge aNN
    have e3 := sum_set_ge aPN
    have e4 := sum_set_ge aNP
    have eE := sum_set_ge bE
    simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 eE
    omega
  · -- equal widths: rank three keeps `±α` out of one triangle's normals
    have hrank : (α ∉ N0 ∧ -α ∉ N0) ∨ (α ∉ N1 ∧ -α ∉ N1) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨h0', h1'⟩ := hcon
      have hA0 : α ∈ N0 ∨ -α ∈ N0 := by
        by_cases h : α ∈ N0
        · exact Or.inl h
        · exact Or.inr (h0' h)
      have hA1 : α ∈ N1 ∨ -α ∈ N1 := by
        by_cases h : α ∈ N1
        · exact Or.inl h
        · exact Or.inr (h1' h)
      apply hX
      refine C.extraPM_of_classes hα0 hW0 (fin3_cases ?_ ?_ (Or.inl hw2))
      · refine Or.inr ⟨rfl, C.two_level_tri h0 ?_⟩
        rcases hA0 with h | h
        · exact Or.inl (hN0 _ h)
        · exact Or.inr (hN0 _ h)
      · refine Or.inr ⟨heq.symm, C.two_level_tri h1 ?_⟩
        rcases hA1 with h | h
        · exact Or.inl (hN1 _ h)
        · exact Or.inr (hN1 _ h)
    have notboth : ∀ X : Finset (E 2), X = N0 ∪ N1 ∨ X = -N0 ∪ -N1 ∨ X = N0 ∪ -N1 ∨
        X = -N0 ∪ N1 → ¬(α ∈ X ∧ -α ∈ X) := by
      intro X hXd ⟨ha, hna⟩
      rcases hrank with ⟨ha0, hna0⟩ | ⟨ha1, hna1⟩
      · rcases hXd with rfl | rfl | rfl | rfl
        · simp only [Finset.mem_union, ha0, hna0, false_or] at ha hna
          exact hanti1 _ ha (by simpa using hna)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha0, hna0, false_or] at ha hna
          exact hanti1 _ hna (by simpa using ha)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha0, hna0, false_or] at ha hna
          exact hanti1 _ hna (by simpa using ha)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha0, hna0, false_or] at ha hna
          exact hanti1 _ ha (by simpa using hna)
      · rcases hXd with rfl | rfl | rfl | rfl
        · simp only [Finset.mem_union, ha1, hna1, or_false] at ha hna
          exact hanti0 _ ha (by simpa using hna)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha1, hna1, or_false] at ha hna
          exact hanti0 _ hna (by simpa using ha)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha1, hna1, or_false] at ha hna
          exact hanti0 _ ha (by simpa using hna)
        · simp only [Finset.mem_union, Finset.mem_neg', neg_neg, ha1, hna1, or_false] at ha hna
          exact hanti0 _ hna (by simpa using ha)
    have hsum := C.sum_card_pats_add_one_le (blkU blocks332)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks332 (by decide)] at hsum
    simp only [blocks332, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have aPP : ∀ S ∈ Blk.set ({lP}, {lP}, sg), 2 * (N0 ∪ N1).card + 3 ≤ (C.pats S).card := by
      intro S hS
      have := allS S (noB hS (by decide) (by decide) lB_not_mem_sg) (sg2 hS) _ (nPP S hS) l3
      have hc := card_union_pair_ge (notboth _ (Or.inl rfl))
      omega
    have aNN : ∀ S ∈ Blk.set ({lN}, {lN}, sg), 2 * (N0 ∪ N1).card + 3 ≤ (C.pats S).card := by
      intro S hS
      have := allS S (noB hS (by decide) (by decide) lB_not_mem_sg) (sg2 hS) _ (nNN S hS)
        (by omega)
      have hc := card_union_pair_ge (notboth _ (Or.inr (Or.inl rfl)))
      omega
    have aPN : ∀ S ∈ Blk.set ({lP}, {lN}, sg), 2 * (N0 ∪ -N1).card + 3 ≤ (C.pats S).card := by
      intro S hS
      have := allS S (noB hS (by decide) (by decide) lB_not_mem_sg) (sg2 hS) _ (nPN S hS) l3'
      have hc := card_union_pair_ge (notboth _ (Or.inr (Or.inr (Or.inl rfl))))
      omega
    have aNP : ∀ S ∈ Blk.set ({lN}, {lP}, sg), 2 * (N0 ∪ -N1).card + 3 ≤ (C.pats S).card := by
      intro S hS
      have := allS S (noB hS (by decide) (by decide) lB_not_mem_sg) (sg2 hS) _ (nNP S hS)
        (by omega)
      have hc := card_union_pair_ge (notboth _ (Or.inr (Or.inr (Or.inr rfl))))
      omega
    have e1 := sum_set_ge aPP
    have e2 := sum_set_ge aNN
    have e3 := sum_set_ge aPN
    have e4 := sum_set_ge aNP
    simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4
    omega
  · -- class `0` is the widest at `α`
    have hJ : ∀ i, i ≠ 0 → C.wd i α < C.wd 0 α :=
      fin3_cases (fun h => absurd rfl h) (fun _ => hgt) (fun _ => by rw [hw2]; exact hW0)
    have hsum := C.sum_card_pats_add_one_le (blkU blocks332a)
      (fun S hS => ne_none_of_mem_blkU (by decide) hS)
    rw [sum_blkU blocks332a (by decide)] at hsum
    simp only [blocks332a, blocks332, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil] at hsum
    have aPP : ∀ S ∈ Blk.set ({lP}, {lP}, sg), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nPP S hS) l3
    have aNN : ∀ S ∈ Blk.set ({lN}, {lN}, sg), 2 * (N0 ∪ N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => by
        have := C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nNN S hS) (by omega)
        omega
    have aPN : ∀ S ∈ Blk.set ({lP}, {lN}, sg), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nPN S hS) l3'
    have aNP : ∀ S ∈ Blk.set ({lN}, {lP}, sg), 2 * (N0 ∪ -N1).card + 1 ≤ (C.pats S).card :=
      fun S hS => by
        have := C.oct_bound (noB hS (by decide) (by decide) lB_not_mem_sg) (nNP S hS) (by omega)
        omega
    have bE : ∀ S ∈ Blk.set ({lB}, o3, sg), 6 ≤ (C.pats S).card := fun S hS =>
      C.six_le_card_pats (onlyB0 hS rfl lB_not_mem_o3 lB_not_mem_sg)
        (mem_sg.1 (Blk.mem_set.1 hS).2.2) hwp hwq hne hcls hα hJ
    have e1 := sum_set_ge aPP
    have e2 := sum_set_ge aNN
    have e3 := sum_set_ge aPN
    have e4 := sum_set_ge aNP
    have eE := sum_set_ge bE
    simp only [card_sg, card_o3, Finset.card_singleton] at e1 e2 e3 e4 eE
    omega

end Config

end Kalai5.LemmaB.Eight
