import Kalai5.LemmaB.Shapes

/-!
# Lemma B: bookkeeping with blocks of labels

A *block* prescribes a set of allowed values for each of the three classes; its labels form a
product (`Blk.set`).  For a list of blocks that are pairwise separated by one class (checked by
`decide`), the sum over the union is the sum of the block sums (`sum_blkU`), and a uniform bound
on a block gives `(size) * (bound)` (`sum_set_ge`).

Also: octahedral bounds from edge normals (`oct_bound`), `≥ 3` and `≥ 1` patterns, the two-level
criteria used for the rank-three exclusions, and cardinalities of unions with pairs `{a, -a}`.
-/

namespace Kalai5.LemmaB

open Set Module Kalai5.LemmaA
open scoped Pointwise

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Config

/-! ### Label values -/

/-- Label values: unused, both signs, `+`, `-`. -/
abbrev lO : ELab := none
abbrev lB : ELab := some none
abbrev lP : ELab := some (some true)
abbrev lN : ELab := some (some false)

/-- The two signs. -/
def sg : Finset ELab := {lP, lN}

/-- The octahedral values. -/
def o3 : Finset ELab := {lO, lP, lN}

lemma card_sg : sg.card = 2 := by decide
lemma card_o3 : o3.card = 3 := by decide
lemma mem_sg {l : ELab} : l ∈ sg ↔ l = lP ∨ l = lN := by simp [sg]
lemma lB_not_mem_sg : lB ∉ sg := by decide
lemma lB_not_mem_o3 : lB ∉ o3 := by decide
lemma lB_not_mem_lO : lB ∉ ({lO} : Finset ELab) := by decide

/-! ### Blocks -/

/-- A block of labels: the allowed values of the three classes. -/
abbrev Blk := Finset ELab × Finset ELab × Finset ELab

/-- The labels of a block. -/
def Blk.set (t : Blk) : Finset (Fin 3 → ELab) := Fintype.piFinset ![t.1, t.2.1, t.2.2]

lemma Blk.mem_set {t : Blk} {S : Fin 3 → ELab} :
    S ∈ t.set ↔ S 0 ∈ t.1 ∧ S 1 ∈ t.2.1 ∧ S 2 ∈ t.2.2 := by
  rw [Blk.set, Fintype.mem_piFinset]
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

lemma Blk.card_set (t : Blk) : t.set.card = t.1.card * t.2.1.card * t.2.2.card := by
  rw [Blk.set, Fintype.card_piFinset, Fin.prod_univ_three]
  rfl

/-- Two blocks separated by one class. -/
def Blk.Sep (t t' : Blk) : Prop :=
  Disjoint t.1 t'.1 ∨ Disjoint t.2.1 t'.2.1 ∨ Disjoint t.2.2 t'.2.2

instance : DecidableRel Blk.Sep := fun _ _ => by unfold Blk.Sep; infer_instance

lemma Blk.disjoint_of_sep {t t' : Blk} (h : t.Sep t') : Disjoint t.set t'.set := by
  rw [Finset.disjoint_left]
  intro S h1 h2
  rw [Blk.mem_set] at h1 h2
  rcases h with h | h | h
  · exact Finset.disjoint_left.1 h h1.1 h2.1
  · exact Finset.disjoint_left.1 h h1.2.1 h2.2.1
  · exact Finset.disjoint_left.1 h h1.2.2 h2.2.2

/-- The union of a list of blocks. -/
def blkU : List Blk → Finset (Fin 3 → ELab)
  | [] => ∅
  | t :: l => t.set ∪ blkU l

lemma disjoint_blkU {t : Blk} {l : List Blk} (h : ∀ t' ∈ l, t.Sep t') :
    Disjoint t.set (blkU l) := by
  induction l with
  | nil => simp [blkU]
  | cons t' l ih =>
    rw [blkU, Finset.disjoint_union_right]
    exact ⟨Blk.disjoint_of_sep (h t' (by simp)), ih fun t'' ht'' => h t'' (by simp [ht''])⟩

lemma sum_blkU (l : List Blk) (h : l.Pairwise Blk.Sep) (f : (Fin 3 → ELab) → ℕ) :
    ∑ S ∈ blkU l, f S = (l.map fun t => ∑ S ∈ t.set, f S).sum := by
  induction l with
  | nil => simp [blkU]
  | cons t l ih =>
    rw [List.pairwise_cons] at h
    rw [blkU, Finset.sum_union (disjoint_blkU h.1), ih h.2, List.map_cons, List.sum_cons]

lemma ne_none_of_mem_blkU {l : List Blk} (hl : ∀ t ∈ l, lO ∉ t.1 ∨ lO ∉ t.2.1 ∨ lO ∉ t.2.2)
    {S : Fin 3 → ELab} (hS : S ∈ blkU l) : S ≠ fun _ => none := by
  induction l with
  | nil => simp [blkU] at hS
  | cons t l ih =>
    rw [blkU, Finset.mem_union] at hS
    rcases hS with hS | hS
    · rintro rfl
      rw [Blk.mem_set] at hS
      rcases hl t (by simp) with h | h | h
      · exact h hS.1
      · exact h hS.2.1
      · exact h hS.2.2
    · exact ih (fun t' ht' => hl t' (by simp [ht'])) hS

lemma sum_set_ge {t : Blk} {f : (Fin 3 → ELab) → ℕ} {m : ℕ} (h : ∀ S ∈ t.set, m ≤ f S) :
    t.1.card * t.2.1.card * t.2.2.card * m ≤ ∑ S ∈ t.set, f S := by
  have := Finset.card_nsmul_le_sum t.set f m h
  rwa [Blk.card_set, smul_eq_mul] at this

lemma fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

lemma noB {t : Blk} {S : Fin 3 → ELab} (hS : S ∈ t.set) (h0 : lB ∉ t.1) (h1 : lB ∉ t.2.1)
    (h2 : lB ∉ t.2.2) : ∀ j, S j ≠ some none := by
  rw [Blk.mem_set] at hS
  refine fin3_cases ?_ ?_ ?_
  · intro h; rw [h] at hS; exact h0 hS.1
  · intro h; rw [h] at hS; exact h1 hS.2.1
  · intro h; rw [h] at hS; exact h2 hS.2.2

lemma onlyB0 {t : Blk} {S : Fin 3 → ELab} (hS : S ∈ t.set) (h0 : t.1 = {lB}) (h1 : lB ∉ t.2.1)
    (h2 : lB ∉ t.2.2) : ∀ i, S i = some none ↔ i = 0 := by
  rw [Blk.mem_set, h0, Finset.mem_singleton] at hS
  obtain ⟨hs0, hs1, hs2⟩ := hS
  refine fin3_cases ⟨fun _ => rfl, fun _ => hs0⟩ ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at hs1; exact absurd hs1 h1
  · exact absurd h (by decide)
  · rw [h] at hs2; exact absurd hs2 h2
  · exact absurd h (by decide)

lemma onlyB1 {t : Blk} {S : Fin 3 → ELab} (hS : S ∈ t.set) (h0 : lB ∉ t.1) (h1 : t.2.1 = {lB})
    (h2 : lB ∉ t.2.2) : ∀ i, S i = some none ↔ i = 1 := by
  rw [Blk.mem_set, h1, Finset.mem_singleton] at hS
  obtain ⟨hs0, hs1, hs2⟩ := hS
  refine fin3_cases ⟨fun h => ?_, fun h => ?_⟩ ⟨fun _ => rfl, fun _ => hs1⟩ ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at hs0; exact absurd hs0 h0
  · exact absurd h (by decide)
  · rw [h] at hs2; exact absurd hs2 h2
  · exact absurd h (by decide)

lemma onlyB2 {t : Blk} {S : Fin 3 → ELab} (hS : S ∈ t.set) (h0 : lB ∉ t.1) (h1 : lB ∉ t.2.1)
    (h2 : t.2.2 = {lB}) : ∀ i, S i = some none ↔ i = 2 := by
  rw [Blk.mem_set, h2, Finset.mem_singleton] at hS
  obtain ⟨hs0, hs1, hs2⟩ := hS
  refine fin3_cases ⟨fun h => ?_, fun h => ?_⟩ ⟨fun h => ?_, fun h => ?_⟩ ⟨fun _ => rfl, fun _ => hs2⟩
  · rw [h] at hs0; exact absurd hs0 h0
  · exact absurd h (by decide)
  · rw [h] at hs1; exact absurd hs1 h1
  · exact absurd h (by decide)

/-! ### Edge-normal sets -/

lemma pnrm_pos (N : Finset (E 2)) : pnrm lP N = N := rfl
lemma pnrm_neg (N : Finset (E 2)) : pnrm lN N = -N := rfl

lemma pnrm_pair {l : ELab} (hl : l = lP ∨ l = lN) (a : E 2) : pnrm l {a, -a} = {a, -a} := by
  rcases hl with rfl | rfl
  · rfl
  · rw [pnrm_neg]
    ext y
    simp only [Finset.mem_neg', Finset.mem_insert, Finset.mem_singleton, neg_eq_iff_eq_neg,
      neg_neg]
    tauto

lemma anti_pnrm {l : ELab} (hl : l = lP ∨ l = lN) {N : Finset (E 2)}
    (h : ∀ n ∈ N, -n ∉ N) : ∀ n ∈ pnrm l N, -n ∉ pnrm l N := by
  rcases hl with rfl | rfl
  · exact h
  · rw [pnrm_neg]
    intro n hn hn'
    rw [Finset.mem_neg'] at hn hn'
    rw [neg_neg] at hn'
    exact h _ hn (by rwa [neg_neg])

lemma not_mem_pnrm {l : ELab} (hl : l = lP ∨ l = lN) {N : Finset (E 2)} {a : E 2}
    (ha : a ∉ N) (hna : -a ∉ N) : a ∉ pnrm l N ∧ -a ∉ pnrm l N := by
  rcases hl with rfl | rfl
  · exact ⟨ha, hna⟩
  · rw [pnrm_neg, Finset.mem_neg', Finset.mem_neg', neg_neg]
    exact ⟨hna, ha⟩

lemma neg_union' (s t : Finset (E 2)) : -s ∪ -t = -(s ∪ t) := by
  ext y; simp [Finset.mem_neg']

lemma ne_neg_self {a : E 2} (h0 : a ≠ 0) : a ≠ -a := by
  intro h
  apply h0
  have h1 := congrArg (fun y => y + a) h
  simp only [neg_add_cancel] at h1
  rw [← two_smul ℝ] at h1
  rcases smul_eq_zero.1 h1 with h' | h'
  · norm_num at h'
  · exact h'

lemma card_union_pair_ge {X : Finset (E 2)} {a : E 2} (h : ¬(a ∈ X ∧ -a ∈ X)) :
    X.card + 1 ≤ (X ∪ {a, -a}).card := by
  by_cases ha : a ∈ X
  · have hna : -a ∉ X := fun h' => h ⟨ha, h'⟩
    rw [← Finset.card_insert_of_notMem hna]
    exact Finset.card_le_card (Finset.insert_subset (by simp) Finset.subset_union_left)
  · rw [← Finset.card_insert_of_notMem ha]
    exact Finset.card_le_card (Finset.insert_subset (by simp) Finset.subset_union_left)

lemma card_union_pair_ge2 {X : Finset (E 2)} {a : E 2} (ha : a ∉ X) (hna : -a ∉ X) (h0 : a ≠ 0) :
    X.card + 2 ≤ (X ∪ {a, -a}).card := by
  have h1 : a ∉ insert (-a) X := by
    rw [Finset.mem_insert, not_or]; exact ⟨ne_neg_self h0, ha⟩
  rw [show X.card + 2 = (insert a (insert (-a) X)).card by
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem hna]]
  exact Finset.card_le_card (Finset.insert_subset (by simp)
    (Finset.insert_subset (by simp) Finset.subset_union_left))

/-- Two non-parallel pairs, each meeting `X` in at most one point. -/
lemma card_union_two_pairs_ge {X : Finset (E 2)} {a g : E 2} (ha : ¬(a ∈ X ∧ -a ∈ X))
    (hg : ¬(g ∈ X ∧ -g ∈ X)) (h1 : g ≠ a) (h2 : g ≠ -a) :
    X.card + 2 ≤ (X ∪ {a, -a} ∪ {g, -g}).card := by
  obtain ⟨a', ha'X, ha'⟩ : ∃ a', a' ∉ X ∧ (a' = a ∨ a' = -a) := by
    by_cases h : a ∈ X
    · exact ⟨-a, fun h' => ha ⟨h, h'⟩, Or.inr rfl⟩
    · exact ⟨a, h, Or.inl rfl⟩
  obtain ⟨g', hg'X, hg'⟩ : ∃ g', g' ∉ X ∧ (g' = g ∨ g' = -g) := by
    by_cases h : g ∈ X
    · exact ⟨-g, fun h' => hg ⟨h, h'⟩, Or.inr rfl⟩
    · exact ⟨g, h, Or.inl rfl⟩
  have hne : a' ≠ g' := by
    rcases ha' with rfl | rfl <;> rcases hg' with rfl | rfl
    · exact fun h => h1 h.symm
    · intro h; apply h2; rw [h, neg_neg]
    · intro h; apply h2; exact h.symm
    · intro h; apply h1; exact neg_injective h.symm
  have h1' : a' ∉ insert g' X := by
    rw [Finset.mem_insert, not_or]; exact ⟨hne, ha'X⟩
  rw [show X.card + 2 = (insert a' (insert g' X)).card by
    rw [Finset.card_insert_of_notMem h1', Finset.card_insert_of_notMem hg'X]]
  refine Finset.card_le_card (Finset.insert_subset ?_ (Finset.insert_subset ?_ ?_))
  · rcases ha' with rfl | rfl <;> simp
  · rcases hg' with rfl | rfl <;> simp
  · exact Finset.subset_union_left.trans Finset.subset_union_left

/-- A pair avoiding `X` and a non-parallel pair meeting it in at most one point. -/
lemma card_union_two_pairs_ge3 {X : Finset (E 2)} {a g : E 2} (ha : a ∉ X) (hna : -a ∉ X)
    (ha0 : a ≠ 0) (hg : ¬(g ∈ X ∧ -g ∈ X)) (h1 : g ≠ a) (h2 : g ≠ -a) :
    X.card + 3 ≤ (X ∪ {a, -a} ∪ {g, -g}).card := by
  obtain ⟨g', hg'X, hg'⟩ : ∃ g', g' ∉ X ∧ (g' = g ∨ g' = -g) := by
    by_cases h : g ∈ X
    · exact ⟨-g, fun h' => hg ⟨h, h'⟩, Or.inr rfl⟩
    · exact ⟨g, h, Or.inl rfl⟩
  have hga : g' ≠ a ∧ g' ≠ -a := by
    rcases hg' with rfl | rfl
    · exact ⟨h1, h2⟩
    · refine ⟨fun h => h2 ?_, fun h => h1 (neg_injective h)⟩
      rw [← h, neg_neg]
  have hm1 : -a ∉ insert g' X := by
    rw [Finset.mem_insert, not_or]; exact ⟨fun h => hga.2 h.symm, hna⟩
  have hm2 : a ∉ insert (-a) (insert g' X) := by
    rw [Finset.mem_insert, Finset.mem_insert, not_or, not_or]
    exact ⟨ne_neg_self ha0, fun h => hga.1 h.symm, ha⟩
  rw [show X.card + 3 = (insert a (insert (-a) (insert g' X))).card by
    rw [Finset.card_insert_of_notMem hm2, Finset.card_insert_of_notMem hm1,
      Finset.card_insert_of_notMem hg'X]]
  refine Finset.card_le_card (Finset.insert_subset (by simp)
    (Finset.insert_subset (by simp) (Finset.insert_subset ?_ ?_)))
  · rcases hg' with rfl | rfl <;> simp
  · exact Finset.subset_union_left.trans Finset.subset_union_left

lemma card_two_pairs {a g : E 2} (ha0 : a ≠ 0) (hg0 : g ≠ 0) (h1 : g ≠ a) (h2 : g ≠ -a) :
    ({a, -a} ∪ {g, -g} : Finset (E 2)).card = 4 := by
  have e : ({a, -a} ∪ {g, -g} : Finset (E 2)) = insert a (insert (-a) (insert g {-g})) := by
    ext y; simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [e, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
    Finset.card_insert_of_notMem, Finset.card_singleton]
  · rw [Finset.mem_singleton]; exact ne_neg_self hg0
  · rw [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨fun h => h2 h.symm, fun h => h1 (neg_injective h).symm⟩
  · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or]
    refine ⟨ne_neg_self ha0, fun h => h1 h.symm, fun h => h2 ?_⟩
    rw [h, neg_neg]

variable {x : Fin 7 → E5} (C : Config x)

/-! ### Octahedral bounds -/

lemma oct_bound {S : Fin 3 → ELab} (hS : ∀ j, S j ≠ some none) {N : Finset (E 2)}
    (hN : ∀ n ∈ N, IsEdgeNormal (C.msum S) n) (h3 : 3 ≤ N.card) :
    2 * N.card + 1 ≤ (C.pats S).card :=
  (card_amaxSets_ge hN h3).trans (C.card_amaxSets_le_pats hS)

lemma card_part_le_msum (S : Fin 3 → ELab) (j : Fin 3) : (C.part S j).card ≤ (C.msum S).card := by
  unfold msum
  fin_cases j
  · exact (Finset.card_le_card_add_right (C.part_nonempty S 1)).trans
      (Finset.card_le_card_add_right (C.part_nonempty S 2))
  · exact (Finset.card_le_card_add_left (C.part_nonempty S 0)).trans
      (Finset.card_le_card_add_right (C.part_nonempty S 2))
  · exact Finset.card_le_card_add_left ((C.part_nonempty S 0).add (C.part_nonempty S 1))

lemma card_part {S : Fin 3 → ELab} {j : Fin 3} (hj : S j = lP ∨ S j = lN) :
    (C.part S j).card = (C.cls j).card := by
  unfold part
  rcases hj with h | h <;> rw [h]
  · exact C.card_K j
  · rw [Finset.card_neg]; exact C.card_K j

lemma three_le_pats {S : Fin 3 → ELab} (hS : ∀ j, S j ≠ some none) {j : Fin 3}
    (hj : S j = lP ∨ S j = lN) (h2 : 2 ≤ (C.cls j).card) : 3 ≤ (C.pats S).card := by
  have hc : 1 < (C.msum S).card := by
    have := C.card_part_le_msum S j
    rw [C.card_part hj] at this
    omega
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.1 hc
  exact (three_le_card_amaxSets hp hq hpq).trans (C.card_amaxSets_le_pats hS)

lemma one_le_pats {S : Fin 3 → ELab} (hS : ∀ j, S j ≠ some none) : 1 ≤ (C.pats S).card :=
  Finset.card_pos.2 ⟨_, C.mem_pats.2 ⟨0, Or.inl hS, rfl⟩⟩

/-- The normals of a sign-labelled class `j`, as normals of `M_S`. -/
lemma normals_msum {S : Fin 3 → ELab} {j : Fin 3} {N : Finset (E 2)}
    (hN : ∀ n ∈ N, IsEdgeNormal (C.K j) n) : ∀ n ∈ pnrm (S j) N, IsEdgeNormal (C.msum S) n :=
  C.edgeNormal_pnrm hN

/-! ### Two levels -/

lemma at_hi_of_wd_zero {j : Fin 3} {b : E 2} (h : C.wd j b = 0) :
    ∀ v, C.c v = j → ⟪b, C.k v⟫ = C.hi j b := by
  intro v hv
  have h1 := C.le_hi' hv b
  have h2 := C.lo_le' hv b
  simp only [wd] at h
  linarith

/-- The fourth `±1`-functional, class by class. -/
lemma extraPM_of_classes {b : E 2} (hb : b ≠ 0) {W : ℝ} (hW : 0 < W)
    (h : ∀ j, C.wd j b = 0 ∨ (C.wd j b = W ∧
      ∀ v, C.c v = j → ⟪b, C.k v⟫ = C.hi j b ∨ ⟪b, C.k v⟫ = C.lo j b)) : C.ExtraPM := by
  refine C.extraPM_of_levels hb hW (fun v => ?_) (fun j => ?_)
  · rcases h (C.c v) with h0 | ⟨-, hl⟩
    · exact Or.inl (C.at_hi_of_wd_zero h0 v rfl)
    · exact hl v rfl
  · rcases h j with h0 | ⟨hw, -⟩
    · exact Or.inl h0
    · exact Or.inr hw

lemma two_level_tri {j : Fin 3} {n : E 2} (h3 : (C.cls j).card = 3)
    (hn : IsEdgeNormal (C.K j) n ∨ IsEdgeNormal (C.K j) (-n)) :
    ∀ v, C.c v = j → ⟪n, C.k v⟫ = C.hi j n ∨ ⟪n, C.k v⟫ = C.lo j n := by
  apply C.two_level_of_card
  rw [C.card_K, h3]
  rcases hn with hn | hn
  · have := hn.2
    have := Finset.card_pos.2 (amax_nonempty (C.K_nonempty j) (-n))
    omega
  · have := hn.2
    have := Finset.card_pos.2 (amax_nonempty (C.K_nonempty j) n)
    omega

lemma two_level_quad {j : Fin 3} {n : E 2} (h4 : (C.cls j).card = 4)
    (hn : IsEdgeNormal (C.K j) n) (hn' : IsEdgeNormal (C.K j) (-n)) :
    ∀ v, C.c v = j → ⟪n, C.k v⟫ = C.hi j n ∨ ⟪n, C.k v⟫ = C.lo j n := by
  apply C.two_level_of_card
  rw [C.card_K, h4]
  have := hn.2; have := hn'.2
  omega

lemma two_level_pair {j : Fin 3} (h2 : (C.cls j).card = 2) (b : E 2) :
    ∀ v, C.c v = j → ⟪b, C.k v⟫ = C.hi j b ∨ ⟪b, C.k v⟫ = C.lo j b := by
  apply C.two_level_of_card
  rw [C.card_K, h2]
  have := Finset.card_pos.2 (amax_nonempty (C.K_nonempty j) b)
  have := Finset.card_pos.2 (amax_nonempty (C.K_nonempty j) (-b))
  omega

lemma wd_pos_of_ne {j : Fin 3} {v w : Fin 7} (hv : C.c v = j) (hw : C.c w = j) {b : E 2}
    (h : ⟪b, C.k v⟫ ≠ ⟪b, C.k w⟫) : 0 < C.wd j b := by
  have h1 := C.le_hi' hv b
  have h2 := C.lo_le' hv b
  have h3 := C.le_hi' hw b
  have h4 := C.lo_le' hw b
  simp only [wd]
  rcases lt_or_gt_of_ne h with h | h <;> linarith

/-- A segment fibre with a unit normal. -/
lemma exists_segment {j : Fin 3} (h2 : (C.cls j).card = 2) :
    ∃ vp vq α, C.c vp = j ∧ C.c vq = j ∧ C.k vp ≠ C.k vq ∧
      (∀ v, C.c v = j → v = vp ∨ v = vq) ∧ ‖α‖ = 1 ∧ ⟪α, C.k vq⟫ = ⟪α, C.k vp⟫ := by
  obtain ⟨vp, vq, hvp, hvq, hne, hcls⟩ := C.exists_pair h2
  obtain ⟨α, hα1, hαo⟩ := exists_unit_orth (C.k vq - C.k vp)
  refine ⟨vp, vq, α, hvp, hvq, hne, hcls, hα1, ?_⟩
  rw [inner_sub_left] at hαo
  linarith [real_inner_comm α (C.k vq), real_inner_comm α (C.k vp)]

end Config

end Kalai5.LemmaB
