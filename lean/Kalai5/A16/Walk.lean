import Kalai5.A16.Sound

/-!
# A16: the decision tree is sound

`walk_sound`: the leaf reached by a parameter `a` gives `need` upper polar vertices or a fifth full
normal.  `Family.sound`: together with the vertical facets and the antipodes, at least `19` vertices
of the polar of the sixteen points, or a fifth full normal.
-/

namespace Kalai5.A16

open Set Kalai5.LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Family

variable (F : Family)

/-- At least `242` distinct nonempty tight sets of families of polar points of the sixteen points. -/
def CountGoalF (a : Fin 4 → ℝ) : Prop :=
  ∃ M : Finset (Set E5), 242 ≤ M.card ∧ ∀ m ∈ M, m.Nonempty ∧ ∃ Z : Finset E5, Z.Nonempty ∧
    (∀ y ∈ Z, F.IsPV a y) ∧ m = {x ∈ range (F.pt a) | ∀ y ∈ Z, ⟪x, y⟫ = 1}

/-- What the leaf reached by `a` provides. -/
def LeafGoal (a : Fin 4 → ℝ) : Prop :=
  (∃ U : Finset E5, F.need ≤ U.card ∧ ∀ y ∈ U, F.IsPV a y ∧ 0 < y 4) ∨
    (∃ y : E5, (∀ w, ⟪F.pt a w, y⟫ = 1 ∨ ⟪F.pt a w, y⟫ = -1) ∧ 0 < y 4) ∨ F.CountGoalF a

lemma sortedLT_cons {a : ℕ} {l : List ℕ} (h : sortedLT (a :: l) = true) :
    sortedLT l = true ∧ ∀ b ∈ l, a < b := by
  induction l generalizing a with
  | nil => simp [sortedLT]
  | cons b l ih =>
    simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hab, hl⟩ := h
    refine ⟨hl, fun c hc => ?_⟩
    rcases List.mem_cons.1 hc with rfl | hc
    · exact hab
    · exact lt_trans hab ((ih hl).2 c hc)

lemma sortedLT_nodup : ∀ {l : List ℕ}, sortedLT l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨hl, hlt⟩ := sortedLT_cons h
    exact List.nodup_cons.2 ⟨fun ha => lt_irrefl a (hlt a ha), sortedLT_nodup hl⟩

lemma maskOf_lt16 (p : ℕ → Bool) : Gale.maskOf 16 p < 2 ^ 16 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [Gale.testBit_maskOf]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

/-- Masks below `2¹⁶` are determined by their bits below `16`. -/
lemma mask_ext {m m' : ℕ} (hm : m < 2 ^ 16) (hm' : m' < 2 ^ 16)
    (h : ∀ w < 16, m.testBit w = m'.testBit w) : m = m' := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · exact h i hi
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- The masks of valid records are below `2¹⁶`. -/
lemma recMask_lt {facts : Facts} {r : FRec} {m : ℕ} (hm : recMask facts r = some m) : m < 2 ^ 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, rfl⟩ := recMask_spec hm
  exact maskOf_lt16 _

/-- Bits of `andOver`: bit `w < 16` is set iff every generator containing `m` has it. -/
lemma andOver_testBit (gens : List ℕ) (m : ℕ) {w : ℕ} (hw : w < 16) :
    (andOver gens m).testBit w = true ↔ ∀ g ∈ gens, m &&& g = m → g.testBit w = true := by
  have key : ∀ (l : List ℕ) (acc : ℕ),
      (l.foldl (fun acc g => if m &&& g == m then acc &&& g else acc) acc).testBit w = true ↔
        acc.testBit w = true ∧ ∀ g ∈ l, m &&& g = m → g.testBit w = true := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons g l ih =>
      intro acc
      rw [List.foldl_cons, ih]
      by_cases hg : m &&& g = m
      · have hb : (m &&& g == m) = true := by simpa using hg
        rw [if_pos hb, Nat.testBit_and, Bool.and_eq_true]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun g' hg' hmg => ?_⟩
          rcases List.mem_cons.1 hg' with rfl | hg'
          · exact h2
          · exact h3 g' hg' hmg
        · rintro ⟨h1, h3⟩
          exact ⟨⟨h1, h3 g (List.mem_cons_self) hg⟩, fun g' hg' hmg => h3 g' (List.mem_cons_of_mem _ hg') hmg⟩
      · have hb : (m &&& g == m) = false := by simpa using hg
        rw [if_neg (by rw [hb]; decide)]
        constructor
        · rintro ⟨h1, h3⟩
          refine ⟨h1, fun g' hg' hmg => ?_⟩
          rcases List.mem_cons.1 hg' with rfl | hg'
          · exact absurd hmg hg
          · exact h3 g' hg' hmg
        · rintro ⟨h1, h3⟩
          exact ⟨h1, fun g' hg' hmg => h3 g' (List.mem_cons_of_mem _ hg') hmg⟩
  rw [andOver, key]
  have h65535 : (65535 : ℕ).testBit w = true := by interval_cases w <;> decide
  simp only [h65535, true_and]

lemma testBit_of_and_eq {m g : ℕ} (h : m &&& g = m) {w : ℕ} (hw : m.testBit w = true) :
    g.testBit w = true := by
  rw [← h, Nat.testBit_and, Bool.and_eq_true] at hw
  exact hw.2

lemma antiMask_testBit (m : ℕ) (w : Fin 16) : (antiMask m).testBit w = m.testBit (anti w) := by
  rw [antiMask, Gale.testBit_maskOf]
  simp [anti, w.2]

lemma masksOK_spec {gens ms : List ℕ} (h : masksOK gens ms = true) {m : ℕ} (hm : m ∈ ms) :
    m ≠ 0 ∧ m < 2 ^ 16 ∧ (∃ g ∈ gens, m &&& g = m) ∧ andOver gens m = m := by
  unfold masksOK at h
  rw [List.all_eq_true] at h
  have h1 := h m hm
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, List.any_eq_true,
    beq_iff_eq] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

lemma recMasks_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true) {a : Fin 4 → ℝ} {facts : Facts}
    (h : F.Holds a facts) {rs : List ℕ} {m : ℕ} (hm : m ∈ F.recMasks facts rs) :
    ∃ y : E5, F.IsPV a y ∧ 0 < y 4 ∧ ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ m.testBit w = true) := by
  obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hm
  split_ifs at hi with hil
  have hmem : F.recs.getD i default ∈ F.recs := by
    rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem _
  exact F.rec_sound (hrecs _ hmem) hi h

/-- Every generator of a count leaf is the tight mask of a polar point. -/
lemma countGens_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true)
    (hvf : ∀ v ∈ F.vf, F.vfOK v = true) {a : Fin 4 → ℝ} (hinj : Function.Injective (F.pt a))
    (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) {facts : Facts} (h : F.Holds a facts)
    (rs : List ℕ) : ∀ g ∈ F.countGens (F.recMasks facts rs), ∃ y : E5, F.IsPV a y ∧
      ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ g.testBit w = true) := by
  intro g hg
  unfold countGens at hg
  rcases List.mem_append.1 hg with hg | hg
  · rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hg
      obtain ⟨y, hy, -, hiff⟩ := F.vf_sound (hvf v hv) hinj hspan
      exact ⟨y, hy, hiff⟩
    · obtain ⟨y, hy, -, hiff⟩ := F.recMasks_sound hrecs h hg
      exact ⟨y, hy, hiff⟩
  · obtain ⟨m0, hm0, rfl⟩ := List.mem_map.1 hg
    obtain ⟨y, hy, -, hiff⟩ := F.recMasks_sound hrecs h hm0
    refine ⟨-y, IsPV.neg F hy, fun w => ?_⟩
    have h1 : ⟪F.pt a w, -y⟫ = ⟪F.pt a (anti w), y⟫ := by
      rw [F.pt_anti, inner_neg_left, inner_neg_right]
    rw [h1, hiff (anti w), antiMask_testBit]

/-- **A count leaf gives `242` tight sets.** -/
lemma count_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true) (hvf : ∀ v ∈ F.vf, F.vfOK v = true)
    {a : Fin 4 → ℝ} (hinj : Function.Injective (F.pt a))
    (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) {facts : Facts}
    (h : F.Holds a facts) {rs ms : List ℕ} {top : Bool}
    (hw : F.walk top facts (.count rs ms) = true) : F.CountGoalF a := by
  classical
  simp only [walk] at hw
  have hc := hw
  unfold countOK at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hmasks, hsort⟩, h242⟩ := hc
  obtain ⟨gens, hgens⟩ : ∃ gens, gens = F.countGens (F.recMasks facts rs) := ⟨_, rfl⟩
  rw [← hgens] at hmasks
  have hgen := F.countGens_sound hrecs hvf hinj hspan h rs
  rw [← hgens] at hgen
  choose! Y hY using hgen
  -- the polar points of the generators containing a mask, and its tight set
  obtain ⟨Zs, hZs⟩ : ∃ Zs : ℕ → Finset E5,
      Zs = fun m => ((gens.filter fun g => m &&& g == m).map Y).toFinset := ⟨_, rfl⟩
  have hmemZ : ∀ m y, y ∈ Zs m ↔ ∃ g ∈ gens, m &&& g = m ∧ Y g = y := by
    intro m y
    simp only [hZs, List.mem_toFinset, List.mem_map, List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨g, ⟨hg, hmg⟩, rfl⟩; exact ⟨g, hg, hmg, rfl⟩
    · rintro ⟨g, hg, hmg, rfl⟩; exact ⟨g, ⟨hg, hmg⟩, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Set E5,
      T = fun m => {x ∈ range (F.pt a) | ∀ y ∈ Zs m, ⟪x, y⟫ = 1} := ⟨_, rfl⟩
  have hmemT : ∀ m ∈ ms, ∀ w : Fin 16, F.pt a w ∈ T m ↔ m.testBit w = true := by
    intro m hm w
    obtain ⟨-, -, -, hand⟩ := masksOK_spec hmasks hm
    rw [hT]
    constructor
    · rintro ⟨-, hx⟩
      rw [← hand, andOver_testBit gens m w.2]
      intro g hg hmg
      exact ((hY g hg).2 w).1 (hx (Y g) ((hmemZ m _).2 ⟨g, hg, hmg, rfl⟩))
    · intro hb
      refine ⟨⟨w, rfl⟩, fun y hy => ?_⟩
      obtain ⟨g, hg, hmg, rfl⟩ := (hmemZ m y).1 hy
      exact ((hY g hg).2 w).2 (testBit_of_and_eq hmg hb)
  have hinjT : ∀ m ∈ ms, ∀ m' ∈ ms, T m = T m' → m = m' := by
    intro m hm m' hm' he
    apply mask_ext (masksOK_spec hmasks hm).2.1 (masksOK_spec hmasks hm').2.1
    intro w hw
    have h1 := hmemT m hm ⟨w, hw⟩
    have h2 := hmemT m' hm' ⟨w, hw⟩
    rw [he] at h1
    exact Bool.eq_iff_iff.2 (h1.symm.trans h2)
  refine ⟨(ms.map T).toFinset, ?_, fun t ht => ?_⟩
  · rw [List.toFinset_card_of_nodup ((sortedLT_nodup hsort).map_on hinjT), List.length_map]
    exact h242
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 ht)
    obtain ⟨hm0, h16, ⟨g, hg, hmg⟩, -⟩ := masksOK_spec hmasks hm
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero hm0
    have hi16 : i < 16 := by
      by_contra hge
      have : m < 2 ^ i := lt_of_lt_of_le h16 (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [Nat.testBit_eq_false_of_lt this] at hi
      exact Bool.false_ne_true hi
    refine ⟨⟨_, (hmemT m hm ⟨i, hi16⟩).2 hi⟩, Zs m, ⟨Y g, (hmemZ m _).2 ⟨g, hg, hmg, rfl⟩⟩,
      fun y hy => ?_, by rw [hT]⟩
    obtain ⟨g', hg', -, rfl⟩ := (hmemZ m y).1 hy
    exact (hY g' hg').1

/-- **A leaf gives `need` upper polar vertices.** -/
lemma leaf_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true) {a : Fin 4 → ℝ} {facts : Facts}
    (h : F.Holds a facts) {rs : List ℕ} {top : Bool} (hw : F.walk top facts (.leaf rs) = true) :
    ∃ U : Finset E5, F.need ≤ U.card ∧ ∀ y ∈ U, F.IsPV a y ∧ 0 < y 4 := by
  classical
  simp only [walk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨hlen, hneed⟩, hsort⟩ := hw
  set g : ℕ → Option ℕ := fun i => if i < F.recs.length then recMask facts (F.recs.getD i default)
    else none with hg
  set ms := rs.filterMap g with hms
  -- every mask of the leaf comes from a valid record
  have hfrom : ∀ m ∈ ms, ∃ y : E5, F.IsPV a y ∧ 0 < y 4 ∧
      ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ m.testBit w = true) := by
    intro m hm
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hm
    simp only [hg] at hi
    split_ifs at hi with hil
    have hmem : F.recs.getD i default ∈ F.recs := by
      rw [List.getD_eq_getElem _ _ hil]; exact List.getElem_mem _
    exact F.rec_sound (hrecs _ hmem) hi h
  have hlt : ∀ m ∈ ms, m < 2 ^ 16 := by
    intro m hm
    obtain ⟨i, -, hi⟩ := List.mem_filterMap.1 hm
    simp only [hg] at hi
    split_ifs at hi
    exact recMask_lt hi
  choose! Y hY using hfrom
  refine ⟨(ms.map Y).toFinset, ?_, fun y hy => ?_⟩
  · have hnd : ms.Nodup := sortedLT_nodup hsort
    have hinjY : ∀ m ∈ ms, ∀ m' ∈ ms, Y m = Y m' → m = m' := by
      intro m hm m' hm' he
      apply mask_ext (hlt m hm) (hlt m' hm')
      intro w hw
      have h1 := (hY m hm).2.2 ⟨w, hw⟩
      have h2 := (hY m' hm').2.2 ⟨w, hw⟩
      rw [he] at h1
      simp only at h1 h2
      cases hb : m.testBit w <;> cases hb' : m'.testBit w <;> simp_all
    rw [List.toFinset_card_of_nodup (hnd.map_on hinjY), List.length_map]
    omega
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
    exact ⟨(hY m hm).1, (hY m hm).2.1⟩

/-- **A rank-5 leaf gives a fifth full normal.** -/
lemma rank5_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true) {a : Fin 4 → ℝ} {facts : Facts}
    (h : F.Holds a facts) {r : ℕ} {top : Bool} (hw : F.walk top facts (.rank5 r) = true) :
    ∃ y : E5, (∀ w, ⟪F.pt a w, y⟫ = 1 ∨ ⟪F.pt a w, y⟫ = -1) ∧ 0 < y 4 := by
  simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hr, hm⟩ := hw
  split at hm
  · rename_i m hrm
    have hmem : F.recs.getD r default ∈ F.recs := by
      rw [List.getD_eq_getElem _ _ hr]; exact List.getElem_mem _
    obtain ⟨y, hpv, hy4, hiff⟩ := F.rec_sound (hrecs _ hmem) hrm h
    refine ⟨y, fun w => ?_, hy4⟩
    simp only [fullMask, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at hm
    by_cases hb : m.testBit w = true
    · exact Or.inl ((hiff w).2 hb)
    · right
      have hanti : m.testBit (anti w) = true := by
        by_cases h8 : (w : ℕ) < 8
        · have := hm w h8
          simp only [anti, Nat.mod_eq_of_lt (show (w : ℕ) + 8 < 16 by omega)]
          cases hc : m.testBit (w + 8) <;> simp_all
        · have := hm (w - 8) (by omega)
          simp only [anti]
          rw [show ((w : ℕ) + 8) % 16 = w - 8 by omega]
          rw [show (w : ℕ) - 8 + 8 = w by omega] at this
          cases hc : m.testBit (w - 8) <;> simp_all
      have := (hiff (anti w)).2 hanti
      rw [F.pt_anti, inner_neg_left] at this
      linarith
  · simp at hm

/-- The last unit vector. -/
noncomputable def e4 : E5 := EuclideanSpace.single 4 1

lemma inner_pt_e4 (a : Fin 4 → ℝ) (w : Fin 16) : ⟪F.pt a w, e4⟫ = (F.z w).ev a := by
  rw [F.inner_pt]; simp [e4]

/-- **The walk is sound** (subtrees not allowed). -/
theorem walk_sound_aux (hrecs : ∀ r ∈ F.recs, F.recOK r = true)
    (hvf : ∀ v ∈ F.vf, F.vfOK v = true) {a : Fin 4 → ℝ}
    (hinj : Function.Injective (F.pt a)) (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) :
    ∀ (node : Node) (facts : Facts), F.walk false facts node = true → F.Holds a facts →
      F.LeafGoal a := by
  intro node
  induction node with
  | leaf rs => intro facts hw h; exact Or.inl (F.leaf_sound hrecs h hw)
  | rank5 r => intro facts hw h; exact Or.inr (Or.inl (F.rank5_sound hrecs h hw))
  | count rs ms => intro facts hw h; exact Or.inr (Or.inr (F.count_sound hrecs hvf hinj hspan h hw))
  | branch p n zr ps ihn ihz ihp =>
    intro facts hw h
    simp only [walk, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨⟨-, -⟩, hn⟩, hz⟩, hp⟩ := hw
    rcases signIs_trichotomy ((F.plane p).ev a) with hs | hs | hs
    · exact ihn _ hn (F.holds_append h hs)
    · exact ihz _ hz (F.holds_append h hs)
    · exact ihp _ hp (F.holds_append h hs)
  | refuted cert =>
    intro facts hw h
    exact absurd (F.refutes_sound hw h) id
  | invalid w w' =>
    intro facts hw h
    exfalso
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, beq_iff_eq,
      Bool.or_eq_true, List.any_eq_true] at hw
    obtain ⟨⟨⟨⟨hw16, hw'16⟩, hww⟩, hq⟩, hz⟩ := hw
    have hze : (F.z w).ev a = (F.z w').ev a := by
      rcases hz with hz | ⟨t, ht, ht0, hpl⟩
      · have := Z4.ev_of_isZero hz a
        simp only [Z4.ev_add, Z4.ev_neg] at this
        linarith
      · have hs := h t ht
        rw [ht0] at hs
        have h0 := hs.eq_zero
        rcases hpl with hpl | hpl
        · rw [hpl] at h0; simp only [Z4.ev_add, Z4.ev_neg] at h0; linarith
        · rw [hpl] at h0; simp only [Z4.ev_neg, Z4.ev_add] at h0; linarith
    have : F.pt a ⟨w, hw16⟩ = F.pt a ⟨w', hw'16⟩ := by
      simp only [pt]
      rw [show F.q (⟨w, hw16⟩ : Fin 16) = F.q (⟨w', hw'16⟩ : Fin 16) from hq]
      simp only [Fin.val_mk]
      rw [hze]
    exact hww (congrArg Fin.val (hinj this))
  | zero p0 p1 p2 p3 C D =>
    intro facts hw h
    exfalso
    have ha := F.eq_zero_of_zero_node h hw
    have := hspan e4 fun w => by rw [F.inner_pt_e4, ha]; simp [Z4.ev]
    have h1 : (e4 : E5) 4 = 1 := by simp [e4]
    rw [this] at h1
    simp at h1
  | implied p s cert den child ih =>
    intro facts hw h
    simp only [walk, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨-, -⟩, hi⟩, hc⟩ := hw
    exact ih _ hc (F.holds_append h (F.impliesSign_sound hi h))
  | sub k =>
    intro facts hw _
    simp [walk] at hw

/-- **The walk is sound** (with separately checked subtrees). -/
theorem walk_sound (hrecs : ∀ r ∈ F.recs, F.recOK r = true) (hvf : ∀ v ∈ F.vf, F.vfOK v = true)
    (hsubs : ∀ k < F.subs.length, F.subOK k = true) {a : Fin 4 → ℝ}
    (hinj : Function.Injective (F.pt a)) (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) :
    ∀ (node : Node) (facts : Facts), F.walk true facts node = true → F.Holds a facts →
      F.LeafGoal a := by
  intro node
  induction node with
  | leaf rs => intro facts hw h; exact Or.inl (F.leaf_sound hrecs h hw)
  | rank5 r => intro facts hw h; exact Or.inr (Or.inl (F.rank5_sound hrecs h hw))
  | count rs ms => intro facts hw h; exact Or.inr (Or.inr (F.count_sound hrecs hvf hinj hspan h hw))
  | branch p n zr ps ihn ihz ihp =>
    intro facts hw h
    simp only [walk, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨⟨-, -⟩, hn⟩, hz⟩, hp⟩ := hw
    rcases signIs_trichotomy ((F.plane p).ev a) with hs | hs | hs
    · exact ihn _ hn (F.holds_append h hs)
    · exact ihz _ hz (F.holds_append h hs)
    · exact ihp _ hp (F.holds_append h hs)
  | refuted cert =>
    intro facts hw h
    exact absurd (F.refutes_sound hw h) id
  | invalid w w' =>
    intro facts hw h
    exact F.walk_sound_aux hrecs hvf hinj hspan (.invalid w w') facts (by simpa [walk] using hw) h
  | zero p0 p1 p2 p3 C D =>
    intro facts hw h
    exact F.walk_sound_aux hrecs hvf hinj hspan (.zero p0 p1 p2 p3 C D) facts
      (by simpa [walk] using hw) h
  | implied p s cert den child ih =>
    intro facts hw h
    simp only [walk, Bool.and_eq_true] at hw
    obtain ⟨⟨⟨-, -⟩, hi⟩, hc⟩ := hw
    exact ih _ hc (F.holds_append h (F.impliesSign_sound hi h))
  | sub k =>
    intro facts hw h
    simp only [walk, Bool.and_eq_true, Bool.true_and, decide_eq_true_eq, beq_iff_eq] at hw
    obtain ⟨hk, hf⟩ := hw
    have hs := hsubs k hk
    unfold subOK at hs
    rw [hf] at hs
    exact F.walk_sound_aux hrecs hvf hinj hspan _ facts hs h

/-- Vertical facet masks are below `2¹⁶`. -/
lemma vf_mask_lt {v : VFacet} (hv : F.vfOK v = true) : v.mask < 2 ^ 16 := by
  unfold vfOK at hv
  simp only [Bool.and_eq_true, beq_iff_eq] at hv
  rw [hv.1.2]
  exact maskOf_lt16 _

/-- **Soundness of a family**: at least `N` polar points with spanning tight sets, a fifth
full normal, or `242` distinct nonempty tight sets. -/
theorem sound_pvN {N : ℕ} (hc : F.checkN N = true) (hrecs : ∀ r ∈ F.recs, F.recOK r = true)
    (hsubs : ∀ k < F.subs.length, F.subOK k = true) {a : Fin 4 → ℝ}
    (hinj : Function.Injective (F.pt a)) (hspan : ∀ u : E5, (∀ w, ⟪F.pt a w, u⟫ = 0) → u = 0) :
    (∃ S : Finset E5, N ≤ S.card ∧ ∀ y ∈ S, F.IsPV a y) ∨
    (∃ y : E5, (∀ w, ⟪F.pt a w, y⟫ = 1 ∨ ⟪F.pt a w, y⟫ = -1) ∧ y 4 ≠ 0) ∨ F.CountGoalF a := by
  classical
  unfold checkN at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hvf⟩, hvsort⟩, h19⟩, hwalk⟩ := hc
  have hgoal := F.walk_sound hrecs hvf hsubs hinj hspan F.tree [] hwalk (fun t ht => by simp at ht)
  rcases hgoal with ⟨U, hU, hUpv⟩ | ⟨y, hy, hy4⟩ | hcount
  · left
    have hvfrom : ∀ v ∈ F.vf, ∃ y : E5, F.IsPV a y ∧ y 4 = 0 ∧
        ∀ w : Fin 16, (⟪F.pt a w, y⟫ = 1 ↔ v.mask.testBit w = true) :=
      fun v hv => F.vf_sound (hvf v hv) hinj hspan
    choose! Yv hYv using hvfrom
    set V := (F.vf.map Yv).toFinset with hVdef
    have hVcard : V.card = F.vf.length := by
      have hnd : (F.vf.map VFacet.mask).Nodup := sortedLT_nodup hvsort
      have hnd' : F.vf.Nodup := List.Nodup.of_map _ hnd
      have hinjY : ∀ v ∈ F.vf, ∀ v' ∈ F.vf, Yv v = Yv v' → v = v' := by
        intro v hv v' hv' he
        have hmask : v.mask = v'.mask := by
          apply mask_ext (F.vf_mask_lt (hvf v hv)) (F.vf_mask_lt (hvf v' hv'))
          intro w hw
          have h1 := (hYv v hv).2.2 ⟨w, hw⟩
          have h2 := (hYv v' hv').2.2 ⟨w, hw⟩
          rw [he] at h1
          simp only at h1 h2
          cases hb : v.mask.testBit w <;> cases hb' : v'.mask.testBit w <;> simp_all
        exact List.inj_on_of_nodup_map hnd hv hv' hmask
      rw [hVdef, List.toFinset_card_of_nodup (hnd'.map_on hinjY), List.length_map]
    set S := V ∪ U ∪ U.image Neg.neg with hSdef
    have hpv : ∀ y ∈ S, F.IsPV a y := by
      intro y hy
      rcases Finset.mem_union.1 hy with hy | hy
      · rcases Finset.mem_union.1 hy with hy | hy
        · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hy)
          exact (hYv v hv).1
        · exact (hUpv y hy).1
      · obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hy
        exact IsPV.neg F (hUpv y' hy').1
    refine ⟨S, ?_, hpv⟩
    · have hd1 : Disjoint V U := by
        rw [Finset.disjoint_left]
        intro y hyV hyU
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hyV)
        have := (hUpv _ hyU).2
        rw [(hYv v hv).2.1] at this
        exact lt_irrefl _ this
      have hd2 : Disjoint (V ∪ U) (U.image Neg.neg) := by
        rw [Finset.disjoint_left]
        intro y hy hyn
        obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hyn
        have hneg : (-y') 4 < 0 := by
          have := (hUpv y' hy').2
          simp only [PiLp.neg_apply]
          linarith
        rcases Finset.mem_union.1 hy with hyV | hyU
        · obtain ⟨v, hv, hve⟩ := List.mem_map.1 (List.mem_toFinset.1 hyV)
          have := (hYv v hv).2.1
          rw [hve] at this
          linarith
        · have := (hUpv _ hyU).2
          linarith
      rw [hSdef, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_image_of_injective _ neg_injective, hVcard]
      omega
  · exact Or.inr (Or.inl ⟨y, hy, hy4.ne'⟩)
  · exact Or.inr (Or.inr hcount)

/-- **Records from chunked checks.** -/
lemma recs_of_chunks (n : ℕ) (h : ∀ c < n, F.recsOK (40 * c) 40 = true)
    (hn : F.recs.length ≤ 40 * n) : ∀ r ∈ F.recs, F.recOK r = true := by
  intro r hr
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hr
  have hc : i / 40 < n := by omega
  have hchunk := h (i / 40) hc
  unfold recsOK at hchunk
  rw [List.all_eq_true] at hchunk
  apply hchunk
  have hmem : F.recs[i] = ((F.recs.drop (40 * (i / 40))).take 40)[i % 40]'(by
      simp only [List.length_take, List.length_drop]; omega) := by
    simp only [List.getElem_take, List.getElem_drop]
    congr 1
    omega
  rw [hmem]
  exact List.getElem_mem _

end Family

end Kalai5.A16
