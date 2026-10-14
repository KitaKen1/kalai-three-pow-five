import Kalai5.Cube5.Check
import Kalai5.FullPrism.Count
import Kalai5.Small.Model

/-!
# Cube polytopes: soundness of the face certificates

`faces_of_cert`: if a representative `R` (eight classes) passes `RepCert.ok` with witnesses, the
cube polytope `conv {±rep c : c ∈ R}` has at least `243` nonempty faces.  Each witness `z / d`
satisfies `|⟪z / d, rep c⟫| ≤ 1` at the eight classes, so the points where it equals `1` form a face
index (`isFaceIdx_idxOf`); that index is the claimed mask; distinct masks give distinct faces.
-/

namespace Kalai5.Cube5

open Set Module Kalai5.Gale Kalai5.FullPrism

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The real point with integer coordinates `q j` (`j < 5`). -/
noncomputable def vecZ (q : ℕ → ℤ) : E5 := (WithLp.equiv 2 (Fin 5 → ℝ)).symm fun j => (q j : ℝ)

@[simp] lemma vecZ_apply (q : ℕ → ℤ) (j : Fin 5) : vecZ q j = (q j : ℝ) := rfl

/-- The representative of class `c`. -/
noncomputable def repPt (c : ℕ) : E5 := vecZ (rep c)

/-- The eight points of a representative. -/
noncomputable def pts (R : List ℕ) (v : Fin 8) : E5 := repPt (R.getD v 0)

lemma sum5_cast (f : ℕ → ℤ) : (sum5 f : ℝ) = ∑ j : Fin 5, (f j : ℝ) := by
  simp [sum5, Fin.sum_univ_five]

lemma inner_vecZ (z q : ℕ → ℤ) : ⟪vecZ z, vecZ q⟫ = ((sum5 fun j => z j * q j : ℤ) : ℝ) := by
  rw [inner_eq_sum, sum5_cast]
  push_cast
  rfl

/-! ### Witnesses -/

/-- The functional `z / d` of a witness. -/
noncomputable def witVec (w : Wit) : E5 := ((w.d : ℝ)⁻¹) • vecZ (fun j => w.z.getD j 0)

lemma inner_witVec (R : List ℕ) (w : Wit) (v : Fin 8) :
    ⟪witVec w, pts R v⟫ = (val R w v : ℝ) / w.d := by
  rw [witVec, real_inner_smul_left, pts, repPt, inner_vecZ, val]
  ring

lemma witOK_spec {R : List ℕ} {w : Wit} (h : witOK R w = true) :
    0 < w.d ∧ (∀ v : Fin 8, |val R w v| ≤ (w.d : ℤ)) ∧ w.m = witMask R w := by
  simp only [witOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact ⟨h.1.1, fun v => h.1.2 v v.2, h.2⟩

lemma abs_inner_witVec_le {R : List ℕ} {w : Wit} (h : witOK R w = true) (v : Fin 8) :
    |⟪witVec w, pts R v⟫| ≤ 1 := by
  obtain ⟨hd, hv, -⟩ := witOK_spec h
  have hd' : (0 : ℝ) < w.d := by exact_mod_cast hd
  rw [inner_witVec, abs_div, abs_of_pos hd', div_le_one hd']
  exact_mod_cast hv v

lemma maskOf_lt (p : ℕ → Bool) : maskOf 16 p < 2 ^ 16 := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_maskOf]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, not_lt]
  exact Or.inl hi

/-- **The face index of a witness is its mask.** -/
lemma idxOf_witVec {R : List ℕ} {w : Wit} (h : witOK R w = true) :
    idxOf (pts R) (witVec w) = ofMask 16 w.m := by
  obtain ⟨hd, -, hm⟩ := witOK_spec h
  have hd' : (w.d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  ext i
  rw [mem_ofMask, hm, witMask, testBit_maskOf]
  simp only [idxOf, Finset.mem_filter, Finset.mem_univ, true_and, i.2, decide_true, Bool.true_and]
  by_cases hi : (i : ℕ) < 8
  · have hpm : pm16 (pts R) i = pts R ⟨i, hi⟩ := by simp [pm16, hi]
    rw [hpm, inner_witVec, if_pos hi, div_eq_iff hd', one_mul, beq_iff_eq]
    exact_mod_cast Iff.rfl
  · have hpm : pm16 (pts R) i = -pts R ⟨i - 8, by omega⟩ := by simp [pm16, hi]
    rw [hpm, inner_neg_right, inner_witVec, if_neg hi, beq_iff_eq, neg_eq_iff_eq_neg,
      div_eq_iff hd', neg_one_mul]
    constructor
    · intro h; exact_mod_cast h
    · intro h; exact_mod_cast h

/-! ### Strictly increasing lists -/

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

/-! ### The face bound of a representative -/

/-- **A representative with witnesses has at least `243` faces.** -/
theorem faces_of_cert {R : List ℕ} {ws : List Wit} (hok : (RepCert.faces ws).ok R = true) :
    243 ≤ (faces (convexHull ℝ (range (pm16 (pts R))))).ncard := by
  classical
  simp only [RepCert.ok, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨-, hw⟩, hsort⟩, hnz⟩, hcount⟩ := hok
  have hlt : ∀ w ∈ ws, w.m < 2 ^ 16 := fun w hwm => by
    rw [(witOK_spec (hw w hwm)).2.2]; exact maskOf_lt _
  have hnd : (ws.map Wit.m).Nodup := sortedLT_nodup hsort
  have hnd' : (ws.map fun w => ofMask 16 w.m).Nodup := by
    have : (ws.map fun w => ofMask 16 w.m) = (ws.map Wit.m).map (ofMask 16) := by
      rw [List.map_map]; rfl
    rw [this]
    refine hnd.map_on fun a ha b hb hab => ?_
    obtain ⟨wa, hwa, rfl⟩ := List.mem_map.1 ha
    obtain ⟨wb, hwb, rfl⟩ := List.mem_map.1 hb
    exact ofMask_injOn (Finset.mem_coe.2 (Finset.mem_range.2 (hlt wa hwa)))
      (Finset.mem_coe.2 (Finset.mem_range.2 (hlt wb hwb))) hab
  -- no witness index is everything: `y_0` and `-y_0` cannot both have value `1`
  have hnuniv : ∀ w ∈ ws, ofMask 16 w.m ≠ Finset.univ := by
    intro w hwm heq
    have h0 : (0 : Fin 16) ∈ idxOf (pts R) (witVec w) := by
      rw [idxOf_witVec (hw w hwm), heq]; exact Finset.mem_univ _
    have h8 : (8 : Fin 16) ∈ idxOf (pts R) (witVec w) := by
      rw [idxOf_witVec (hw w hwm), heq]; exact Finset.mem_univ _
    simp only [idxOf, Finset.mem_filter, Finset.mem_univ, true_and] at h0 h8
    have e0 : pm16 (pts R) 0 = pts R 0 := by simp [pm16]
    have e8 : pm16 (pts R) 8 = -pts R 0 := by simp [pm16]
    rw [e0] at h0
    rw [e8, inner_neg_right, h0] at h8
    norm_num at h8
  set S : Finset (Finset (Fin 16)) := insert Finset.univ (ws.map fun w => ofMask 16 w.m).toFinset
    with hS
  have hcard : S.card = ws.length + 1 := by
    rw [hS, Finset.card_insert_of_notMem, List.toFinset_card_of_nodup hnd', List.length_map]
    rw [List.mem_toFinset]
    rintro h
    obtain ⟨w, hwm, hw'⟩ := List.mem_map.1 h
    exact hnuniv w hwm hw'
  have hle := le_ncard_faces (W := pm16 (pts R)) S fun F hF => by
    rcases Finset.mem_insert.1 hF with rfl | hF
    · exact ⟨Finset.univ_nonempty, isFaceIdx_univ⟩
    · obtain ⟨w, hwm, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hF)
      refine ⟨(ofMask_nonempty_iff (hlt w hwm)).2 (hnz w hwm), ?_⟩
      rw [← idxOf_witVec (hw w hwm)]
      exact isFaceIdx_idxOf fun j => abs_inner_witVec_le (hw w hwm) j
  omega

end Kalai5.Cube5
