import Kalai5.A16.Facts
import Kalai5.Small.Model

/-!
# A16: the points of a family and records as polar vertices

`pt a w = (q_w, ζ_w · a)`; `IsPV a y`: `y` is in the polar of the sixteen points and the tight points
span (the hypotheses of L2).  `rec_sound`: a record valid on the stratum gives such a `y` with
positive last coordinate whose tight set is the record's mask.
-/

namespace Kalai5.A16

open Set Kalai5.LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace Family

variable (F : Family)

/-- The sixteen points `v_w(a)`. -/
noncomputable def pt (a : Fin 4 → ℝ) (w : Fin 16) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![((F.q w).getD 0 0 : ℝ), ((F.q w).getD 1 0 : ℝ), ((F.q w).getD 2 0 : ℝ),
      ((F.q w).getD 3 0 : ℝ), (F.z w).ev a]

lemma inner_pt (a : Fin 4 → ℝ) (w : Fin 16) (y : E5) :
    ⟪F.pt a w, y⟫ = ((F.q w).getD 0 0 : ℝ) * y 0 + ((F.q w).getD 1 0 : ℝ) * y 1 +
      ((F.q w).getD 2 0 : ℝ) * y 2 + ((F.q w).getD 3 0 : ℝ) * y 3 + (F.z w).ev a * y 4 := by
  rw [inner_eq_sum, Fin.sum_univ_five]
  simp [pt]

/-- `y` is a polar point of the sixteen points whose tight points span. -/
def IsPV (a : Fin 4 → ℝ) (y : E5) : Prop :=
  (∀ w, ⟪F.pt a w, y⟫ ≤ 1) ∧ ∀ v : E5, (∀ w, ⟪F.pt a w, y⟫ = 1 → ⟪F.pt a w, v⟫ = 0) → v = 0

lemma getD_neg (l : List ℤ) (i : ℕ) : (l.map (- ·)).getD i 0 = -(l.getD i 0) := by
  by_cases hi : i < l.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]; simp
  · rw [List.getD_eq_default _ _ (by simpa using hi), List.getD_eq_default _ _ (by omega)]; simp

/-- **Antipodes.** -/
lemma pt_add8 (a : Fin 4 → ℝ) (w : Fin 8) :
    F.pt a ⟨w + 8, by omega⟩ = -F.pt a ⟨w, by omega⟩ := by
  have hq : F.q (w + 8) = (F.q w).map (- ·) := by
    simp [q, show ¬ ((w : ℕ) + 8 < 8) by omega, w.2]
  have hz : F.z (w + 8) = (F.z w).neg := by
    simp [z, show ¬ ((w : ℕ) + 8 < 8) by omega, w.2]
  ext j
  fin_cases j <;> simp only [pt, hq, hz, getD_neg, Z4.ev_neg] <;> simp

/-- The real dot product of the base point of `w` with the first four coordinates of `v`. -/
lemma dotR_q (a : Fin 4 → ℝ) (w : Fin 16) (v : E5) :
    ⟪F.pt a w, v⟫ = dotR (F.q w) (fun j => v (Fin.castSucc j)) + (F.z w).ev a * v 4 := by
  rw [inner_pt]
  simp only [dotR]
  rfl

/-! ### Records -/

/-- What `recOK` guarantees. -/
lemma recOK_spec {r : FRec} (h : F.recOK r = true) :
    r.T.length = 5 ∧ r.T.Nodup ∧ (∀ t ∈ r.T, t < 16) ∧ r.ent.length = 16 ∧
    (∀ w < 16, F.recValue r w = F.entForm (r.ent.getD w (none, 0))) ∧
    (∀ t ∈ r.T, (r.ent.getD t (some 0, 0)).1 = none) ∧
    r.C5 = Z4.smul r.o.2 (F.plane r.o.1) ∧ r.o.2 ≠ 0 ∧ r.lam.length = 5 ∧
    (∀ j < 4, (List.range 5).foldl (fun acc k =>
      acc + r.lam.getD k 0 * (F.q (r.T.getD k 0)).getD j 0) 0 = 0) ∧
    r.k5 < 5 ∧ r.lam.getD r.k5 0 ≠ 0 ∧
    spanCert (((List.range 5).filter (· != r.k5)).map fun k => F.q (r.T.getD k 0)) r.B r.D = true ∧
    (List.range 5).foldl (fun acc k => Z4.add acc (Z4.smul (r.lam.getD k 0) (F.z (r.T.getD k 0))))
      Z4.zero = Z4.smul r.sp.2 (F.plane r.sp.1) ∧ r.sp.2 ≠ 0 := by
  unfold recOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    bne_iff_ne, ne_eq, Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hl, hnd⟩, hlt⟩, hel⟩, hval⟩, hT⟩, hC5⟩, ho⟩, hll⟩, hlam⟩, hk5⟩, hlk⟩, hsc⟩,
    hsp⟩, hsp2⟩ := h
  exact ⟨hl, by simpa using hnd, hlt, hel, hval, hT, hC5, ho, hll, hlam, hk5, hlk, hsc, hsp, hsp2⟩

/-- The value of a record's functional at a point. -/
lemma recValue_ev (r : FRec) (a : Fin 4 → ℝ) (w : Fin 16) :
    (F.recValue r w).ev a = ((F.q w).getD 0 0 : ℝ) * (r.C.getD 0 Z4.zero).ev a +
      ((F.q w).getD 1 0 : ℝ) * (r.C.getD 1 Z4.zero).ev a +
      ((F.q w).getD 2 0 : ℝ) * (r.C.getD 2 Z4.zero).ev a +
      ((F.q w).getD 3 0 : ℝ) * (r.C.getD 3 Z4.zero).ev a + (r.c4 : ℝ) * (F.z w).ev a + r.C5.ev a := by
  simp only [recValue, Z4.ev_add, Z4.ev_smul]
  ring

/-- The gradient of a record's functional. -/
noncomputable def recGrad (r : FRec) (a : Fin 4 → ℝ) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![(r.C.getD 0 Z4.zero).ev a, (r.C.getD 1 Z4.zero).ev a, (r.C.getD 2 Z4.zero).ev a,
      (r.C.getD 3 Z4.zero).ev a, (r.c4 : ℝ)]

lemma inner_recGrad (r : FRec) (a : Fin 4 → ℝ) (w : Fin 16) :
    ⟪F.pt a w, recGrad r a⟫ + r.C5.ev a = (F.recValue r w).ev a := by
  rw [inner_pt, recValue_ev]
  simp only [recGrad]
  simp
  ring

/-- The sign of a recorded entry on the stratum. -/
lemma entSign_sound {a : Fin 4 → ℝ} {facts : Facts} (h : F.Holds a facts) {e : Option ℕ × ℤ}
    {s : ℤ} (he : entSign facts e = some s) : SignIs ((F.entForm e).ev a) s := by
  unfold entSign at he
  unfold entForm
  rcases hp : e.1 with _ | p
  · rw [hp] at he
    simp only [Option.some.injEq] at he
    subst he
    exact Or.inr (Or.inl ⟨rfl, by simp⟩)
  · rw [hp] at he
    simp only [Option.map_eq_some_iff] at he
    obtain ⟨s', hs', rfl⟩ := he
    have hsg := F.holds_of_factOf h hs'
    simp only [Z4.ev_smul]
    rcases lt_trichotomy e.2 0 with hneg | hzero | hpos
    · rcases hsg with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
      · refine Or.inr (Or.inr ⟨by simp [Int.sign_eq_neg_one_of_neg hneg], ?_⟩)
        have : (e.2 : ℝ) < 0 := by exact_mod_cast hneg
        nlinarith
      · exact Or.inr (Or.inl ⟨by simp, by rw [hx]; ring⟩)
      · refine Or.inl ⟨by simp [Int.sign_eq_neg_one_of_neg hneg], ?_⟩
        have : (e.2 : ℝ) < 0 := by exact_mod_cast hneg
        nlinarith
    · rw [hzero]; exact Or.inr (Or.inl ⟨by simp, by simp⟩)
    · rcases hsg with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
      · refine Or.inl ⟨by simp [Int.sign_eq_one_of_pos hpos], ?_⟩
        have : (0 : ℝ) < e.2 := by exact_mod_cast hpos
        nlinarith
      · exact Or.inr (Or.inl ⟨by simp, by rw [hx]; ring⟩)
      · refine Or.inr (Or.inr ⟨by simp [Int.sign_eq_one_of_pos hpos], ?_⟩)
        have : (0 : ℝ) < e.2 := by exact_mod_cast hpos
        nlinarith

end Family

end Kalai5.A16
