import Kalai5.A16.Points

/-!
# A16: records give upper polar vertices

`rec_span`: the points of a record's 5-set span `ℝ⁵` (dependency `λ`, the nonzero form `sp`, and the
spanning certificate of the other four base points).  `rec_sound`: a record valid on the stratum
gives a polar point whose tight points span, with positive last coordinate, whose tight set is the
record's mask.
-/

namespace Kalai5.A16

open Set Kalai5.LemmaA

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- Scaling a sign. -/
lemma signIs_smul_int {x : ℝ} {s : ℤ} (h : SignIs x s) {c : ℤ} (hc : c ≠ 0) :
    SignIs ((c : ℝ) * x) (c.sign * s) := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · have hc' : (c : ℝ) < 0 := by exact_mod_cast hneg
    rw [Int.sign_eq_neg_one_of_neg hneg]
    rcases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact Or.inr (Or.inr ⟨by norm_num, by nlinarith⟩)
    · exact Or.inr (Or.inl ⟨by norm_num, by rw [hx]; ring⟩)
    · exact Or.inl ⟨by norm_num, by nlinarith⟩
  · have hc' : (0 : ℝ) < c := by exact_mod_cast hpos
    rw [Int.sign_eq_one_of_pos hpos]
    rcases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact Or.inl ⟨by norm_num, by nlinarith⟩
    · exact Or.inr (Or.inl ⟨by norm_num, by rw [hx]; ring⟩)
    · exact Or.inr (Or.inr ⟨by norm_num, by nlinarith⟩)

lemma signIs_ne_zero {x : ℝ} {s : ℤ} (h : SignIs x s) (hs : s ≠ 0) : x ≠ 0 := by
  rcases h with ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
  · exact hx.ne
  · exact absurd rfl hs
  · exact hx.ne'

namespace Family

variable (F : Family)

/-- The base points of a record's basis (the 5-set without `k₅`). -/
lemma basis_getD (T : List ℕ) (k5 : ℕ) (hk5 : k5 < 5) (k : ℕ) (hk : k < 4) :
    (((List.range 5).filter (· != k5)).map fun i => F.q (T.getD i 0)).getD k [] =
      F.q (T.getD (if k < k5 then k else k + 1) 0) := by
  interval_cases k5 <;> interval_cases k <;> rfl

/-- **The points of a record's 5-set span.** -/
lemma rec_span {r : FRec} (hok : F.recOK r = true) {a : Fin 4 → ℝ}
    (hsp : (F.plane r.sp.1).ev a ≠ 0) {v : E5}
    (hv : ∀ k < 5, ∀ h : r.T.getD k 0 < 16, ⟪F.pt a ⟨r.T.getD k 0, h⟩, v⟫ = 0) : v = 0 := by
  obtain ⟨hl, -, hlt, -, -, -, -, -, hll, hlam, hk5, hlk, hsc, hspf, hsp2⟩ := F.recOK_spec hok
  have hT : ∀ k < 5, r.T.getD k 0 < 16 := fun k hk =>
    hlt _ (by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hr : List.range 5 = [0, 1, 2, 3, 4] := rfl
  -- the inner products with the five points
  have e : ∀ k < 5, dotR (F.q (r.T.getD k 0)) (fun j => v (Fin.castSucc j)) +
      (F.z (r.T.getD k 0)).ev a * v 4 = 0 := by
    intro k hk
    have := hv k hk (hT k hk)
    rwa [dotR_q] at this
  -- `v 4 = 0` from the dependency
  have hv4 : v 4 = 0 := by
    have hsum := Z4.eq_of_ev hspf a
    simp only [hr, List.foldl_cons, List.foldl_nil, Z4.ev_add, Z4.ev_smul, Z4.ev_zero, zero_add]
      at hsum
    have hdep : ∀ j < 4, (r.lam.getD 0 0 * (F.q (r.T.getD 0 0)).getD j 0 +
        r.lam.getD 1 0 * (F.q (r.T.getD 1 0)).getD j 0 + r.lam.getD 2 0 * (F.q (r.T.getD 2 0)).getD j 0 +
        r.lam.getD 3 0 * (F.q (r.T.getD 3 0)).getD j 0 +
        r.lam.getD 4 0 * (F.q (r.T.getD 4 0)).getD j 0 : ℝ) = 0 := by
      intro j hj
      have := hlam j hj
      simp only [hr, List.foldl_cons, List.foldl_nil, zero_add] at this
      exact_mod_cast this
    have d0 := hdep 0 (by norm_num); have d1 := hdep 1 (by norm_num)
    have d2 := hdep 2 (by norm_num); have d3 := hdep 3 (by norm_num)
    have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num); have e2 := e 2 (by norm_num)
    have e3 := e 3 (by norm_num); have e4 := e 4 (by norm_num)
    simp only [dotR] at e0 e1 e2 e3 e4
    have key : ((r.sp.2 : ℝ) * (F.plane r.sp.1).ev a) * v 4 = 0 := by
      rw [← hsum]
      linear_combination (r.lam.getD 0 0 : ℝ) * e0 + (r.lam.getD 1 0 : ℝ) * e1 +
        (r.lam.getD 2 0 : ℝ) * e2 + (r.lam.getD 3 0 : ℝ) * e3 + (r.lam.getD 4 0 : ℝ) * e4 -
        v (Fin.castSucc 0) * d0 - v (Fin.castSucc 1) * d1 - v (Fin.castSucc 2) * d2 -
        v (Fin.castSucc 3) * d3
    have hne : (r.sp.2 : ℝ) * (F.plane r.sp.1).ev a ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hsp2) hsp
    exact (mul_eq_zero.1 key).resolve_left hne
  -- the first four coordinates from the spanning certificate
  have h4 : (fun j : Fin 4 => v (Fin.castSucc j)) = 0 := by
    refine spanCert_sound hsc fun k hk => ?_
    rw [basis_getD F r.T r.k5 hk5 k hk]
    have hk' : (if k < r.k5 then k else k + 1) < 5 := by split_ifs <;> omega
    have := e _ hk'
    rwa [hv4, mul_zero, add_zero] at this
  ext j
  fin_cases j
  · exact congrFun h4 0
  · exact congrFun h4 1
  · exact congrFun h4 2
  · exact congrFun h4 3
  · exact hv4

/-- What a valid record mask gives. -/
lemma recMask_spec {facts : Facts} {r : FRec} {m : ℕ} (hm : recMask facts r = some m) :
    ∃ so ss : ℤ, factOf facts r.o.1 = some so ∧ factOf facts r.sp.1 = some ss ∧
      r.o.2.sign * so ≠ 0 ∧ ss ≠ 0 ∧ r.o.2.sign * so * r.c4 < 0 ∧
      (∀ w < r.ent.length, entSign facts (r.ent.getD w (none, 0)) = some 0 ∨
        entSign facts (r.ent.getD w (none, 0)) = some (r.o.2.sign * so)) ∧
      m = Gale.maskOf 16 fun w => (r.ent.map (entSign facts)).getD w none == some 0 := by
  unfold recMask at hm
  split at hm
  · rename_i so ss hso hss
    simp only at hm
    split_ifs at hm with h1 h2
    simp only [Option.some.injEq] at hm
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, Bool.or_eq_true, beq_iff_eq] at h2
    refine ⟨so, ss, hso, hss, ?_, ?_, ?_, fun w hw => ?_, hm.symm⟩
    · intro h0; exact h1 (Or.inl (Or.inl h0))
    · intro h0; exact h1 (Or.inl (Or.inr h0))
    · by_contra hc; push_neg at hc; exact h1 (Or.inr (by simpa [not_lt] using hc))
    · rw [List.getD_eq_getElem _ _ hw]
      exact h2 _ (List.getElem_mem hw)
  · simp at hm

end Family

end Kalai5.A16
