import Kalai5.LemmaA.Cert
import Kalai5.Gale.Closure

/-!
# Lemma A: soundness of the certificate checker

`Family.check_sound`: if `F.check = true`, then for every parameter `a ≠ 0` for which the fourteen
points `F.pt a` are distinct, `conv {F.pt a w}` has at least 243 nonempty faces.
-/

namespace Kalai5.LemmaA

open Set Module Kalai5.Gale

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- `u · a` for `u ∈ ℤ³`. -/
def Z3.dot (u : Z3) (a : Fin 3 → ℝ) : ℝ := (u.1 : ℝ) * a 0 + (u.2.1 : ℝ) * a 1 + (u.2.2 : ℝ) * a 2

@[simp] lemma Z3.dot_add (u v : Z3) (a : Fin 3 → ℝ) : (Z3.add u v).dot a = u.dot a + v.dot a := by
  simp only [Z3.add, Z3.dot]; push_cast; ring

@[simp] lemma Z3.dot_smul (c : ℤ) (u : Z3) (a : Fin 3 → ℝ) :
    (Z3.smul c u).dot a = c * u.dot a := by
  simp only [Z3.smul, Z3.dot]; push_cast; ring

@[simp] lemma Z3.dot_zero (a : Fin 3 → ℝ) : Z3.zero.dot a = 0 := by simp [Z3.zero, Z3.dot]

lemma Z3.eq_of_dot {u v : Z3} (h : u = v) (a : Fin 3 → ℝ) : u.dot a = v.dot a := by rw [h]

lemma foldl_dot {α : Type*} (g : α → Z3) (a : Fin 3 → ℝ) (l : List α) (acc : Z3) :
    (l.foldl (fun acc t => Z3.add acc (g t)) acc).dot a = acc.dot a + (l.map fun t => (g t).dot a).sum := by
  induction l generalizing acc with
  | nil => simp
  | cons t l ih => rw [List.foldl_cons, ih, Z3.dot_add, List.map_cons, List.sum_cons]; ring

/-- Signs. -/
def SignIs (x : ℝ) (s : ℤ) : Prop := (s = -1 ∧ x < 0) ∨ (s = 0 ∧ x = 0) ∨ (s = 1 ∧ 0 < x)

lemma signIs_trichotomy (x : ℝ) : SignIs x (-1) ∨ SignIs x 0 ∨ SignIs x 1 := by
  rcases lt_trichotomy x 0 with h | h | h
  · exact Or.inl (Or.inl ⟨rfl, h⟩)
  · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨rfl, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))

/-- `s · x > 0` for a strict sign, `x = 0` for sign `0`. -/
lemma SignIs.mul_pos {x : ℝ} {s : ℤ} (h : SignIs x s) (hs : s ≠ 0) : 0 < (s : ℝ) * x := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, -⟩ | ⟨rfl, h⟩
  · push_cast; linarith
  · exact absurd rfl hs
  · push_cast; linarith

lemma SignIs.eq_zero {x : ℝ} (h : SignIs x 0) : x = 0 := by
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · omega
  · exact h
  · omega

lemma SignIs.range {x : ℝ} {s : ℤ} (h : SignIs x s) : s = -1 ∨ s = 0 ∨ s = 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]

/-- `x = s · |x|`. -/
lemma SignIs.eq_mul_abs {x : ℝ} {s : ℤ} (h : SignIs x s) : x = s * |x| := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rw [abs_of_neg h]; push_cast; ring
  · rw [h]; simp
  · rw [abs_of_pos h]; push_cast; ring

namespace Family

variable (F : Family)

/-- The fourteen points `v_w(a)`. -/
noncomputable def pt (a : Fin 3 → ℝ) (w : Fin 14) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm
    ![(F.qc w 0 : ℝ), (F.qc w 1 : ℝ), (F.qc w 2 : ℝ), (F.qc w 3 : ℝ), (F.zt w).dot a]

/-- The facts hold at `a`. -/
def Holds (a : Fin 3 → ℝ) (facts : List (ℕ × ℤ)) : Prop :=
  ∀ t ∈ facts, SignIs ((F.plane t.1).dot a) t.2

lemma holds_of_factOf {a : Fin 3 → ℝ} {facts : List (ℕ × ℤ)} (h : F.Holds a facts) {p : ℕ}
    {s : ℤ} (hp : factOf facts p = some s) : SignIs ((F.plane p).dot a) s := by
  unfold factOf at hp
  rw [Option.map_eq_some_iff] at hp
  obtain ⟨t, ht, rfl⟩ := hp
  have hmem := List.mem_of_find?_eq_some ht
  have hp' := List.find?_some ht
  simp only [beq_iff_eq] at hp'
  rw [← hp']
  exact h t hmem

/-- **Motzkin refutations are sound.** -/
lemma refutes_sound {a : Fin 3 → ℝ} {facts : List (ℕ × ℤ)} {cert : List (ℕ × ℤ × ℤ)}
    (hc : F.refutes facts cert = true) (h : F.Holds a facts) : False := by
  unfold refutes at hc
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq, Bool.or_eq_true,
    decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨hall, ⟨t0, ht0, hs0, hc0⟩⟩, hsum⟩ := hc
  have hdot := congrArg (fun u : Z3 => u.dot a) hsum
  rw [foldl_dot, Z3.dot_zero, zero_add] at hdot
  have key : ∀ g : ℕ × ℤ × ℤ → ℝ, (∀ t ∈ cert, 0 ≤ g t) → 0 < g t0 → 0 < (cert.map g).sum := by
    intro g hg hg0
    exact lt_of_lt_of_le hg0 (List.single_le_sum (fun x hx => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx; exact hg t ht) _ (List.mem_map_of_mem ht0))
  refine absurd hdot (ne_of_gt (key _ (fun t ht => ?_) ?_))
  · obtain ⟨hf, hnn⟩ := hall t ht
    have hsg := F.holds_of_factOf h hf
    simp only [Z3.dot_smul]
    split_ifs with hs
    · rw [hs] at hsg; rw [hsg.eq_zero]; simp
    · have hpos := hsg.mul_pos hs
      have hnn' : (0 : ℝ) ≤ t.2.2 := by exact_mod_cast hnn.resolve_left hs
      push_cast
      nlinarith
  · obtain ⟨hf, -⟩ := hall t0 ht0
    have hsg := F.holds_of_factOf h hf
    have hp := hsg.mul_pos hs0
    have hc0' : (0 : ℝ) < t0.2.2 := by exact_mod_cast hc0
    simp only [Z3.dot_smul, hs0, if_false]
    push_cast
    nlinarith

/-- **Three independent vanishing forms force `a = 0`.** -/
lemma eq_zero_of_det3 {u v w : Z3} (hdet : det3 u v w ≠ 0) {a : Fin 3 → ℝ} (hu : u.dot a = 0)
    (hv : v.dot a = 0) (hw : w.dot a = 0) : a = 0 := by
  have hd : ((det3 u v w : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hdet
  unfold Z3.dot at hu hv hw
  unfold det3 at hd
  push_cast at hd
  funext k
  fin_cases k <;> simp only [Pi.zero_apply]
  · have : (u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
        u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1) : ℝ) * a 0 = 0 := by
      linear_combination ((v.2.1 : ℝ) * w.2.2 - v.2.2 * w.2.1) * hu -
        ((u.2.1 : ℝ) * w.2.2 - u.2.2 * w.2.1) * hv + ((u.2.1 : ℝ) * v.2.2 - u.2.2 * v.2.1) * hw
    exact (mul_eq_zero.1 this).resolve_left hd
  · have : (u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
        u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1) : ℝ) * a 1 = 0 := by
      linear_combination -((v.1 : ℝ) * w.2.2 - v.2.2 * w.1) * hu +
        ((u.1 : ℝ) * w.2.2 - u.2.2 * w.1) * hv - ((u.1 : ℝ) * v.2.2 - u.2.2 * v.1) * hw
    exact (mul_eq_zero.1 this).resolve_left hd
  · have : (u.1 * (v.2.1 * w.2.2 - v.2.2 * w.2.1) - u.2.1 * (v.1 * w.2.2 - v.2.2 * w.1) +
        u.2.2 * (v.1 * w.2.1 - v.2.1 * w.1) : ℝ) * a 2 = 0 := by
      linear_combination ((v.1 : ℝ) * w.2.1 - v.2.1 * w.1) * hu -
        ((u.1 : ℝ) * w.2.1 - u.2.1 * w.1) * hv + ((u.1 : ℝ) * v.2.1 - u.2.1 * v.1) * hw
    exact (mul_eq_zero.1 this).resolve_left hd

/-! ### Records give faces -/

/-- The affine functional of a facet record. -/
noncomputable def recFun (r : FacetRec) (a : Fin 3 → ℝ) (x : E5) : ℝ :=
  (r.c.getD 0 Z3.zero).dot a * x 0 + (r.c.getD 1 Z3.zero).dot a * x 1 +
    (r.c.getD 2 Z3.zero).dot a * x 2 + (r.c.getD 3 Z3.zero).dot a * x 3 + (r.c5 : ℝ) * x 4 +
      r.c6.dot a

lemma pt_apply (a : Fin 3 → ℝ) (w : Fin 14) :
    F.pt a w 0 = F.qc w 0 ∧ F.pt a w 1 = F.qc w 1 ∧ F.pt a w 2 = F.qc w 2 ∧
      F.pt a w 3 = F.qc w 3 ∧ F.pt a w 4 = (F.zt w).dot a := by
  simp [pt]

lemma recFun_pt (r : FacetRec) (a : Fin 3 → ℝ) (w : Fin 14) :
    recFun r a (F.pt a w) = (F.recValue r w).dot a := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := F.pt_apply a w
  have hr : List.range 4 = [0, 1, 2, 3] := rfl
  simp only [recFun, recValue, hr, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Z3.dot_add, Z3.dot_smul, Z3.dot_zero, h0, h1, h2, h3, h4]
  ring

lemma recFun_mem_affVals (r : FacetRec) (a : Fin 3 → ℝ) :
    (fun w => recFun r a (F.pt a w)) ∈ affVals (F.pt a) := by
  refine ⟨((WithLp.equiv 2 (Fin 5 → ℝ)).symm ![(r.c.getD 0 Z3.zero).dot a,
    (r.c.getD 1 Z3.zero).dot a, (r.c.getD 2 Z3.zero).dot a, (r.c.getD 3 Z3.zero).dot a,
    (r.c5 : ℝ)], r.c6.dot a), ?_⟩
  funext w
  simp only [evalMap_apply, recFun, PiLp.inner_apply, Fin.sum_univ_five]
  simp [mul_comm]

/-- What `recOK` guarantees. -/
lemma recOK_spec {r : FacetRec} (h : F.recOK r = true) :
    (∀ e ∈ r.ent, (e.2.1 = none → F.recValue r e.1 = Z3.zero) ∧
      ∀ p, e.2.1 = some p → F.recValue r e.1 = Z3.smul e.2.2 (F.plane p)) ∧
    ∀ w < 14, ∃ e ∈ r.ent, e.1 = w := by
  unfold recOK at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, List.contains_iff_mem,
    List.mem_map] at h
  obtain ⟨⟨-, hcov⟩, hval⟩ := h
  refine ⟨fun e he => ⟨fun hn => ?_, fun p hp => ?_⟩, fun w hw => ?_⟩
  · have := hval e he; rw [hn] at this; simpa using this
  · have := hval e he; rw [hp] at this; simpa using this
  · obtain ⟨e, he, rfl⟩ := hcov w hw; exact ⟨e, he, rfl⟩

/-- Sign of the record's functional at a point, from the state of its entry. -/
lemma entState_sign {r : FacetRec} (hok : F.recOK r = true) {facts : List (ℕ × ℤ)}
    {a : Fin 3 → ℝ} (h : F.Holds a facts) {e : ℕ × Option ℕ × ℤ} (he : e ∈ r.ent) {b : Bool}
    (hb : entState facts r.eps e = some b) :
    (b = true → (r.eps : ℝ) * (F.recValue r e.1).dot a = 0) ∧
      (b = false → (r.eps : ℝ) * (F.recValue r e.1).dot a < 0) := by
  obtain ⟨hval, -⟩ := F.recOK_spec hok
  obtain ⟨hnone, hsome⟩ := hval e he
  unfold entState at hb
  rcases hp : e.2.1 with _ | p
  · simp only [hp, Option.some.injEq] at hb
    subst hb
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    rw [hnone hp]; simp
  · simp only [hp] at hb
    rw [hsome p hp, Z3.dot_smul]
    cases hf : factOf facts p with
    | none => simp [hf] at hb
    | some s =>
      simp only [hf] at hb
      have hsg := F.holds_of_factOf h hf
      by_cases h0 : r.eps * e.2.2 * s = 0
      · rw [if_pos (by simpa using h0)] at hb
        simp only [Option.some.injEq] at hb
        subst hb
        refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
        by_cases hs : s = 0
        · rw [hs] at hsg; rw [hsg.eq_zero]; ring
        · have : r.eps * e.2.2 = 0 := by
            rcases mul_eq_zero.1 h0 with h | h
            · exact h
            · exact absurd h hs
          have : (r.eps : ℝ) * e.2.2 = 0 := by exact_mod_cast this
          calc (r.eps : ℝ) * (e.2.2 * (F.plane p).dot a)
              = ((r.eps : ℝ) * e.2.2) * (F.plane p).dot a := by ring
            _ = 0 := by rw [this, zero_mul]
      · rw [if_neg (by simpa using h0)] at hb
        by_cases hneg : r.eps * e.2.2 * s < 0
        · rw [if_pos (by simpa using hneg)] at hb
          simp only [Option.some.injEq] at hb
          subst hb
          refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
          have hs : s ≠ 0 := fun hs => h0 (by rw [hs, mul_zero])
          have habs := hsg.eq_mul_abs
          have hpos : 0 < |(F.plane p).dot a| := by
            rcases hsg with ⟨-, hx⟩ | ⟨hs', -⟩ | ⟨-, hx⟩
            · exact abs_pos.2 hx.ne
            · exact absurd hs' hs
            · exact abs_pos.2 hx.ne'
          have hneg' : ((r.eps * e.2.2 * s : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
          push_cast at hneg'
          rw [habs]
          calc (r.eps : ℝ) * (e.2.2 * (s * |(F.plane p).dot a|))
              = ((r.eps : ℝ) * e.2.2 * s) * |(F.plane p).dot a| := by ring
            _ < 0 := mul_neg_of_neg_of_pos hneg' hpos
        · rw [if_neg (by simpa using hneg)] at hb
          simp at hb

/-- **A record's mask on a stratum is a face index.** -/
lemma recMask_isFaceIdx {r : FacetRec} (hok : F.recOK r = true) {facts : List (ℕ × ℤ)}
    {a : Fin 3 → ℝ} (h : F.Holds a facts) {m : ℕ} (hm : recMask facts r = some m) :
    IsFaceIdx (F.pt a) (ofMask 14 m) := by
  unfold recMask at hm
  split_ifs at hm with hall
  simp only [Option.some.injEq] at hm
  subst hm
  rw [List.all_eq_true] at hall
  obtain ⟨-, hcov⟩ := F.recOK_spec hok
  refine ⟨fun w => -(r.eps : ℝ) * recFun r a (F.pt a w),
    Submodule.smul_mem _ (-(r.eps : ℝ)) (recFun_mem_affVals F r a), fun w hw => ?_, fun w hw => ?_⟩ <;>
  · obtain ⟨e0, he0, hw0⟩ := hcov w w.2
    have hfind : ∃ e, r.ent.find? (fun e => e.1 == (w : ℕ)) = some e := by
      cases hf : r.ent.find? (fun e => e.1 == (w : ℕ)) with
      | some e => exact ⟨e, rfl⟩
      | none =>
        exfalso
        have := List.find?_eq_none.1 hf e0 he0
        simp [hw0] at this
    obtain ⟨e, he⟩ := hfind
    have hemem := List.mem_of_find?_eq_some he
    have hew : e.1 = w := by simpa using List.find?_some he
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (hall e hemem)
    have hsign := F.entState_sign hok h hemem hb
    rw [mem_ofMask, testBit_maskOf] at hw
    simp only [he, Option.bind_some, hb, w.2, decide_true, Bool.true_and, beq_iff_eq,
      Option.some.injEq] at hw
    simp only [recFun_pt]
    rw [← hew]
    first
    | (have := hsign.1 hw; linarith)
    | (cases b
       · have := hsign.2 rfl; linarith
       · exact absurd rfl hw)

/-- `meetAbove` of face indices is a face index. -/
lemma meetAbove_isFaceIdx {a : Fin 3 → ℝ} {masks : List ℕ}
    (hmasks : ∀ f ∈ masks, IsFaceIdx (F.pt a) (ofMask 14 f)) (m : ℕ) :
    IsFaceIdx (F.pt a) (ofMask 14 (meetAbove masks m)) := by
  unfold meetAbove
  suffices key : ∀ (l : List ℕ) (acc : ℕ), (∀ f ∈ l, IsFaceIdx (F.pt a) (ofMask 14 f)) →
      IsFaceIdx (F.pt a) (ofMask 14 acc) →
      IsFaceIdx (F.pt a) (ofMask 14 (l.foldl (fun acc f => if m &&& f == m then acc &&& f else acc) acc)) by
    apply key masks _ hmasks
    have : ofMask 14 (2 ^ 14 - 1) = Finset.univ := by
      ext j
      rw [mem_ofMask, Nat.testBit_two_pow_sub_one]
      simp [j.2]
    rw [this]; exact isFaceIdx_univ
  intro l
  induction l with
  | nil => intro acc _ hacc; exact hacc
  | cons f l ih =>
    intro acc hl hacc
    rw [List.foldl_cons]
    apply ih _ (fun g hg => hl g (List.mem_cons_of_mem _ hg))
    split_ifs
    · have : ofMask 14 (acc &&& f) = ofMask 14 acc ∩ ofMask 14 f := by
        ext j; simp [mem_ofMask, Nat.testBit_land]
      rw [this]
      exact hacc.inter (hl f List.mem_cons_self)
    · exact hacc

/-! ### Leaves, collisions and the tree -/

lemma nodup_of_sortedLT : ∀ l : List ℕ, sortedLT l = true → l.Nodup
  | [] , _ => List.nodup_nil
  | [_], _ => List.nodup_singleton _
  | a :: b :: l, h => by
    simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := nodup_of_sortedLT (b :: l) h.2
    refine List.nodup_cons.2 ⟨fun ha => ?_, ih⟩
    have key : ∀ l : List ℕ, ∀ b, sortedLT (b :: l) = true → ∀ x ∈ b :: l, b ≤ x := by
      intro l
      induction l with
      | nil => intro b _ x hx; simp at hx; omega
      | cons c l ih' =>
        intro b hb x hx
        simp only [sortedLT, Bool.and_eq_true, decide_eq_true_eq] at hb
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact le_trans hb.1.le (ih' c hb.2 x hx)
    have := key l b h.2 a ha
    omega

/-- **Leaves are sound.** -/
lemma leaf_sound (hall : F.facets.all F.recOK = true) {facts : List (ℕ × ℤ)} {fs fl : List ℕ}
    (hck : F.leafOK facts fs fl = true) {a : Fin 3 → ℝ} (h : F.Holds a facts) :
    243 ≤ (faces (convexHull ℝ (range (F.pt a)))).ncard := by
  classical
  unfold leafOK at hck
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq] at hck
  obtain ⟨⟨⟨hrange, hlen⟩, hsort⟩, hfaces⟩ := hck
  have hmasks : ∀ f ∈ F.leafMasks facts fs, IsFaceIdx (F.pt a) (ofMask 14 f) := by
    intro f hf
    unfold leafMasks at hf
    obtain ⟨i, hi, hrm⟩ := List.mem_filterMap.1 hf
    have hi' := hrange i hi
    rw [List.getD_eq_getElem _ _ hi'] at hrm
    rw [List.all_eq_true] at hall
    exact F.recMask_isFaceIdx (hall _ (List.getElem_mem hi')) h hrm
  have hface : ∀ m ∈ fl, (ofMask 14 m).Nonempty ∧ IsFaceIdx (F.pt a) (ofMask 14 m) := by
    intro m hm
    obtain ⟨⟨hm0, hm14⟩, hmeet⟩ := hfaces m hm
    refine ⟨(ofMask_nonempty_iff hm14).2 hm0, ?_⟩
    have := F.meetAbove_isFaceIdx hmasks m
    rwa [hmeet] at this
  set S := fl.toFinset.image (ofMask 14)
  have hS : S.card = fl.length := by
    rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup (nodup_of_sortedLT fl hsort)]
    intro x hx y hy hxy
    have hx' := List.mem_toFinset.1 (Finset.mem_coe.1 hx)
    have hy' := List.mem_toFinset.1 (Finset.mem_coe.1 hy)
    exact ofMask_injOn (Finset.mem_coe.2 (Finset.mem_range.2 (hfaces x hx').1.2))
      (Finset.mem_coe.2 (Finset.mem_range.2 (hfaces y hy').1.2)) hxy
  have hle := le_ncard_faces S (by
    intro F' hF'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hF'
    exact hface m (List.mem_toFinset.1 hm))
  omega

/-- **Collisions are excluded.** -/
lemma invalid_sound {facts : List (ℕ × ℤ)} {i j : ℕ} {num : List (ℕ × ℤ)} {den : ℤ}
    (hck : F.walk facts (.invalid i j num den) = true) {a : Fin 3 → ℝ} (h : F.Holds a facts)
    (hinj : Function.Injective (F.pt a)) : False := by
  unfold walk at hck
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    List.mem_range, beq_iff_eq, and_assoc] at hck
  obtain ⟨hi, hj, hij, hden, hq, hnum, hsum⟩ := hck
  have hdot := congrArg (fun u : Z3 => u.dot a) hsum
  rw [foldl_dot, Z3.dot_zero, zero_add, Z3.dot_smul, Z3.dot_add, Z3.dot_smul] at hdot
  have hzero : (num.map fun t => (Z3.smul t.2 (F.plane t.1)).dot a).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
    have := (F.holds_of_factOf h (hnum t ht)).eq_zero
    rw [Z3.dot_smul, this, mul_zero]
  rw [hzero] at hdot
  have hden' : (den : ℝ) ≠ 0 := by exact_mod_cast hden
  have hz : (F.zt i).dot a = (F.zt j).dot a := by
    have := (mul_eq_zero.1 hdot.symm).resolve_left hden'
    push_cast at this
    linarith
  have hpt : F.pt a ⟨i, hi⟩ = F.pt a ⟨j, hj⟩ := by
    obtain ⟨a0, a1, a2, a3, a4⟩ := F.pt_apply a ⟨i, hi⟩
    obtain ⟨b0, b1, b2, b3, b4⟩ := F.pt_apply a ⟨j, hj⟩
    ext k
    fin_cases k
    · exact a0.trans ((congrArg _ (hq 0 (by norm_num))).trans b0.symm)
    · exact a1.trans ((congrArg _ (hq 1 (by norm_num))).trans b1.symm)
    · exact a2.trans ((congrArg _ (hq 2 (by norm_num))).trans b2.symm)
    · exact a3.trans ((congrArg _ (hq 3 (by norm_num))).trans b3.symm)
    · exact a4.trans (hz.trans b4.symm)
  exact hij (congrArg Fin.val (hinj hpt))

/-- **The tree walk is sound.** -/
theorem walk_sound (hall : F.facets.all F.recOK = true) {a : Fin 3 → ℝ} (ha : a ≠ 0)
    (hinj : Function.Injective (F.pt a)) :
    ∀ (node : Node) (facts : List (ℕ × ℤ)), F.walk facts node = true → F.Holds a facts →
      243 ≤ (faces (convexHull ℝ (range (F.pt a)))).ncard
  | .leaf fs faces, facts, hck, h => F.leaf_sound hall (by simpa [walk] using hck) h
  | .branch p n z q, facts, hck, h => by
    unfold walk at hck
    simp only [Bool.and_eq_true] at hck
    obtain ⟨⟨⟨-, hn⟩, hz⟩, hq⟩ := hck
    have hext : ∀ s, SignIs ((F.plane p).dot a) s → F.Holds a ((p, s) :: facts) := by
      intro s hs t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · exact hs
      · exact h t ht
    rcases signIs_trichotomy ((F.plane p).dot a) with hs | hs | hs
    · exact walk_sound hall ha hinj n _ hn (hext _ hs)
    · exact walk_sound hall ha hinj z _ hz (hext _ hs)
    · exact walk_sound hall ha hinj q _ hq (hext _ hs)
  | .refuted cert, facts, hck, h => (F.refutes_sound (by simpa [walk] using hck) h).elim
  | .zeroRank3 p q r, facts, hck, h => by
    unfold walk at hck
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hck
    obtain ⟨⟨⟨hp, hq⟩, hr⟩, hdet⟩ := hck
    exact (ha (eq_zero_of_det3 hdet (F.holds_of_factOf h hp).eq_zero
      (F.holds_of_factOf h hq).eq_zero (F.holds_of_factOf h hr).eq_zero)).elim
  | .invalid i j num den, facts, hck, h => (F.invalid_sound hck h hinj).elim

/-- **Soundness of the Lemma A certificate.** -/
theorem check_sound (hck : F.check = true) {a : Fin 3 → ℝ} (ha : a ≠ 0)
    (hinj : Function.Injective (F.pt a)) :
    243 ≤ (faces (convexHull ℝ (range (F.pt a)))).ncard := by
  unfold check at hck
  rw [Bool.and_eq_true] at hck
  exact F.walk_sound hck.1 ha hinj F.tree [] hck.2 (fun t ht => by simp at ht)

end Family

end Kalai5.LemmaA
