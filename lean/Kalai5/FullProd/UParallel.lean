import Kalai5.FullProd.UConf

/-!
# The facet `U` at `(18, 18)`: the parallel case

If the four product edges of `U` are parallel (direction `d = x 7 - x 2`):
* `x 2, x 3, x 0, x 1, d` is a basis; the pentagon gives
  `z = x 6 = x 0 + (multiple of d) + β (x 1 - x 0)` with `0 < β < 1` (witnesses of `G 3`, `G 4`);
* the sixteen functionals `w a b c e` (values `±1` at `x 2, x 3, x 0, x 1` and `0` at `d`) are
  vertices of the polar (L2); those tight at `z` have `c = e = +`;
* two more vertices of the polar tight at `z` would give, with their negatives, twenty vertices;
  so at most one, `y`, is, and a nonzero `v ∈ span {d, x 0 - x 1}` orthogonal to `y` is orthogonal
  to every vertex of the polar tight at `z`: by L1, `z` is not a vertex of `P`.
-/

namespace Kalai5

open Set Module Submodule

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The sign `±1` of a boolean. -/
def bsgn (b : Bool) : ℝ := cond b 1 (-1)

lemma bsgn_bounds (b : Bool) : -1 ≤ bsgn b ∧ bsgn b ≤ 1 := by cases b <;> norm_num [bsgn]

lemma bsgn_inj {b b' : Bool} (h : bsgn b = bsgn b') : b = b' := by
  cases b <;> cases b' <;> first | rfl | (norm_num [bsgn] at h)

lemma bsgn_not (b : Bool) : bsgn (!b) = -bsgn b := by cases b <;> norm_num [bsgn]

lemma forall_fin9 {Q : Fin 9 → Prop} (h0 : Q 0) (h1 : Q 1) (h2 : Q 2) (h3 : Q 3) (h4 : Q 4)
    (h5 : Q 5) (h6 : Q 6) (h7 : Q 7) (h8 : Q 8) : ∀ i, Q i := by
  intro i; fin_cases i
  exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]

namespace UConf

variable {P : Set E5} (C : UConf P)

/-- A vertex `±a` with value `bsgn b` at `a` is tight. -/
lemma tight_sgn {w v a : E5} (b : Bool) (ha : ⟪a, w⟫ = bsgn b) (haX : a ∈ C.X) (hnaX : -a ∈ C.X)
    (hv : ∀ y ∈ C.X, ⟪y, w⟫ = 1 → ⟪y, v⟫ = 0) : ⟪a, v⟫ = 0 := by
  cases b
  · have := hv (-a) hnaX (by rw [inner_neg_left, ha]; norm_num [bsgn])
    rwa [inner_neg_left, neg_eq_zero] at this
  · exact hv a haX (by rw [ha]; rfl)

variable (hP : IsCSPolytope5 P)
include hP

/-- **The parallel case is impossible** at at most eighteen facets. -/
theorem parallel_false_of_le (hh : fvec P 4 ≤ 18) {μB μC μD : ℝ}
    (hB : C.x 8 - C.x 3 = μB • (C.x 7 - C.x 2)) (hC : C.x 4 - C.x 0 = μC • (C.x 7 - C.x 2))
    (hD : C.x 5 - C.x 1 = μD • (C.x 7 - C.x 2)) : False := by
  classical
  have hA0 := C.sub_ne (a := 7) (b := 2) (by decide)
  -- the pentagon
  have f12 := C.plane (j := 1) (k := 2) (a := 0) (b := 2) (by decide) (by decide)
  obtain ⟨α, β, hz⟩ := mem_span_pair_of_finrank_le f12
    (C.mem_plane (j := 1) (k := 2) (a := 4) (b := 0) (by decide) (by decide))
    (C.mem_plane (j := 1) (k := 2) (a := 1) (b := 0) (by decide) (by decide))
    (C.mem_plane (j := 1) (k := 2) (a := 6) (b := 0) (by decide) (by decide))
    (C.indep (a := 0) (b := 4) (c := 1) (by decide) (by decide) (by decide))
  have hz' : C.x 6 = C.x 0 + (α * μC) • (C.x 7 - C.x 2) + β • (C.x 1 - C.x 0) := by
    have : C.x 6 = C.x 0 + α • (C.x 4 - C.x 0) + β • (C.x 1 - C.x 0) := by
      rw [add_assoc, ← hz]; abel
    rw [this, hC, smul_smul]
  -- inner products with the vertices in terms of the basis
  have e6 : ∀ y : E5, ⟪C.x 6, y⟫ =
      ⟪C.x 0, y⟫ + (α * μC) * ⟪C.x 7 - C.x 2, y⟫ + β * ⟪C.x 1 - C.x 0, y⟫ := fun y => by
    rw [hz', inner_add_left, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e7 : ∀ y : E5, ⟪C.x 7, y⟫ = ⟪C.x 2, y⟫ + ⟪C.x 7 - C.x 2, y⟫ := fun y => by
    rw [inner_sub_left]; ring
  have e8 : ∀ y : E5, ⟪C.x 8, y⟫ = ⟪C.x 3, y⟫ + μB * ⟪C.x 7 - C.x 2, y⟫ := fun y => by
    rw [← real_inner_smul_left, ← hB, inner_sub_left]; ring
  have e4 : ∀ y : E5, ⟪C.x 4, y⟫ = ⟪C.x 0, y⟫ + μC * ⟪C.x 7 - C.x 2, y⟫ := fun y => by
    rw [← real_inner_smul_left, ← hC, inner_sub_left]; ring
  have e5 : ∀ y : E5, ⟪C.x 5, y⟫ = ⟪C.x 1, y⟫ + μD * ⟪C.x 7 - C.x 2, y⟫ := fun y => by
    rw [← real_inner_smul_left, ← hD, inner_sub_left]; ring
  -- `0 < β < 1` from the witnesses of `G 3` and `G 4`
  obtain ⟨ψ3, hψ3⟩ := C.witness hP 3
  obtain ⟨ψ4, hψ4⟩ := C.witness hP 4
  have hβ0 : 0 < β := by
    have h1 := (hψ3 6).2 (by decide)
    have h2 := (hψ3 1).2 (by decide)
    rw [e6, inner_sub_left, inner_sub_left, (hψ3 0).1 (by decide), (hψ3 7).1 (by decide),
      (hψ3 2).1 (by decide)] at h1
    have h1' : 0 < β * ⟪C.x 1, ψ3⟫ := by linarith
    exact (mul_pos_iff_of_pos_right h2).1 h1'
  have hβ1 : β < 1 := by
    have h1 := (hψ4 6).2 (by decide)
    have h2 := (hψ4 0).2 (by decide)
    rw [e6, inner_sub_left, inner_sub_left, (hψ4 1).1 (by decide), (hψ4 7).1 (by decide),
      (hψ4 2).1 (by decide)] at h1
    have h1' : 0 < (1 - β) * ⟪C.x 0, ψ4⟫ := by linarith
    have := (mul_pos_iff_of_pos_right h2).1 h1'
    linarith
  -- the basis
  have hli : LinearIndependent ℝ ![C.x 2, C.x 3, C.x 0, C.x 1, C.x 7 - C.x 2] := by
    refine indep5 fun S h2 h3 h0 h1 hd => C.span_top hP S h0 h1 h2 h3 ?_ ?_ ?_ ?_ ?_
    · have : C.x 4 = C.x 0 + μC • (C.x 7 - C.x 2) := by rw [← hC]; abel
      rw [this]; exact add_mem h0 (smul_mem _ _ hd)
    · have : C.x 5 = C.x 1 + μD • (C.x 7 - C.x 2) := by rw [← hD]; abel
      rw [this]; exact add_mem h1 (smul_mem _ _ hd)
    · rw [hz']; exact add_mem (add_mem h0 (smul_mem _ _ hd)) (smul_mem _ _ (sub_mem h1 h0))
    · have : C.x 7 = C.x 2 + (C.x 7 - C.x 2) := by abel
      rw [this]; exact add_mem h2 hd
    · have : C.x 8 = C.x 3 + μB • (C.x 7 - C.x 2) := by rw [← hB]; abel
      rw [this]; exact add_mem h3 (smul_mem _ _ hd)
  -- the sixteen vertical functionals
  have hdual : ∀ a b c e : Bool, ∃ w : E5, ⟪C.x 2, w⟫ = bsgn a ∧ ⟪C.x 3, w⟫ = bsgn b ∧
      ⟪C.x 0, w⟫ = bsgn c ∧ ⟪C.x 1, w⟫ = bsgn e ∧ ⟪C.x 7 - C.x 2, w⟫ = 0 :=
    fun a b c e => exists_dual5 hli _ _ _ _ _
  choose wv hwv using hdual
  have hbd : ∀ a b c e, ∀ i, -1 ≤ ⟪C.x i, wv a b c e⟫ ∧ ⟪C.x i, wv a b c e⟫ ≤ 1 := by
    intro a b c e
    obtain ⟨w2, w3, w0, w1, wd⟩ := hwv a b c e
    refine forall_fin9 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [w0]; exact bsgn_bounds _
    · rw [w1]; exact bsgn_bounds _
    · rw [w2]; exact bsgn_bounds _
    · rw [w3]; exact bsgn_bounds _
    · rw [e4, w0, wd, mul_zero, add_zero]; exact bsgn_bounds _
    · rw [e5, w1, wd, mul_zero, add_zero]; exact bsgn_bounds _
    · rw [e6, w0, wd, inner_sub_left, w1, w0, mul_zero, add_zero]
      have hc := bsgn_bounds c
      have he := bsgn_bounds e
      constructor <;> nlinarith
    · rw [e7, w2, wd, add_zero]; exact bsgn_bounds _
    · rw [e8, w3, wd, mul_zero, add_zero]; exact bsgn_bounds _
  have hext : ∀ a b c e, wv a b c e ∈ (polarSet P).extremePoints ℝ := by
    intro a b c e
    obtain ⟨w2, w3, w0, w1, wd⟩ := hwv a b c e
    rw [C.hPX]
    refine mem_extremePoints_polarSet_of_tight (fun y hy => ?_) (fun v hv => ?_)
    · obtain ⟨i, rfl | rfl⟩ := C.memX y hy
      · exact (hbd a b c e i).2
      · rw [inner_neg_left]; linarith [(hbd a b c e i).1]
    · have t2 := C.tight_sgn a w2 (C.xX 2).1 (C.xX 2).2 hv
      have t7 := C.tight_sgn a (by rw [e7, w2, wd, add_zero]) (C.xX 7).1 (C.xX 7).2 hv
      have t3 := C.tight_sgn b w3 (C.xX 3).1 (C.xX 3).2 hv
      have t0 := C.tight_sgn c w0 (C.xX 0).1 (C.xX 0).2 hv
      have t1 := C.tight_sgn e w1 (C.xX 1).1 (C.xX 1).2 hv
      refine eq_zero5 hli t2 t3 t0 t1 ?_
      rw [inner_sub_left, t7, t2, sub_self]
  have hinj : ∀ {a b c e a' b' c' e' : Bool}, wv a b c e = wv a' b' c' e' →
      a = a' ∧ b = b' ∧ c = c' ∧ e = e' := by
    intro a b c e a' b' c' e' h
    obtain ⟨w2, w3, w0, w1, -⟩ := hwv a b c e
    obtain ⟨w2', w3', w0', w1', -⟩ := hwv a' b' c' e'
    rw [h] at w2 w3 w0 w1
    exact ⟨bsgn_inj (w2.symm.trans w2'), bsgn_inj (w3.symm.trans w3'),
      bsgn_inj (w0.symm.trans w0'), bsgn_inj (w1.symm.trans w1')⟩
  have hneg : ∀ a b c e, -wv a b c e = wv (!a) (!b) (!c) (!e) := by
    intro a b c e
    obtain ⟨w2, w3, w0, w1, wd⟩ := hwv a b c e
    obtain ⟨w2', w3', w0', w1', wd'⟩ := hwv (!a) (!b) (!c) (!e)
    refine sub_eq_zero.1 (eq_zero5 hli ?_ ?_ ?_ ?_ ?_) <;>
      simp only [inner_sub_right, inner_neg_right, w2, w3, w0, w1, wd, w2', w3', w0', w1', wd',
        bsgn_not] <;> ring
  -- the vertical functionals tight at `z`
  have htz : ∀ a b c e, ⟪C.x 6, wv a b c e⟫ = 1 → c = true ∧ e = true := by
    intro a b c e h
    obtain ⟨-, -, w0, w1, wd⟩ := hwv a b c e
    rw [e6, w0, wd, inner_sub_left, w1, w0, mul_zero, add_zero] at h
    cases c <;> cases e <;> first | exact ⟨rfl, rfl⟩ | (exfalso; norm_num [bsgn] at h <;> linarith)
  -- `z` is a vertex of `P = polarSet (conv W)`
  obtain ⟨W, hWext, hPW⟩ := hP.exists_polar_finset
  have hzW : C.x 6 ∈ (polarSet (convexHull ℝ (W : Set E5))).extremePoints ℝ := by
    rw [← hPW]; exact C.xP 6
  have hval_ne : ∀ u u' : E5, ⟪C.x 6, u⟫ = 1 → ⟪C.x 6, u'⟫ = 1 → u ≠ -u' := by
    intro u u' h h' he
    rw [he, inner_neg_right, h'] at h
    norm_num at h
  by_cases h2 : ∃ y1 ∈ (polarSet P).extremePoints ℝ, ∃ y2 ∈ (polarSet P).extremePoints ℝ,
      y1 ≠ y2 ∧ ⟪C.x 6, y1⟫ = 1 ∧ ⟪C.x 6, y2⟫ = 1 ∧ (∀ a b c e, y1 ≠ wv a b c e) ∧
      (∀ a b c e, y2 ≠ wv a b c e)
  · -- twenty vertices of the polar
    obtain ⟨y1, hy1, y2, hy2, hne, hz1, hz2, hn1, hn2⟩ := h2
    set S16 : Finset E5 := (Finset.univ : Finset (Bool × Bool × Bool × Bool)).image
      fun ε => wv ε.1 ε.2.1 ε.2.2.1 ε.2.2.2 with hS16def
    have hS16 : S16.card = 16 := by
      rw [hS16def, Finset.card_image_of_injective]
      · rfl
      · rintro ⟨a, b, c, e⟩ ⟨a', b', c', e'⟩ h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hinj h
        rfl
    have hS4 : ({y1, y2, -y1, -y2} : Finset E5).card = 4 := by
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair_eq_two_iff.2 (neg_injective.ne hne)]
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hval_ne _ _ hz2 hz1, hval_ne _ _ hz2 hz2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, hval_ne _ _ hz1 hz1, hval_ne _ _ hz1 hz2⟩
    have hdisj : Disjoint S16 ({y1, y2, -y1, -y2} : Finset E5) := by
      rw [Finset.disjoint_left]
      intro w hw hw4
      obtain ⟨⟨a, b, c, e⟩, -, rfl⟩ := Finset.mem_image.1 hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw4
      rcases hw4 with h | h | h | h
      · exact hn1 a b c e h.symm
      · exact hn2 a b c e h.symm
      · apply hn1 (!a) (!b) (!c) (!e); rw [← hneg, h, neg_neg]
      · apply hn2 (!a) (!b) (!c) (!e); rw [← hneg, h, neg_neg]
    have hall : ∀ w ∈ S16 ∪ {y1, y2, -y1, -y2}, w ∈ (polarSet P).extremePoints ℝ := by
      intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · obtain ⟨⟨a, b, c, e⟩, -, rfl⟩ := Finset.mem_image.1 hw
        exact hext a b c e
      · simp only [Finset.mem_insert, Finset.mem_singleton] at hw
        rcases hw with rfl | rfl | rfl | rfl
        · exact hy1
        · exact hy2
        · exact hP.polar.neg_mem_extremePoints hy1
        · exact hP.polar.neg_mem_extremePoints hy2
    have := hP.card_le_of_polar_vertices_of_le hh _ hall
    rw [Finset.card_union_of_disjoint hdisj, hS16, hS4] at this
    norm_num at this
  · -- at most one other vertex of the polar is tight at `z`
    push_neg at h2
    obtain ⟨y, hy⟩ : ∃ y : E5, ∀ y' ∈ (polarSet P).extremePoints ℝ, ⟪C.x 6, y'⟫ = 1 →
        (∀ a b c e, y' ≠ wv a b c e) → y' = y := by
      by_cases h1 : ∃ y1 ∈ (polarSet P).extremePoints ℝ, ⟪C.x 6, y1⟫ = 1 ∧
          ∀ a b c e, y1 ≠ wv a b c e
      · obtain ⟨y1, hy1, hz1, hn1⟩ := h1
        refine ⟨y1, fun y' hy' hz' hn' => ?_⟩
        by_contra hne
        obtain ⟨a, b, c, e, h⟩ := h2 y' hy' y1 hy1 hne hz' hz1 hn'
        exact hn1 a b c e h
      · push_neg at h1
        refine ⟨0, fun y' hy' hz' hn' => ?_⟩
        obtain ⟨a, b, c, e, h⟩ := h1 y' hy' hz'
        exact absurd h (hn' a b c e)
    -- a nonzero vector orthogonal to all vertices of the polar tight at `z`
    have hvert : ∀ a b, ⟪C.x 7 - C.x 2, wv a b true true⟫ = 0 ∧
        ⟪C.x 0 - C.x 1, wv a b true true⟫ = 0 := by
      intro a b
      obtain ⟨-, -, w0, w1, wd⟩ := hwv a b true true
      exact ⟨wd, by rw [inner_sub_left, w0, w1, sub_self]⟩
    obtain ⟨v, hv0, hvy, hvv⟩ : ∃ v : E5, v ≠ 0 ∧ ⟪y, v⟫ = 0 ∧
        ∀ a b, ⟪wv a b true true, v⟫ = 0 := by
      by_cases he : ⟪C.x 7 - C.x 2, y⟫ = 0
      · refine ⟨C.x 7 - C.x 2, hA0, by rw [real_inner_comm, he], fun a b => ?_⟩
        rw [real_inner_comm]; exact (hvert a b).1
      · refine ⟨⟪C.x 0 - C.x 1, y⟫ • (C.x 7 - C.x 2) - ⟪C.x 7 - C.x 2, y⟫ • (C.x 0 - C.x 1),
          fun h0 => ?_, ?_, fun a b => ?_⟩
        · obtain ⟨-, -, w0, w1, wd⟩ := hwv true true true false
          have := congrArg (fun u => ⟪u, wv true true true false⟫) h0
          simp only [inner_zero_left, inner_sub_left, real_inner_smul_left, wd, w0, w1] at this
          norm_num [bsgn] at this
          exact he (by rw [inner_sub_left]; linarith)
        · rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
            real_inner_comm y (C.x 7 - C.x 2), real_inner_comm y (C.x 0 - C.x 1)]
          ring
        · rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right,
            real_inner_comm (C.x 7 - C.x 2) (wv a b true true),
            real_inner_comm (C.x 0 - C.x 1) (wv a b true true), (hvert a b).1, (hvert a b).2]
          ring
    refine hv0 (eq_zero_of_tight_of_extreme hzW fun w hw hwz => ?_)
    have hwext : w ∈ (polarSet P).extremePoints ℝ := by rw [← hWext]; exact hw
    rw [real_inner_comm] at hwz
    by_cases hwv' : ∃ a b c e, w = wv a b c e
    · obtain ⟨a, b, c, e, rfl⟩ := hwv'
      obtain ⟨rfl, rfl⟩ := htz a b c e hwz
      exact hvv a b
    · push_neg at hwv'
      rw [hy w hwext hwz hwv']
      exact hvy

/-- The original equality interface is retained. -/
theorem parallel_false (hh : fvec P 4 = 18) {μB μC μD : ℝ}
    (hB : C.x 8 - C.x 3 = μB • (C.x 7 - C.x 2))
    (hC : C.x 4 - C.x 0 = μC • (C.x 7 - C.x 2))
    (hD : C.x 5 - C.x 1 = μD • (C.x 7 - C.x 2)) : False :=
  C.parallel_false_of_le hP hh.le hB hC hD

end UConf

end Kalai5
