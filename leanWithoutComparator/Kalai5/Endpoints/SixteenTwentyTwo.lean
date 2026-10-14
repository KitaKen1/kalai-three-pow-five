import Kalai5.Endpoints.Sixteen
import Kalai5.Rows.SixCount
import Kalai5.Rigidity.PolygonStar
import Kalai5.FullPrism.Final
import Kalai5.Faces.Facets

/-!
# Endpoint `(16,22)`

With `L = L1 + 9·[n = 8]` and `m` the number of facets with eight vertices,
`12 t = 1398 - 9m + 4A + 6G + Σ L` (`sum_L1`).  A counterexample has `t ≤ 118`.

* Row costs: `L ∈ A = {0, 5, 10, 14, 15} ∪ [19, ∞)` for `n ≤ 7` (Gale rows), and `A` is closed under
  addition; `L ≥ 13` for `n = 8` (the duals of the Gale rows with eight facets, and Euler with
  `J + 4n ≤ 4e` otherwise), the prism `tRow` being excluded by `full_prism`.
* `G ≥ 2`: then `m = 0`, `A = 0`, `G = 2` and `12 t ∈ {1410, 1415}`, impossible.
* `G = 0`: local `g ≥ 0` and stress localization give `g = 0` on every facet, the polygon-star
  lemma gives `A = 0`; `m ∈ {0, 2}` (facets pair up), and the residues mod 12 force `m = 2`, both
  eight-vertex facets of row `zRow = (8,19,18,7; 35)`, and every other facet of cost `0`: a simplex
  or a pyramid over a triangular prism (`excRow`).  Then `I = 144` gives `6` simplices and `14`
  pyramids (`closure_16_22`).
* **Ridge parity**: the 3-faces with six vertices: `0` per simplex, `1` per pyramid, `2` per
  `zRow` facet, `6·0 + 14·1 + 2·2 = 18 ≢ 0 (mod 4)` (`IsCSPolytope5.four_dvd_sum_six3`).
-/

namespace Kalai5

/-! ### Row facts at sixteen vertices -/

/-- The extended cost `L = L1 + 9·[n = 8]`. -/
def Row.Lx (R : Row) : ℤ := R.L1 + if R.n = 8 then 9 else 0

/-- The additive set `A = {0, 5, 10, 14, 15} ∪ [19, ∞)`. -/
abbrev InA (x : ℤ) : Prop := x = 0 ∨ x = 5 ∨ x = 10 ∨ x = 14 ∨ x = 15 ∨ 19 ≤ x

lemma InA.add {x y : ℤ} (hx : InA x) (hy : InA y) : InA (x + y) := by
  unfold InA at *
  omega

/-- Row of the dual of the Gale row `(7,17,18,8; 35)`. -/
def xRow : Row := ⟨8, 18, 17, 7, 35⟩

/-- Row of the dual of the Gale row `(7,17,18,8; 36)`. -/
def uRow : Row := ⟨8, 18, 17, 7, 36⟩

lemma smallRows_InA : ∀ R ∈ smallRows, InA R.L1 := by decide

lemma smallRows_g0 : ∀ R ∈ smallRows, R.g = 0 →
    R.L1 = 0 ∨ R.L1 = 5 ∨ R.L1 = 10 ∨ R.L1 = 14 ∨ R.L1 = 15 ∨ 20 ≤ R.L1 := by decide

lemma smallRows_zero : ∀ R ∈ smallRows, R.g = 0 → R.L1 = 0 → R = sRow ∨ R = excRow := by decide

lemma smallRows_dual8 : ∀ R ∈ smallRows, R.r = 8 →
    R.dual = tRow ∨ R.dual = xRow ∨ R.dual = uRow ∨ R.dual = zRow := by decide

/-- **Facts on the facet rows at sixteen vertices.** -/
theorem row16_facts (hcls : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows) {R : Row}
    (hR : IsRealRow R) (h8 : R.n ≤ 8) (hT : R ≠ tRow) :
    0 ≤ R.Lx ∧ (R.n ≤ 7 → InA R.Lx) ∧ (R.n = 8 → 13 ≤ R.Lx) ∧
    (R.g = 0 → R.n = 8 → (R.Lx = 14 ∨ R.Lx = 18 ∨ 20 ≤ R.Lx) ∧ (R.Lx = 18 → R = zRow)) ∧
    (R.g = 0 → R.n ≤ 7 → R.Lx = 0 → R = sRow ∨ R = excRow) := by
  rcases Nat.lt_or_ge R.n 8 with h7 | h8'
  · have hmem := hcls R hR (by omega)
    have hLx : R.Lx = R.L1 := by simp [Row.Lx, show R.n ≠ 8 by omega]
    have hA := smallRows_InA R hmem
    rw [hLx]
    refine ⟨by unfold InA at hA; omega, fun _ => hA, fun h => by omega, fun _ h => by omega,
      fun hg _ h0 => smallRows_zero R hmem hg h0⟩
  · have hn : R.n = 8 := by omega
    have hLx : R.Lx = R.L1 + 9 := by simp [Row.Lx, hn]
    rcases Nat.lt_or_ge R.r 8 with hr | hr
    · -- the dual row is a Gale row with eight facets
      have hd := realRow_dual hR
      have hmem := hcls _ hd (show R.r ≤ 7 by omega)
      have hdd : (⟨R.r, R.p, R.e, R.n, R.J⟩ : Row).dual = R := rfl
      rcases smallRows_dual8 _ hmem (by simp [hn]) with h | h | h | h <;> rw [hdd] at h
      · exact absurd h hT
      · subst h; decide
      · subst h; decide
      · subst h; decide
    · -- many facets: Euler and `J + 4n ≤ 4e`
      have he := realRow_euler hR
      have hb := realRow_B4 hR
      rw [hLx]
      simp only [Row.L1, Row.g]
      refine ⟨by omega, fun h => by omega, fun _ => by omega, fun hg _ => ⟨by omega, fun h => by omega⟩,
        fun _ h => by omega⟩

/-! ### Lists of rows -/

section lists

lemma sum_InA (f : Row → ℤ) {l : List Row} (h : ∀ R ∈ l, InA (f R)) : InA (l.map f).sum := by
  induction l with
  | nil => simp [InA]
  | cons R l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (h R List.mem_cons_self).add (ih fun S hS => h S (List.mem_cons_of_mem _ hS))

lemma le_sum_of_forall (f : Row → ℤ) {l : List Row} {c : ℤ} (h : ∀ R ∈ l, c ≤ f R) :
    c * l.length ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons R l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have h1 := h R List.mem_cons_self
    have h2 := ih fun S hS => h S (List.mem_cons_of_mem _ hS)
    push_cast
    linarith

lemma eq_zero_of_sum_eq_zero (f : Row → ℤ) {l : List Row} (h0 : ∀ R ∈ l, 0 ≤ f R)
    (hs : (l.map f).sum = 0) : ∀ R ∈ l, f R = 0 := by
  induction l with
  | nil => simp
  | cons R l ih =>
    simp only [List.map_cons, List.sum_cons] at hs
    have h1 := h0 R List.mem_cons_self
    have h2 : 0 ≤ (l.map f).sum := List.sum_nonneg fun x hx => by
      obtain ⟨S, hS, rfl⟩ := List.mem_map.1 hx
      exact h0 S (List.mem_cons_of_mem _ hS)
    intro S hS
    rcases List.mem_cons.1 hS with rfl | hS
    · linarith
    · exact ih (fun T hT => h0 T (List.mem_cons_of_mem _ hT)) (by linarith) S hS

lemma sum_split (f : Row → ℤ) (p : Row → Bool) (l : List Row) :
    (l.map f).sum = ((l.filter p).map f).sum + ((l.filter fun R => !p R).map f).sum := by
  induction l with
  | nil => simp
  | cons R l ih =>
    by_cases hp : p R = true
    · simp [List.filter_cons, hp, ih]; ring
    · simp [List.filter_cons, hp, ih]; ring

lemma sum_three {M : Type*} [AddCommMonoid M] (g : Row → M) {a b c : Row} {l : List Row}
    (h : ∀ R ∈ l, R = a ∨ R = b ∨ R = c) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (l.map g).sum = l.count a • g a + l.count b • g b + l.count c • g c := by
  induction l with
  | nil => simp
  | cons R l ih =>
    have ih' := ih fun S hS => h S (List.mem_cons_of_mem _ hS)
    simp only [List.map_cons, List.sum_cons, List.count_cons, ih']
    rcases h R List.mem_cons_self with rfl | rfl | rfl
    · simp [hab, hac, add_smul]; abel
    · simp [hab.symm, hbc, add_smul]; abel
    · simp [hac.symm, hbc.symm, add_smul]; abel

lemma length_three {a b c : Row} {l : List Row} (h : ∀ R ∈ l, R = a ∨ R = b ∨ R = c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    l.length = l.count a + l.count b + l.count c := by
  have := sum_three (fun _ => (1 : ℕ)) h hab hac hbc
  simpa using this

end lists

/-- `A` is even for valid flag data. -/
lemma FlagData.even_A {D : FlagData} (hD : D.Valid) : Even D.A := by
  obtain ⟨a, ha⟩ := hD.even_I; obtain ⟨b, hb⟩ := hD.even_x
  obtain ⟨c, hc⟩ := hD.even_y; obtain ⟨e, he⟩ := hD.even_p
  have h := hD.f024_eq
  refine ⟨2 * a - b - c - 2 * (D.e + D.r) + 9 * e, ?_⟩
  simp only [FlagData.A]
  rw [h, ha, hb, hc, he]
  push_cast
  ring

/-! ### The counting closure -/

set_option maxHeartbeats 1000000 in
/-- **Endpoint `(16,22)` by counting**: a counterexample has exactly `6` simplex facets, `14`
pyramids over triangular prisms and `2` facets of row `zRow`, and no other facets. -/
theorem closure_16_22 {D : FlagData} (hD : D.Valid) (F : FacetRows D) (hv : D.v = 16)
    (hh : D.h = 22) (hcls : ∀ R, IsRealRow R → R.n ≤ 7 → R ∈ smallRows)
    (hrows : ∀ R ∈ F.rows, IsRealRow R ∧ R.n ≤ 8 ∧ R ≠ tRow ∧ 0 ≤ R.g ∧ 2 * R.g ≤ D.G)
    (hAG : D.G = 0 → D.A = 0) (heven : ∀ q : Row → Bool, Even (F.rows.filter q).length)
    (hlt : D.total < 243) :
    (∀ R ∈ F.rows, R = sRow ∨ R = excRow ∨ R = zRow) ∧
      F.rows.count sRow = 6 ∧ F.rows.count excRow = 14 ∧ F.rows.count zRow = 2 := by
  have hf : ∀ R ∈ F.rows, _ := fun R hR =>
    row16_facts hcls (hrows R hR).1 (hrows R hR).2.1 (hrows R hR).2.2.1
  -- `t ≤ 118`
  have ht : D.t ≤ 118 := by
    by_contra h
    exact absurd (FlagData.total_ge_of_t_gt hD (by omega)) (by omega)
  have htev := FlagData.even_t hD
  -- the identity
  have hsum := F.sum_L1 hD
  rw [hv, hh] at hsum
  set l := F.rows with hl
  set l8 := l.filter fun R => decide (R.n = 8) with hl8
  set l7 := l.filter fun R => !decide (R.n = 8) with hl7
  have hLx : (l.map Row.Lx).sum = (l.map Row.L1).sum + 9 * l8.length := by
    have h1 : (l.map Row.Lx).sum = (l.map Row.L1).sum +
        (l.map fun R => if R.n = 8 then (9 : ℤ) else 0).sum := by
      rw [← List.sum_map_add]
      rfl
    rw [h1, sum_map_ite]
  have hsplit := sum_split Row.Lx (fun R => decide (R.n = 8)) l
  rw [← hl8, ← hl7] at hsplit
  have h7mem : ∀ R ∈ l7, R ∈ l ∧ R.n ≤ 7 := fun R hR => by
    rw [hl7, List.mem_filter] at hR
    have := (hrows R hR.1).2.1
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hR
    exact ⟨hR.1, by omega⟩
  have h8mem : ∀ R ∈ l8, R ∈ l ∧ R.n = 8 := fun R hR => by
    rw [hl8, List.mem_filter, decide_eq_true_eq] at hR
    exact hR
  have hs7 : InA (l7.map Row.Lx).sum :=
    sum_InA _ fun R hR => (hf R (h7mem R hR).1).2.1 (h7mem R hR).2
  have hs8 : 13 * (l8.length : ℤ) ≤ (l8.map Row.Lx).sum :=
    le_sum_of_forall _ fun R hR => (hf R (h8mem R hR).1).2.2.1 (h8mem R hR).2
  have hm8 : Even l8.length := heven _
  have hGev := FlagData.even_G hD
  have hAev := FlagData.even_A hD
  have hG0 := hD.G_nonneg
  have hA0 := hD.A_nonneg
  obtain ⟨m, hm⟩ := hm8
  obtain ⟨g2, hg2⟩ := hGev
  obtain ⟨a2, ha2⟩ := hAev
  obtain ⟨t2, ht2⟩ := htev
  by_cases hG : D.G = 0
  · -- `G = 0`: all facets have `g = 0`, and `A = 0`
    have hA := hAG hG
    have hg0 : ∀ R ∈ l, R.g = 0 := fun R hR => by
      have h1 := (hrows R hR).2.2.2.1
      have h2 := (hrows R hR).2.2.2.2
      rw [hG] at h2
      omega
    have hs8' : 14 * (l8.length : ℤ) ≤ (l8.map Row.Lx).sum :=
      le_sum_of_forall _ fun R hR => by
        have := ((hf R (h8mem R hR).1).2.2.2.1 (hg0 R (h8mem R hR).1) (h8mem R hR).2).1
        omega
    -- `m ≤ 1`, i.e. `m ∈ {0, 2}`
    have hle : (l8.length : ℤ) ≤ 3 := by
      unfold InA at hs7
      push_cast at hsum
      omega
    rcases (show m = 0 ∨ m = 1 by omega) with hm0 | hm1
    · -- no facet with eight vertices
      exfalso
      have hl80 : l8 = [] := List.length_eq_zero_iff.1 (by omega)
      rw [hl80] at hsplit
      simp only [List.map_nil, List.sum_nil, zero_add] at hsplit
      unfold InA at hs7
      push_cast at hsum
      rw [hl80] at hLx
      simp only [List.length_nil, Nat.cast_zero, mul_zero, add_zero] at hLx
      omega
    · -- two facets with eight vertices, of the same row
      obtain ⟨R1, R2, h12⟩ := List.length_eq_two.1 (show l8.length = 2 by omega)
      have hR1 : R1 ∈ l8 := by rw [h12]; simp
      have hR1l := h8mem R1 hR1
      have hcount : 2 ≤ l.count R1 := by
        have hev := heven fun R => R == R1
        rw [← List.count_eq_length_filter] at hev
        have hpos : 0 < l.count R1 := List.count_pos_iff.2 hR1l.1
        obtain ⟨k, hk⟩ := hev
        omega
      have hcount8 : l8.count R1 = l.count R1 := by
        rw [hl8, List.count_filter]
        simp [hR1l.2]
      have hR2 : R2 = R1 := by
        by_contra hne
        rw [h12] at hcount8
        simp [List.count_cons, Ne.symm hne] at hcount8
        omega
      subst hR2
      have hs8eq : (l8.map Row.Lx).sum = 2 * R2.Lx := by rw [h12]; simp; ring
      have hd := (hf R2 hR1l.1).2.2.2.1 (hg0 R2 hR1l.1) hR1l.2
      have h18 : R2.Lx = 18 ∧ (l7.map Row.Lx).sum = 0 := by
        unfold InA at hs7
        push_cast at hsum
        omega
      have hZ : R2 = zRow := hd.2 h18.1
      -- every other facet has cost `0`: a simplex or a pyramid over a prism
      have h7zero := eq_zero_of_sum_eq_zero Row.Lx (fun R hR => (hf R (h7mem R hR).1).1) h18.2
      have hall : ∀ R ∈ l, R = sRow ∨ R = excRow ∨ R = zRow := by
        intro R hR
        by_cases hn : R.n = 8
        · have hR8 : R ∈ l8 := by rw [hl8, List.mem_filter]; exact ⟨hR, by simp [hn]⟩
          rw [h12] at hR8
          simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hR8
          right; right; rw [hR8, hZ]
        · have hR7 : R ∈ l7 := by rw [hl7, List.mem_filter]; exact ⟨hR, by simp [hn]⟩
          have h0 := h7zero R hR7
          rcases (hf R hR).2.2.2.2 (hg0 R hR) (h7mem R hR7).2 h0 with h | h
          · left; exact h
          · right; left; exact h
      -- counting vertices
      have hZcount : l.count zRow = 2 := by
        rw [← hZ, ← hcount8, h12]
        simp
      have hlen := length_three hall (by decide) (by decide) (by decide)
      rw [F.length_eq, hh] at hlen
      have hsn := sum_three (fun R => (R.n : ℤ)) hall (by decide) (by decide) (by decide)
      simp only [nsmul_eq_mul] at hsn
      have e5 : ((sRow.n : ℕ) : ℤ) = 5 := rfl
      have e7 : ((excRow.n : ℕ) : ℤ) = 7 := rfl
      have e8 : ((zRow.n : ℕ) : ℤ) = 8 := rfl
      rw [e5, e7, e8] at hsn
      have hsg := F.sum_g hD
      rw [← hl] at hsg
      have hg0sum : (l.map Row.g).sum = 0 := by
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx
        exact hg0 R hR
      rw [hg0sum, hG, hv, hh] at hsg
      have hIn := F.sum_n
      rw [← hl] at hIn
      have hsn' : ((l.map Row.n).sum : ℤ) = (l.map fun R => (R.n : ℤ)).sum := by
        rw [Nat.cast_list_sum, List.map_map]
        rfl
      rw [hsn, hIn] at hsn'
      refine ⟨hall, ?_, ?_, hZcount⟩
      · push_cast at hsn' hsg hlen
        omega
      · push_cast at hsn' hsg hlen
        omega
  · -- `G ≥ 2`
    exfalso
    have hm0 : m = 0 := by
      unfold InA at hs7
      push_cast at hsum
      omega
    have hl80 : l8 = [] := List.length_eq_zero_iff.1 (by omega)
    rw [hl80] at hsplit hLx
    simp only [List.map_nil, List.sum_nil, zero_add, List.length_nil, Nat.cast_zero, mul_zero,
      add_zero] at hsplit hLx
    unfold InA at hs7
    push_cast at hsum
    omega

/-! ### The endpoint -/

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The flag data of a centrally symmetric 5-polytope is valid (all fields proved). -/
theorem IsCSPolytope5.flagData_valid : (flagDataOf P).Valid where
  euler := hP.euler_relation
  even_v := hP.even_fvec 0 (by norm_num)
  even_e := hP.even_fvec 1 (by norm_num)
  even_p := hP.even_fvec 2 (by norm_num)
  even_r := hP.even_fvec 3 (by norm_num)
  even_h := hP.even_fvec 4 (by norm_num)
  even_I := hP.even_flag2 0 4 le_rfl
  even_x := hP.even_flag2 0 2 (by norm_num)
  even_y := hP.even_flag2 2 4 le_rfl
  f03_eq := hP.flag03_identity
  f14_eq := hP.flag14_of_polar hP.polar.flag03_identity
  f13_eq := hP.flag13_identity
  f024_eq := hP.flag024_identity
  A_nonneg := hP.A_nonneg
  B_nonneg := hP.B_nonneg
  C_nonneg := by have := hP.polar.B_nonneg; rwa [hP.B_polar] at this
  G_nonneg := hP.G_nonneg_of_whiteley (hP.whiteleyCS_of_w3 alexandrov3_proof)
  Gs_nonneg := by
    have := hP.polar.G_nonneg_of_whiteley (hP.polar.whiteleyCS_of_w3 alexandrov3_proof)
    rwa [hP.G_polar] at this
  incidence := hP.incidence_bound

/-- The facet rows of a centrally symmetric 5-polytope. -/
noncomputable def IsCSPolytope5.rowsData : FacetRows (flagDataOf P) where
  rows := facetRows P
  length_eq := hP.facetRows_length
  sum_n := hP.facetRows_sum_n
  sum_e := hP.facetRows_sum_e
  sum_p := hP.facetRows_sum_p
  sum_r := hP.facetRows_sum_r
  sum_J := hP.facetRows_sum_J

end cs

/-- Three-faces with six vertices by row, for the three rows of the residual profile. -/
def sixOf (R : Row) : ℕ := if R = excRow then 1 else if R = zRow then 2 else 0

/-- **Endpoint `(16,22)`.** -/
theorem endpoint_16_22_proof : EndpointClaim 16 22 := by
  intro P hP hv hh
  by_contra hlt
  push_neg at hlt
  by_cases hT : tRow ∈ facetRows P
  · exact absurd (hP.full_prism hv hT) (by omega)
  have hD := hP.flagData_valid
  have htot : (flagDataOf P).total < 243 := by
    have h := hP.faces_ncard
    change _ = (flagDataOf P).total at h
    rw [← h]
    exact hlt
  have hW := hP.whiteleyCS_of_w3 alexandrov3_proof
  obtain ⟨hall, hS, hY, hZ⟩ := closure_16_22 hD hP.rowsData hv hh
    Gale.small_classification_proof
    (fun R hR => ⟨hP.facetRows_real R hR, by have := hP.facetRows_n_le R hR; omega,
      fun h => hT (h ▸ hR), hP.facet_g_nonneg R hR, hP.stress_localization_of_whiteley hW R hR⟩)
    hP.A_eq_zero_of_G_eq_zero (fun q => hP.facetRows_filter_even q) htot
  -- ridge parity
  have hsix : ∀ F ∈ (hP.kfaces_finite 4).toFinset, six3 P F = sixOf (faceRow P F) := by
    intro F hF
    rw [Set.Finite.mem_toFinset] at hF
    have hmem : faceRow P F ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨F, by simp [hF.1, hF.2], rfl⟩
    rcases hall _ hmem with h | h | h
    · rw [hP.six3_sRow h, h]; decide
    · rw [hP.six3_excRow hF.1 hF.2 h, h]; decide
    · rw [hP.six3_zRow hF.1 hF.2 h, h]; decide
  have h18 : ∑ F ∈ (hP.kfaces_finite 4).toFinset, six3 P F = 18 := by
    rw [Finset.sum_congr rfl hsix, ← hP.facetRows_sum sixOf]
    have := sum_three sixOf hall (by decide) (by decide) (by decide)
    change ((hP.rowsData).rows.map sixOf).sum = 18
    rw [this, hS, hY, hZ]
    decide
  have h4 := hP.four_dvd_sum_six3
  rw [h18] at h4
  omega

end Kalai5
