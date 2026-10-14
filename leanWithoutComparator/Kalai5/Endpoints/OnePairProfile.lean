import Kalai5.Endpoints.SixteenEighteenLow
import Kalai5.Endpoints.OnePairArithmetic

/-!
# The actual facet profile in the one-full-pair residual case

Antipodal parity turns row multiplicities into integer pair counts. Summing
over the nine seven-vertex zero-stress rows then supplies the hypotheses of
`one_pair_profile_arithmetic`. No catalogue of eight-vertex polytopes is used.
-/

namespace Kalai5

namespace OnePairProfile

def jRow : Row := ⟨7, 17, 17, 7, 32⟩
def fullRow (k : ℕ) : Row := ⟨8, k, k, 8, 38⟩

def sevenRows : List Row :=
  [excRow, eRow, jRow, ⟨7, 17, 18, 8, 35⟩, ⟨7, 17, 19, 9, 38⟩,
   ⟨7, 18, 19, 8, 35⟩, ⟨7, 18, 20, 9, 38⟩, ⟨7, 18, 21, 10, 41⟩,
   ⟨7, 18, 22, 11, 44⟩]

lemma seven_classification : ∀ R ∈ smallRows, R.n = 7 → R.g = 0 →
    R ∈ sevenRows := by decide +kernel

/-- Count a list by any finite, duplicate-free catalogue containing its support. -/
lemma sum_catalogue {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (l catalogue : List α) (f : α → M) (hn : catalogue.Nodup)
    (hs : ∀ a ∈ l, a ∈ catalogue) :
    (l.map f).sum = (catalogue.map fun a => l.count a • f a).sum := by
  rw [Finset.sum_list_map_count, ← List.sum_toFinset _ hn]
  apply Finset.sum_subset
  · intro a ha
    exact List.mem_toFinset.2 (hs a (List.mem_toFinset.1 ha))
  · intro a _ ha
    rw [List.count_eq_zero_of_not_mem (fun h => ha (List.mem_toFinset.2 h)), zero_nsmul]

/-- With even multiplicities, a filter of length two contains a single row twice. -/
lemma full_pair_uniform (l : List Row)
    (heven : ∀ q : Row → Bool, Even (l.filter q).length) (hc : cnt8 l = 2) :
    ∃ R ∈ l, R.n = 8 ∧ l.count R = 2 ∧ ∀ S ∈ l, S.n = 8 → S = R := by
  let l8 := l.filter fun R => decide (R.n = 8)
  obtain ⟨R, S, hrs⟩ := List.length_eq_two.1 hc
  have hmem : R ∈ l8 := by change R ∈ l.filter _; rw [hrs]; simp
  obtain ⟨hRl, hRn⟩ := List.mem_filter.1 hmem
  have hn : R.n = 8 := of_decide_eq_true hRn
  have hct : l8.count R = l.count R := List.count_filter hRn
  have hev := heven fun T => T == R
  rw [← List.count_eq_length_filter] at hev
  have hpos := List.count_pos_iff.2 hRl
  have htwo : 2 ≤ l.count R := by obtain ⟨a, ha⟩ := hev; omega
  have hSR : S = R := by
    by_contra hne
    change (l.filter _).count R = l.count R at hct
    rw [hrs] at hct
    simp [hne] at hct
    omega
  subst S
  have hcount : l.count R = 2 := by
    change (l.filter _).count R = l.count R at hct
    simpa [hrs] using hct.symm
  refine ⟨R, hRl, hn, hcount, ?_⟩
  intro T hT hTn
  have hm : T ∈ l.filter (fun U => decide (U.n = 8)) :=
    List.mem_filter.2 ⟨hT, by simp [hTn]⟩
  simpa [hrs] using hm

lemma full_weight (k : ℕ) (hlo : 19 ≤ k) (hhi : k ≤ 22) :
    q55StrongRowWeight (fullRow k) = if k = 19 then 3 else 0 := by
  interval_cases k <;> decide +kernel

/-- The list-level closure: all nine integer variables are actual row counts. -/
theorem counts_closure (l : List Row) (k e r : ℕ)
    (hklo : 19 ≤ k) (hkhi : k ≤ 22)
    (hs : ∀ R ∈ l, R ∈ fullRow k :: sevenRows)
    (heven : ∀ q : Row → Bool, Even (l.filter q).length)
    (hc : l.count (fullRow k) = 2) (hlen : l.length = 18)
    (he : (l.map Row.e).sum = 3 * e + 122)
    (hr : (l.map Row.r).sum = 2 * r)
    (ht : e + r ≤ 118)
    (hw : (l.map q55StrongRowWeight).sum + 6 * e ≤ 420) :
    k = 20 ∧ l.count excRow = 8 ∧ l.count jRow = 8 ∧ e = 58 ∧ r = 60 ∧
      ∀ R ∈ l, R = excRow ∨ R = jRow ∨ R = fullRow 20 := by
  have even_count : ∀ R, Even (l.count R) := by
    intro R
    simpa only [List.count_eq_length_filter] using heven (fun S => S == R)
  obtain ⟨y, hy⟩ := even_count excRow
  obtain ⟨q, hq⟩ := even_count eRow
  obtain ⟨j, hj⟩ := even_count jRow
  obtain ⟨a, ha⟩ := even_count ⟨7, 17, 18, 8, 35⟩
  obtain ⟨b, hb⟩ := even_count ⟨7, 17, 19, 9, 38⟩
  obtain ⟨c, hc'⟩ := even_count ⟨7, 18, 19, 8, 35⟩
  obtain ⟨d, hd⟩ := even_count ⟨7, 18, 20, 9, 38⟩
  obtain ⟨u, hu⟩ := even_count ⟨7, 18, 21, 10, 41⟩
  obtain ⟨v, hv⟩ := even_count ⟨7, 18, 22, 11, 44⟩
  have hn : (fullRow k :: sevenRows).Nodup := by
    simp [sevenRows, fullRow, excRow, eRow, jRow, List.nodup_cons]
  have hsum := fun f : Row → ℕ => sum_catalogue l (fullRow k :: sevenRows) f hn hs
  have hl := hsum (fun _ => 1)
  have he' := hsum Row.e
  have hr' := hsum Row.r
  have hw' := hsum q55StrongRowWeight
  simp only [sevenRows, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    hc, hy, hq, hj, ha, hb, hc', hd, hu, hv, smul_eq_mul] at hl he' hr' hw'
  simp only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one, hlen] at hl
  have hcount : y + q + j + a + b + c + d + u + v = 8 := by linarith only [hl]
  have hedges : 3 * e + 122 = 2 * k + 30 * y + 32 * q + 34 * j +
      34 * a + 34 * b + 36 * c + 36 * d + 36 * u + 36 * v := by
    simp only [he, fullRow, excRow, eRow, jRow] at he'
    linarith only [he']
  have hridges : r = 8 + 6 * y + 7 * q + 7 * j + 8 * a + 9 * b +
      8 * c + 9 * d + 10 * u + 11 * v := by
    simp only [hr, fullRow, excRow, eRow, jRow] at hr'
    linarith only [hr']
  have hweight : 9 * y + 4 * q + (if k = 19 then 3 else 0) + 3 * e ≤ 210 := by
    rw [full_weight k hklo hkhi] at hw'
    norm_num [q55StrongRowWeight, q55RowWeight, q55ElementaryWeight,
      excRow, eRow, jRow, r0Row, r35Row, zRow] at hw'
    by_cases hk19 : k = 19 <;> simp only [hk19, ite_true, ite_false] at hw' ⊢ <;>
      linarith only [hw, hw']
  obtain ⟨hk, hy4, hj4, hq0, ha0, hb0, hc0, hd0, hu0, hv0, he58, hr60⟩ :=
    one_pair_profile_arithmetic k y q j a b c d u v e r hklo hkhi
      hcount hedges hridges ht hweight
  refine ⟨hk, by simpa only [hy4] using hy, by simpa only [hj4] using hj, he58, hr60, ?_⟩
  intro R hR
  have hm := hs R hR
  have hp := List.count_pos_iff.2 hR
  simp only [List.mem_cons, List.not_mem_nil, or_false, sevenRows] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h
  · exact Or.inr (Or.inr (by simpa [hk] using h))
  · exact Or.inl h
  · rw [h, hq, hq0] at hp; omega
  · exact Or.inr (Or.inl h)
  · rw [h, ha, ha0] at hp; omega
  · rw [h, hb, hb0] at hp; omega
  · rw [h, hc', hc0] at hp; omega
  · rw [h, hd, hd0] at hp; omega
  · rw [h, hu, hu0] at hp; omega
  · rw [h, hv, hv0] at hp; omega

end OnePairProfile

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The two global budgets used in the integer profile calculation. -/
lemma IsCSPolytope5.fewFull18_one_pair_budgets
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    (flagDataOf P).f14 = 3 * (flagDataOf P).e + 122 ∧
      ((facetRows P).map q55StrongRowWeight).sum + 6 * (flagDataOf P).e ≤ 420 := by
  obtain ⟨hG, hS⟩ := hP.fewFull18_one_pair_stresses hv hh hc hlt
  have hI := hP.fewFull18_one_pair_incidence hv hh hc hlt
  have hA := hP.A_eq_zero_of_G_eq_zero hG
  have hw := hP.q55_strong_rows hv
  have hD := hP.flagData_valid
  have he := hD.euler
  have hf := hD.f14_eq
  have h024 := hD.f024_eq
  have hvD : (flagDataOf P).v = 16 := hv
  have hhD : (flagDataOf P).h = 18 := hh
  simp only [FlagData.G, FlagData.Gs, FlagData.A, hvD, hhD, hI] at hG hS hA he hf hw h024
  constructor
  · omega
  · omega

/-- A one-full-pair counterexample has exactly eight Y, eight J, and two H
facets, with H = (8,20,20,8;38), and global edge/ridge counts 58 and 60. -/
theorem IsCSPolytope5.fewFull18_one_pair_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    (∀ R ∈ facetRows P, R = excRow ∨ R = OnePairProfile.jRow ∨
      R = OnePairProfile.fullRow 20) ∧
    (facetRows P).count excRow = 8 ∧
    (facetRows P).count OnePairProfile.jRow = 8 ∧
    (facetRows P).count (OnePairProfile.fullRow 20) = 2 ∧
    (flagDataOf P).e = 58 ∧ (flagDataOf P).r = 60 := by
  obtain ⟨R, hR, hn, hRc, hfull⟩ := OnePairProfile.full_pair_uniform
    (facetRows P) hP.facetRows_filter_even hc
  obtain ⟨k, hklo, hkhi, hk⟩ := hP.fewFull18_one_pair_full_row_candidates hv hh hc hlt hR hn
  change R = OnePairProfile.fullRow k at hk
  have hG := (hP.fewFull18_one_pair_stresses hv hh hc hlt).1
  have h7 := hP.fewFull18_one_pair_rows_ge_seven hv hh hc hlt
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hs : ∀ S ∈ facetRows P, S ∈ OnePairProfile.fullRow k :: OnePairProfile.sevenRows := by
    intro S hS
    by_cases hSn : S.n = 8
    · exact List.mem_cons.2 (Or.inl ((hfull S hS hSn).trans hk))
    · have hrow := C.rowF S hS
      have hn7 := h7 S hS
      have hn8 := hrow.n_le
      have hg0 := hrow.g_nonneg
      have hgb := hrow.g_le
      change 2 * S.g ≤ (flagDataOf P).G at hgb
      rw [hG] at hgb
      exact List.mem_cons.2 (Or.inr (OnePairProfile.seven_classification S
        (hrow.small (by omega)) (by omega) (by omega)))
  obtain ⟨hf14, hweight⟩ := hP.fewFull18_one_pair_budgets hv hh hc hlt
  have he : ((facetRows P).map Row.e).sum = 3 * (flagDataOf P).e + 122 :=
    hP.facetRows_sum_e.trans hf14
  obtain ⟨hk20, hY, hJ, he58, hr60, hall⟩ := OnePairProfile.counts_closure
    (facetRows P) k (flagDataOf P).e (flagDataOf P).r hklo hkhi hs
    hP.facetRows_filter_even (by simpa only [hk] using hRc)
    (hP.facetRows_length.trans hh) he hP.facetRows_sum_r
    (by exact_mod_cast hP.t_le_of_faces_lt hlt) hweight
  exact ⟨hall, hY, hJ, by simpa only [hk, hk20] using hRc, he58, hr60⟩

/-- All face and flag numbers are fixed by the one-pair profile. -/
theorem IsCSPolytope5.fewFull18_one_pair_flagData
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243) :
    flagDataOf P = ⟨16, 58, 86, 60, 18, 128, 270, 288, 282, 450, 296, 900⟩ := by
  obtain ⟨-, -, -, -, he, hr⟩ := hP.fewFull18_one_pair_profile hv hh hc hlt
  obtain ⟨hG, hS⟩ := hP.fewFull18_one_pair_stresses hv hh hc hlt
  have hI := hP.fewFull18_one_pair_incidence hv hh hc hlt
  have hD := hP.flagData_valid
  have hvD : (flagDataOf P).v = 16 := hv
  have hhD : (flagDataOf P).h = 18 := hh
  have heul := hD.euler
  have h03 := hD.f03_eq
  have h13 := hD.f13_eq
  have h14 := hD.f14_eq
  have h024 := hD.f024_eq
  simp only [FlagData.G, FlagData.Gs, hvD, hhD, he, hr, hI] at hG hS heul h03 h13 h14 h024
  rcases hEq : flagDataOf P with ⟨v, e, p, r, h, I, x, y, f03, f13, f14, f024⟩
  simp only [hEq] at hvD hhD he hr hI hG hS heul h03 h13 h14 h024
  congr 1 <;> omega

end Kalai5
