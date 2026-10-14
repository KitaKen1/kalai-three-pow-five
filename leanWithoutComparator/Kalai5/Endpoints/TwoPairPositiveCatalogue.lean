import Kalai5.Endpoints.TwoPairZeroRows

/-! Finite local row support for positive-stress two-full-pair configurations.
The 8-vertex table is an arithmetic superset, not a realizability catalogue. -/
namespace Kalai5.TwoPairPositiveProfile

def sevenRows : List Row :=
  [⟨7,15,14,6,29⟩,
   ⟨7,16,16,7,32⟩,
   ⟨7,17,17,7,32⟩,
   ⟨7,17,18,8,35⟩,
   ⟨7,17,18,8,36⟩,
   ⟨7,17,19,9,38⟩,
   ⟨7,18,19,8,35⟩,
   ⟨7,18,20,9,38⟩,
   ⟨7,18,20,9,39⟩,
   ⟨7,18,21,10,41⟩,
   ⟨7,18,21,10,42⟩,
   ⟨7,18,22,11,44⟩,
   ⟨7,19,22,10,42⟩,
   ⟨7,19,23,11,45⟩,
   ⟨7,19,24,12,48⟩]

def fullRows : List Row :=
  [⟨8,18,17,7,35⟩,
   ⟨8,18,17,7,36⟩,
   ⟨8,19,18,7,35⟩,
   ⟨8,19,19,8,38⟩,
   ⟨8,19,19,8,39⟩,
   ⟨8,19,20,9,41⟩,
   ⟨8,20,20,8,38⟩,
   ⟨8,20,20,8,39⟩,
   ⟨8,20,21,9,41⟩,
   ⟨8,20,21,9,42⟩,
   ⟨8,20,22,10,44⟩,
   ⟨8,20,22,10,45⟩,
   ⟨8,21,21,8,38⟩,
   ⟨8,21,21,8,39⟩,
   ⟨8,21,22,9,41⟩,
   ⟨8,21,22,9,42⟩,
   ⟨8,21,23,10,44⟩,
   ⟨8,21,23,10,45⟩,
   ⟨8,21,24,11,47⟩,
   ⟨8,21,24,11,48⟩,
   ⟨8,22,22,8,38⟩,
   ⟨8,22,22,8,39⟩,
   ⟨8,22,23,9,41⟩,
   ⟨8,22,23,9,42⟩,
   ⟨8,22,24,10,44⟩,
   ⟨8,22,24,10,45⟩,
   ⟨8,22,25,11,47⟩,
   ⟨8,22,25,11,48⟩,
   ⟨8,23,23,8,39⟩,
   ⟨8,23,24,9,42⟩,
   ⟨8,23,25,10,45⟩,
   ⟨8,23,26,11,48⟩]

def catalogue : List Row := sevenRows ++ fullRows

lemma catalogue_nodup : catalogue.Nodup := by decide +kernel

lemma seven_classification : ∀ R ∈ smallRows,
    R.n = 7 → 0 ≤ R.g → R.g ≤ 1 → R ∈ sevenRows := by decide +kernel

lemma full_small_dual_classification : ∀ S ∈ smallRows,
    S.r = 8 → 0 ≤ S.g → S.g ≤ 1 → S.dual ≠ tRow → S.dual ∈ fullRows := by
  decide +kernel

lemma full_box_classification {R : Row} (hn : R.n = 8)
    (hrlo : 8 ≤ R.r) (hrhi : R.r ≤ 11) (hg0 : 0 ≤ R.g) (hg1 : R.g ≤ 1)
    (he : (R.n : ℤ) - R.e + R.p - R.r = 0)
    (hB : R.J + 4 * R.n ≤ 4 * R.e)
    (hX : R.e + 3 * R.r ≤ R.J + R.n)
    (hf : R ∉ fake8) : R ∈ fullRows := by
  rcases R with ⟨n,e,p,r,J⟩
  change n = 8 at hn
  subst n
  change 8 ≤ r at hrlo
  change r ≤ 11 at hrhi
  change 0 ≤ (J : ℤ) - 3 * 8 - 3 * r + 10 at hg0
  change (J : ℤ) - 3 * 8 - 3 * r + 10 ≤ 1 at hg1
  change (8 : ℤ) - e + p - r = 0 at he
  change J + 4 * 8 ≤ 4 * e at hB
  change e + 3 * r ≤ J + 8 at hX
  have hJ : J = 14 + 3 * r ∨ J = 15 + 3 * r := by omega
  have hp : p = e + r - 8 := by omega
  have hlo : 18 ≤ e := by omega
  have hhi : e ≤ 23 := by omega
  subst p
  rcases hJ with hJ | hJ <;> subst J <;> interval_cases r <;> interval_cases e
  all_goals first
    | decide +kernel
    | omega
    | exact (hf (by decide +kernel)).elim

end Kalai5.TwoPairPositiveProfile

namespace Kalai5
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The sole full row with at most six ridges is the excluded prism. -/
theorem IsCSPolytope5.full_row_r_ge_seven
    (hT : tRow ∉ facetRows P) {R : Row} (hR : R ∈ facetRows P) (hn : R.n = 8) :
    7 ≤ R.r := by
  by_contra hbad
  have hctx := hP.rowOK_P_le (nmax := fvec P 0)
    (fun S hS => by have := hP.facetRows_n_le S hS; omega)
    (show ∀ S ∈ facetRows P, S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil) R hR
  have hs := hctx.smalld (by omega)
  have hcheck : ∀ S ∈ smallRows, S.r = 8 → S.n ≤ 6 → S.dual = tRow := by
    decide +kernel
  have hx := hcheck R.dual hs hn (by change R.r ≤ 6; omega)
  rw [Row.dual_dual] at hx
  exact hT (hx ▸ hR)

/-- Four full facets have total ridge count at most 36, forcing each to have at most 11. -/
theorem IsCSPolytope5.two_pair_full_ridge_bounds
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hT : tRow ∉ facetRows P)
    {R : Row} (hR : R ∈ facetRows P) (hn : R.n = 8) :
    7 ≤ R.r ∧ R.r ≤ 11 := by
  have hr7 := hP.full_row_r_ge_seven hT hR hn
  have hct := two_le_count_of_even (facetRows P) hP.facetRows_filter_even hR
  have hs8 : sumR8 (facetRows P) ≤ 36 := by
    have hs := hP.full_ridge_rows hv
    rw [hh,hc] at hs
    omega
  let l := (facetRows P).filter fun S => decide (S.n = 8)
  have hbase : ∀ S ∈ l, 7 ≤ S.r := by
    intro S hS
    obtain ⟨hS,hSn⟩ := List.mem_filter.1 hS
    exact hP.full_row_r_ge_seven hT hS (of_decide_eq_true hSn)
  have hlo := list_weight_count_lower l Row.r 7 hbase R
  have hlen : l.length = 4 := hc
  have hcount : l.count R = (facetRows P).count R := List.count_filter (by simp [hn])
  have hsum : (l.map Row.r).sum ≤ 36 := hs8
  rw [hlen,hcount] at hlo
  have hm := Nat.mul_le_mul_left (R.r - 7) hct
  exact ⟨hr7,by omega⟩

/-- Every actual row lies in the 15+32 row table used by the integer enumerator. -/
theorem IsCSPolytope5.two_pair_positive_catalogue
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 4) (hT : tRow ∉ facetRows P)
    (hseven : ∀ R ∈ facetRows P, 7 ≤ R.n)
    (hcap : ∀ R ∈ facetRows P, R.g ≤ 1) :
    ∀ R ∈ facetRows P, R ∈ TwoPairPositiveProfile.catalogue := by
  intro R hR
  have hctx := hP.rowOK_P_le (nmax := 8)
    (fun S hS => by have := hP.facetRows_n_le S hS; omega)
    (show ∀ S ∈ facetRows P, S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil) R hR
  have hn7 := hseven R hR
  have hn8 := hctx.n_le
  by_cases hn : R.n = 8
  · apply List.mem_append_right
    by_cases hr : R.r ≤ 7
    · have hs := hctx.smalld hr
      have hg0 : 0 ≤ R.dual.g := by
        have := hctx.g_nonneg; simp only [Row.dual,Row.g] at *; omega
      have hg1 : R.dual.g ≤ 1 := by
        have := hcap R hR; simp only [Row.dual,Row.g] at *; omega
      have hx := TwoPairPositiveProfile.full_small_dual_classification R.dual hs hn hg0 hg1
        (by rw [Row.dual_dual]; exact fun h => hT (h ▸ hR))
      simpa only [Row.dual_dual] using hx
    · have hb := hP.two_pair_full_ridge_bounds hv hh hc hT hR hn
      have hreal := hP.facetRows_real R hR
      exact TwoPairPositiveProfile.full_box_classification hn (by omega) hb.2
        hctx.g_nonneg (hcap R hR) hctx.euler hctx.B4
        (realRow_polygon_excess hreal) (hP.facetRows_not_fake8 R hR)
  · apply List.mem_append_left
    exact TwoPairPositiveProfile.seven_classification R (hctx.small (by omega))
      (by omega) hctx.g_nonneg (hcap R hR)

end Kalai5
