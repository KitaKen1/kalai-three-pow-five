import Kalai5.Endpoints.FullSixRidges
import Kalai5.Endpoints.WeightBRefined

/-! Geometric row bounds for the two-full-pair, zero-stress cell. -/
namespace Kalai5
open scoped Classical

lemma list_weight_count_lower {α : Type*} [DecidableEq α]
    (l : List α) (f : α → ℕ) (b : ℕ) (hb : ∀ a ∈ l,b≤f a) (a : α) :
    b*l.length+(f a-b)*l.count a≤(l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx := hb x (List.mem_cons_self ..)
    have ht := ih (fun y hy => hb y (List.mem_cons_of_mem x hy))
    by_cases h : x=a
    · subst x
      simp only [List.length_cons,List.count_cons_self,List.map_cons,List.sum_cons] at *
      have hs := Nat.sub_add_cancel hx
      simp only [Nat.mul_add,Nat.mul_one] at *
      omega
    · simp only [List.length_cons,List.count_cons_of_ne h,List.map_cons,List.sum_cons] at *
      simp only [Nat.mul_add,Nat.mul_one] at *
      omega

lemma two_le_count_of_even {α : Type*} [DecidableEq α] (l : List α)
    (heven : ∀ q : α → Bool,Even (l.filter q).length) {a : α} (ha : a ∈ l) :
    2≤l.count a := by
  have hev := heven fun x => x==a
  rw [← List.count_eq_length_filter] at hev
  have hp := List.count_pos_iff.2 ha
  obtain ⟨k,hk⟩ := hev
  omega

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.zero_stress_eighteen_budgets
    (hv : fvec P 0=16) (hh : fvec P 4=18)
    (hG : (flagDataOf P).G=0) (hS : (flagDataOf P).Gs=10) :
    (flagDataOf P).I=128 ∧ (flagDataOf P).f14=3*(flagDataOf P).e+122 ∧
      ((facetRows P).map q55RefinedRowWeight).sum+6*(flagDataOf P).e≤420 := by
  have hD := hP.flagData_valid
  have hA := hP.A_eq_zero_of_G_eq_zero hG
  have hgg := FlagData.GGA_identity hD
  have he := hD.euler
  have hf := hD.f14_eq
  have h024 := hD.f024_eq
  have hw := hP.q55_refined_rows hv
  have hvD : (flagDataOf P).v=16 := hv
  have hhD : (flagDataOf P).h=18 := hh
  simp only [FlagData.G,FlagData.Gs,FlagData.A,FlagData.s,hvD,hhD] at hG hS hA hgg he hf h024 hw
  omega

theorem IsCSPolytope5.two_pair_zero_row_bounds
    (hv : fvec P 0=16) (hh : fvec P 4=18)
    (hc : cnt8 (facetRows P)=4) (hG : (flagDataOf P).G=0)
    (hS : (flagDataOf P).Gs=10) (hlt : (faces P).ncard<243) :
    ∀ R ∈ facetRows P,6≤R.n ∧ R.n≤8 ∧ R.g=0 ∧ (R.n=8 → 8≤R.r ∧ R.r≤10) := by
  have hT : tRow ∉ facetRows P := fun h => (not_le_of_gt hlt) (hP.full_prism hv h)
  have hn : ∀ R ∈ facetRows P,R.n≤8 := fun R hR => by
    have := hP.facetRows_n_le R hR; omega
  have hI := (hP.zero_stress_eighteen_budgets hv hh hG hS).1
  change flag2 P 0 4=128 at hI
  have hdef := sum_n_add_sevenDeficit (facetRows P) hn
  rw [hP.facetRows_sum_n,hP.facetRows_length,hh,hc,hI] at hdef
  have hs8 : sumR8 (facetRows P)≤36 := by
    have hridge := hP.full_ridge_rows hv
    rw [hh,hc] at hridge; omega
  intro R hR
  have hct := two_le_count_of_even (facetRows P) hP.facetRows_filter_even hR
  have h6 : 6≤R.n := by
    by_contra hbad
    have hlo := list_weight_count_lower (facetRows P) sevenDeficit 0 (by intros; omega) R
    have hdf : 2 ≤ sevenDeficit R := by unfold sevenDeficit; split_ifs <;> omega
    have hh := Nat.mul_le_mul hdf hct
    simp only [zero_mul,zero_add,Nat.sub_zero] at hlo
    omega
  have hg0 : R.g=0 := by
    have hr := hP.rowOK_P_le hn (show ∀ S ∈ facetRows P,S ∉ ([] : List Row) from fun _ _ => List.not_mem_nil) R hR
    have hg := hr.g_le
    change 2*R.g≤(flagDataOf P).G at hg
    rw [hG] at hg
    have := hr.g_nonneg
    omega
  refine ⟨h6,hn R hR,hg0,?_⟩
  intro h8
  have hr8 := hP.full_row_r_ge_eight_of_G0 hv hG hT hR h8
  let l := (facetRows P).filter fun S => decide (S.n=8)
  have hbase : ∀ S ∈ l,8≤S.r := by
    intro S hS
    obtain ⟨hS,hSn⟩ := List.mem_filter.1 hS
    exact hP.full_row_r_ge_eight_of_G0 hv hG hT hS (of_decide_eq_true hSn)
  have hlo := list_weight_count_lower l Row.r 8 hbase R
  have hlen : l.length=4 := hc
  have hcount : l.count R=(facetRows P).count R := List.count_filter (by simp [h8])
  have hsum : (l.map Row.r).sum≤36 := hs8
  rw [hlen,hcount] at hlo
  have hm := Nat.mul_le_mul_left (R.r-8) hct
  exact ⟨hr8,by omega⟩

end Kalai5
