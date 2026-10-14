import Kalai5.Endpoints.TwoPairZeroBMixed
import Kalai5.Cube3.Endpoint

/-! Closure of the zero-stress two-full-pair case by an injective ridge count. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The zero-stress two-pair cell is impossible: four forced tetrahedra exceed three. -/
theorem IsCSPolytope5.three_pow_five_16_18_two_pair_zero
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4) (hG : (flagDataOf P).G = 0) :
    243 ≤ (faces P).ncard := by
  by_contra hbad
  have hlt : (faces P).ncard < 243 := by omega
  have hp := (hP.two_pair_zero_profileB hv hh hc hG hlt).1
  have hm : OnePairProfile.fullRow 20 ∈ facetRows P := hp.mem_iff.mpr (by decide +kernel)
  obtain ⟨H, hH, hH4, hHr⟩ := hP.mem_facetRows hm
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHr
  have hq := (hP.two_pair_zero_full_quads hv hh hc hG hlt hH hH4 (by omega) (by omega) hHr).1
  norm_num at hq
  obtain ⟨Q, R, hQR, he⟩ := Set.ncard_eq_two.1 hq
  have hqmem : Q ∈ {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 2 ∧ cnt P T 0 = 4} := by rw [he]; simp
  have hrmem : R ∈ {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 2 ∧ cnt P T 0 = 4} := by rw [he]; simp
  obtain ⟨a⟩ := hP.two_pair_zero_prism_exists hv hh hc hG hlt hqmem.1 hqmem.2.2.1 hqmem.2.2.2
  obtain ⟨b⟩ := hP.two_pair_zero_prism_exists hv hh hc hG hlt hrmem.1 hrmem.2.2.1 hrmem.2.2.2
  let S := a.mixed ∪ b.mixed
  have hfin (T : Set E5) (c : OnePairPrism P T) : c.mixed.Finite :=
    hP.faces_finite.subset fun U hU => hU.1
  have hSc : S.ncard = 4 := by
    rw [Set.ncard_union_eq (hP.two_pair_zero_mixed_disjoint hv hh hc hG hlt hH hH4 hHr
      hqmem.1 hqmem.2.1 hqmem.2.2.1 hqmem.2.2.2 hrmem.1 hrmem.2.1 hrmem.2.2.1 hrmem.2.2.2
      hQR a b) (hfin Q a) (hfin R b),
      hP.one_pair_prism_mixed_card a hqmem.1 hqmem.2.2.1 hqmem.2.2.2,
      hP.one_pair_prism_mixed_card b hrmem.1 hrmem.2.2.1 hrmem.2.2.2]
  have make (Q' : Set E5) (hq' : Q' ∈ faces P) (hqH : Q' ⊆ H) (hq2 : dim Q' = 2)
      (hq4 : cnt P Q' 0 = 4) (c : OnePairPrism P Q') (T : Set E5) (hT : T ∈ c.mixed) :
      ∃ J, J ∈ faces P ∧ dim J = 4 ∧ q4 P J ≤ 1 ∧ T ⊆ J ∧
        H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) :=
    hP.two_pair_zero_mixed_tetra hv hh hc hG hlt hH hH4 hHr
      c.hY c.hY4 c.hYrow c.hZ c.hZ4 c.hZrow c.hYZ c.hK c.hK3 (congrArg Prod.fst c.hKt) c.hKI
      hq' c.hQK hqH hq2 hq4 hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.symm
  have hex : ∀ T ∈ S, ∃ J, J ∈ faces P ∧ dim J = 4 ∧ q4 P J ≤ 1 ∧ T ⊆ J ∧
      H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
    intro T hT
    rcases hT with hT | hT
    · exact make Q hqmem.1 hqmem.2.1 hqmem.2.2.1 hqmem.2.2.2 a T hT
    · exact make R hrmem.1 hrmem.2.1 hrmem.2.2.1 hrmem.2.2.2 b T hT
  let j : Set E5 → Set E5 := fun T => if h : T ∈ S then Classical.choose (hex T h) else H
  have hj (T : Set E5) (ht : T ∈ S) : j T ∈ faces P ∧ dim (j T) = 4 ∧
      q4 P (j T) ≤ 1 ∧ T ⊆ j T ∧ H ∩ j T ∈ faces P ∧
      dim (H ∩ j T) = 3 ∧ tri3 P (H ∩ j T) = (4, 6, 4) := by
    simpa only [j, dif_pos ht] using Classical.choose_spec (hex T ht)
  have hquad (T : Set E5) (ht : T ∈ S) : T ∈ faces P ∧ dim T = 2 ∧ cnt P T 0 = 4 := by
    rcases ht with ht | ht <;> exact ⟨ht.1, ht.2.2.1, ht.2.2.2.1⟩
  have j_ne (T : Set E5) (ht : T ∈ S) : j T ≠ H := by
    have hsmall := (hj T ht).2.2.1
    intro he
    rw [he] at hsmall
    omega
  have hinj : Set.InjOn (fun T => H ∩ j T) S := by
    intro T hT U hU he
    have ht := hj T hT
    have hu := hj U hU
    have hjj := hP.ridge_neighbour_unique hH hH4 ht.1 ht.2.1 (j_ne T hT)
      hu.1 hu.2.1 (j_ne U hU) ht.2.2.2.2.1 ht.2.2.2.2.2.1 inter_subset_left inter_subset_right
      (by change H ∩ j T = H ∩ j U at he; rw [he]; exact inter_subset_right)
    exact hP.quad_unique_of_q4_le_one ht.2.2.1
      (hquad T hT).1 ht.2.2.2.1 (hquad T hT).2.1 (hquad T hT).2.2
      (hquad U hU).1 (by rw [hjj]; exact hu.2.2.2.1) (hquad U hU).2.1 (hquad U hU).2.2
  have hle := Set.ncard_le_ncard_of_injOn (fun T => H ∩ j T)
    (t := {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 3 ∧ tri3 P T = (4, 6, 4)})
    (fun T hT => ⟨(hj T hT).2.2.2.2.1, inter_subset_left, (hj T hT).2.2.2.2.2⟩)
    hinj (hP.faces_finite.subset fun T hT => hT.1)
  change S.ncard ≤ tcnt P H (4, 6, 4) at hle
  rw [hSc] at hle
  have hu := (hP.two_pair_zero_H20_tetra_bounds hv hh hc hG hlt hH hH4 hHr).2
  omega

end Kalai5

namespace Kalai5.TwoPairPositive

/-- The prior lists remain unchanged for their historical certificates. -/
def remainingCells : List (ℤ × ℤ) :=
  (E18refined.remainingCells 2).filter (fun c => decide (c.1 ≠ 0))

theorem remainingCells_eq : remainingCells =
    [(2,2),(2,4),(2,6),(2,8),(2,10),(4,2),(4,4),(4,6)] := by decide +kernel

end Kalai5.TwoPairPositive

namespace Kalai5
open Set
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Only eight positive-stress two-pair cells remain. -/
theorem IsCSPolytope5.fewFull18_residual_two_positive
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    cnt8 (facetRows P) = 4 ∧
      ((flagDataOf P).G,(flagDataOf P).Gs) ∈ TwoPairPositive.remainingCells := by
  obtain ⟨hc,hm⟩ := hP.fewFull18_residual_two hv hh h1 h6 hlt
  have hn : (flagDataOf P).G ≠ 0 := fun hG =>
    (not_le_of_gt hlt) (hP.three_pow_five_16_18_two_pair_zero hv hh hc hG)
  exact ⟨hc,List.mem_filter.mpr ⟨hm,by simpa using hn⟩⟩

end Kalai5
