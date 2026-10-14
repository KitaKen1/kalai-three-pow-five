import Kalai5.Endpoints.TwoPairPositivePairs
import Kalai5.Endpoints.TwoPairPositivePrisms

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.fewFull18_positive_actual_weight_budget
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (∑ F ∈ (hP.kfaces_finite 4).toFinset, (q55w P F + 2 * exc P F)) ≤
      156 - 6 * (flagDataOf P).Gs := by
  obtain ⟨he,hp,hr,hi,_⟩ := hP.fewFull18_positive_face_numbers hv hh h1 h6 hlt
  change (flagDataOf P).e = 58 at he
  change (flagDataOf P).p = 86 at hp
  change (flagDataOf P).r = 60 at hr
  have hhD : (flagDataOf P).h = 18 := hh
  have hw := hP.q55 hv
  have hf := hP.flagData_valid.f024_eq
  simp only [FlagData.A,FlagData.Gs,he,hp,hr,hi,hhD] at hw hf ⊢
  push_cast at hw hf ⊢
  linarith

omit hP in
def g2s10Pairs : List Row :=
  [excRow,excRow,excRow,excRow,excRow,OnePairProfile.jRow,OnePairProfile.jRow,
   OnePairProfile.fullRow 20,⟨8,20,20,8,39⟩]

theorem IsCSPolytope5.two_pair_g2s10_weight_eq
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 10)
    (hprof : (facetRows P).Perm (g2s10Pairs ++ g2s10Pairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F = q55BSixRowWeight (faceRow P F) := by
  have hsum : ((facetRows P).map q55BSixRowWeight).sum = 96 := by
    rw [(hprof.map q55BSixRowWeight).sum_eq]
    decide +kernel
  rw [hP.facetRows_sum q55BSixRowWeight] at hsum
  have hsumZ : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55BSixRowWeight (faceRow P H) : ℤ)) = 96 := by exact_mod_cast hsum
  have hu := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hu
  have hlo : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55BSixRowWeight (faceRow P H) : ℤ) ≤ q55w P H + 2 * exc P H := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    exact hP.q55_bSix_row_weight hH.1 hH.2
  have hl := Finset.sum_le_sum hlo
  have heq : (∑ H ∈ (hP.kfaces_finite 4).toFinset,
      (q55BSixRowWeight (faceRow P H) : ℤ)) =
      ∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H) := by omega
  exact ((Finset.sum_eq_sum_iff_of_le hlo).1 heq F
    (by rw [Set.Finite.mem_toFinset]; exact ⟨hF,h4⟩)).symm

theorem IsCSPolytope5.two_pair_g2s10_profile_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 10)
    (hprof : (facetRows P).Perm (g2s10Pairs ++ g2s10Pairs)) : False := by
  let prismCount : Row → ℕ := fun R => if R = excRow then 1 else 0
  have hs : ((facetRows P).map prismCount).sum = 10 := by
    rw [(hprof.map prismCount).sum_eq]
    decide +kernel
  rw [hP.facetRows_sum prismCount] at hs
  have heq : ∀ H ∈ (hP.kfaces_finite 4).toFinset,
      tcnt P H (6,9,5) = prismCount (faceRow P H) := by
    intro H hH
    have hHP := hH
    rw [Set.Finite.mem_toFinset] at hHP
    have hm : faceRow P H ∈ facetRows P := by
      rw [hP.facetRows_eq]
      exact List.mem_map.2 ⟨H,Finset.mem_toList.2 hH,rfl⟩
    have hm' := hprof.mem_iff.1 hm
    have hcases : faceRow P H = excRow ∨ faceRow P H = OnePairProfile.jRow ∨
        faceRow P H = OnePairProfile.fullRow 20 ∨ faceRow P H = ⟨8,20,20,8,39⟩ := by
      simpa only [g2s10Pairs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,
        or_self,or_self_left,or_assoc] using hm'
    rcases hcases with hY | hJ | hH20 | hC
    · rw [hP.Y_prism_count hHP.1 hHP.2 hY]
      simp [prismCount,hY]
    · rw [hP.J_no_prism hHP.1 hHP.2 hJ]
      simp [prismCount,hJ,OnePairProfile.jRow,excRow]
    · rw [hP.h20_no_prism hHP.1 hHP.2 hH20]
      simp [prismCount,hH20,OnePairProfile.fullRow,excRow]
    · have hw := hP.two_pair_g2s10_weight_eq hv hh h1 h6 hlt hS hprof hHP.1 hHP.2
      rw [hC] at hw
      have hwC : q55BSixRowWeight (⟨8,20,20,8,39⟩ : Row) = 3 := by decide +kernel
      rw [hwC] at hw
      have hz : tcnt P H (6,9,5) = 0 := by
        by_contra hn
        have hx := hP.c20_prism_weight_nine hHP.1 hHP.2 hC (by omega)
        omega
      rw [hz]
      simp [prismCount,hC,excRow]
  have htotal : (∑ H ∈ (hP.kfaces_finite 4).toFinset, tcnt P H (6,9,5)) = 10 := by
    rw [Finset.sum_congr rfl heq]
    exact hs
  have hdvd := hP.four_dvd_sum_tcnt (6,9,5)
  rw [htotal] at hdvd
  omega

end Kalai5
