import Kalai5.Endpoints.TwoPairZeroWeights

/-! Saturation fixes the quadrilateral and square-pyramid counts in the full facets. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.full_quads_of_refined_equality
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4)
    {k : ℕ} (hklo : 19≤k) (hkhi : k≤21)
    (hrow : faceRow P F=OnePairProfile.fullRow k)
    (hw : q55w P F+2*exc P F=q55RefinedRowWeight (faceRow P F)) :
    q4 P F=(if k=20 then 2 else 1) ∧ big2 P F=(if k=19 then 1 else 0) ∧
      (b55set P F).ncard=q4 P F ∧ tcnt P F (5,8,5)=2*q4 P F ∧
      q55w P F= -2*(q4 P F : ℤ) := by
  have hexc := hP.exc_eq_faceRow hF h4
  rw [hrow] at hexc hw
  have hq := hP.q4_add_big_le_exc F
  have hlo := hP.q55w_ge F
  have hb := hP.q55w_eq_b55 F
  have hpyr := hP.two_b55_le hF h4
  have hn : cnt P F 0=8 := congrArg Row.n hrow
  have hl := hP.two_q4_lb hF h4 hn (fun _ => 0)
    (fun _ _ _ _ => by positivity) (fun _ _ _ => rfl)
  simp only [Finset.sum_const_zero,add_zero] at hl
  interval_cases k
  · norm_num [OnePairProfile.fullRow,q55RefinedRowWeight] at hexc hw ⊢
    have hq1 : q4 P F=1 := by omega
    have hbig : big2 P F=1 := by
      by_cases hz : big2 P F=0
      · have hh := hP.exc_eq_q4_of_big F hz
        omega
      · omega
    omega
  · norm_num [OnePairProfile.fullRow,q55RefinedRowWeight,q55StrongRowWeight,
      q55RowWeight,q55ElementaryWeight,excRow,eRow,r0Row,r35Row,zRow] at hexc hw ⊢
    omega
  · norm_num [OnePairProfile.fullRow,q55RefinedRowWeight,q55StrongRowWeight,
      q55RowWeight,q55ElementaryWeight,excRow,eRow,r0Row,r35Row,zRow] at hexc hw ⊢
    omega

theorem IsCSPolytope5.two_pair_zero_full_quads
    (hv : fvec P 0=16) (hh : fvec P 4=18) (hc : cnt8 (facetRows P)=4)
    (hG : (flagDataOf P).G=0) (hlt : (faces P).ncard<243)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4)
    {k : ℕ} (hklo : 19≤k) (hkhi : k≤21)
    (hrow : faceRow P F=OnePairProfile.fullRow k) :
    q4 P F=(if k=20 then 2 else 1) ∧ big2 P F=(if k=19 then 1 else 0) ∧
      (b55set P F).ncard=q4 P F ∧ tcnt P F (5,8,5)=2*q4 P F ∧
      q55w P F= -2*(q4 P F : ℤ) :=
  hP.full_quads_of_refined_equality hF h4 hklo hkhi hrow
    (hP.two_pair_zero_weight_eq hv hh hc hG hlt hF h4)

theorem IsCSPolytope5.full_b_types_of_refined_equality
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F=4)
    (hrow : faceRow P F=OnePairProfile.fullRow 19)
    (hweight : q55w P F+2*exc P F=q55RefinedRowWeight (faceRow P F)) :
    tcnt P F (4,6,4)=4 ∧ tcnt P F (5,8,5)=2 ∧ tcnt P F (5,9,6)=0 ∧
      tcnt P F (6,9,5)=0 ∧ tcnt P F (6,10,6)=2 ∧ tcnt P F (6,11,7)=0 ∧
      tcnt P F (6,12,8)=0 ∧ ∀ e p,tcnt P F (7,e,p)=0 := by
  obtain ⟨hq,_,hb,hy,hw⟩ := hP.full_quads_of_refined_equality hF h4
    (by omega) (by omega) hrow hweight
  norm_num at hq
  rw [hq] at hb hy hw
  have hrow' := hrow
  simp only [faceRow,OnePairProfile.fullRow,Row.mk.injEq] at hrow'
  obtain ⟨hn,_,hp,hr,hJ⟩ := hrow'
  have h7 := hP.tcnt_seven_eq_zero_of_q55_neg hF h4 hn (by omega)
  have hprism : tcnt P F (6,9,5)=0 := by
    by_contra hz
    obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1≤tcnt P F (6,9,5))
    have hT6 : cnt P T 0=6 := congrArg Prod.fst ht
    have hqT := (hP.q4_695 hT hT3 ht).1
    have hle := hP.b55_add_q4_le hT hTF hT3 (by omega)
    omega
  have h611 : tcnt P F (6,11,7)=0 := by
    by_contra hz
    obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1≤tcnt P F (6,11,7))
    simp only [tri3,Prod.mk.injEq] at ht
    have hex := hP.exc_threeface hT hT3
    rw [ht.2.1,ht.2.2] at hex
    have hbound := hP.q4_add_big_le_exc T
    have hbig : big2 P T=0 := by omega
    have heq := hP.exc_eq_q4_of_big T hbig
    have hle := hP.b55_add_q4_le hT hTF hT3 (by omega)
    omega
  obtain ⟨c1,c2,c3,_⟩ := hP.facet8_arith hF h4 hn
  simp only [hy,hprism,h611,h7,hp,hr,hJ] at c1 c2 c3
  refine ⟨?_,hy,?_,hprism,?_,h611,?_,h7⟩ <;> omega

end Kalai5
