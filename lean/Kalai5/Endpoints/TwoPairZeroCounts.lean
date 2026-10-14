import Kalai5.Endpoints.TwoPairZeroCatalogue

/-! The finite arithmetic is connected to actual even row multiplicities. -/
namespace Kalai5.TwoPairZeroProfile

lemma perm_of_catalogue_counts (l p : List Row)
    (hl : ∀ R ∈ l,R ∈ catalogue) (hp : ∀ R ∈ p,R ∈ catalogue)
    (hc : ∀ R ∈ catalogue,l.count R=p.count R) : l.Perm p := by
  apply List.perm_iff_count.2
  intro R
  by_cases hR : R ∈ catalogue
  · exact hc R hR
  · rw [List.count_eq_zero_of_not_mem (fun h => hR (hl R h)),
      List.count_eq_zero_of_not_mem (fun h => hR (hp R h))]

set_option maxHeartbeats 1000000 in
theorem counts_closure (l : List Row) (e r : ℕ)
    (hs : ∀ R ∈ l,R ∈ catalogue)
    (heven : ∀ q : Row → Bool,Even (l.filter q).length)
    (hlen : l.length=18) (hn : (l.map Row.n).sum=128) (hc8 : cnt8 l=4)
    (he : (l.map Row.e).sum=3*e+122) (hr : (l.map Row.r).sum=2*r)
    (ht : e+r≤118) (hw : (l.map q55RefinedRowWeight).sum+6*e≤420)
    (hee : Even e) (her : Even r) :
    (l.Perm profileA ∧ e=56 ∧ r=62) ∨ (l.Perm profileB ∧ e=58 ∧ r=60) := by
  have even_count (R : Row) : Even (l.count R) := by
    simpa only [List.count_eq_length_filter] using heven (fun S => S==R)
  obtain ⟨s0,hs0⟩ := even_count ⟨6,13,13,6,26⟩
  obtain ⟨s1,hs1⟩ := even_count ⟨6,14,15,7,29⟩
  obtain ⟨s2,hs2⟩ := even_count ⟨6,14,16,8,32⟩
  obtain ⟨y,hy⟩ := even_count excRow
  obtain ⟨q,hq⟩ := even_count eRow
  obtain ⟨j,hj⟩ := even_count OnePairProfile.jRow
  obtain ⟨a,ha⟩ := even_count ⟨7,17,18,8,35⟩
  obtain ⟨b,hb⟩ := even_count ⟨7,17,19,9,38⟩
  obtain ⟨c,hc⟩ := even_count ⟨7,18,19,8,35⟩
  obtain ⟨d,hd⟩ := even_count ⟨7,18,20,9,38⟩
  obtain ⟨u,hu⟩ := even_count ⟨7,18,21,10,41⟩
  obtain ⟨v,hv⟩ := even_count ⟨7,18,22,11,44⟩
  obtain ⟨f0,hf0⟩ := even_count ⟨8,19,19,8,38⟩
  obtain ⟨f1,hf1⟩ := even_count ⟨8,19,20,9,41⟩
  obtain ⟨f2,hf2⟩ := even_count ⟨8,20,20,8,38⟩
  obtain ⟨f3,hf3⟩ := even_count ⟨8,20,21,9,41⟩
  obtain ⟨f4,hf4⟩ := even_count ⟨8,20,22,10,44⟩
  obtain ⟨f5,hf5⟩ := even_count ⟨8,21,21,8,38⟩
  obtain ⟨f6,hf6⟩ := even_count ⟨8,21,22,9,41⟩
  obtain ⟨f7,hf7⟩ := even_count ⟨8,21,23,10,44⟩
  obtain ⟨f8,hf8⟩ := even_count ⟨8,22,22,8,38⟩
  obtain ⟨f9,hf9⟩ := even_count ⟨8,22,23,9,41⟩
  obtain ⟨f10,hf10⟩ := even_count ⟨8,22,24,10,44⟩
  have hsum := fun f : Row → ℕ => OnePairProfile.sum_catalogue l catalogue f catalogue_nodup hs
  have hl := hsum (fun _ => 1)
  have hn' := hsum Row.n
  have he' := hsum Row.e
  have hr' := hsum Row.r
  have hw' := hsum q55RefinedRowWeight
  have h8 := hsum (fun R => if R.n=8 then 1 else 0)
  have h8count : (l.map (fun R => if R.n=8 then 1 else 0)).sum=4 := by
    rw [← length_filter_eq_sum]; exact hc8
  simp only [catalogue,sixRows,OnePairProfile.sevenRows,fullRows,List.map_append,List.sum_append,
    List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,hs0,hs1,hs2,hy,hq,hj,ha,hb,hc,hd,hu,hv,hf0,hf1,hf2,hf3,hf4,hf5,hf6,hf7,hf8,hf9,hf10,smul_eq_mul] at hl hn' he' hr' hw' h8
  simp only [List.map_const',List.sum_replicate,smul_eq_mul,mul_one,hlen] at hl
  norm_num [excRow,eRow,OnePairProfile.jRow,hn,he,hr,h8count] at hn' he' hr' h8
  norm_num [q55RefinedRowWeight,q55StrongRowWeight,q55RowWeight,q55ElementaryWeight,
    excRow,eRow,OnePairProfile.jRow,r0Row,r35Row,zRow] at hw'
  have hsix : s0+s1+s2=1 := by linarith only [hl,hn',h8]
  have hseven : y+q+j+a+b+c+d+u+v=6 := by linarith only [hl,hn',h8]
  have hfull : f0+f1+f2+f3+f4+f5+f6+f7+f8+f9+f10=2 := by linarith only [h8]
  have hedges : 3*e+122=26*s0+28*s1+28*s2+30*y+32*q+34*j+34*a+34*b+
      36*c+36*d+36*u+36*v+38*f0+38*f1+40*f2+40*f3+40*f4+
      42*f5+42*f6+42*f7+44*f8+44*f9+44*f10 := by linarith only [he']
  have hridges : r=6*s0+7*s1+8*s2+6*y+7*q+7*j+8*a+9*b+8*c+9*d+10*u+11*v+
      8*f0+9*f1+8*f2+9*f3+10*f4+8*f5+9*f6+10*f7+8*f8+9*f9+10*f10 := by linarith only [hr']
  have hweight : 9*y+4*q+4*f0+8*f1+3*e≤210 := by linarith only [hw,hw']
  obtain ⟨zs0,zs1,zs2,za,zb,zc,zd,zu,zv,zf1,zf3,zf4,zf6,zf7,zf8,zf9,zf10,hcase⟩ :=
    two_pair_zero_profile_arithmetic s0 s1 s2 y q j a b c d u v f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 e r
      hsix hseven hfull hedges hridges ht hweight hee her
  rcases hcase with ⟨zy,zq,zj,zf0,zf2,zf5,ze,zr⟩ | ⟨zy,zq,zj,zf0,zf2,zf5,ze,zr⟩
  · left
    refine ⟨perm_of_catalogue_counts l profileA hs profileA_support ?_,ze,zr⟩
    intro R hR
    simp only [catalogue,sixRows,OnePairProfile.sevenRows,fullRows,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zs0] using hs0
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zs1] using hs1
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zs2] using hs2
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zy] using hy
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zq] using hq
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zj] using hj
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,za] using ha
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zb] using hb
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zc] using hc
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zd] using hd
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zu] using hu
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zv] using hv
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf0] using hf0
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf1] using hf1
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf2] using hf2
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf3] using hf3
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf4] using hf4
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf5] using hf5
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf6] using hf6
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf7] using hf7
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf8] using hf8
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf9] using hf9
    · simpa [profileA,excRow,eRow,OnePairProfile.jRow,zf10] using hf10
  · right
    refine ⟨perm_of_catalogue_counts l profileB hs profileB_support ?_,ze,zr⟩
    intro R hR
    simp only [catalogue,sixRows,OnePairProfile.sevenRows,fullRows,List.mem_append,
      List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hR
    rcases hR with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zs0] using hs0
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zs1] using hs1
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zs2] using hs2
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zy] using hy
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zq] using hq
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zj] using hj
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,za] using ha
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zb] using hb
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zc] using hc
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zd] using hd
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zu] using hu
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zv] using hv
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf0] using hf0
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf1] using hf1
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf2] using hf2
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf3] using hf3
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf4] using hf4
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf5] using hf5
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf6] using hf6
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf7] using hf7
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf8] using hf8
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf9] using hf9
    · simpa [profileB,excRow,eRow,OnePairProfile.jRow,zf10] using hf10

end Kalai5.TwoPairZeroProfile
