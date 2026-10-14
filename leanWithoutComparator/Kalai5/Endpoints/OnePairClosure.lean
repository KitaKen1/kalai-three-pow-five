import Kalai5.Endpoints.OnePairTetra

/-!
# Exclusion of the one-full-pair (16,18) configuration

Each of the two quadrilaterals of H gives two mixed quadrilaterals. The
four are distinct because their Y pairs are disjoint. Each gives a distinct
J facet, hence a distinct tetrahedral ridge of H. This contradicts H's two
tetrahedra.
-/

namespace Kalai5

open Set
open scoped Classical

/-- The prism pair over a quadrilateral; all fields concern actual faces. -/
structure OnePairPrism (P Q : Set E5) where
  Y : Set E5
  Z : Set E5
  K : Set E5
  hY : Y ∈ faces P
  hY4 : dim Y = 4
  hYrow : faceRow P Y = excRow
  hZ : Z ∈ faces P
  hZ4 : dim Z = 4
  hZrow : faceRow P Z = excRow
  hYZ : Y ≠ Z
  hK : K ∈ faces P
  hK3 : dim K = 3
  hKt : tri3 P K = (6, 9, 5)
  hKI : K = Y ∩ Z
  hQK : Q ⊆ K

def OnePairPrism.mixed {P Q : Set E5} (a : OnePairPrism P Q) : Set (Set E5) :=
  {R | R ∈ faces P ∧ R ⊆ a.K ∧ dim R = 2 ∧ cnt P R 0 = 4 ∧ R ≠ Q}

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.fewFull18_one_pair_prism_exists
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {Q : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) :
    Nonempty (OnePairPrism P Q) := by
  have htwo := hP.fewFull18_one_pair_quad_two_Y hv hh hc hlt hQ hQ2 hQ4
  obtain ⟨Y, hY⟩ := Finset.card_pos.1 (show 0 <
    ((hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)).card by omega)
  rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hY
  obtain ⟨Z, K, hZ, hZ4, hZY, hZrow, hK, hK3, hKt, hKI, hbase, -⟩ :=
    hP.fewFull18_one_pair_Y_partner hv hh hc hlt hY.1.1 hY.1.2.2 hY.2
  have hQZ := hbase Q hQ hY.1.2.1 hQ2 hQ4
  exact ⟨⟨Y, Z, K, hY.1.1, hY.1.2.2, hY.2, hZ, hZ4, hZrow, hZY.symm,
    hK, hK3, hKt, hKI, hKI ▸ subset_inter hY.1.2.1 hQZ⟩⟩

lemma IsCSPolytope5.one_pair_prism_mixed_card {Q : Set E5} (a : OnePairPrism P Q)
    (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4) : a.mixed.ncard = 2 := by
  have he : a.mixed = {R | R ∈ faces P ∧ R ⊆ a.K ∧ dim R = 2 ∧ cnt P R 0 = 4} \ {Q} := by
    ext R
    simp only [OnePairPrism.mixed, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
    tauto
  rw [he, Set.ncard_sdiff_singleton_of_mem (show Q ∈
    {R | R ∈ faces P ∧ R ⊆ a.K ∧ dim R = 2 ∧ cnt P R 0 = 4} from ⟨hQ, a.hQK, hQ2, hQ4⟩)]
  change q4 P a.K - 1 = 2
  rw [(hP.q4_695 a.hK a.hK3 a.hKt).1]

/-- Two known Y facets exhaust the Y facets over a quadrilateral. -/
lemma IsCSPolytope5.one_pair_quad_Y_exhaust
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {Q Y Z X : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hY : Y ∈ faces P) (hY4 : dim Y = 4) (hYr : faceRow P Y = excRow) (hQY : Q ⊆ Y)
    (hZ : Z ∈ faces P) (hZ4 : dim Z = 4) (hZr : faceRow P Z = excRow) (hQZ : Q ⊆ Z) (hYZ : Y ≠ Z)
    (hX : X ∈ faces P) (hX4 : dim X = 4) (hXr : faceRow P X = excRow) (hQX : Q ⊆ X) :
    X = Y ∨ X = Z := by
  let S := (hP.above_finite Q 4).toFinset.filter (fun F => faceRow P F = excRow)
  have hcard : S.card = 2 := hP.fewFull18_one_pair_quad_two_Y hv hh hc hlt hQ hQ2 hQ4
  have mem (F : Set E5) (hf : F ∈ faces P) (hd : dim F = 4) (hr : faceRow P F = excRow)
      (hq : Q ⊆ F) : F ∈ S := by
    simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hf, hq, hd⟩, hr⟩
  have he : ({Y, Z} : Finset (Set E5)) = S := Finset.eq_of_subset_of_card_le
    (by intro F hF; rcases Finset.mem_insert.1 hF with rfl | hF
        · exact mem _ hY hY4 hYr hQY
        · exact Finset.mem_singleton.1 hF ▸ mem Z hZ hZ4 hZr hQZ)
    (by rw [hcard, Finset.card_pair hYZ])
  have hm := mem X hX hX4 hXr hQX
  rwa [← he, Finset.mem_insert, Finset.mem_singleton] at hm

lemma IsCSPolytope5.one_pair_mixed_disjoint
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 2) (hlt : (faces P).ncard < 243)
    {H Q R : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4)
    (hHr : faceRow P H = OnePairProfile.fullRow 20)
    (hQ : Q ∈ faces P) (hQH : Q ⊆ H) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hR : R ∈ faces P) (hRH : R ⊆ H) (hR2 : dim R = 2) (hR4 : cnt P R 0 = 4) (hQR : Q ≠ R)
    (a : OnePairPrism P Q) (b : OnePairPrism P R) : Disjoint a.mixed b.mixed := by
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHr
  have neq (X : Set E5) (hr : faceRow P X = excRow) : H ≠ X := by
    have hx : cnt P X 0 = 7 := congrArg Row.n hr
    intro he; rw [he] at hH8; omega
  have hqaY : Q ⊆ a.Y := a.hQK.trans (a.hKI ▸ inter_subset_left)
  have hqaZ : Q ⊆ a.Z := a.hQK.trans (a.hKI ▸ inter_subset_right)
  have hrbY : R ⊆ b.Y := b.hQK.trans (b.hKI ▸ inter_subset_left)
  rw [Set.disjoint_left]
  intro T ha hb
  have haY : T ⊆ a.Y := ha.2.1.trans (a.hKI ▸ inter_subset_left)
  have haZ : T ⊆ a.Z := ha.2.1.trans (a.hKI ▸ inter_subset_right)
  have hbY : T ⊆ b.Y := hb.2.1.trans (b.hKI ▸ inter_subset_left)
  rcases hP.one_pair_quad_Y_exhaust hv hh hc hlt ha.1 ha.2.2.1 ha.2.2.2.1
    a.hY a.hY4 a.hYrow haY a.hZ a.hZ4 a.hZrow haZ a.hYZ b.hY b.hY4 b.hYrow hbY with he | he
  · exact hQR (hP.fewFull18_one_pair_H_shared_quad_unique hv hh hc hlt
      hH hH4 hHr a.hY a.hY4 (neq a.Y a.hYrow) hQ hQH hqaY hQ2 hQ4
      hR hRH (he ▸ hrbY) hR2 hR4)
  · exact hQR (hP.fewFull18_one_pair_H_shared_quad_unique hv hh hc hlt
      hH hH4 hHr a.hZ a.hZ4 (neq a.Z a.hZrow) hQ hQH hqaZ hQ2 hQ4
      hR hRH (he ▸ hrbY) hR2 hR4)

/-- Distinct neighbouring facets cannot give the same ridge of H. -/
lemma IsCSPolytope5.ridge_neighbour_unique {H J L T : Set E5}
    (hH : H ∈ faces P) (hH4 : dim H = 4)
    (hJ : J ∈ faces P) (hJ4 : dim J = 4) (hJH : J ≠ H)
    (hL : L ∈ faces P) (hL4 : dim L = 4) (hLH : L ≠ H)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hTH : T ⊆ H) (hTJ : T ⊆ J) (hTL : T ⊆ L) : J = L := by
  by_contra hJL
  have hs : ({H, J, L} : Set (Set E5)) ⊆ {F | F ∈ faces P ∧ T ⊆ F ∧ dim F = 4} := by
    intro F hF
    rcases hF with rfl | rfl | rfl
    · exact ⟨hH, hTH, hH4⟩
    · exact ⟨hJ, hTJ, hJ4⟩
    · exact ⟨hL, hTL, hL4⟩
  have hl := Set.ncard_le_ncard hs (hP.above_finite T 4)
  rw [Set.ncard_eq_three.2 ⟨H, J, L, hJH.symm, hLH.symm, hJL, rfl⟩, hP.ridge_two hT hT3] at hl
  omega

/-- There is no one-full-pair counterexample at (16,18). -/
theorem IsCSPolytope5.three_pow_five_16_18_one_pair
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 2) :
    243 ≤ (faces P).ncard := by
  by_contra hbad
  have hlt : (faces P).ncard < 243 := by omega
  have hp := hP.fewFull18_one_pair_profile hv hh hc hlt
  have hm : OnePairProfile.fullRow 20 ∈ facetRows P := List.count_pos_iff.1 (by rw [hp.2.2.2.1]; decide)
  obtain ⟨H, hH, hH4, hHr⟩ := hP.mem_facetRows hm
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHr
  have hq := (hP.fewFull18_one_pair_full_quads hv hh hc hlt hH hH4 hHr).1
  obtain ⟨Q, R, hQR, he⟩ := Set.ncard_eq_two.1 hq
  have hqmem : Q ∈ {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 2 ∧ cnt P T 0 = 4} := by rw [he]; simp
  have hrmem : R ∈ {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 2 ∧ cnt P T 0 = 4} := by rw [he]; simp
  obtain ⟨a⟩ := hP.fewFull18_one_pair_prism_exists hv hh hc hlt hqmem.1 hqmem.2.2.1 hqmem.2.2.2
  obtain ⟨b⟩ := hP.fewFull18_one_pair_prism_exists hv hh hc hlt hrmem.1 hrmem.2.2.1 hrmem.2.2.2
  let S := a.mixed ∪ b.mixed
  have hfin (T : Set E5) (c : OnePairPrism P T) : c.mixed.Finite :=
    hP.faces_finite.subset fun U hU => hU.1
  have hSc : S.ncard = 4 := by
    rw [Set.ncard_union_eq (hP.one_pair_mixed_disjoint hv hh hc hlt hH hH4 hHr
      hqmem.1 hqmem.2.1 hqmem.2.2.1 hqmem.2.2.2 hrmem.1 hrmem.2.1 hrmem.2.2.1 hrmem.2.2.2
      hQR a b) (hfin Q a) (hfin R b),
      hP.one_pair_prism_mixed_card a hqmem.1 hqmem.2.2.1 hqmem.2.2.2,
      hP.one_pair_prism_mixed_card b hrmem.1 hrmem.2.2.1 hrmem.2.2.2]
  have make (Q' : Set E5) (hq' : Q' ∈ faces P) (hqH : Q' ⊆ H) (hq2 : dim Q' = 2)
      (hq4 : cnt P Q' 0 = 4) (c : OnePairPrism P Q') (T : Set E5) (hT : T ∈ c.mixed) :
      ∃ J, J ∈ faces P ∧ dim J = 4 ∧ faceRow P J = OnePairProfile.jRow ∧ T ⊆ J ∧
        H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) :=
    hP.fewFull18_one_pair_mixed_tetra hv hh hc hlt hH hH4 hHr
      c.hY c.hY4 c.hYrow c.hZ c.hZ4 c.hZrow c.hYZ c.hK c.hK3 (congrArg Prod.fst c.hKt) c.hKI
      hq' c.hQK hqH hq2 hq4 hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1 hT.2.2.2.2.symm
  have hex : ∀ T ∈ S, ∃ J, J ∈ faces P ∧ dim J = 4 ∧ faceRow P J = OnePairProfile.jRow ∧ T ⊆ J ∧
      H ∩ J ∈ faces P ∧ dim (H ∩ J) = 3 ∧ tri3 P (H ∩ J) = (4, 6, 4) := by
    intro T hT
    rcases hT with hT | hT
    · exact make Q hqmem.1 hqmem.2.1 hqmem.2.2.1 hqmem.2.2.2 a T hT
    · exact make R hrmem.1 hrmem.2.1 hrmem.2.2.1 hrmem.2.2.2 b T hT
  let j : Set E5 → Set E5 := fun T => if h : T ∈ S then Classical.choose (hex T h) else H
  have hj (T : Set E5) (ht : T ∈ S) : j T ∈ faces P ∧ dim (j T) = 4 ∧
      faceRow P (j T) = OnePairProfile.jRow ∧ T ⊆ j T ∧ H ∩ j T ∈ faces P ∧
      dim (H ∩ j T) = 3 ∧ tri3 P (H ∩ j T) = (4, 6, 4) := by
    simpa only [j, dif_pos ht] using Classical.choose_spec (hex T ht)
  have hquad (T : Set E5) (ht : T ∈ S) : T ∈ faces P ∧ dim T = 2 ∧ cnt P T 0 = 4 := by
    rcases ht with ht | ht <;> exact ⟨ht.1, ht.2.2.1, ht.2.2.2.1⟩
  have j_ne (T : Set E5) (ht : T ∈ S) : j T ≠ H := by
    have hn : cnt P (j T) 0 = 7 := congrArg Row.n (hj T ht).2.2.1
    intro he; rw [he] at hn; omega
  have hinj : Set.InjOn (fun T => H ∩ j T) S := by
    intro T hT U hU he
    have ht := hj T hT
    have hu := hj U hU
    have hjj := hP.ridge_neighbour_unique hH hH4 ht.1 ht.2.1 (j_ne T hT)
      hu.1 hu.2.1 (j_ne U hU) ht.2.2.2.2.1 ht.2.2.2.2.2.1 inter_subset_left inter_subset_right
      (by change H ∩ j T = H ∩ j U at he; rw [he]; exact inter_subset_right)
    exact hP.J_quad_unique ht.1 ht.2.1 ht.2.2.1
      (hquad T hT).1 ht.2.2.2.1 (hquad T hT).2.1 (hquad T hT).2.2
      (hquad U hU).1 (by rw [hjj]; exact hu.2.2.2.1) (hquad U hU).2.1 (hquad U hU).2.2
  have hle := Set.ncard_le_ncard_of_injOn (fun T => H ∩ j T)
    (t := {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 3 ∧ tri3 P T = (4, 6, 4)})
    (fun T hT => ⟨(hj T hT).2.2.2.2.1, inter_subset_left, (hj T hT).2.2.2.2.2⟩)
    hinj (hP.faces_finite.subset fun T hT => hT.1)
  change S.ncard ≤ tcnt P H (4, 6, 4) at hle
  rw [hSc, (hP.fewFull18_one_pair_full_types hv hh hc hlt hH hH4 hHr).1] at hle
  omega

/-- Only the nine two-pair and twenty-three three-pair cells remain. -/
theorem IsCSPolytope5.fewFull18_residual_two_three
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (cnt8 (facetRows P) = 4 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18low.remainingCells 2) ∨
    (cnt8 (facetRows P) = 6 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18low.remainingCells 3) := by
  rcases hP.fewFull18_residual hv hh h1 h6 hlt with h | h
  · exact False.elim ((not_le_of_gt hlt) (hP.three_pow_five_16_18_one_pair hv hh h.1))
  · exact h

end Kalai5
