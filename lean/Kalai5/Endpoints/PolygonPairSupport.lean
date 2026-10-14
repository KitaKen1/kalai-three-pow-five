import Kalai5.Endpoints.ContextWeight
import Kalai5.Endpoints.Ridge6106Capacity

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Facets above a polygon occupy distinct antipodal pairs. At least
three such facets exist, so every carrier list must contain three pairs. -/
theorem IsCSPolytope5.polygon_pair_capacity
    (carrier : Row → Prop) [DecidablePred carrier] {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    {Q : Set E5} (hQ : Q ∈ faces P) (hQ2 : dim Q = 2)
    (hcar : ∀ H ∈ faces P, dim H = 4 → Q ⊆ H → carrier (faceRow P H)) :
    3 ≤ (rows.filter fun R => decide (carrier R)).length := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let C := Fs.filter (fun H => carrier (faceRow P H))
  let S := Fs.filter (fun H => Q ⊆ H)
  have mFs : ∀ {H}, H ∈ Fs ↔ H ∈ faces P ∧ dim H = 4 := fun {H} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have mS : ∀ {H}, H ∈ S ↔ H ∈ faces P ∧ dim H = 4 ∧ Q ⊆ H := by
    intro H
    simp only [S,Finset.mem_filter,mFs,and_assoc]
  have hSC : ∀ H ∈ S, H ∈ C := by
    intro H hH
    obtain ⟨hH,hH4,hQH⟩ := mS.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hcar H hH hH4 hQH⟩
  have hCn : ∀ H ∈ C, -H ∈ C := by
    intro H hH
    obtain ⟨hH,hHC⟩ := Finset.mem_filter.1 hH
    obtain ⟨hH,hH4⟩ := mFs.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4]⟩,
      by rwa [hP.faceRow_neg]⟩
  have hd : Disjoint S (S.image fun H => -H) := by
    rw [Finset.disjoint_left]
    intro H hHS hHN
    obtain ⟨K,hKS,hKH⟩ := Finset.mem_image.1 hHN
    obtain ⟨hH,hH4,hQH⟩ := mS.1 hHS
    have hQnH : Q ⊆ -H := by rw [← hKH,neg_neg]; exact (mS.1 hKS).2.2
    obtain ⟨x,hx⟩ := hQ.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hH hH4) (hQH hx) (hQnH hx)
  have hs : S ∪ S.image (fun H => -H) ⊆ C := by
    intro H hH
    rcases Finset.mem_union.1 hH with hs | hs
    · exact hSC H hs
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.1 hs
      exact hCn K (hSC K hK)
  have hc := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ neg_injective] at hc
  have hS3 : 3 ≤ S.card := by
    have he : (S : Set (Set E5)) = {H | H ∈ faces P ∧ Q ⊆ H ∧ dim H = 4} := by
      ext H
      simp only [Finset.mem_coe,mS,Set.mem_setOf_eq]
      tauto
    rw [← Set.ncard_coe_finset,he]
    exact hP.three_le_up hQ hQ2
  have he : C.card = ((facetRows P).filter fun R => decide (carrier R)).length := by
    rw [length_filter_eq_sum,hP.facetRows_sum (fun R => if carrier R then 1 else 0)]
    simp only [C,Fs,Finset.card_filter]
  have hp' := (hp.filter (fun R => decide (carrier R))).length_eq
  rw [List.filter_append,List.length_append] at hp'
  rw [he,hp'] at hc
  omega

/-- If only two row pairs could contain a large polygon, none exists. -/
theorem IsCSPolytope5.big2_zero_of_pair_support
    (carrier : Row → Prop) [DecidablePred carrier] {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hk : (rows.filter fun R => decide (carrier R)).length ≤ 2)
    (hfree : ∀ H ∈ faces P, dim H = 4 → ¬ carrier (faceRow P H) → big2 P H = 0)
    (F : Set E5) : big2 P F = 0 := by
  by_contra hn
  obtain ⟨Q,hQ,hQF,hQ2,hQ5⟩ := Set.nonempty_of_ncard_ne_zero hn
  have hc := hP.polygon_pair_capacity carrier hp hQ hQ2 (fun H hH hH4 hQH => ?_)
  · omega
  · by_contra hf
    have hz := hfree H hH hH4 hf
    have hfin : {Q | Q ∈ faces P ∧ Q ⊆ H ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0}.Finite :=
      hP.faces_finite.subset fun Q hQ => hQ.1
    have hpos : 0 < big2 P H := (Set.ncard_pos hfin).2 ⟨Q,hQ,hQH,hQ2,hQ5⟩
    omega

theorem IsCSPolytope5.big2_zero_of_prism_exc_le_four {F : Set E5}
    (ht : 1 ≤ tcnt P F (6,9,5)) (he : exc P F ≤ 4) : big2 P F = 0 := by
  have hq := hP.b55_add_three_le_of_prism ht
  have hb := hP.q4_add_big_le_exc F
  omega

/-- In A, eliminating the pentagonal option reserves both quadrilaterals
for a six-vertex ridge and raises the row weight from four to six. -/
theorem IsCSPolytope5.a_weight_six_of_no_big {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = ⟨7,16,16,7,32⟩) (hb : big2 P F = 0) :
    q55w P F + 2 * exc P F = 6 := by
  have he : exc P F = 2 := by
    have he := hP.exc_eq_faceRow hF h4
    rw [hR] at he
    norm_num at he
    exact he
  have ht := hP.ridge6106_row_need hF h4
  rw [hR] at ht
  have hneed : PrismBudget.ridge6106Need (⟨7,16,16,7,32⟩ : Row) = 1 := by decide +kernel
  rw [hneed] at ht
  have hreserve := hP.b55_add_two_le_of_6106_no_big hb ht
  have hq := hP.exc_eq_q4_of_big F hb
  have hw := hP.q55w_eq_b55 F
  omega

end Kalai5
