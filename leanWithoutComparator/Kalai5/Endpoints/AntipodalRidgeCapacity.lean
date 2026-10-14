import Kalai5.Endpoints.NegativeGapSupport

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- Every proper facet is disjoint from its antipodal facet. -/
theorem IsCSPolytope5.facet_disjoint_neg {F : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) : Disjoint F (-F) := by
  rw [Set.disjoint_left]
  intro x hx hn
  have he := hP.eq_of_mem_of_neg_mem hF hx (by simpa only [Set.mem_neg] using hn)
  have hd := hP.dim_self
  rw [← he,h4] at hd
  omega

theorem IsCSPolytope5.cnt_zero_add_le_of_disjoint {F T U : Set E5}
    (hTF : T ⊆ F) (hUF : U ⊆ F) (hd : Disjoint T U) :
    cnt P T 0 + cnt P U 0 ≤ cnt P F 0 := by
  have hv : Disjoint (vset P T) (vset P U) := by
    rw [Set.disjoint_left]
    intro V hT hU
    obtain ⟨x,hx⟩ := hT.1.1
    exact Set.disjoint_left.1 hd (hT.2.1 hx) (hU.2.1 hx)
  have hs : vset P T ∪ vset P U ⊆ vset P F := by
    rintro V (hV | hV)
    · exact ⟨hV.1,hV.2.1.trans hTF,hV.2.2⟩
    · exact ⟨hV.1,hV.2.1.trans hUF,hV.2.2⟩
  have hc := Set.ncard_le_ncard hs (hP.vset_finite F)
  rw [Set.ncard_union_eq hv (hP.vset_finite T) (hP.vset_finite U),
    ← cnt_eq_vset,← cnt_eq_vset,← cnt_eq_vset] at hc
  exact hc

/-- A list of distinct types counts each selected ridge exactly once. -/
theorem IsCSPolytope5.tcnt_list_sum_eq_card (F : Set E5)
    (types : List (ℕ × ℕ × ℕ)) (hnd : types.Nodup) :
    (types.map (tcnt P F)).sum =
      ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ types).card := by
  induction types with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨hnt,hnd⟩ := List.nodup_cons.1 hnd
    simp only [List.map_cons,List.sum_cons]
    rw [hP.tcnt_eq_card,ih hnd]
    have he : ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ t :: ts) =
        ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t) ∪
        ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ ts) := by
      ext T
      simp only [Finset.mem_filter,Finset.mem_union,List.mem_cons]
      tauto
    have hd : Disjoint ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t)
        ((hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ ts) := by
      rw [Finset.disjoint_left]
      intro T hT hU
      exact hnt ((Finset.mem_filter.1 hT).2 ▸ (Finset.mem_filter.1 hU).2)
    rw [he,Finset.card_union_of_disjoint hd]

/-- Wide ridges need distinct antipodal partner pairs. The two facets of
the current pair cannot be partners, so every selected ridge costs a pair. -/
theorem IsCSPolytope5.ridge_antipodal_capacity
    (carrier : Row → Prop) [DecidablePred carrier]
    {F : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hFC : carrier (faceRow P F)) (A : Finset (Set E5))
    (hA : ∀ T ∈ A, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3)
    (hwide : ∀ T ∈ A, ∀ U ∈ A, cnt P F 0 < cnt P T 0 + cnt P U 0)
    (hcar : ∀ T ∈ A, ∀ H ∈ faces P, dim H = 4 → T ⊆ H → carrier (faceRow P H)) :
    2 * A.card + 2 ≤ ((facetRows P).filter fun R => decide (carrier R)).length := by
  let Fs := (hP.kfaces_finite 4).toFinset
  let C := Fs.filter (fun H => carrier (faceRow P H))
  let S := Fs.filter (fun H => H ≠ F ∧ ∃ T ∈ A, T ⊆ H)
  have mFs : ∀ {H}, H ∈ Fs ↔ H ∈ faces P ∧ dim H = 4 := fun {H} => by
    rw [Set.Finite.mem_toFinset]; rfl
  have mS : ∀ {H}, H ∈ S ↔ H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ ∃ T ∈ A, T ⊆ H := by
    intro H
    simp only [S,Finset.mem_filter,mFs]
    tauto
  have hSC : ∀ H ∈ S, H ∈ C := by
    intro H hH
    obtain ⟨hH,hH4,_,T,hTA,hTH⟩ := mS.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨hH,hH4⟩,hcar T hTA H hH hH4 hTH⟩
  have hCn : ∀ H ∈ C, -H ∈ C := by
    intro H hH
    obtain ⟨hH,hHC⟩ := Finset.mem_filter.1 hH
    obtain ⟨hH,hH4⟩ := mFs.1 hH
    exact Finset.mem_filter.2 ⟨mFs.2 ⟨neg_mem_faces hP.symm hH,by rw [dim_neg,hH4]⟩,
      by rwa [hP.faceRow_neg]⟩
  have hcard : A.card ≤ S.card := by
    have hs : A ⊆ S.image (fun H => F ∩ H) := by
      intro T hTA
      obtain ⟨hT,hTF,hT3⟩ := hA T hTA
      obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
      refine Finset.mem_image.2 ⟨H,mS.2 ⟨hH,hH4,hHF,T,hTA,hTH⟩,?_⟩
      exact (hP.three_face_eq_inter hF hF4 hH hH4 hHF.symm hT hT3 hTF hTH).symm
    exact (Finset.card_le_card hs).trans Finset.card_image_le
  have hdisj : Disjoint S (S.image (fun H => -H)) := by
    rw [Finset.disjoint_left]
    intro H hHS hHN
    obtain ⟨K,hKS,hKH⟩ := Finset.mem_image.1 hHN
    obtain ⟨hH,hH4,_,T,hTA,hTH⟩ := mS.1 hHS
    obtain ⟨_,_,_,U,hUA,hUK⟩ := mS.1 hKS
    have hUnH : U ⊆ -H := by rw [← hKH,neg_neg]; exact hUK
    have hd := Set.disjoint_of_subset hTH hUnH (hP.facet_disjoint_neg hH hH4)
    have hc := hP.cnt_zero_add_le_of_disjoint (hA T hTA).2.1 (hA U hUA).2.1 hd
    exact (not_lt_of_ge hc) (hwide T hTA U hUA)
  have hnotF : F ∉ S := fun hm => (mS.1 hm).2.2.1 rfl
  have hnotN : -F ∉ S := by
    intro hm
    obtain ⟨_,_,_,T,hTA,hTN⟩ := mS.1 hm
    obtain ⟨x,hx⟩ := (hA T hTA).1.1
    exact Set.disjoint_left.1 (hP.facet_disjoint_neg hF hF4)
      ((hA T hTA).2.1 hx) (hTN hx)
  have hsub : S ∪ S.image (fun H => -H) ⊆ (C.erase F).erase (-F) := by
    intro H hH
    rcases Finset.mem_union.1 hH with hs | hs
    · exact Finset.mem_erase.2 ⟨fun he => hnotN (he ▸ hs),
        Finset.mem_erase.2 ⟨fun he => hnotF (he ▸ hs),hSC H hs⟩⟩
    · obtain ⟨K,hK,rfl⟩ := Finset.mem_image.1 hs
      exact Finset.mem_erase.2 ⟨fun he => hnotF ((neg_injective he) ▸ hK),
        Finset.mem_erase.2 ⟨fun he => hnotN ((neg_eq_iff_eq_neg.1 he) ▸ hK),hCn K (hSC K hK)⟩⟩
  have hFC' : F ∈ C := Finset.mem_filter.2 ⟨mFs.2 ⟨hF,hF4⟩,hFC⟩
  have hne : -F ≠ F := fun he =>
    (hP.ne_of_dim_ne' (by rw [hF4]; decide)) (hP.eq_of_neg_eq hF he)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj,Finset.card_image_of_injective _ neg_injective,
    Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hne,hCn F hFC'⟩),
    Finset.card_erase_of_mem hFC'] at hc
  have he : C.card = ((facetRows P).filter fun R => decide (carrier R)).length := by
    rw [length_filter_eq_sum,hP.facetRows_sum (fun R => if carrier R then 1 else 0)]
    simp only [C,Fs,Finset.card_filter]
  rw [← he]
  have ht : 2 ≤ C.card := by
    have hs : ({F,-F} : Finset (Set E5)) ⊆ C := by
      intro H hH
      rcases Finset.mem_insert.1 hH with rfl | hH
      · exact hFC'
      · exact Finset.mem_singleton.1 hH ▸ hCn F hFC'
    have hh := Finset.card_le_card hs
    rwa [Finset.card_pair hne.symm] at hh
  omega

/-- A reusable Hall-type bound for any finite set of wide ridge types. -/
theorem IsCSPolytope5.ridge_type_pair_capacity
    (carrier : Row → Prop) [DecidablePred carrier]
    (types : List (ℕ × ℕ × ℕ)) (hnd : types.Nodup) {rows : List Row}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hfree : ∀ H ∈ faces P, dim H = 4 → ¬ carrier (faceRow P H) →
      ∀ t ∈ types, tcnt P H t = 0)
    {F : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hFC : carrier (faceRow P F))
    (hwide : ∀ t ∈ types, ∀ u ∈ types, cnt P F 0 < t.1 + u.1) :
    (types.map (tcnt P F)).sum + 1 ≤ (rows.filter fun R => decide (carrier R)).length := by
  let A := (hP.below_finite F 3).toFinset.filter fun T => tri3 P T ∈ types
  have hA : ∀ T ∈ A, T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 := by
    intro T hT
    have hh := (Finset.mem_filter.1 hT).1
    rwa [Set.Finite.mem_toFinset] at hh
  have hw : ∀ T ∈ A, ∀ U ∈ A, cnt P F 0 < cnt P T 0 + cnt P U 0 := by
    intro T hT U hU
    exact hwide _ (Finset.mem_filter.1 hT).2 _ (Finset.mem_filter.1 hU).2
  have hcar : ∀ T ∈ A, ∀ H ∈ faces P, dim H = 4 → T ⊆ H → carrier (faceRow P H) := by
    intro T hT H hH hH4 hTH
    by_contra hn
    have hz := hfree H hH hH4 hn _ (Finset.mem_filter.1 hT).2
    have ht := hP.one_le_tcnt (hA T hT).1 hTH (hA T hT).2.2
    omega
  have hc := hP.ridge_antipodal_capacity carrier hF hF4 hFC A hA hw hcar
  have he := (hp.filter (fun R => decide (carrier R))).length_eq
  rw [List.filter_append,List.length_append] at he
  rw [he] at hc
  have ha := hP.tcnt_list_sum_eq_card F types hnd
  change (types.map (tcnt P F)).sum = A.card at ha
  omega

end Kalai5
