import Kalai5.Endpoints.EventBudget

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.q4_neg (F : Set E5) : q4 P (-F) = q4 P F := by
  have hs : {Q | Q ∈ faces P ∧ Q ⊆ -F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} =
      (fun Q : Set E5 => -Q) '' {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    ext Q
    constructor
    · rintro ⟨hQ,hQF,h2,h4⟩
      exact ⟨-Q,⟨neg_mem_faces hP.symm hQ,neg_subset_iff.1 hQF,
        by rw [dim_neg,h2],by rw [hP.cnt_neg,h4]⟩,neg_neg Q⟩
    · rintro ⟨Q,⟨hQ,hQF,h2,h4⟩,rfl⟩
      exact ⟨neg_mem_faces hP.symm hQ,Set.neg_subset_neg.2 hQF,
        by rw [dim_neg,h2],by rw [hP.cnt_neg,h4]⟩
  rw [q4,q4,hs,Set.ncard_image_of_injective _ neg_injective]

theorem IsCSPolytope5.non5_neg_empty_iff (F Q : Set E5) :
    non5 P (-F) (-Q) = ∅ ↔ non5 P F Q = ∅ := by
  have hmap (F Q : Set E5) : non5 P F Q = ∅ → non5 P (-F) (-Q) = ∅ := by
    intro he
    apply Set.eq_empty_iff_forall_notMem.2
    intro T hT
    have hn : -T ∈ non5 P F Q :=
      ⟨neg_mem_faces hP.symm hT.1,neg_subset_iff.1 hT.2.1,
        by rw [dim_neg]; exact hT.2.2.1,
        by simpa only [neg_neg] using Set.neg_subset_neg.2 hT.2.2.2.1,
        by rw [hP.cnt_neg]; exact hT.2.2.2.2⟩
    rw [he] at hn
    exact hn
  exact ⟨fun h => by simpa only [neg_neg] using hmap (-F) (-Q) h,hmap F Q⟩

theorem IsCSPolytope5.b55_ncard_neg (F : Set E5) :
    (b55set P (-F)).ncard = (b55set P F).ncard := by
  have hs : b55set P (-F) = (fun Q : Set E5 => -Q) '' b55set P F := by
    ext Q
    constructor
    · rintro ⟨hQ,hQF,h2,h4,hno⟩
      refine ⟨-Q,⟨neg_mem_faces hP.symm hQ,neg_subset_iff.1 hQF,
        by rw [dim_neg,h2],by rw [hP.cnt_neg,h4],?_⟩,neg_neg Q⟩
      apply (hP.non5_neg_empty_iff F (-Q)).1
      simpa only [neg_neg] using hno
    · rintro ⟨Q,⟨hQ,hQF,h2,h4,hno⟩,rfl⟩
      exact ⟨neg_mem_faces hP.symm hQ,Set.neg_subset_neg.2 hQF,
        by rw [dim_neg,h2],by rw [hP.cnt_neg,h4],(hP.non5_neg_empty_iff F Q).2 hno⟩
  rw [hs,Set.ncard_image_of_injective _ neg_injective]

theorem IsCSPolytope5.q55w_neg (F : Set E5) : q55w P (-F) = q55w P F := by
  rw [hP.q55w_eq_b55,hP.q55w_eq_b55,hP.q4_neg,hP.b55_ncard_neg]

theorem IsCSPolytope5.exc_neg (F : Set E5) : exc P (-F) = exc P F := by
  simp only [exc,hP.incid_neg,hP.cnt_neg]

/-- Antipodal facets have identical actual weights as well as identical rows. -/
theorem IsCSPolytope5.actual_weight_neg (F : Set E5) :
    q55w P (-F) + 2 * exc P (-F) = q55w P F + 2 * exc P F := by
  rw [hP.q55w_neg,hP.exc_neg]

/-- Both antipodal deficits occur in the sum. Thus a single facet can spend
at most half the global slack, for any certified row lower bound. -/
theorem IsCSPolytope5.twice_facet_weight_le_of_lower_bound
    (w : Row → ℕ)
    (hw : ∀ F ∈ faces P, dim F = 4 → (w (faceRow P F) : ℤ) ≤ q55w P F + 2 * exc P F)
    (B : ℤ)
    (hbudget : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ B)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    2 * (q55w P F + 2 * exc P F - (w (faceRow P F) : ℤ)) ≤
      B - ((facetRows P).map w).sum := by
  let d : Set E5 → ℤ := fun H => q55w P H + 2 * exc P H - (w (faceRow P H) : ℤ)
  have hnonneg : ∀ H ∈ (hP.kfaces_finite 4).toFinset, 0 ≤ d H := by
    intro H hH
    rw [Set.Finite.mem_toFinset] at hH
    exact sub_nonneg.2 (hw H hH.1 hH.2)
  have hnF : -F ≠ F := fun he =>
    (hP.ne_of_dim_ne' (by rw [h4]; decide)) (hP.eq_of_neg_eq hF he)
  have hsub : ({F,-F} : Finset (Set E5)) ⊆ (hP.kfaces_finite 4).toFinset := by
    intro H hH
    rw [Set.Finite.mem_toFinset]
    rcases Finset.mem_insert.1 hH with rfl | hH
    · exact ⟨hF,h4⟩
    · rw [Finset.mem_singleton] at hH
      subst H
      exact ⟨neg_mem_faces hP.symm hF,by rw [dim_neg,h4]⟩
  have hl := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun H hH _ => hnonneg H hH)
  have he : d (-F) = d F := by simp only [d,hP.actual_weight_neg,hP.faceRow_neg]
  rw [Finset.sum_pair hnF.symm,he] at hl
  dsimp only [d] at hl
  rw [Finset.sum_sub_distrib] at hl
  rw [hP.facetRows_sum w,Nat.cast_sum]
  convert_to 2 * (q55w P F + 2 * exc P F - (w (faceRow P F) : ℤ)) ≤
    B - ∑ H ∈ (hP.kfaces_finite 4).toFinset, (w (faceRow P H) : ℤ) using 1
  linarith

namespace PrismBudget

def pairSlack (S : ℤ) (rows : List Row) : ℤ := 78 - 3 * S - (rows.map q55QThreeRowWeight).sum

def pairParityOK (S : ℤ) (rows : List Row) : Bool :=
  decide (2 ∣ yCount rows) || !(rows.all fun R => decide (R = excRow ∨ freeAt (pairSlack S rows) R))

def pairEventParityOK (S : ℤ) (rows : List Row) : Bool :=
  decide (2 ∣ (rows.map rowEvent).sum) ||
    !(rows.all fun R => decide (eventKnown (pairSlack S rows) R))

end PrismBudget

theorem IsCSPolytope5.facet_weight_le_of_pair_slack {rows : List Row} {S : ℤ}
    (hp : (facetRows P).Perm (rows ++ rows))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 156 - 6 * S)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    q55w P F + 2 * exc P F ≤ (q55QThreeRowWeight (faceRow P F) : ℤ) + PrismBudget.pairSlack S rows := by
  have hu := hP.twice_facet_weight_le_of_lower_bound q55QThreeRowWeight
    (fun _ => hP.q55_qThree_row_weight) (156 - 6 * S) hb hF h4
  rw [(hp.map q55QThreeRowWeight).sum_eq,List.map_append,List.sum_append,Nat.cast_add] at hu
  unfold PrismBudget.pairSlack
  omega

end Kalai5
