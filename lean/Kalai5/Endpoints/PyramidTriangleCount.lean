import Kalai5.Endpoints.NearPyramidRidge

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- If at most one square pyramid meets a six-vertex ridge in a triangle,
all other square pyramids use distinct quadrilaterals of that ridge. -/
theorem IsCSPolytope5.pyramid_count_le_quad_add_one
    {F T : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4) (hF8 : cnt P F 0 = 8)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (hT6 : cnt P T 0 = 6)
    (hunique : ∀ R ∈ faces P, R ⊆ F → dim R = 3 → tri3 P R = (5,8,5) →
      cnt P (T ∩ R) 0 = 3 →
      ∀ S ∈ faces P, S ⊆ F → dim S = 3 → tri3 P S = (5,8,5) →
      cnt P (T ∩ S) 0 = 3 → R = S) :
    tcnt P F (5,8,5) ≤ q4 P T + 1 := by
  let AP : Set (Set E5) := {R | R ∈ faces P ∧ R ⊆ F ∧ dim R = 3 ∧ tri3 P R = (5,8,5)}
  have hfin : AP.Finite := hP.faces_finite.subset fun R hR => hR.1
  let A := hfin.toFinset
  let B := A.filter (fun R => cnt P (T ∩ R) 0 = 3)
  let D := A.filter (fun R => cnt P (T ∩ R) 0 ≠ 3)
  have mA : ∀ {R}, R ∈ A ↔ R ∈ faces P ∧ R ⊆ F ∧ dim R = 3 ∧ tri3 P R = (5,8,5) := by
    intro R
    exact Set.Finite.mem_toFinset hfin
  have hAc : A.card = tcnt P F (5,8,5) := by
    rw [← Set.ncard_coe_finset]
    change (↑hfin.toFinset : Set (Set E5)).ncard = _
    rw [Set.Finite.coe_toFinset]
    rfl
  have hsplit : B.card + D.card = A.card :=
    Finset.card_filter_add_card_filter_not (p := fun R => cnt P (T ∩ R) 0 = 3)
  have hBc : B.card ≤ 1 := by
    apply Finset.card_le_one.2
    intro R hRB S hSB
    obtain ⟨hRA,hR3⟩ := Finset.mem_filter.1 hRB
    obtain ⟨hSA,hS3⟩ := Finset.mem_filter.1 hSB
    obtain ⟨hR,hRF,hRd,htR⟩ := mA.1 hRA
    obtain ⟨hS,hSF,hSd,htS⟩ := mA.1 hSA
    exact hunique R hR hRF hRd htR hR3 S hS hSF hSd htS hS3
  have hquad : ∀ R ∈ D, T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 ∧ cnt P (T ∩ R) 0 = 4 := by
    intro R hRD
    obtain ⟨hRA,hnot⟩ := Finset.mem_filter.1 hRD
    obtain ⟨hR,hRF,hR3,htR⟩ := mA.1 hRA
    have hR5 : cnt P R 0 = 5 := congrArg Prod.fst htR
    have hTR : T ≠ R := by intro he; rw [he] at hT6; omega
    obtain ⟨hQ,hQ2⟩ := hP.ridge_inter_polygon_of_vertex_budget hT hTF hT3 hR hRF hR3 hTR (by omega)
    have hlo := hP.three_le_cnt hQ hQ2
    have hhi := hP.cnt_zero_lt hQ hR inter_subset_right (by intro he; rw [he,hR3] at hQ2; omega)
    exact ⟨hQ,hQ2,by omega⟩
  have hi : Set.InjOn (fun R => T ∩ R) (↑D : Set (Set E5)) := by
    intro R hRD S hSD he
    change T ∩ R = T ∩ S at he
    obtain ⟨hR,hRF,hR3,htR⟩ := mA.1 (Finset.mem_filter.1 hRD).1
    obtain ⟨hS,hSF,hS3,htS⟩ := mA.1 (Finset.mem_filter.1 hSD).1
    have hR5 : cnt P R 0 = 5 := congrArg Prod.fst htR
    have hS5 : cnt P S 0 = 5 := congrArg Prod.fst htS
    have hRT : R ≠ T := by intro he; rw [he] at hR5; omega
    have hST : S ≠ T := by intro he; rw [he] at hS5; omega
    obtain ⟨hQ,hQ2,_⟩ := hquad R hRD
    exact hP.ridge_partner_unique_inside hF hF4 hQ (inter_subset_left.trans hTF) hQ2
      hT hTF hT3 inter_subset_left hR hRF hR3 inter_subset_right hRT
      hS hSF hS3 (by change T ∩ R ⊆ S; rw [he]; exact inter_subset_right) hST
  have hs : (fun R => T ∩ R) '' (↑D : Set (Set E5)) ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    rintro Q ⟨R,hRD,rfl⟩
    obtain ⟨hQ,hQ2,hQ4⟩ := hquad R hRD
    exact ⟨hQ,inter_subset_left,hQ2,hQ4⟩
  have hDc := Set.ncard_le_ncard hs (hP.faces_finite.subset fun Q hQ => hQ.1)
  rw [hi.ncard_image,Set.ncard_coe_finset] at hDc
  change D.card ≤ q4 P T at hDc
  omega

end Kalai5
