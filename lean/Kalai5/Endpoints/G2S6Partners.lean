import Kalai5.Endpoints.G2S6Ridges
import Kalai5.Endpoints.G2S6Profile

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A rare row cannot reappear across a ridge: the only other facet with
that row is antipodal and disjoint. -/
theorem IsCSPolytope5.unique_pair_ridge_partner_row_ne {rows : List Row} {R : Row}
    (hp : (facetRows P).Perm (rows ++ rows)) (hc : PrismBudget.pairRowCount R rows = 1)
    {F H T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hR : faceRow P F = R)
    (hH : H ∈ faces P) (hH4 : dim H = 4) (hHF : H ≠ F)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hTH : T ⊆ H) : faceRow P H ≠ R := by
  intro hHR
  have hcount : ((facetRows P).map fun U => if U = R then 1 else 0).sum = 2 := by
    rw [(hp.map _).sum_eq,List.map_append,List.sum_append]
    change PrismBudget.pairRowCount R rows + PrismBudget.pairRowCount R rows = 2
    omega
  rcases hP.two_row_facets_eq_or_neg hcount hF h4 hR hH hH4 hHR with he | he
  · exact hHF he
  · obtain ⟨x,hx⟩ := hT.1
    have hxneg : -x ∈ F := by
      have hh := hTH hx
      rwa [he,Set.mem_neg] at hh
    exact (hP.ne_of_dim_ne' (by rw [h4]; decide))
      (hP.eq_of_mem_of_neg_mem hF (hTF hx) hxneg)

theorem IsCSPolytope5.g2s6_h_6117_partner
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) :
    ∃ C T, C ∈ faces P ∧ dim C = 4 ∧ C ≠ F ∧ faceRow P C = G2S6.cRow ∧
      T ∈ faces P ∧ dim T = 3 ∧ tri3 P T = (6,11,7) ∧ T = F ∩ C := by
  have hc := (hP.g2s6_h_ridge_profile hp hb hF h4 hR).2.2.2
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hc
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,11,7))
  obtain ⟨C,hC,hC4,hCF,hTC⟩ := hP.exists_other_facet hT hT3 hTF
  have hne := hP.unique_pair_ridge_partner_row_ne hp (by decide +kernel)
    hF h4 hR hC hC4 hCF hT hTF hTC
  have hpos := hP.one_le_tcnt hT hTC hT3
  rw [ht] at hpos
  have hCR := (hP.g2s6_6117_carrier hp hb hC hC4 hpos).resolve_left hne
  exact ⟨C,T,hC,hC4,hCF,hCR,hT,hT3,ht,
    hP.three_face_eq_inter hF h4 hC hC4 hCF.symm hT hT3 hTF hTC⟩

theorem IsCSPolytope5.g2s6_h_bipyr_partner
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow) :
    ∃ D B, D ∈ faces P ∧ dim D = 4 ∧ D ≠ F ∧ faceRow P D = G2S6.dRow ∧
      B ∈ faces P ∧ dim B = 3 ∧ tri3 P B = (5,9,6) ∧ B = F ∩ D := by
  have hc := (hP.g2s6_h_ridge_profile hp hb hF h4 hR).2.2.2
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hc
  obtain ⟨B,hB,hBF,hB3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (5,9,6))
  obtain ⟨D,hD,hD4,hDF,hBD⟩ := hP.exists_other_facet hB hB3 hBF
  have hne := hP.unique_pair_ridge_partner_row_ne hp (by decide +kernel)
    hF h4 hR hD hD4 hDF hB hBF hBD
  have hpos := hP.one_le_tcnt hB hBD hB3
  rw [ht] at hpos
  have hDR : faceRow P D = G2S6.dRow := by
    rcases hP.g2s6_row_cases hp hD hD4 with hY | hDrow | hH | hC
    · have hz := hP.bipyr_free_rows_count_zero hD hD4 (by rw [hY]; decide +kernel)
      omega
    · exact hDrow
    · exact (hne hH).elim
    · have hz := hP.g2s6_c_bipyr_zero hp hb hD hD4 hC
      omega
  exact ⟨D,B,hD,hD4,hDF,hDR,hB,hB3,ht,
    hP.three_face_eq_inter hF h4 hD hD4 hDF.symm hB hB3 hBF hBD⟩

/-- The shared six-vertex ridge meets every other ridge in both full
facets. This conclusion only uses the equality seven plus one equals eight. -/
theorem IsCSPolytope5.g2s6_full_6117_universal
    {F T : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = G2S6.hRow ∨ faceRow P F = G2S6.cRow)
    (hT : T ∈ faces P) (hTF : T ⊆ F) (hT3 : dim T = 3) (ht : tri3 P T = (6,11,7)) :
    ∀ R ∈ faces P, R ⊆ F → dim R = 3 → R ≠ T →
      T ∩ R ∈ faces P ∧ dim (T ∩ R) = 2 := by
  have hr : cnt P F 3 = 8 := hR.elim (congrArg Row.r) (congrArg Row.r)
  have htp : cnt P T 2 = 7 := congrArg (fun t => t.2.2) ht
  exact fun R hR hRF hR3 hRT =>
    hP.universal_ridge_of_count hF h4 hT hTF hT3 (by omega) hR hRF hR3 hRT

/-- Package the rigid local profile and both shared-ridge partners for
the actual remaining Gs=6 counterexample cell. -/
theorem IsCSPolytope5.fewFull18_positive_g2s6_structure
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) (hS : (flagDataOf P).Gs = 6) :
    ∃ F D C B T, F ∈ faces P ∧ dim F = 4 ∧ faceRow P F = G2S6.hRow ∧
      q55w P F + 2 * exc P F = 3 ∧
      D ∈ faces P ∧ dim D = 4 ∧ faceRow P D = G2S6.dRow ∧
      C ∈ faces P ∧ dim C = 4 ∧ faceRow P C = G2S6.cRow ∧
      B ∈ faces P ∧ dim B = 3 ∧ tri3 P B = (5,9,6) ∧ B = F ∩ D ∧
      T ∈ faces P ∧ dim T = 3 ∧ tri3 P T = (6,11,7) ∧ T = F ∩ C := by
  have hp := hP.fewFull18_positive_g2s6_profile hv hh h1 h6 hlt hS
  have hbudget := hP.fewFull18_positive_actual_weight_budget hv hh h1 h6 hlt
  rw [hS] at hbudget
  have hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120 :=
    by simpa using hbudget
  have hm : G2S6.hRow ∈ facetRows P := hp.mem_iff.2
    (List.mem_append_left _ (by decide +kernel))
  obtain ⟨F,hF,h4,hR⟩ := hP.mem_facetRows hm
  obtain ⟨D,B,hD,hD4,_,hDR,hB,hB3,hBt,hBF⟩ := hP.g2s6_h_bipyr_partner hp hb hF h4 hR
  obtain ⟨C,T,hC,hC4,_,hCR,hT,hT3,hTt,hTF⟩ := hP.g2s6_h_6117_partner hp hb hF h4 hR
  have hw := hP.g2s6_weight_eq hp hb hF h4
  rw [hR] at hw
  have hf : G2S6.rowWeight G2S6.hRow = 3 := by decide +kernel
  rw [hf] at hw
  exact ⟨F,D,C,B,T,hF,h4,hR,hw,hD,hD4,hDR,hC,hC4,hCR,hB,hB3,hBt,hBF,hT,hT3,hTt,hTF⟩

/-- Every full facet has a six-vertex shared ridge with another full facet. -/
theorem IsCSPolytope5.g2s6_full_partner
    (hp : (facetRows P).Perm (G2S6.pairs ++ G2S6.pairs))
    (hb : (∑ H ∈ (hP.kfaces_finite 4).toFinset, (q55w P H + 2 * exc P H)) ≤ 120)
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hn : cnt P F 0 = 8) :
    ∃ H T, H ∈ faces P ∧ dim H = 4 ∧ H ≠ F ∧ H ≠ -F ∧ cnt P H 0 = 8 ∧
      T ∈ faces P ∧ dim T = 3 ∧ tri3 P T = (6,11,7) ∧ T = F ∩ H := by
  have htpos : 1 ≤ tcnt P F (6,11,7) := by
    rcases hP.g2s6_row_cases hp hF h4 with hY | hD | hH | hC
    · have := congrArg Row.n hY
      change cnt P F 0 = 7 at this
      omega
    · have := congrArg Row.n hD
      change cnt P F 0 = 7 at this
      omega
    · have ht := (hP.g2s6_h_ridge_profile hp hb hF h4 hH).2.2.2
      simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at ht
      omega
    · have ht := (hP.g2s6_c_ridge_profile hp hb hF h4 hC).2.2.2
      simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at ht
      omega
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt htpos
  obtain ⟨H,hH,hH4,hHF,hTH⟩ := hP.exists_other_facet hT hT3 hTF
  have hpos := hP.one_le_tcnt hT hTH hT3
  rw [ht] at hpos
  have hHr := hP.g2s6_6117_carrier hp hb hH hH4 hpos
  have hH8 : cnt P H 0 = 8 := hHr.elim (congrArg Row.n) (congrArg Row.n)
  have hneg : H ≠ -F := by
    intro he
    have hd := hP.facet_disjoint_neg hF h4
    obtain ⟨x,hx⟩ := hT.1
    exact Set.disjoint_left.1 hd (hTF hx) (he ▸ hTH hx)
  exact ⟨H,T,hH,hH4,hHF,hneg,hH8,hT,hT3,ht,
    hP.three_face_eq_inter hF h4 hH hH4 hHF.symm hT hT3 hTF hTH⟩

end Kalai5
