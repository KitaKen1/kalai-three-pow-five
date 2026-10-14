import Kalai5.Endpoints.G2S2LastStructure
import Kalai5.Endpoints.FullSixAllNeighbours
import Kalai5.Endpoints.Full6106PyramidObstruction

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- The no-prism branch has four pyramids across a shared (6,10,6)
ridge, contradicting the saturated full-neighbour bound. -/
theorem IsCSPolytope5.g2s2_last_6106_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow)
    (hprof : fv8.map (tcnt P F) = [3,4,0,0,1,0,0,0,0,0,0,0]) : False := by
  have hcF := hprof
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hcF
  have hn : cnt P F 0 = 8 := congrArg Row.n hB
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,10,6))
  obtain ⟨H,hH,hH4,hHF,hHnF,hHB,hTI⟩ := hP.g2s2_last_special_partner hp hF h4 hB hT hTF hT3
    (by rw [ht]; decide +kernel)
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHB
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hone := hP.full_six_all_partner_unique hv hc hF h4 hn hH hH4 hH8 hHF hHnF hT6 hTI
  exact hP.full_6106_four_pyramids_false hv hh hc
    (fun _ hX hX4 hX8 => hP.g2s2_last_small_seven hp hX hX4 hX8)
    (fun _ hX hX4 hX8 => congrArg Row.r (hP.g2s2_last_full_b hp hX hX4 hX8))
    hone hF h4 hn hH hH4 hH8 hHF hHnF hT hT3 ht hTI (by omega)

/-- The (6,11,7) branch has a second six-vertex ridge. Its small
partner misses a full pair, impossible for an eight-ridge full neighbour. -/
theorem IsCSPolytope5.g2s2_last_6117_false
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow)
    (hprof : fv8.map (tcnt P F) = [4,2,0,1,0,1,0,0,0,0,0,0]) : False := by
  have hcF := hprof
  simp only [fv8,List.map_cons,List.map_nil,List.cons.injEq] at hcF
  have hn : cnt P F 0 = 8 := congrArg Row.n hB
  obtain ⟨T,hT,hTF,hT3,ht⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,11,7))
  obtain ⟨U,hU,hUF,hU3,hu⟩ := hP.exists_of_tcnt (by omega : 1 ≤ tcnt P F (6,9,5))
  obtain ⟨H,hH,hH4,hHF,hHnF,hHB,hTI⟩ := hP.g2s2_last_special_partner hp hF h4 hB hT hTF hT3
    (by rw [ht]; decide +kernel)
  have hH8 : cnt P H 0 = 8 := congrArg Row.n hHB
  have hHr : cnt P H 3 = 8 := congrArg Row.r hHB
  have hT6 : cnt P T 0 = 6 := congrArg Prod.fst ht
  have hU6 : cnt P U 0 = 6 := congrArg Prod.fst hu
  have hUT : U ≠ T := by intro he; rw [he,ht] at hu; contradiction
  exact hP.full_two_six_ridges_shared_eight_false hv hh hc
    (fun _ hX hX4 hX8 => hP.g2s2_last_small_seven hp hX hX4 hX8)
    hF h4 hn (hP.g2s2_last_no_big hp F) hH hH4 hH8 hHF hHnF (by omega)
    hT hT3 hT6 hTI hU hUF hU3 hU6 hUT

/-- Every full facet in the last profile must have three tetrahedra,
three square pyramids, one triangular bipyramid and one triangular prism. -/
theorem IsCSPolytope5.g2s2_last_b_ridge_profile
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) (hc : cnt8 (facetRows P) = 4)
    (hp : (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs))
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) (hB : faceRow P F = G2S4.bRow) :
    fv8.map (tcnt P F) = [3,3,1,1,0,0,0,0,0,0,0,0] := by
  rcases hP.g2s2_last_b_cases hv hh hp hF h4 hB with h | h | h
  · exact (hP.g2s2_last_6106_false hv hh hc hp hF h4 hB h).elim
  · exact (hP.g2s2_last_6117_false hv hh hc hp hF h4 hB h).elim
  · exact h

/-- Package the unique remaining local configuration for the main endpoint. -/
theorem IsCSPolytope5.fewFull18_positive_last_b_structure
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (facetRows P).Perm (G2S2.lastPairs ++ G2S2.lastPairs) ∧
      ∀ F ∈ faces P, dim F = 4 → cnt P F 0 = 8 →
        fv8.map (tcnt P F) = [3,3,1,1,0,0,0,0,0,0,0,0] := by
  have he := hP.fewFull18_positive_last_pairs hv hh h1 h6 hlt
  have hp := hP.fewFull18_positive_pairs_perm hv hh h1 h6 hlt
  rw [he] at hp
  refine ⟨hp,?_⟩
  intro F hF h4 hn
  exact hP.g2s2_last_b_ridge_profile hv hh (hP.fewFull18_positive_constraints hv hh h1 h6 hlt).1
    hp hF h4 (hP.g2s2_last_full_b hp hF h4 hn)

end Kalai5
