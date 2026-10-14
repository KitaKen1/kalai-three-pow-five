import Kalai5.FullProd.UConcurrent

/-!
# The facet `U = (9, 19, 17, 7; 38)` at eighteen vertices and facets

`noU1818`: a centrally symmetric 5-polytope with eighteen vertices and eighteen facets has no
facet of row `u9Row = (9, 19, 17, 7; 38)`.

* The dual of such a facet has seven vertices, so its combinatorial type is unique (Gale diagrams,
  `Gale.uStar_facets`); this labels its vertices and 3-faces (`IsCSPolytope5.u_structure`), and
  with eighteen vertices the vertices of `P` are the `±x i` (`IsCSPolytope5.uConf`).
* Its two triangular prisms share a quadrilateral, so their four product edges are parallel or
  concurrent (`UConf.lines`).
* Parallel: the sixteen "vertical" vertices of the polar, and the vertex `z` of the pentagon, force
  twenty vertices of the polar (`UConf.parallel_false`).
* Concurrent: in normal form the polar has twenty-four vertices (`UConf.concurrent_false`).
-/

namespace Kalai5

/-- The row of the facet `U`. -/
def u9Row : Row := ⟨9, 19, 17, 7, 38⟩

/-- The geometric vertex count excludes U for every facet count at most eighteen. -/
theorem IsCSPolytope5.u9Row_not_mem_of_facets_le_eighteen {P : Set E5}
    (hP : IsCSPolytope5 P) (hv : fvec P 0 = 18) (hh : fvec P 4 ≤ 18) :
    u9Row ∉ facetRows P := by
  intro hU
  obtain ⟨U,hUf,h4,hrow⟩ := hP.mem_facetRows hU
  obtain ⟨C⟩ := hP.uConf hv hUf h4 hrow
  rcases C.lines hP with ⟨p,sA,sB,sC,sD,hpA,hpB,hpC,hpD⟩ | ⟨μB,μC,μD,hB,hC,hD⟩
  · exact C.concurrent_false_of_le hP hh hpA hpB hpC hpD
  · exact C.parallel_false_of_le hP hh hB hC hD

/-- A full U facet at eighteen vertices forces at least twenty facets. -/
theorem IsCSPolytope5.twenty_le_facets_of_u9Row {P : Set E5}
    (hP : IsCSPolytope5 P) (hv : fvec P 0 = 18) (hU : u9Row ∈ facetRows P) :
    20 ≤ fvec P 4 := by
  by_contra hn
  obtain ⟨k,hk⟩ := hP.even_fvec 4 (by omega)
  exact hP.u9Row_not_mem_of_facets_le_eighteen hv (by omega) hU

/-- In particular U is absent on the polar side of the (16,18) endpoint. -/
theorem IsCSPolytope5.u9Row_not_mem_polar_16_18 {P : Set E5}
    (hP : IsCSPolytope5 P) (hv : fvec P 0 = 16) (hh : fvec P 4 = 18) :
    u9Row ∉ facetRows (polarSet P) := by
  have h0 := hP.fvec_polar 4 (by norm_num)
  have h4 := hP.fvec_polar 0 (by norm_num)
  norm_num at h0 h4
  apply hP.polar.u9Row_not_mem_of_facets_le_eighteen
  · rw [h0,hh]
  · rw [h4,hv]; norm_num

/-- **No facet `U` at `(18, 18)`.** -/
theorem noU1818 : ∀ P : Set E5, IsCSPolytope5 P → fvec P 0 = 18 → fvec P 4 = 18 →
    u9Row ∉ facetRows P := by
  intro P hP hv hh hU
  obtain ⟨U, hUf, h4, hrow⟩ := hP.mem_facetRows hU
  obtain ⟨C⟩ := hP.uConf hv hUf h4 hrow
  rcases C.lines hP with ⟨p, sA, sB, sC, sD, hpA, hpB, hpC, hpD⟩ | ⟨μB, μC, μD, hB, hC, hD⟩
  · exact C.concurrent_false hP hh hpA hpB hpC hpD
  · exact C.parallel_false hP hh hB hC hD

end Kalai5
