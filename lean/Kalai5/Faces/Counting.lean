import Kalai5.Faces.Basic

/-!
# Double counting of flags, and facets of centrally symmetric polytopes

* `flag2 P i j = Σ_{j-faces F} cnt P F i` (double counting over the larger face);
* a proper face contains at most half of the vertices (no antipodal pair);
* consequences: the incidence bound `2 f₀₄ ≤ f₀ f₄`, and the facet-row facts
  `length = f₄`, `Σ n = f₀₄`, `Σ e = f₁₄`, `Σ p = f₂₄`, `2n ≤ f₀`.
-/

namespace Kalai5

open Set Pointwise

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.kfaces_finite (k : ℕ) : {F | F ∈ faces P ∧ dim F = k}.Finite :=
  hP.faces_finite.subset fun F hF => hF.1

lemma IsCSPolytope5.below_finite (F : Set E5) (k : ℕ) :
    {G | G ∈ faces P ∧ G ⊆ F ∧ dim G = k}.Finite :=
  hP.faces_finite.subset fun G hG => hG.1

/-- **Double counting.** `flag2 P i j = Σ_{F : j-face} #{i-faces in F}`. -/
lemma IsCSPolytope5.flag2_eq_sum (i j : ℕ) :
    flag2 P i j = ∑ F ∈ (hP.kfaces_finite j).toFinset, cnt P F i := by
  classical
  have hS : {FG : Set E5 × Set E5 | FG.1 ∈ faces P ∧ FG.2 ∈ faces P ∧ FG.1 ⊆ FG.2 ∧
      dim FG.1 = i ∧ dim FG.2 = j}.Finite :=
    (hP.faces_finite.prod hP.faces_finite).subset fun FG h => ⟨h.1, h.2.1⟩
  rw [flag2, Set.ncard_eq_toFinset_card _ hS,
    Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := (hP.kfaces_finite j).toFinset)
      (fun FG hFG => by
        rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hFG
        rw [Finset.mem_coe, Set.Finite.mem_toFinset]
        exact ⟨hFG.2.1, hFG.2.2.2.2⟩)]
  refine Finset.sum_congr rfl fun F hF => ?_
  rw [Set.Finite.mem_toFinset] at hF
  rw [cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F i)]
  refine Finset.card_nbij' Prod.fst (fun G => (G, F)) ?_ ?_ ?_ ?_
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset] at hFG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    obtain ⟨⟨h1, -, h3, h4, -⟩, h⟩ := hFG
    exact ⟨h1, h ▸ h3, h4⟩
  · intro G hG
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hG
    rw [Finset.mem_coe, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hG.1, hF.1, hG.2.1, hG.2.2, hF.2⟩, rfl⟩
  · intro FG hFG
    rw [Finset.mem_coe, Finset.mem_filter] at hFG
    obtain ⟨-, h⟩ := hFG
    ext <;> simp [h]
  · intro G _; rfl

/-- A proper face contains at most half of the vertices. -/
lemma IsCSPolytope5.two_mul_cnt_le {F : Set E5} (hF : F ∈ faces P) (hne : F ≠ P) :
    2 * cnt P F 0 ≤ fvec P 0 := by
  set A := {G | G ∈ faces P ∧ G ⊆ F ∧ dim G = 0} with hAdef
  have hAfin : A.Finite := hP.below_finite F 0
  have hVfin : {G | G ∈ faces P ∧ dim G = 0}.Finite := hP.kfaces_finite 0
  have himg : ((fun G : Set E5 => -G) '' A).ncard = A.ncard :=
    Set.ncard_image_of_injective _ neg_injective
  have hdisj : Disjoint A ((fun G : Set E5 => -G) '' A) := by
    rw [Set.disjoint_left]
    rintro G ⟨-, hGF, -⟩ ⟨G', ⟨hG', hG'F, -⟩, rfl⟩
    obtain ⟨x, hx⟩ := hG'.1
    have h1 : x ∈ F := hG'F hx
    have h2 : -x ∈ F := hGF (by simpa using hx)
    exact hne (hP.eq_of_mem_of_neg_mem hF h1 h2)
  have hsub : A ∪ ((fun G : Set E5 => -G) '' A) ⊆ {G | G ∈ faces P ∧ dim G = 0} := by
    rintro G (⟨hG, -, hd⟩ | ⟨G', ⟨hG', -, hd'⟩, rfl⟩)
    · exact ⟨hG, hd⟩
    · exact ⟨neg_mem_faces hP.symm hG', by rw [dim_neg]; exact hd'⟩
  have hle := Set.ncard_le_ncard hsub hVfin
  rw [Set.ncard_union_eq hdisj hAfin (hAfin.image _), himg] at hle
  show 2 * A.ncard ≤ _
  rw [fvec]; omega

/-- **Incidence bound** `2 f₀₄ ≤ f₀ f₄`. -/
theorem IsCSPolytope5.incidence_bound : 2 * flag2 P 0 4 ≤ fvec P 0 * fvec P 4 := by
  rw [hP.flag2_eq_sum 0 4, Finset.mul_sum]
  calc ∑ F ∈ (hP.kfaces_finite 4).toFinset, 2 * cnt P F 0
      ≤ ∑ _F ∈ (hP.kfaces_finite 4).toFinset, fvec P 0 := by
        refine Finset.sum_le_sum fun F hF => ?_
        simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
        refine hP.two_mul_cnt_le hF.1 fun h => ?_
        have := hP.dim_self; rw [← h] at this; omega
    _ = fvec P 0 * fvec P 4 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
        congr 1
        rw [fvec, Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 4)]

/-! ### Facet rows -/

lemma IsCSPolytope5.facetList_eq :
    facetList P = (hP.kfaces_finite 4).toFinset.toList := by
  classical
  rw [facetList, dif_pos (hP.kfaces_finite 4)]

lemma IsCSPolytope5.facetRows_eq :
    facetRows P = (hP.kfaces_finite 4).toFinset.toList.map (faceRow P) := by
  rw [facetRows, hP.facetList_eq]

theorem IsCSPolytope5.facetRows_length : (facetRows P).length = fvec P 4 := by
  rw [hP.facetRows_eq, List.length_map, Finset.length_toList, fvec,
    Set.ncard_eq_toFinset_card _ (hP.kfaces_finite 4)]

lemma IsCSPolytope5.facetRows_sum (f : Row → ℕ) :
    ((facetRows P).map f).sum = ∑ F ∈ (hP.kfaces_finite 4).toFinset, f (faceRow P F) := by
  rw [hP.facetRows_eq, List.map_map, Finset.sum_map_toList]; rfl

theorem IsCSPolytope5.facetRows_sum_n : ((facetRows P).map Row.n).sum = flag2 P 0 4 := by
  rw [hP.facetRows_sum, hP.flag2_eq_sum]; rfl

theorem IsCSPolytope5.facetRows_sum_e : ((facetRows P).map Row.e).sum = flag2 P 1 4 := by
  rw [hP.facetRows_sum, hP.flag2_eq_sum]; rfl

theorem IsCSPolytope5.facetRows_sum_p : ((facetRows P).map Row.p).sum = flag2 P 2 4 := by
  rw [hP.facetRows_sum, hP.flag2_eq_sum]; rfl

lemma IsCSPolytope5.mem_facetRows {R : Row} (hR : R ∈ facetRows P) :
    ∃ F, F ∈ faces P ∧ dim F = 4 ∧ faceRow P F = R := by
  rw [hP.facetRows_eq, List.mem_map] at hR
  obtain ⟨F, hF, rfl⟩ := hR
  simp only [Finset.mem_toList, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hF
  exact ⟨F, hF.1, hF.2, rfl⟩

/-- A facet contains at most one vertex of each antipodal pair. -/
theorem IsCSPolytope5.facetRows_n_le : ∀ R ∈ facetRows P, 2 * R.n ≤ fvec P 0 := by
  intro R hR
  obtain ⟨F, hF, hd, rfl⟩ := hP.mem_facetRows hR
  refine hP.two_mul_cnt_le hF fun h => ?_
  have := hP.dim_self; rw [← h] at this; omega

end Kalai5
