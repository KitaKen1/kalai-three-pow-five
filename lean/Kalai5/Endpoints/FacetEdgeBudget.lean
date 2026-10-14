import Kalai5.Endpoints.RareRowRidges

namespace Kalai5
open Set
open scoped Classical

def edgeSet (P F : Set E5) : Set (Set E5) :=
  {e | e ∈ faces P ∧ e ⊆ F ∧ dim e = 1}

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.vertex_degree_four {F v : Set E5}
    (hF : F ∈ faces P) (h4 : dim F = 4) (hv : v ∈ vset P F) : 4 ≤ vdeg P F v := by
  obtain ⟨V,hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hvF : v ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ hv.1,hv.2.1⟩
  have h1 := vertex_up_dim_four hFV h4 hvF hv.2.2
  have h2 := vertex_three_r_le hFV h4 hvF hv.2.2
  have h3 := vertex_four_le_r hFV h4 hvF hv.2.2
  have hup : upIn F v 1 = vdeg P F v := by
    unfold upIn vdeg
    congr 1
    ext e
    simp only [Set.mem_ofPred_eq,mem_faces_face_iff hF',← hV]
    tauto
  rw [hup] at h1
  omega

theorem IsCSPolytope5.edge_vertex_card {e : Set E5}
    (he : e ∈ faces P) (h1 : dim e = 1) : (vset P e).ncard = 2 := by
  obtain ⟨V,hV⟩ := hP.polytope
  rw [← cnt_eq_vset,hV]
  exact cnt_zero_of_dim_one (hV ▸ he) h1

/-- At most one edge can have both endpoints in a set of at most two vertices. -/
theorem IsCSPolytope5.edges_on_two_vertices {U : Set (Set E5)}
    (hU : U.Finite) (h2 : U.ncard ≤ 2) :
    {e | e ∈ faces P ∧ dim e = 1 ∧ vset P e ⊆ U}.ncard ≤ 1 := by
  apply (Set.ncard_le_one (hP.faces_finite.subset fun _ h => h.1)).2
  intro e he f hf
  have he2 := hP.edge_vertex_card he.1 he.2.1
  have hf2 := hP.edge_vertex_card hf.1 hf.2.1
  have ee := Set.eq_of_subset_of_ncard_le he.2.2 (by omega) hU
  have ef := Set.eq_of_subset_of_ncard_le hf.2.2 (by omega) hU
  exact hP.eq_of_subset_of_dim_le he.1 hf.1
    (hP.subset_of_vset he.1 hf.1 (by rw [ee,ef])) (by rw [he.2.1,hf.2.1])

theorem IsCSPolytope5.edgeSet_inter_le_one {A B : Set E5}
    (h2 : (vset P A ∩ vset P B).ncard ≤ 2) :
    (edgeSet P A ∩ edgeSet P B).ncard ≤ 1 := by
  have hs : edgeSet P A ∩ edgeSet P B ⊆
      {e | e ∈ faces P ∧ dim e = 1 ∧ vset P e ⊆ vset P A ∩ vset P B} := by
    intro e he
    exact ⟨he.1.1,he.1.2.2,fun v hv => ⟨vset_mono' he.1.2.1 hv,vset_mono' he.2.2.1 hv⟩⟩
  exact (Set.ncard_le_ncard hs (hP.faces_finite.subset fun _ h => h.1)).trans
    (hP.edges_on_two_vertices ((hP.vset_finite A).inter_of_left _) h2)

/-- Two distinct vertices can have at most one common incident edge. -/
theorem IsCSPolytope5.edge_stars_inter_le_one {F v w : Set E5}
    (hv : v ∈ vset P F) (hw : w ∈ vset P F) (hvw : v ≠ w) :
    ({e | e ∈ faces P ∧ v ⊆ e ∧ e ⊆ F ∧ dim e = 1} ∩
      {e | e ∈ faces P ∧ w ⊆ e ∧ e ⊆ F ∧ dim e = 1}).ncard ≤ 1 := by
  have hs : {e | e ∈ faces P ∧ v ⊆ e ∧ e ⊆ F ∧ dim e = 1} ∩
      {e | e ∈ faces P ∧ w ⊆ e ∧ e ⊆ F ∧ dim e = 1} ⊆
      {e | e ∈ faces P ∧ dim e = 1 ∧ vset P e ⊆ ({v,w} : Set (Set E5))} := by
    intro e he
    have hp : ({v,w} : Set (Set E5)) ⊆ vset P e := by
      rintro x (rfl | rfl)
      · exact ⟨hv.1,he.1.2.1,hv.2.2⟩
      · exact ⟨hw.1,he.2.2.1,hw.2.2⟩
    have eqp := Set.eq_of_subset_of_ncard_le hp
      (by rw [hP.edge_vertex_card he.1.1 he.1.2.2.2,Set.ncard_pair hvw]) (hP.vset_finite e)
    exact ⟨he.1.1,he.1.2.2.2,eqp ▸ Set.Subset.rfl⟩
  exact (Set.ncard_le_ncard hs (hP.faces_finite.subset fun _ h => h.1)).trans
    (hP.edges_on_two_vertices (by simp) (by rw [Set.ncard_pair hvw]))

/-- Three six-edge faces meeting pairwise in at most one edge contain
at least fifteen edges. -/
theorem IsCSPolytope5.three_edge_sets_fifteen {A B C : Set E5}
    (ha : cnt P A 1 = 6) (hb : cnt P B 1 = 6) (hc : cnt P C 1 = 6)
    (hab : (vset P A ∩ vset P B).ncard ≤ 2)
    (hac : (vset P A ∩ vset P C).ncard ≤ 2)
    (hbc : (vset P B ∩ vset P C).ncard ≤ 2) :
    15 ≤ (edgeSet P A ∪ edgeSet P B ∪ edgeSet P C).ncard := by
  have h1 := hP.edgeSet_inter_le_one hab
  have h2 := hP.edgeSet_inter_le_one hac
  have h3 := hP.edgeSet_inter_le_one hbc
  have hf (X : Set E5) : (edgeSet P X).Finite := hP.below_finite X 1
  have s1 := Set.ncard_union_add_ncard_inter (edgeSet P A) (edgeSet P B) (hf A) (hf B)
  have s2 := Set.ncard_union_add_ncard_inter (edgeSet P A ∪ edgeSet P B)
    (edgeSet P C) ((hf A).union (hf B)) (hf C)
  have hu := Set.ncard_union_le (edgeSet P A ∩ edgeSet P C) (edgeSet P B ∩ edgeSet P C)
  rw [← Set.union_inter_distrib_right] at hu
  change (edgeSet P A).ncard = 6 at ha
  change (edgeSet P B).ncard = 6 at hb
  change (edgeSet P C).ncard = 6 at hc
  omega

/-- Fifteen edges on a core, and two outside vertices of degree at least
four, force at least 15 + 4 + 4 - 1 = 22 edges. -/
theorem IsCSPolytope5.edges_twenty_two_of_core
    {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    {U D : Set (Set E5)} (hd : D ⊆ edgeSet P F)
    (hdu : ∀ e ∈ D, vset P e ⊆ U) (hc : 15 ≤ D.ncard)
    {v w : Set E5} (hv : v ∈ vset P F) (hw : w ∈ vset P F)
    (hvw : v ≠ w) (hvU : v ∉ U) (hwU : w ∉ U) : 22 ≤ cnt P F 1 := by
  let S : Set (Set E5) := {e | e ∈ faces P ∧ v ⊆ e ∧ e ⊆ F ∧ dim e = 1}
  let T : Set (Set E5) := {e | e ∈ faces P ∧ w ⊆ e ∧ e ⊆ F ∧ dim e = 1}
  have hs : S.Finite := hP.faces_finite.subset fun e he => he.1
  have ht : T.Finite := hP.faces_finite.subset fun e he => he.1
  have hf : (edgeSet P F).Finite := hP.below_finite F 1
  have hdf : D.Finite := hf.subset hd
  have hlS : 4 ≤ S.ncard := hP.vertex_degree_four hF h4 hv
  have hlT : 4 ≤ T.ncard := hP.vertex_degree_four hF h4 hw
  have hi : (S ∩ T).ncard ≤ 1 := hP.edge_stars_inter_le_one hv hw hvw
  have hu := Set.ncard_union_add_ncard_inter S T hs ht
  have hdis : Disjoint D (S ∪ T) := by
    rw [Set.disjoint_left]
    intro e he he'
    rcases he' with hes | het
    · exact hvU (hdu e he ⟨hv.1,hes.2.1,hv.2.2⟩)
    · exact hwU (hdu e he ⟨hw.1,het.2.1,hw.2.2⟩)
  have heq := Set.ncard_union_eq hdis hdf (hs.union ht)
  have hsub : D ∪ (S ∪ T) ⊆ edgeSet P F := by
    rintro e (he | he | he)
    · exact hd he
    · exact ⟨he.1,he.2.2⟩
    · exact ⟨he.1,he.2.2⟩
  have hle := Set.ncard_le_ncard hsub hf
  change (D ∪ (S ∪ T)).ncard ≤ cnt P F 1 at hle
  omega

end Kalai5
