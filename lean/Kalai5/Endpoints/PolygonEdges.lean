import Kalai5.Endpoints.PolygonPyramid

/-! Three sides of a triangle cannot occur as edges of a quadrilateral. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.vertex_in_polygon_edges {Q v : Set E5}
    (hQ : Q ∈ faces P) (h2 : dim Q=2)
    (hv : v ∈ faces P) (hvQ : v ⊆ Q) (hv0 : dim v=0) :
    {E | E ∈ faces P ∧ v ⊆ E ∧ E ⊆ Q ∧ dim E=1}.ncard=2 := by
  obtain ⟨V,hV⟩ := hP.polytope
  have hQ' : Q ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hQ
  have hQV : Q=convexHull ℝ ((V.filter (· ∈ Q) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hQ'
  have hvQ' : v ∈ faces Q := (mem_faces_face_iff hQ').2 ⟨hV ▸ hv,hvQ⟩
  have key := face_up_codim_two hQV hvQ' (by rw [hv0,h2])
  rw [hv0] at key
  refine Eq.trans ?_ key
  unfold upIn
  congr 1
  ext E
  simp only [Set.mem_ofPred_eq,mem_faces_face_iff hQ',← hV]
  tauto

theorem IsCSPolytope5.quadrilateral_no_triangle_edges {Q A B C a b c : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q=2) (hQ4 : cnt P Q 0=4)
    (hA : A ∈ faces P) (hAQ : A ⊆ Q) (hA1 : dim A=1)
    (hB : B ∈ faces P) (hBQ : B ⊆ Q) (hB1 : dim B=1)
    (hC : C ∈ faces P) (hCQ : C ⊆ Q) (hC1 : dim C=1)
    (hAB : A≠B) (hAC : A≠C) (hBC : B≠C)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (vA : vset P A={a,b}) (vB : vset P B={a,c}) (vC : vset P C={b,c}) : False := by
  have haA : a ∈ vset P A := by rw [vA]; simp
  have hbA : b ∈ vset P A := by rw [vA]; simp
  have haB : a ∈ vset P B := by rw [vB]; simp
  have hcB : c ∈ vset P B := by rw [vB]; simp
  have hbC : b ∈ vset P C := by rw [vC]; simp
  have hcC : c ∈ vset P C := by rw [vC]; simp
  let U : Set (Set E5) := {a,b,c}
  have hUfin : U.Finite := by simp [U]
  have hUcard : U.ncard=3 := Set.ncard_eq_three.2 ⟨a,b,c,hab,hac,hbc,rfl⟩
  have hUQ : U ⊆ vset P Q := by
    rintro v (rfl | rfl | rfl)
    · exact vset_mono' hAQ haA
    · exact vset_mono' hAQ hbA
    · exact vset_mono' hBQ hcB
  have hdiff : (vset P Q \ U).ncard=1 := by
    rw [Set.ncard_sdiff hUQ hUfin,← cnt_eq_vset,hQ4,hUcard]
  obtain ⟨z,hz⟩ := Set.nonempty_of_ncard_ne_zero (show (vset P Q \ U).ncard≠0 by omega)
  have hze := hP.vertex_in_polygon_edges hQ hQ2 hz.1.1 hz.1.2.1 hz.1.2.2
  obtain ⟨E,hE,hzE,hEQ,hE1⟩ := Set.nonempty_of_ncard_ne_zero
    (show {E | E ∈ faces P ∧ z ⊆ E ∧ E ⊆ Q ∧ dim E=1}.ncard≠0 by omega)
  have hza : E≠A := by
    intro he
    have hm : z ∈ vset P A := he ▸ ⟨hz.1.1,hzE,hz.1.2.2⟩
    rw [vA] at hm
    exact hz.2 (by rcases hm with h | h <;> simp_all [U])
  have hzb : E≠B := by
    intro he
    have hm : z ∈ vset P B := he ▸ ⟨hz.1.1,hzE,hz.1.2.2⟩
    rw [vB] at hm
    exact hz.2 (by rcases hm with h | h <;> simp_all [U])
  have hzc : E≠C := by
    intro he
    have hm : z ∈ vset P C := he ▸ ⟨hz.1.1,hzE,hz.1.2.2⟩
    rw [vC] at hm
    exact hz.2 (by rcases hm with h | h <;> simp_all [U])
  have exhaust (v R S : Set E5) (hv : v ∈ vset P Q)
      (hR : R ∈ faces P) (hRQ : R ⊆ Q) (hR1 : dim R=1)
      (hS : S ∈ faces P) (hSQ : S ⊆ Q) (hS1 : dim S=1)
      (hRS : R≠S) (hvR : v ⊆ R) (hvS : v ⊆ S) (hvE : v ⊆ E) : E=R ∨ E=S := by
    have htwo := hP.vertex_in_polygon_edges hQ hQ2 hv.1 hv.2.1 hv.2.2
    have heq : ({R,S} : Set (Set E5))=
        {H | H ∈ faces P ∧ v ⊆ H ∧ H ⊆ Q ∧ dim H=1} :=
      Set.eq_of_subset_of_ncard_le
        (by rintro H (rfl | rfl)
            · exact ⟨hR,hvR,hRQ,hR1⟩
            · exact ⟨hS,hvS,hSQ,hS1⟩)
        (by rw [htwo,Set.ncard_pair hRS])
        (hP.faces_finite.subset fun H hH => hH.1)
    have hm : E ∈ ({R,S} : Set (Set E5)) := by rw [heq]; exact ⟨hE,hvE,hEQ,hE1⟩
    exact hm
  have hsub : vset P E ⊆ vset P Q \ U := by
    intro v hv
    refine ⟨vset_mono' hEQ hv,?_⟩
    intro hm
    rcases hm with he | he | he
    · subst v
      exact (exhaust a A B (vset_mono' hAQ haA) hA hAQ hA1 hB hBQ hB1 hAB
        haA.2.1 haB.2.1 hv.2.1).elim hza hzb
    · subst v
      exact (exhaust b A C (vset_mono' hAQ hbA) hA hAQ hA1 hC hCQ hC1 hAC
        hbA.2.1 hbC.2.1 hv.2.1).elim hza hzc
    · subst v
      exact (exhaust c B C (vset_mono' hBQ hcB) hB hBQ hB1 hC hCQ hC1 hBC
        hcB.2.1 hcC.2.1 hv.2.1).elim hzb hzc
  have hle := Set.ncard_le_ncard hsub (hP.vset_finite Q).sdiff
  obtain ⟨V,hV⟩ := hP.polytope
  have he2 : cnt P E 0=2 := by
    rw [hV]
    exact cnt_zero_of_dim_one (hV ▸ hE) hE1
  rw [← cnt_eq_vset,he2,hdiff] at hle
  omega

/-- A proper intersection containing two different polygon vertices is their edge. -/
theorem IsCSPolytope5.polygon_inter_edge {Q R a b : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q=2) (hR : R ∈ faces P)
    (hnot : ¬ Q ⊆ R) (hab : a≠b)
    (ha : a ∈ vset P (Q ∩ R)) (hb : b ∈ vset P (Q ∩ R)) :
    Q ∩ R ∈ faces P ∧ dim (Q ∩ R)=1 ∧ vset P (Q ∩ R)={a,b} := by
  have hI := inter_mem_faces_of_nonempty hQ hR (ha.1.1.mono ha.2.1)
  have hIQ := mem_faces_of_subset (face_subset hQ) hI inter_subset_left
  have hne : Q ∩ R≠Q := fun he => hnot (he ▸ inter_subset_right)
  have hd := dim_lt_of_mem_faces_ne hIQ hne
  have hle := hP.cnt_le_two_of_dim_le_one hI (by omega)
  have hp : ({a,b} : Set (Set E5)) ⊆ vset P (Q ∩ R) := by
    rintro v (rfl | rfl)
    · exact ha
    · exact hb
  have heq : ({a,b} : Set (Set E5))=vset P (Q ∩ R) :=
    Set.eq_of_subset_of_ncard_le hp (by rw [Set.ncard_pair hab,← cnt_eq_vset]; exact hle)
      (hP.vset_finite (Q ∩ R))
  have h1 : dim (Q ∩ R)=1 := by
    by_contra hn
    have hd0 : dim (Q ∩ R)=0 := by omega
    have hA := hP.eq_of_subset_of_dim_le ha.1 hI ha.2.1 (by rw [ha.2.2,hd0])
    have hB := hP.eq_of_subset_of_dim_le hb.1 hI hb.2.1 (by rw [hb.2.2,hd0])
    exact hab (hA.trans hB.symm)
  exact ⟨hI,h1,heq.symm⟩

end Kalai5
