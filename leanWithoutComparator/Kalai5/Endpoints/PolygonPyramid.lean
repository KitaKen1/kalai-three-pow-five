import Kalai5.Endpoints.FullSixRidges

/-! Vertex-set recognition of a pyramid over a polygon, without coordinates. -/
namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.polygon_pyramid_apex {T Q : Set E5}
    (hQT : Q ⊆ T) (hn : cnt P T 0=cnt P Q 0+1) :
    ∃ a, a ∈ vset P T ∧ a ∉ vset P Q ∧ vset P T=insert a (vset P Q) := by
  have hs := vset_mono' (P := P) hQT
  have hc : (vset P T \ vset P Q).ncard=1 := by
    rw [Set.ncard_sdiff hs (hP.vset_finite Q),← cnt_eq_vset,← cnt_eq_vset,hn]
    omega
  obtain ⟨a,ha⟩ := Set.ncard_eq_one.1 hc
  have hm : a ∈ vset P T \ vset P Q := by rw [ha]; exact Set.mem_singleton a
  refine ⟨a,hm.1,hm.2,?_⟩
  ext v
  constructor
  · intro hv
    by_cases hvQ : v ∈ vset P Q
    · exact Or.inr hvQ
    · exact Or.inl (show v=a from Set.mem_singleton_iff.1 (ha ▸ ⟨hv,hvQ⟩))
  · rintro (rfl | hv)
    · exact hm.1
    · exact hs hv

theorem IsCSPolytope5.polygon_pyramid_side {T Q R a : Set E5}
    (hQ : Q ∈ faces P) (hQ2 : dim Q=2)
    (hR : R ∈ faces P) (hRT : R ⊆ T) (hR2 : dim R=2) (hRQ : R≠Q)
    (hvT : vset P T=insert a (vset P Q)) :
    a ∈ vset P R ∧ cnt P R 0=3 ∧ (vset P R ∩ vset P Q).ncard=2 := by
  have hsub : vset P R ⊆ insert a (vset P R ∩ vset P Q) := by
    intro v hv
    have hm : v ∈ insert a (vset P Q) := hvT ▸ vset_mono' hRT hv
    rcases hm with rfl | hm
    · exact Or.inl rfl
    · exact Or.inr ⟨hv,hm⟩
  have hupper := Set.ncard_le_ncard hsub
    (((hP.vset_finite R).inter_of_left (vset P Q)).insert a)
  have hinsert := Set.ncard_insert_le a (vset P R ∩ vset P Q)
  have hcommon := hP.polygon_common_vertices_le_two hR hR2 hQ hQ2 hRQ
  have hlower := hP.three_le_cnt hR hR2
  have hR3 : cnt P R 0=3 := by rw [cnt_eq_vset] at hlower ⊢; omega
  have ha : a ∈ vset P R := by
    by_contra hnot
    have hs : vset P R ⊆ vset P Q := by
      intro v hv
      have hm : v ∈ insert a (vset P Q) := hvT ▸ vset_mono' hRT hv
      exact hm.resolve_left (fun he => hnot (he ▸ hv))
    exact hRQ (hP.eq_of_subset_of_dim_le hR hQ (hP.subset_of_vset hR hQ hs) (by omega))
  refine ⟨ha,hR3,?_⟩
  rw [cnt_eq_vset] at hR3
  omega

/-- A ridge with at most as many vertices as the base meets a polygonal
pyramid ridge in at most a triangle. -/
theorem IsCSPolytope5.polygon_pyramid_inter_small_ridge {C Q T : Set E5}
    (hC : C ∈ faces P) (hC3 : dim C=3)
    (hQ : Q ∈ faces P) (hQC : Q ⊆ C) (hQ2 : dim Q=2)
    (hn : cnt P C 0=cnt P Q 0+1)
    (hT : T ∈ faces P) (hT3 : dim T=3) (hsmall : cnt P T 0 ≤ cnt P Q 0) :
    cnt P (T ∩ C) 0 ≤ 3 := by
  by_cases hnon : (T ∩ C).Nonempty
  · have hI := inter_mem_faces_of_nonempty hT hC hnon
    have hIT := mem_faces_of_subset (face_subset hT) hI inter_subset_left
    have hne : T ∩ C≠T := by
      intro he
      have hTC := hP.eq_of_subset_of_dim_le hT hC
        (by rw [← he]; exact inter_subset_right) (by omega)
      rw [hTC] at hsmall
      omega
    have hdim := dim_lt_of_mem_faces_ne hIT hne
    by_cases hlo : dim (T ∩ C) ≤ 1
    · exact (hP.cnt_le_two_of_dim_le_one hI hlo).trans (by omega)
    · have hI2 : dim (T ∩ C)=2 := by omega
      have hcnt := hP.cnt_zero_lt hI hT inter_subset_left hne
      have hIQ : T ∩ C≠Q := by intro he; rw [he] at hcnt; omega
      obtain ⟨a,_,_,ha⟩ := hP.polygon_pyramid_apex hQC hn
      exact (hP.polygon_pyramid_side hQ hQ2 hI inter_subset_right hI2 hIQ ha).2.1.le
  · have he : vset P (T ∩ C)=∅ := by
      apply Set.eq_empty_of_forall_notMem
      intro v hv
      exact hnon (hv.1.1.mono hv.2.1)
    rw [cnt_eq_vset,he,Set.ncard_empty]
    omega

end Kalai5
