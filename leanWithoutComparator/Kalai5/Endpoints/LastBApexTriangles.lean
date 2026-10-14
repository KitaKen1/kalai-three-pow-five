import Kalai5.Endpoints.LastBPrismShell

namespace Kalai5
open Set
open scoped Classical
variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A pyramid on a prism quadrilateral meets the bipyramid in a triangle:
the common base edge together with its apex. -/
theorem IsCSPolytope5.bipyr_prism_pyramid_triangle {T R Q Y a : Set E5}
    (hT : T ∈ faces P) (hT3 : dim T = 3) (ht : tri3 P T = (5,9,6))
    (hR : R ∈ faces P) (hR3 : dim R = 3) (hr : tri3 P R = (6,9,5))
    (hA : T ∩ R ∈ faces P) (hA2 : dim (T ∩ R) = 2) (hA3 : cnt P (T ∩ R) 0 = 3)
    (hQ : Q ∈ faces P) (hQR : Q ⊆ R) (hQ2 : dim Q = 2) (hQ4 : cnt P Q 0 = 4)
    (hY : Y ∈ faces P) (hY3 : dim Y = 3) (hy : tri3 P Y = (5,8,5))
    (haT : a ∈ vset P T) (haR : a ∉ vset P R)
    (hvs : vset P Y = insert a (vset P Q)) :
    T ∩ Y ∈ faces P ∧ dim (T ∩ Y) = 2 ∧ cnt P (T ∩ Y) 0 = 3 ∧
      vset P (T ∩ Y) = insert a (vset P (T ∩ R) ∩ vset P Q) := by
  have hverts : vset P (T ∩ Y) = insert a (vset P (T ∩ R) ∩ vset P Q) := by
    rw [vset_inter',hvs,vset_inter']
    ext v
    simp only [Set.mem_inter_iff,Set.mem_insert_iff]
    constructor
    · rintro ⟨hvT,rfl | hvQ⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hvT,vset_mono' hQR hvQ⟩,hvQ⟩
    · rintro (rfl | ⟨⟨hvT,_⟩,hvQ⟩)
      · exact ⟨haT,Or.inl rfl⟩
      · exact ⟨hvT,Or.inr hvQ⟩
  have hc := hP.prism_triangle_quad_inter_two hR hR3 hr hA inter_subset_right hA2 hA3 hQ hQR hQ2 hQ4
  have hI3 : cnt P (T ∩ Y) 0 = 3 := by
    rw [cnt_eq_vset,hverts,Set.ncard_insert_of_notMem
      (fun h => haR (vset_mono' inter_subset_right h.1))
      ((hP.vset_finite (T ∩ R)).inter_of_left _),← vset_inter',← cnt_eq_vset,hc]
  have haY : a ∈ vset P Y := hvs ▸ Or.inl rfl
  have hI := inter_mem_faces_of_nonempty hT hY
    (haT.1.1.mono (Set.subset_inter haT.2.1 haY.2.1))
  have hTY : T ≠ Y := by
    intro he
    have hte : cnt P T 1 = 9 := congrArg (fun t => t.2.1) ht
    have hye : cnt P Y 1 = 8 := congrArg (fun t => t.2.1) hy
    rw [he] at hte
    omega
  have hproper : T ∩ Y ≠ T := by
    intro he
    exact hTY (hP.eq_of_subset_of_dim_le hT hY
      (by rw [← he]; exact inter_subset_right) (by omega))
  have hd := dim_lt_of_mem_faces_ne
    (mem_faces_of_subset (face_subset hT) hI inter_subset_left) hproper
  have hI2 : dim (T ∩ Y) = 2 := by
    by_contra hn
    have := hP.cnt_le_two_of_dim_le_one hI (by omega)
    omega
  exact ⟨hI,hI2,hI3,hverts⟩

end Kalai5
