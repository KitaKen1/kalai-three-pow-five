import Kalai5.Endpoints.OnePairMixed

/-!
# Antipodal vertex counting for the mixed J facets

The union of two Y facets has eight vertices and contains no antipodal
pair, once both extra vertices belong to H. It therefore selects one vertex
from every antipodal pair. This gives the four-vertex intersection H ∩ J
without choosing labels for the eight pairs or coordinates for the prism.
-/

namespace Kalai5

open Set
open scoped Classical

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- A proper face cannot contain a vertex and its antipode. -/
lemma IsCSPolytope5.vset_no_antipodes {F v : Set E5}
    (hF : F ∈ faces P) (hproper : F ≠ P) (hv : v ∈ vset P F) : -v ∉ vset P F := by
  intro hn
  obtain ⟨x, hx⟩ := hv.1.1
  exact hproper (hP.eq_of_mem_of_neg_mem hF (hv.2.1 hx) (hn.2.1 (by simpa using hx)))

/-- Any antipode-free set containing half the vertices selects exactly one
vertex from each antipodal pair; the set need not itself be a face. -/
lemma IsCSPolytope5.vertex_cover_of_half_set {A : Set (Set E5)}
    (hA : ∀ v ∈ A, v ∈ faces P ∧ dim v = 0)
    (hno : ∀ v ∈ A, -v ∉ A) (hhalf : 2 * A.ncard = fvec P 0)
    {v : Set E5} (hv : v ∈ faces P) (hv0 : dim v = 0) : v ∈ A ∨ -v ∈ A := by
  have hfin : A.Finite := hP.faces_finite.subset fun v hv => (hA v hv).1
  let B := (fun w : Set E5 => -w) '' A
  have hBfin : B.Finite := hfin.image _
  have hBc : B.ncard = A.ncard := Set.ncard_image_of_injective _ neg_injective
  have hd : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro w hw ⟨u, hu, rfl⟩
    exact hno u hu hw
  have hs : A ∪ B ⊆ {w | w ∈ faces P ∧ dim w = 0} := by
    rintro w (hw | ⟨u, hu, rfl⟩)
    · exact hA w hw
    · exact ⟨neg_mem_faces hP.symm (hA u hu).1, by rw [dim_neg]; exact (hA u hu).2⟩
  have hcard : (A ∪ B).ncard = {w | w ∈ faces P ∧ dim w = 0}.ncard := by
    rw [Set.ncard_union_eq hd hfin hBfin, hBc]
    change A.ncard + A.ncard = fvec P 0
    omega
  have heq := Set.eq_of_subset_of_ncard_le hs hcard.ge (hP.kfaces_finite 0)
  have hm : v ∈ A ∪ B := by rw [heq]; exact ⟨hv, hv0⟩
  rcases hm with hm | ⟨u, hu, rfl⟩
  · exact Or.inl hm
  · exact Or.inr (by simpa using hu)

/-- The union of two facets whose extra vertices lie in the same proper
face contains no antipodal pair. -/
lemma IsCSPolytope5.Y_union_no_antipodes {H Y Z K : Set E5}
    (hH : H ∈ faces P) (hHP : H ≠ P)
    (hY : Y ∈ faces P) (hYP : Y ≠ P) (hZ : Z ∈ faces P) (hZP : Z ≠ P)
    (hKI : K = Y ∩ Z)
    (ha : vset P Y \ vset P K ⊆ vset P H)
    (hb : vset P Z \ vset P K ⊆ vset P H) :
    ∀ v ∈ vset P Y ∪ vset P Z, -v ∉ vset P Y ∪ vset P Z := by
  have hKY : vset P K ⊆ vset P Y := vset_mono' (hKI ▸ inter_subset_left)
  have hKZ : vset P K ⊆ vset P Z := vset_mono' (hKI ▸ inter_subset_right)
  have cross : ∀ v ∈ vset P Y, -v ∉ vset P Z := by
    intro v hv hn
    by_cases hk : v ∈ vset P K
    · exact hP.vset_no_antipodes hZ hZP (hKZ hk) hn
    by_cases hnk : -v ∈ vset P K
    · exact hP.vset_no_antipodes hY hYP hv (hKY hnk)
    exact hP.vset_no_antipodes hH hHP (ha ⟨hv, hk⟩) (hb ⟨hn, hnk⟩)
  intro v hv hn
  rcases hv with hv | hv <;> rcases hn with hn | hn
  · exact hP.vset_no_antipodes hY hYP hv hn
  · exact cross v hv hn
  · exact cross (-v) hn (by simpa using hv)
  · exact hP.vset_no_antipodes hZ hZP hv hn

/-- The mixed J meets H in exactly four vertices. The hypotheses are only
ridge intersections and vertex counts, not a labelled signed configuration. -/
theorem IsCSPolytope5.mixed_J_four_vertices (hv : fvec P 0 = 16)
    {H Y Z K Q R J : Set E5}
    (hH : H ∈ faces P) (hHP : H ≠ P)
    (hY : Y ∈ faces P) (hYP : Y ≠ P) (hY7 : cnt P Y 0 = 7)
    (hZ : Z ∈ faces P) (hZP : Z ≠ P) (hZ7 : cnt P Z 0 = 7)
    (hKI : K = Y ∩ Z) (hK6 : cnt P K 0 = 6)
    (ha : vset P Y \ vset P K ⊆ vset P H)
    (hb : vset P Z \ vset P K ⊆ vset P H)
    (hKH : K ∩ H = Q) (hQ4 : cnt P Q 0 = 4)
    (hQR : vset P Q ∪ vset P R = vset P K) (hR4 : cnt P R 0 = 4)
    (hJ : J ∈ faces P) (hJP : J ≠ P)
    (hYJ5 : cnt P (Y ∩ J) 0 = 5) (hZJ5 : cnt P (Z ∩ J) 0 = 5) (hKJ : K ∩ J = R) :
    cnt P (H ∩ J) 0 = 4 := by
  let U := vset P Y ∪ vset P Z
  let C := U \ vset P H
  let W := vset P (Y ∩ J) ∪ vset P (Z ∩ J)
  have hKU : vset P K ⊆ U := Set.subset_union_of_subset_left
    (vset_mono' (hKI ▸ inter_subset_left)) _
  have hUc : U.ncard = 8 := by
    obtain ⟨hc, -⟩ := hP.cnt_add_le (face_subset hY) (face_subset hZ) hKI.symm
    change cnt P Y 0 + cnt P Z 0 = U.ncard + cnt P K 0 at hc
    omega
  have hUno : ∀ v ∈ U, -v ∉ U := hP.Y_union_no_antipodes hH hHP hY hYP hZ hZP hKI ha hb
  have hUA : ∀ v ∈ U, v ∈ faces P ∧ dim v = 0 := by
    intro v hv
    rcases hv with hv | hv <;> exact ⟨hv.1, hv.2.2⟩
  have hC : C = vset P K \ vset P Q := by
    have hi : vset P K ∩ vset P H = vset P Q := by rw [← vset_inter', hKH]
    rw [← hi]
    ext v
    constructor
    · rintro ⟨hvu, hvh⟩
      have hvk : v ∈ vset P K := by
        by_contra hn
        rcases hvu with h | h
        · exact hvh (ha ⟨h, hn⟩)
        · exact hvh (hb ⟨h, hn⟩)
      exact ⟨hvk, fun h => hvh h.2⟩
    · rintro ⟨hvk, hn⟩
      exact ⟨hKU hvk, fun h => hn ⟨hvk, h⟩⟩
  have hQK : vset P Q ⊆ vset P K := by rw [← hQR]; exact Set.subset_union_left
  have hCc : C.ncard = 2 := by
    rw [hC, Set.ncard_sdiff hQK (hP.vset_finite Q), ← cnt_eq_vset, ← cnt_eq_vset, hK6, hQ4]
  have hCR : C ⊆ vset P R := by
    rw [hC, ← hQR]
    exact fun _ h => h.1.resolve_left h.2
  have hRJ : vset P R ⊆ vset P J := vset_mono' (hKJ ▸ inter_subset_right)
  have hW : W = U ∩ vset P J := by
    ext v
    simp only [W, U, vset_inter', Set.mem_union, Set.mem_inter_iff]
    tauto
  have hCW : C ⊆ W := by
    rw [hW]
    exact fun _ h => ⟨h.1, hRJ (hCR h)⟩
  have hWc : W.ncard = 6 := by
    have hi : (Y ∩ J) ∩ (Z ∩ J) = R := by
      rw [← hKJ, hKI]
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    obtain ⟨hc, -⟩ := hP.cnt_add_le (inter_subset_right : Y ∩ J ⊆ J)
      (inter_subset_right : Z ∩ J ⊆ J) hi
    change cnt P (Y ∩ J) 0 + cnt P (Z ∩ J) 0 = W.ncard + cnt P R 0 at hc
    omega
  have hHJ : vset P (H ∩ J) = W \ C := by
    ext v
    constructor
    · intro hm
      have hvH : v ∈ vset P H := vset_mono' inter_subset_left hm
      have hvJ : v ∈ vset P J := vset_mono' inter_subset_right hm
      have hvU : v ∈ U := by
        rcases hP.vertex_cover_of_half_set hUA hUno (by rw [hUc, hv]) hm.1 hm.2.2 with h | h
        · exact h
        · have hnH := hP.vset_no_antipodes hH hHP hvH
          exact False.elim (hP.vset_no_antipodes hJ hJP hvJ (hRJ (hCR ⟨h, hnH⟩)))
      exact ⟨hW ▸ ⟨hvU, hvJ⟩, fun h => h.2 hvH⟩
    · rintro ⟨hm, hn⟩
      rw [hW] at hm
      have hvH : v ∈ vset P H := by by_contra h; exact hn ⟨hm.1, h⟩
      rw [vset_inter']
      exact ⟨hvH, hm.2⟩
  rw [cnt_eq_vset, hHJ, Set.ncard_sdiff hCW ((hP.vset_finite Y).union (hP.vset_finite Z)).sdiff,
    hWc, hCc]

end Kalai5
