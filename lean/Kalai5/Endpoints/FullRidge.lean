import Kalai5.Rigidity.FaceFacts
import Kalai5.Rigidity.Step
import Kalai5.Euler.Relations
import Kalai5.Polar.Intervals
import Kalai5.Full.Basic
import Kalai5.Faces.Symmetry
import Kalai5.Full.Normals

/-!
# Ridges of full facets at sixteen vertices

At `f₀ = 16` a facet with eight vertices is full.  Every ridge of a full facet `F` lies in exactly
one other facet; that facet is full (at most `|Ful| - 2` of them, distinct ridges giving distinct
facets) or not full.  A facet `X` that is not full meets at most one of `F`, `-F` in a ridge (two
disjoint ridges would give `X` eight vertices).  Hence

  `2 Σ_{F full} r(F) ≤ 2 a (a - 2) + a (h - a)`,  `a` = number of full facets.

(`IsCSPolytope5.full_ridge_count`; `r(F)` is the number of ridges of `P` in `F`.)
-/

namespace Kalai5

open Set

variable {P : Set E5}

/-- Number of facet rows with `n = 8`. -/
def cnt8 (rows : List Row) : ℕ := (rows.filter fun R => R.n = 8).length

/-- Sum of `r` over the facet rows with `n = 8`. -/
def sumR8 (rows : List Row) : ℕ := ((rows.filter fun R => R.n = 8).map Row.r).sum

lemma sumR8_eq_sum (rows : List Row) :
    sumR8 rows = (rows.map fun R => if R.n = 8 then R.r else 0).sum := by
  induction rows with
  | nil => simp [sumR8]
  | cons R rs ih =>
    simp only [sumR8] at ih
    by_cases h : R.n = 8 <;> simp [sumR8, List.filter_cons, h, ih]

section

variable (hP : IsCSPolytope5 P)
include hP

/-- **Two distinct facets containing a 3-face meet exactly in it.** -/
lemma IsCSPolytope5.three_face_eq_inter {F G T : Set E5} (hF : F ∈ faces P) (hF4 : dim F = 4)
    (hG : G ∈ faces P) (hG4 : dim G = 4) (hFG : F ≠ G) (hT : T ∈ faces P) (hT3 : dim T = 3)
    (hTF : T ⊆ F) (hTG : T ⊆ G) : T = F ∩ G := by
  have hI : F ∩ G ∈ faces P :=
    inter_mem_faces_of_nonempty hF hG (hT.1.mono (subset_inter hTF hTG))
  have hIF : F ∩ G ∈ faces F := mem_faces_of_subset (face_subset hF) hI inter_subset_left
  have hIne : F ∩ G ≠ F := by
    intro h
    have hFsub : F ⊆ G := by rw [← h]; exact inter_subset_right
    have hFG' : F ∈ faces G := mem_faces_of_subset (face_subset hG) hF hFsub
    have := dim_lt_of_mem_faces_ne hFG' hFG
    omega
  have hIdim : dim (F ∩ G) < 4 := by have := dim_lt_of_mem_faces_ne hIF hIne; omega
  have hTI : T ∈ faces (F ∩ G) := mem_faces_of_subset (face_subset hI) hT (subset_inter hTF hTG)
  by_contra hne
  have := dim_lt_of_mem_faces_ne hTI hne
  omega

/-- The vertex finset of `P`. -/
lemma IsCSPolytope5.exists_vertFinset :
    ∃ W : Finset E5, P = convexHull ℝ (W : Set E5) ∧ ConvPos W := by
  obtain ⟨V, hV⟩ := hP.polytope
  exact ⟨vertFinset V, by rw [convexHull_vertFinset, hV], convPos_vertFinset V⟩

/-- **A 3-face has at least four vertices.** -/
lemma IsCSPolytope5.four_le_cnt_three {T : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3) :
    4 ≤ cnt P T 0 := by
  classical
  obtain ⟨W, hW, -⟩ := hP.exists_vertFinset
  rw [hW] at hT ⊢
  rw [← fvec_face_eq_cnt hT 0]
  have hTe := face_eq_convexHull_filter hT
  have hne : (W.filter (· ∈ T)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.coe_empty, convexHull_empty] at hTe
    exact hT.1.ne_empty hTe
  have h1 := dim_add_one_le_ncard_extremePoints _ hne
  rw [← hTe, hT3] at h1
  rw [hTe, fvec_zero_eq]
  rw [← hTe]
  exact h1

/-- A full facet misses its antipode. -/
lemma IsCSPolytope5.disjoint_neg_of_full {F : Set E5} (hF : F ∈ faces P) (hne : F ≠ P)
    (hfull : 2 * cnt P F 0 = fvec P 0) : Disjoint F (-F) := by
  obtain ⟨u, -, hFu, -⟩ := hP.exists_full_normal hF hne hfull
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [hFu] at hx
  have hx2 : -x ∈ F := hx'
  rw [hFu] at hx2
  have h1 := hx.2
  have h2 := hx2.2
  rw [map_neg] at h2
  linarith

/-- **Two disjoint 3-faces inside a facet**: the facet has at least eight vertices. -/
lemma IsCSPolytope5.eight_le_cnt_of_disjoint {X T T' : Set E5} (hX : X ∈ faces P)
    (hT : T ∈ faces P) (hT3 : dim T = 3) (hT' : T' ∈ faces P) (hT3' : dim T' = 3)
    (hTX : T ⊆ X) (hTX' : T' ⊆ X) (hdisj : Disjoint T T') : 8 ≤ cnt P X 0 := by
  have h4 := hP.four_le_cnt_three hT hT3
  have h4' := hP.four_le_cnt_three hT' hT3'
  obtain ⟨W, hW, hcp⟩ := hP.exists_vertFinset
  rw [hW] at hX hT hT' h4 h4' ⊢
  rw [cnt_zero_eq_card hcp hT] at h4
  rw [cnt_zero_eq_card hcp hT'] at h4'
  rw [cnt_zero_eq_card hcp hX]
  classical
  have h4c : 4 ≤ (W.filter (· ∈ T)).card := by convert h4 using 2
  have h4c' : 4 ≤ (W.filter (· ∈ T')).card := by convert h4' using 2
  suffices h8 : 8 ≤ (W.filter (· ∈ X)).card by convert h8 using 2
  have hd : Disjoint (W.filter (· ∈ T)) (W.filter (· ∈ T')) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    exact Set.disjoint_left.1 hdisj (Finset.mem_filter.1 hy).2 (Finset.mem_filter.1 hy').2
  have hsub : W.filter (· ∈ T) ∪ W.filter (· ∈ T') ⊆ W.filter (· ∈ X) := by
    intro y hy
    rcases Finset.mem_union.1 hy with hy | hy
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hTX (Finset.mem_filter.1 hy).2⟩
    · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hy).1, hTX' (Finset.mem_filter.1 hy).2⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd] at this
  omega


open Classical in
/-- The 3-faces inside `F`, as a finset count. -/
lemma IsCSPolytope5.cnt_three_eq (F : Set E5) :
    cnt P F 3 = ((hP.kfaces_finite 3).toFinset.filter (· ⊆ F)).card := by
  rw [cnt, ← Set.ncard_coe_finset]
  congr 1
  ext G
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  tauto

/-- **The other facet through a 3-face.** -/
lemma IsCSPolytope5.exists_other_facet {T F : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3)
    (hTF : T ⊆ F) : ∃ G, G ∈ faces P ∧ dim G = 4 ∧ G ≠ F ∧ T ⊆ G := by
  by_contra hno
  push Not at hno
  have h2 := hP.ridge_two hT hT3
  have hsub : {G | G ∈ faces P ∧ T ⊆ G ∧ dim G = 4} ⊆ {F} := by
    intro G hG
    by_contra hne
    exact hno G hG.1 hG.2.2 hne hG.2.1
  have := Set.ncard_le_ncard hsub (Set.finite_singleton F)
  rw [Set.ncard_singleton] at this
  omega

/-- **Ridge count of the full facets at sixteen vertices.** -/
theorem IsCSPolytope5.full_ridge_count (h16 : fvec P 0 = 16) :
    2 * ∑ F ∈ (hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8), cnt P F 3 ≤
      2 * ((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card *
          (((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card - 2) +
        ((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card *
          ((hP.kfaces_finite 4).toFinset.card -
            ((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card) := by
  classical
  set Fs := (hP.kfaces_finite 4).toFinset with hFs
  set Ts := (hP.kfaces_finite 3).toFinset with hTs
  set Ful := Fs.filter (fun F => cnt P F 0 = 8) with hFul
  set NF := Fs.filter (fun F => ¬ cnt P F 0 = 8) with hNF
  have mFs : ∀ {F}, F ∈ Fs ↔ F ∈ faces P ∧ dim F = 4 := fun {F} => by
    rw [hFs, Set.Finite.mem_toFinset]; rfl
  have mTs : ∀ {T}, T ∈ Ts ↔ T ∈ faces P ∧ dim T = 3 := fun {T} => by
    rw [hTs, Set.Finite.mem_toFinset]; rfl
  have mFul : ∀ {F}, F ∈ Ful ↔ (F ∈ faces P ∧ dim F = 4) ∧ cnt P F 0 = 8 := fun {F} => by
    rw [hFul, Finset.mem_filter, mFs]
  -- facts about full facets
  have fne : ∀ {F}, F ∈ faces P → dim F = 4 → F ≠ P := fun hF hd h => by
    have := hP.dim_self; rw [← h, hd] at this; omega
  have fdisj : ∀ {F}, F ∈ Ful → Disjoint F (-F) := fun hF => by
    obtain ⟨⟨hF, hd⟩, h8⟩ := mFul.1 hF
    exact hP.disjoint_neg_of_full hF (fne hF hd) (by rw [h8, h16])
  have fneg : ∀ {F}, F ∈ Ful → -F ∈ Ful := fun hF => by
    obtain ⟨⟨hF, hd⟩, h8⟩ := mFul.1 hF
    exact mFul.2 ⟨⟨neg_mem_faces hP.symm hF, by rw [dim_neg]; exact hd⟩, by rw [hP.cnt_neg]; exact h8⟩
  have fneF : ∀ {F}, F ∈ Ful → -F ≠ F := fun hF h => by
    obtain ⟨⟨hF', -⟩, -⟩ := mFul.1 hF
    obtain ⟨x, hx⟩ := hF'.1
    exact Set.disjoint_left.1 (fdisj hF) hx (by rw [h]; exact hx)
  have cle : ∀ {X}, X ∈ Fs → cnt P X 0 ≤ 8 := fun hX => by
    obtain ⟨hX, hd⟩ := mFs.1 hX
    have := hP.two_mul_cnt_le hX (fne hX hd)
    omega
  -- relation: `F` and `X` meet in a 3-face
  set rel : Set E5 → Set E5 → Prop := fun F X => ∃ T ∈ Ts, T ⊆ F ∧ T ⊆ X with hrel
  -- (1) the ridges of a full facet
  have step1 : ∀ F ∈ Ful, cnt P F 3 ≤ (Ful.card - 2) + (NF.filter (rel F)).card := by
    intro F hF
    obtain ⟨⟨hFf, hFd⟩, -⟩ := mFul.1 hF
    rw [hP.cnt_three_eq F, ← hTs]
    set A := (Ful.filter (fun G => G ≠ F ∧ G ≠ -F)).image (fun G => F ∩ G) with hA
    set B := (NF.filter (rel F)).image (fun X => F ∩ X) with hB
    have hsub : Ts.filter (· ⊆ F) ⊆ A ∪ B := by
      intro T hT
      rw [Finset.mem_filter, mTs] at hT
      obtain ⟨⟨hTf, hT3⟩, hTF⟩ := hT
      obtain ⟨G, hGf, hGd, hGF, hTG⟩ := hP.exists_other_facet hTf hT3 hTF
      have hTeq : T = F ∩ G := hP.three_face_eq_inter hFf hFd hGf hGd (Ne.symm hGF) hTf hT3 hTF hTG
      by_cases hGful : cnt P G 0 = 8
      · refine Finset.mem_union_left _ (Finset.mem_image.2 ⟨G, ?_, hTeq.symm⟩)
        refine Finset.mem_filter.2 ⟨mFul.2 ⟨⟨hGf, hGd⟩, hGful⟩, hGF, fun h => ?_⟩
        obtain ⟨x, hx⟩ := hTf.1
        exact Set.disjoint_left.1 (fdisj hF) (hTF hx) (by rw [← h]; exact hTG hx)
      · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨G, ?_, hTeq.symm⟩)
        refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨mFs.2 ⟨hGf, hGd⟩, hGful⟩, ?_⟩
        exact ⟨T, mTs.2 ⟨hTf, hT3⟩, hTF, hTG⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le A B
    have h3 : A.card ≤ Ful.card - 2 := by
      refine (Finset.card_image_le).trans ?_
      have hs : Ful.filter (fun G => G ≠ F ∧ G ≠ -F) ⊆ (Ful.erase F).erase (-F) := by
        intro G hG
        rw [Finset.mem_filter] at hG
        exact Finset.mem_erase.2 ⟨hG.2.2, Finset.mem_erase.2 ⟨hG.2.1, hG.1⟩⟩
      refine (Finset.card_le_card hs).trans ?_
      rw [Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨fneF hF, fneg hF⟩),
        Finset.card_erase_of_mem hF]
      omega
    have h4 : B.card ≤ (NF.filter (rel F)).card := Finset.card_image_le
    have key : (Ts.filter (· ⊆ F)).card ≤ (Ful.card - 2) + (NF.filter (rel F)).card := by omega
    convert key using 3
  -- (2) a non-full facet meets at most half of the full facets in a 3-face
  have step2 : ∀ X ∈ NF, 2 * (Ful.filter (fun F => rel F X)).card ≤ Ful.card := by
    intro X hX
    rw [hNF, Finset.mem_filter] at hX
    obtain ⟨hXfs, hX8⟩ := hX
    obtain ⟨hXf, -⟩ := mFs.1 hXfs
    set S := Ful.filter (fun F => rel F X) with hS
    have hdisj : Disjoint S (S.image (fun F => -F)) := by
      rw [Finset.disjoint_left]
      intro F hF hF'
      obtain ⟨G, hG, hGF⟩ := Finset.mem_image.1 hF'
      rw [hS, Finset.mem_filter] at hF hG
      obtain ⟨hFful, T, hT, hTF, hTX⟩ := hF
      obtain ⟨-, T', hT', hTG, hTX'⟩ := hG
      rw [mTs] at hT hT'
      have hTG' : T' ⊆ -F := by rw [← hGF, neg_neg]; exact hTG
      have hd : Disjoint T T' := Set.disjoint_of_subset hTF hTG' (fdisj hFful)
      have := hP.eight_le_cnt_of_disjoint hXf hT.1 hT.2 hT'.1 hT'.2 hTX hTX' hd
      have := cle hXfs
      omega
    have hsub : S ∪ S.image (fun F => -F) ⊆ Ful := by
      intro F hF
      rcases Finset.mem_union.1 hF with hF | hF
      · exact (Finset.mem_filter.1 hF).1
      · obtain ⟨G, hG, rfl⟩ := Finset.mem_image.1 hF
        exact fneg (Finset.mem_filter.1 hG).1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ neg_injective] at hc
    omega
  -- (3) assemble
  have hsum1 : ∑ F ∈ Ful, cnt P F 3 ≤ ∑ F ∈ Ful, ((Ful.card - 2) + (NF.filter (rel F)).card) :=
    Finset.sum_le_sum step1
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul] at hsum1
  have hswap : ∑ F ∈ Ful, (NF.filter (rel F)).card = ∑ X ∈ NF, (Ful.filter (fun F => rel F X)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hsum2 : 2 * ∑ X ∈ NF, (Ful.filter (fun F => rel F X)).card ≤ ∑ X ∈ NF, Ful.card := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum step2
  rw [Finset.sum_const, smul_eq_mul] at hsum2
  have hNFc : NF.card = Fs.card - Ful.card := by
    have := Finset.card_filter_add_card_filter_not (s := Fs) (p := fun F => cnt P F 0 = 8)
    rw [← hFul, ← hNF] at this
    omega
  rw [hswap] at hsum1
  rw [hNFc] at hsum2
  nlinarith [hsum1, hsum2]



/-- **The ridge count in rows**: `2 Σ_{n = 8} r ≤ 2a(a - 2) + a(h - a)`, `a = #(n = 8)`. -/
theorem IsCSPolytope5.full_ridge_rows (h16 : fvec P 0 = 16) :
    2 * sumR8 (facetRows P) ≤ 2 * cnt8 (facetRows P) * (cnt8 (facetRows P) - 2) +
      cnt8 (facetRows P) * (fvec P 4 - cnt8 (facetRows P)) := by
  classical
  have h := hP.full_ridge_count h16
  have hs : sumR8 (facetRows P) =
      ∑ F ∈ (hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8), cnt P F 3 := by
    rw [sumR8_eq_sum, hP.facetRows_sum (fun R => if R.n = 8 then R.r else 0), Finset.sum_filter]
    rfl
  have hc : cnt8 (facetRows P) = ((hP.kfaces_finite 4).toFinset.filter (fun F => cnt P F 0 = 8)).card := by
    rw [cnt8, length_filter_eq_sum, hP.facetRows_sum (fun R => if R.n = 8 then 1 else 0),
      Finset.card_filter]
    rfl
  have hf : fvec P 4 = (hP.kfaces_finite 4).toFinset.card := by
    rw [fvec, ← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  rw [hs, hc, hf]
  exact h

end

end Kalai5
