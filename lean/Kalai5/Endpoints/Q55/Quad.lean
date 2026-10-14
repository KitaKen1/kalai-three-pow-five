import Kalai5.Endpoints.Q55.Core

/-!
# The (5,5)-quadrilateral inequality at one quadrilateral

For a quadrilateral `Q` and a facet `H ⊇ Q`, `non5 P H Q` is the set of 3-faces of `H` through `Q`
whose number of vertices is not five; `H` is of type `(5,5)` at `Q` when it is empty.

At sixteen vertices, if `Q` lies in exactly three facets then every facet through `Q` has at most
one such 3-face (`IsCSPolytope5.non5_le_one`: two of them would have at least six vertices each,
`|R| + |S| ≤ |H| + 4 ≤ 12` forces a full cover, and `four_le_up_of_cover` gives a fourth facet), and
by parity some facet is of type `(5,5)` (`IsCSPolytope5.exists_five_five`).  Hence

  `Σ_{H ⊇ Q} (if (5,5) then -2 else 1) ≤ 4 (ℓ(Q) - 3)`          (`IsCSPolytope5.quad55_ineq`).
-/

namespace Kalai5

open Set

open scoped Classical

/-- The 3-faces of `H` through `Q` whose number of vertices is not five. -/
def non5 (P H Q : Set E5) : Set (Set E5) :=
  {T | T ∈ faces P ∧ T ⊆ H ∧ dim T = 3 ∧ Q ⊆ T ∧ cnt P T 0 ≠ 5}

/-- The vertex faces of `P` inside `X`. -/
def vset (P X : Set E5) : Set (Set E5) := {v | v ∈ faces P ∧ v ⊆ X ∧ dim v = 0}

lemma cnt_eq_vset (P X : Set E5) : cnt P X 0 = (vset P X).ncard := rfl

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

lemma IsCSPolytope5.non5_finite (H Q : Set E5) : (non5 P H Q).Finite :=
  hP.faces_finite.subset fun T hT => hT.1

/-- A 3-face through a quadrilateral has at least five vertices. -/
lemma IsCSPolytope5.five_le_of_quad {W : Finset E5} (hPW : P = convexHull ℝ (W : Set E5))
    (hcp : ConvPos W) {T Q : Set E5} (hT : T ∈ faces P) (hT3 : dim T = 3) (hQ : Q ∈ faces P)
    (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4) (hQT : Q ⊆ T) : 5 ≤ cnt P T 0 := by
  have h4 := hP.four_le_cnt_three hT hT3
  by_contra hlt
  have hT4 : cnt P T 0 = 4 := by omega
  have hcT := hT; have hcQ := hQ
  rw [hPW] at hcT hcQ
  have eT := cnt_zero_eq_card hcp hcT
  have eQ := cnt_zero_eq_card hcp hcQ
  rw [← hPW] at eT eQ
  have hsub : W.filter (· ∈ Q) ⊆ W.filter (· ∈ T) := by
    intro w hw
    rw [Finset.mem_filter] at hw ⊢
    exact ⟨hw.1, hQT hw.2⟩
  have heq : W.filter (· ∈ Q) = W.filter (· ∈ T) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [← eT, ← eQ, hT4, h4Q])
  have hTQ : T = Q := by
    rw [face_eq_convexHull_filter hcT, face_eq_convexHull_filter hcQ, heq]
  rw [hTQ, h2] at hT3
  omega

lemma IsCSPolytope5.vset_finite (X : Set E5) : (vset P X).Finite :=
  hP.faces_finite.subset fun v hv => hv.1

/-- **Vertex count of two 3-faces through `Q`**: `|R| + |S| ≤ |H| + |Q|`, with equality
exactly when `R ∪ S` contains every vertex of `H`. -/
lemma IsCSPolytope5.cnt_add_le {H Q R S : Set E5} (hRH : R ⊆ H) (hSH : S ⊆ H) (hRS : R ∩ S = Q) :
    cnt P R 0 + cnt P S 0 = (vset P R ∪ vset P S).ncard + cnt P Q 0 ∧
      vset P R ∪ vset P S ⊆ vset P H := by
  have hinter : vset P R ∩ vset P S = vset P Q := by
    ext v
    simp only [vset, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hv, hvR, hd⟩, -, hvS, -⟩
      exact ⟨hv, by rw [← hRS]; exact subset_inter hvR hvS, hd⟩
    · rintro ⟨hv, hvQ, hd⟩
      rw [← hRS] at hvQ
      exact ⟨⟨hv, hvQ.trans inter_subset_left, hd⟩, hv, hvQ.trans inter_subset_right, hd⟩
  have h1 := Set.ncard_union_add_ncard_inter (vset P R) (vset P S) (hP.vset_finite R)
    (hP.vset_finite S)
  rw [hinter] at h1
  refine ⟨by rw [cnt_eq_vset, cnt_eq_vset, cnt_eq_vset]; omega, ?_⟩
  rintro v (⟨hv, hvR, hd⟩ | ⟨hv, hvS, hd⟩)
  · exact ⟨hv, hvR.trans hRH, hd⟩
  · exact ⟨hv, hvS.trans hSH, hd⟩

/-- The two 3-faces of a facet through a 2-face, as named faces. -/
lemma IsCSPolytope5.exists_two_three {H Q : Set E5} (hH : H ∈ faces P) (hH4 : dim H = 4)
    (hQ : Q ∈ faces P) (hQH : Q ⊆ H) (h2 : dim Q = 2) :
    ∃ R S, R ∈ faces P ∧ dim R = 3 ∧ R ⊆ H ∧ Q ⊆ R ∧ S ∈ faces P ∧ dim S = 3 ∧ S ⊆ H ∧ Q ⊆ S ∧
      R ≠ S ∧ ∀ T, T ∈ faces P → T ⊆ H → dim T = 3 → Q ⊆ T → T = R ∨ T = S := by
  have hcnt := hP.card_three_through hH hH4 hQ hQH h2
  obtain ⟨R, S, hRS, heq⟩ := Finset.card_eq_two.1 hcnt
  have hR : R ∈ (hP.below_finite H 3).toFinset.filter fun T => Q ⊆ T := by
    rw [heq]; exact Finset.mem_insert_self _ _
  have hS : S ∈ (hP.below_finite H 3).toFinset.filter fun T => Q ⊆ T := by
    rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hR hS
  refine ⟨R, S, hR.1.1, hR.1.2.2, hR.1.2.1, hR.2, hS.1.1, hS.1.2.2, hS.1.2.1, hS.2, hRS,
    fun T hT hTH hT3 hQT => ?_⟩
  have hmem : T ∈ (hP.below_finite H 3).toFinset.filter fun T => Q ⊆ T := by
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨hT, hTH, hT3⟩, hQT⟩
  rw [heq, Finset.mem_insert, Finset.mem_singleton] at hmem
  exact hmem

/-- **At most one non-five 3-face** through `Q` in each facet when `Q` lies in exactly three
facets (sixteen vertices). -/
lemma IsCSPolytope5.non5_le_one (h16 : fvec P 0 = 16) {H Q : Set E5} (hH : H ∈ faces P)
    (hH4 : dim H = 4) (hQ : Q ∈ faces P) (hQH : Q ⊆ H) (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4)
    (hℓ : {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard = 3) :
    (non5 P H Q).ncard ≤ 1 := by
  obtain ⟨W, hPW, hcp⟩ := hP.exists_vertFinset
  obtain ⟨R, S, hR, hR3, hRH, hQR, hS, hS3, hSH, hQS, hRS, hall⟩ :=
    hP.exists_two_three hH hH4 hQ hQH h2
  have hsub : non5 P H Q ⊆ {R, S} := fun T hT => hall T hT.1 hT.2.1 hT.2.2.1 hT.2.2.2.1
  by_contra hgt
  push Not at hgt
  have h2le := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair hRS] at h2le
  have heq : non5 P H Q = {R, S} :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [Set.ncard_pair hRS]; omega) (Set.toFinite _)
  have hRn : R ∈ non5 P H Q := by rw [heq]; exact Or.inl rfl
  have hSn : S ∈ non5 P H Q := by rw [heq]; exact Or.inr rfl
  have hR5 := hP.five_le_of_quad hPW hcp hR hR3 hQ h2 h4Q hQR
  have hS5 := hP.five_le_of_quad hPW hcp hS hS3 hQ h2 h4Q hQS
  have hR6 : 6 ≤ cnt P R 0 := by have := hRn.2.2.2.2; omega
  have hS6 : 6 ≤ cnt P S 0 := by have := hSn.2.2.2.2; omega
  have hinter := hP.inter_three_eq hQ h2 hR hR3 hS hS3 hRS hQR hQS
  obtain ⟨hadd, hsubH⟩ := hP.cnt_add_le hRH hSH hinter
  have hHP : H ≠ P := hP.ne_of_dim_ne' (by rw [hH4]; norm_num)
  have hH8 := hP.two_mul_cnt_le hH hHP
  rw [h16] at hH8
  have hU8 := Set.ncard_le_ncard hsubH (hP.vset_finite H)
  rw [← cnt_eq_vset] at hU8
  have hfull : 2 * cnt P H 0 = fvec P 0 := by omega
  -- the cover
  have hU : vset P R ∪ vset P S = vset P H :=
    Set.eq_of_subset_of_ncard_le hsubH (by rw [← cnt_eq_vset]; omega) (hP.vset_finite H)
  have hcov : ∀ w ∈ W, w ∈ H → w ∈ R ∨ w ∈ S := by
    intro w hw hwH
    have hext : w ∈ (convexHull ℝ (W : Set E5)).extremePoints ℝ := hcp w hw
    have hface : ({w} : Set E5) ∈ faces P := by
      rw [hPW]; exact singleton_mem_faces_of_extreme hext
    have hmem : ({w} : Set E5) ∈ vset P H := ⟨hface, by simpa using hwH, dim_singleton w⟩
    rw [← hU] at hmem
    rcases hmem with ⟨-, h, -⟩ | ⟨-, h, -⟩
    · exact Or.inl (by simpa using h)
    · exact Or.inr (by simpa using h)
  have h4 := hP.four_le_up_of_cover hPW hcp hH hH4 hfull hQ h2 hR hR3 hS hS3 hRS hQR hQS hRH hSH
    hcov
  omega

/-- **Parity**: the pairs (facet `H ⊇ Q`, non-five 3-face of `H` through `Q`) number twice the
non-five 3-faces through `Q`. -/
lemma IsCSPolytope5.sum_non5_eq_two {Q : Set E5} (hQ : Q ∈ faces P) :
    ∑ H ∈ (hP.above_finite Q 4).toFinset, (non5 P H Q).ncard =
      2 * ((hP.above_finite Q 3).toFinset.filter fun T => cnt P T 0 ≠ 5).card := by
  have hrw : ∀ H ∈ (hP.above_finite Q 4).toFinset, (non5 P H Q).ncard =
      ((hP.below_finite H 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 ≠ 5).card := by
    intro H _
    rw [← Set.ncard_coe_finset]
    congr 1
    ext T
    simp only [non5, Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    tauto
  rw [Finset.sum_congr rfl hrw]
  simp only [Finset.card_eq_sum_ones]
  rw [Finset.sum_comm' (t' := (hP.above_finite Q 3).toFinset.filter fun T => cnt P T 0 ≠ 5)
    (s' := fun T => (hP.above_finite T 4).toFinset)]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hT
    rw [← Finset.card_eq_sum_ones, ← Set.ncard_eq_toFinset_card _ (hP.above_finite T 4),
      hP.ridge_two hT.1.1 hT.1.2.2, mul_one]
  · intro H T
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hH, hQH, hH4⟩, ⟨hT, hTH, hT3⟩, hQT, h5⟩
      exact ⟨⟨hH, hTH, hH4⟩, ⟨hT, hQT, hT3⟩, h5⟩
    · rintro ⟨⟨hH, hTH, hH4⟩, ⟨hT, hQT, hT3⟩, h5⟩
      exact ⟨⟨hH, hQT.trans hTH, hH4⟩, ⟨hT, hTH, hT3⟩, hQT, h5⟩

/-- **Some facet through `Q` is of type `(5,5)`** when `Q` lies in exactly three facets. -/
lemma IsCSPolytope5.exists_five_five (h16 : fvec P 0 = 16) {Q : Set E5} (hQ : Q ∈ faces P)
    (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4)
    (hℓ : {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard = 3) :
    ∃ H ∈ (hP.above_finite Q 4).toFinset, non5 P H Q = ∅ := by
  by_contra hno
  push Not at hno
  have hone : ∀ H ∈ (hP.above_finite Q 4).toFinset, (non5 P H Q).ncard = 1 := by
    intro H hH
    have hH' := hH
    rw [Set.Finite.mem_toFinset] at hH'
    have hle := hP.non5_le_one h16 hH'.1 hH'.2.2 hQ hH'.2.1 h2 h4Q hℓ
    have hpos : 0 < (non5 P H Q).ncard :=
      (Set.ncard_pos (hP.non5_finite H Q)).2 (hno H hH)
    omega
  have hpar := hP.sum_non5_eq_two hQ
  rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one,
    ← Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4), hℓ] at hpar
  omega

/-- **The inequality at one quadrilateral** (sixteen vertices). -/
lemma IsCSPolytope5.quad55_ineq (h16 : fvec P 0 = 16) {Q : Set E5} (hQ : Q ∈ faces P)
    (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4) :
    ∑ H ∈ (hP.above_finite Q 4).toFinset, (if non5 P H Q = ∅ then (-2 : ℤ) else 1) ≤
      4 * (((hP.above_finite Q 4).toFinset.card : ℤ) - 3) := by
  have hℓ3 : 3 ≤ (hP.above_finite Q 4).toFinset.card := by
    have := hP.three_le_up hQ h2
    rwa [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)] at this
  have hle : ∀ H ∈ (hP.above_finite Q 4).toFinset,
      (if non5 P H Q = ∅ then (-2 : ℤ) else 1) ≤ 1 := by
    intro H _; split_ifs <;> norm_num
  by_cases h4 : 4 ≤ (hP.above_finite Q 4).toFinset.card
  · have := Finset.sum_le_sum hle
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at this
    push_cast at h4 ⊢
    have h4' : (4 : ℤ) ≤ ((hP.above_finite Q 4).toFinset.card : ℤ) := by exact_mod_cast h4
    linarith
  · have h3 : (hP.above_finite Q 4).toFinset.card = 3 := by omega
    have hℓ : {F | F ∈ faces P ∧ Q ⊆ F ∧ dim F = 4}.ncard = 3 := by
      rw [Set.ncard_eq_toFinset_card _ (hP.above_finite Q 4)]; exact h3
    obtain ⟨H0, hH0, h55⟩ := hP.exists_five_five h16 hQ h2 h4Q hℓ
    rw [← Finset.add_sum_erase _ _ hH0, if_pos h55]
    have := Finset.sum_le_sum (s := (hP.above_finite Q 4).toFinset.erase H0)
      fun H hH => hle H (Finset.mem_of_mem_erase hH)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hH0, h3] at this
    rw [h3]
    push_cast at this ⊢
    linarith

end cs

end Kalai5
