import Kalai5.Endpoints.Z20.LocalY
import Kalai5.Rigidity.PolygonStar

/-!
# Quadrilaterals in the facets `Y = (7,15,14,6; 29)` and `E = (7,16,16,7; 32)`

* `IsCSPolytope5.two_card_facet`: a property of 2-faces, counted in a facet, is counted twice
  over its 3-faces.
* `IsCSPolytope5.five_one_core`: if the 3-faces of a facet `F` are simplices and square pyramids
  except one `T₆` with six vertices and `exc T₆ ≤ 3`, and the pyramids number `exc F`, then
  `q4 F = exc F` and every quadrilateral of `F` lies in exactly one 3-face of `F` with five
  vertices (all quadrilaterals lie in `T₆`, and the other 3-face through one is a pyramid).
* `IsCSPolytope5.q4_zero_core`: if the 3-faces are simplices except two, and `exc F = 2`, then
  `F` has no quadrilateral (a quadrilateral is the intersection of the two, and a single
  quadrilateral leaves an excess of `1`).
* `IsCSPolytope5.Y_quad`, `IsCSPolytope5.E_quad`: the two rows, through the facet profiles
  `[2,3,0,1,0,0,0]`, `[4,2,0,0,1,0,0]` and `[5,0,0,0,2,0,0]`.
-/

namespace Kalai5

open Set

open scoped Classical

/-- The row `(7,16,16,7; 32)`. -/
def eRow : Row := ⟨7, 16, 16, 7, 32⟩

lemma smallRowsX_eRow : ∀ X ∈ smallRowsX, X.1 = eRow →
    X.2.1 = [4, 2, 0, 0, 1, 0, 0] ∨ X.2.1 = [5, 0, 0, 0, 2, 0, 0] := by
  decide

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **Double counting a property of 2-faces** in a facet. -/
lemma IsCSPolytope5.two_card_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (p : Set E5 → Prop) [DecidablePred p] :
    2 * (((hP.below_finite F 2).toFinset.filter p).card : ℤ) =
      ∑ T ∈ (hP.below_finite F 3).toFinset,
        (((hP.below_finite T 2).toFinset.filter p).card : ℤ) := by
  have hq : ∀ G, (((hP.below_finite G 2).toFinset.filter p).card : ℤ) =
      ∑ Q ∈ (hP.below_finite G 2).toFinset, if p Q then (1 : ℤ) else 0 := by
    intro G
    rw [Finset.sum_boole]
  rw [Finset.sum_congr rfl fun T _ => hq T, hP.sum_below_comm F 2 3, hq F, Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Set.Finite.mem_toFinset] at hQ
  rw [hP.twoface_in_facet hF h4 hQ.1 hQ.2.1 hQ.2.2]
  push_cast
  ring

/-- **Double counting large polygons** in a facet. -/
lemma IsCSPolytope5.two_big2_facet {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4) :
    2 * (big2 P F : ℤ) = ∑ T ∈ (hP.below_finite F 3).toFinset, (big2 P T : ℤ) := by
  simp only [hP.big2_eq_card]
  exact hP.two_card_facet hF h4 _

/-- A face containing a quadrilateral has one. -/
lemma IsCSPolytope5.q4_pos_of_quad {T Q : Set E5} (hQ : Q ∈ faces P) (hQT : Q ⊆ T)
    (h2 : dim Q = 2) (h4Q : cnt P Q 0 = 4) : 0 < q4 P T := by
  have hfin : {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  unfold q4
  exact (Set.ncard_pos hfin).2 ⟨Q, hQ, hQT, h2, h4Q⟩

/-- The 3-faces of a facet through a 2-face of it: exactly two. -/
lemma IsCSPolytope5.card_three_through {F Q : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (h2 : dim Q = 2) :
    ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T).card = 2 := by
  classical
  rw [← hP.twoface_in_facet hF h4 hQ hQF h2, ← Set.ncard_coe_finset]
  congr 1
  ext T
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  tauto

/-- **Core of the quadrilateral colouring.** -/
theorem IsCSPolytope5.five_one_core {F T6 : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hT6 : T6 ∈ (hP.below_finite F 3).toFinset) (h6 : cnt P T6 0 = 6) (hx6 : exc P T6 ≤ 3)
    (hrest : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ T6 →
      tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5))
    (hb : ((((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 8, 5)).card : ℕ) : ℤ)
      = exc P F) :
    (q4 P F : ℤ) = exc P F ∧ ∀ Q, Q ∈ faces P → Q ⊆ F → dim Q = 2 → cnt P Q 0 = 4 →
      ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5).card = 1 := by
  classical
  have hmem : ∀ T, T ∈ (hP.below_finite F 3).toFinset ↔ (T ∈ faces P ∧ T ⊆ F ∧ dim T = 3) :=
    fun T => by rw [Set.Finite.mem_toFinset]; rfl
  obtain ⟨-, hT6F, -⟩ := (hmem T6).1 hT6
  -- no polygon with five or more vertices
  have hbig : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ T6 → big2 P T = 0 := by
    intro T hT hne
    obtain ⟨hTP, -, hT3⟩ := (hmem T).1 hT
    rcases hrest T hT hne with h | h
    · have he := hP.exc_threeface hTP hT3
      simp only [tri3, Prod.mk.injEq] at h
      rw [h.2.1, h.2.2] at he
      have := hP.q4_add_big_le_exc T
      have : (0 : ℤ) ≤ q4 P T := by positivity
      omega
    · exact (hP.q4_585 hTP hT3 h).2
  have h2big := hP.two_big2_facet hF h4
  rw [Finset.sum_eq_single_of_mem T6 hT6 fun T hT hne => by rw [hbig T hT hne]; rfl] at h2big
  have hle6 := hP.q4_add_big_le_exc T6
  have hq6pos : (0 : ℤ) ≤ q4 P T6 := by positivity
  have hbF : big2 P F = 0 := by omega
  have hqF := hP.exc_eq_q4_of_big F hbF
  -- the six-vertex 3-face carries all quadrilaterals
  have h2q := hP.two_q4_facet hF h4
  rw [← Finset.add_sum_erase _ _ hT6] at h2q
  have hsum : ∑ T ∈ (hP.below_finite F 3).toFinset.erase T6, (q4 P T : ℤ) =
      (((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = (5, 8, 5)).card : ℤ) := by
    rw [Finset.card_filter, Nat.cast_sum, ← Finset.add_sum_erase _ _ hT6]
    have h585 : ¬ tri3 P T6 = (5, 8, 5) := by simp [tri3, h6]
    rw [if_neg h585, Nat.cast_zero, zero_add]
    refine Finset.sum_congr rfl fun T hT => ?_
    obtain ⟨hne, hT⟩ := Finset.mem_erase.1 hT
    obtain ⟨hTP, -, hT3⟩ := (hmem T).1 hT
    rcases hrest T hT hne with h | h
    · rw [if_neg (by rw [h]; decide), hP.q4_464 hTP hT3 h]
    · rw [if_pos h, (hP.q4_585 hTP hT3 h).1]
  rw [hsum, hb] at h2q
  have hq6 : q4 P T6 = q4 P F := by omega
  have hfinF : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4}.Finite :=
    hP.faces_finite.subset fun Q hQ => hQ.1
  have hsubQ : {Q | Q ∈ faces P ∧ Q ⊆ T6 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} :=
    fun Q hQ => ⟨hQ.1, hQ.2.1.trans hT6F, hQ.2.2⟩
  have heqQ := Set.eq_of_subset_of_ncard_le hsubQ (by unfold q4 at hq6; exact hq6.symm.le) hfinF
  refine ⟨hqF.symm, fun Q hQ hQF h2 h4Q => ?_⟩
  have hQT6 : Q ⊆ T6 := by
    have hQm : Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := ⟨hQ, hQF, h2, h4Q⟩
    rw [← heqQ] at hQm
    exact hQm.2.1
  -- the other 3-face of `F` through `Q` is a pyramid
  have hT6Q : T6 ∈ (hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T :=
    Finset.mem_filter.2 ⟨hT6, hQT6⟩
  have hfilt : ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T ∧ cnt P T 0 = 5) =
      ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T).erase T6 := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hT, hQT, h5⟩
      refine ⟨fun h => ?_, hT, hQT⟩
      rw [h, h6] at h5
      exact absurd h5 (by norm_num)
    · rintro ⟨hne, hT, hQT⟩
      refine ⟨hT, hQT, ?_⟩
      obtain ⟨hTP, -, hT3⟩ := (hmem T).1 hT
      have hpos := hP.q4_pos_of_quad hQ hQT h2 h4Q
      rcases hrest T hT hne with h | h
      · rw [hP.q4_464 hTP hT3 h] at hpos
        exact absurd hpos (lt_irrefl 0)
      · simp only [tri3, Prod.mk.injEq] at h
        exact h.1
  rw [hfilt, Finset.card_erase_of_mem hT6Q, hP.card_three_through hF h4 hQ hQF h2]

/-- **No quadrilateral** when all 3-faces but two are simplices and the excess is `2`. -/
theorem IsCSPolytope5.q4_zero_core {F Ta Tb : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hTa : Ta ∈ (hP.below_finite F 3).toFinset) (hTb : Tb ∈ (hP.below_finite F 3).toFinset)
    (hab : Ta ≠ Tb)
    (hrest : ∀ T ∈ (hP.below_finite F 3).toFinset, T ≠ Ta → T ≠ Tb → tri3 P T = (4, 6, 4))
    (hexc : exc P F = 2) : q4 P F = 0 := by
  classical
  have hmem : ∀ T, T ∈ (hP.below_finite F 3).toFinset ↔ (T ∈ faces P ∧ T ⊆ F ∧ dim T = 3) :=
    fun T => by rw [Set.Finite.mem_toFinset]; rfl
  obtain ⟨hTaP, -, hTa3⟩ := (hmem Ta).1 hTa
  obtain ⟨hTbP, -, hTb3⟩ := (hmem Tb).1 hTb
  have hquad : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ⊆ {Ta ∩ Tb} := by
    rintro Q ⟨hQ, hQF, h2, h4Q⟩
    have hsub : ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T) ⊆ {Ta, Tb} := by
      intro T hT
      rw [Finset.mem_filter] at hT
      by_contra hn
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      have h464 := hrest T hT.1 hn.1 hn.2
      obtain ⟨hTP, -, hT3⟩ := (hmem T).1 hT.1
      have hpos := hP.q4_pos_of_quad hQ hT.2 h2 h4Q
      rw [hP.q4_464 hTP hT3 h464] at hpos
      exact lt_irrefl 0 hpos
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [hP.card_three_through hF h4 hQ hQF h2, Finset.card_pair hab])
    have hQa : Q ⊆ Ta := by
      have : Ta ∈ ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T) := by
        rw [heq]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_filter.1 this).2
    have hQb : Q ⊆ Tb := by
      have : Tb ∈ ((hP.below_finite F 3).toFinset.filter fun T => Q ⊆ T) := by
        rw [heq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (Finset.mem_filter.1 this).2
    rw [Set.mem_singleton_iff]
    exact (hP.inter_eq_of_three_faces hQ h2 hTaP hTa3 hTbP hTb3 hQa hQb hab).symm
  have hle1 : q4 P F ≤ 1 := by
    unfold q4
    calc _ ≤ ({Ta ∩ Tb} : Set (Set E5)).ncard := Set.ncard_le_ncard hquad (Set.finite_singleton _)
      _ = 1 := Set.ncard_singleton _
  have h1 := hP.q4_add_big_le_exc F
  by_cases hb : big2 P F = 0
  · have := hP.exc_eq_q4_of_big F hb
    omega
  · omega

/-- **Excess from the facet profile**: `2 exc F = Σ_{t ∈ fv7} #{T : tri3 T = t} (2 t₁ - 3 t₂)`. -/
lemma IsCSPolytope5.two_exc_profile {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hn : cnt P F 0 ≤ 7) :
    2 * exc P F = (fv7.map fun t =>
      (((hP.below_finite F 3).toFinset.filter fun T => tri3 P T = t).card : ℤ) *
        (2 * (t.2.1 : ℤ) - 3 * t.2.2)).sum := by
  classical
  rw [hP.two_exc_facet hF h4]
  have hT : ∀ T ∈ (hP.below_finite F 3).toFinset,
      exc P T = (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2) (tri3 P T) := by
    intro T hT
    rw [Set.Finite.mem_toFinset] at hT
    rw [hP.exc_threeface hT.1 hT.2.2]
    rfl
  rw [Finset.sum_congr rfl hT]
  exact sum_of_cover _ _ fv7_nodup (hP.facet_profile hF h4 hn).1
    (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2)

end cs

end Kalai5
