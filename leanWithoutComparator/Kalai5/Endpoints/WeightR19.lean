import Kalai5.Endpoints.EdgeLink
import Kalai5.FullPrism.Upper

/-!
# The Q55 weight of the row `R₁₉ = (8,19,18,7;35)`

The polar of a facet `F` with row `R₁₉ = zRow` has row `(7,18,19,8;35)`, a single catalogued type, so
the 3-faces of `F` are two tetrahedra, two square pyramids, one triangular bipyramid and two 3-faces
with face numbers `(6,10,6)` (`IsCSPolytope5.r19_types`).  The row gives `Σ_T f₁(T) = 3 f₁(F)`, so
every edge of `F` lies in exactly three 3-faces (`IsCSPolytope5.r19_edges_three`).
-/

namespace Kalai5

open Set

open scoped Classical

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A vertex of a facet lies in at least four of its 3-faces.** -/
theorem IsCSPolytope5.vertex_in_facet_four {F v : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hv : v ∈ faces P) (hvF : v ⊆ F) (h0 : dim v = 0) :
    4 ≤ {T | T ∈ faces P ∧ v ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard := by
  obtain ⟨V, hV⟩ := hP.polytope
  have hF' : F ∈ faces (convexHull ℝ (V : Set E5)) := hV ▸ hF
  have hFV : F = convexHull ℝ ((V.filter (· ∈ F) : Finset E5) : Set E5) :=
    face_eq_convexHull_filter hF'
  have hvF' : v ∈ faces F := (mem_faces_face_iff hF').2 ⟨hV ▸ hv, hvF⟩
  have key := vertex_four_le_r hFV h4 hvF' h0
  have hup : upIn F v 3 = {T | T ∈ faces P ∧ v ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard := by
    unfold upIn
    congr 1
    ext T
    simp only [Set.mem_ofPred_eq, mem_faces_face_iff hF', ← hV]
    constructor
    · rintro ⟨⟨h1', h3'⟩, h2', h4'⟩; exact ⟨h1', h2', h3', h4'⟩
    · rintro ⟨h1', h2', h3', h4'⟩; exact ⟨⟨h1', h3'⟩, h2', h4'⟩
  rw [hup] at key
  exact key

/-- **The 3-faces of a facet with row `R₁₉`**. -/
lemma IsCSPolytope5.r19_types {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) :
    tcnt P F (4, 6, 4) = 2 ∧ tcnt P F (5, 8, 5) = 2 ∧ tcnt P F (5, 9, 6) = 1 ∧
      tcnt P F (6, 10, 6) = 2 ∧ tcnt P F (6, 9, 5) = 0 ∧ tcnt P F (7, 11, 6) = 0 := by
  simp only [faceRow, zRow, Row.mk.injEq] at hR
  obtain ⟨h0, h1, h2, h3, hJ⟩ := hR
  obtain ⟨X, hX, hX1, hX2⟩ := hP.facet_types_r7 hF h4 (by omega)
  rw [h0, h1, h2, h3, hJ] at hX1
  rw [smallRowsX_zdual X hX hX1] at hX2
  simp only [fv7, List.map_cons, List.map_nil, List.cons.injEq] at hX2
  omega

/-- In a facet with row `R₁₉` every 3-face has one of the four types. -/
lemma IsCSPolytope5.r19_type_cases {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) :
    tri3 P T = (4, 6, 4) ∨ tri3 P T = (5, 8, 5) ∨ tri3 P T = (5, 9, 6) ∨
      tri3 P T = (6, 10, 6) := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, -, -⟩ := hP.r19_types hF h4 hR
  obtain ⟨e1, -, -, -⟩ := hP.facet8_arith hF h4 hn
  have h1 := hP.one_le_tcnt hT hTF h3
  have hne : T ≠ F := by
    rintro rfl
    rw [h3] at h4
    exact absurd h4 (by norm_num)
  have hlt := hP.cnt_zero_lt hT hF hTF hne
  have hin := hP.tri3_mem_fv8 hT h3 (by omega)
  simp only [fv8, List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] at h1 ⊢ <;>
    first | (left; rfl) | (right; left; rfl) | (right; right; left; rfl) |
      (right; right; right; rfl) | omega

/-- **Every edge of a facet with row `R₁₉` lies in exactly three of its 3-faces.** -/
theorem IsCSPolytope5.r19_edges_three {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {e : Set E5} (he : e ∈ faces P) (heF : e ⊆ F) (h1 : dim e = 1) :
    {T | T ∈ faces P ∧ e ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard = 3 := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, he1, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r19_types hF h4 hR
  obtain ⟨e1, -, -, -⟩ := hP.facet8_arith hF h4 hn
  refine hP.edge_three_of_sum hF h4 ?_ he heF h1
  have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset,
      (cnt P T 1 : ℤ) = (fun t : ℕ × ℕ × ℕ => (t.2.1 : ℤ)) (tri3 P T) := fun T _ => rfl
  have hsum := hP.facet8_sum hF h4 hn (fun t : ℕ × ℕ × ℕ => (t.2.1 : ℤ))
  rw [Finset.sum_congr rfl hpt, hsum, he1]
  simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  push_cast
  omega

/-- The excess of a facet with row `R₁₉` is three. -/
lemma IsCSPolytope5.r19_exc {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) : exc P F = 3 := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r19_types hF h4 hR
  obtain ⟨e1, -, -, -⟩ := hP.facet8_arith hF h4 hn
  have h2 : 2 * exc P F = 6 := by
    rw [hP.two_exc_facet hF h4]
    have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset,
        exc P T = (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2) (tri3 P T) := by
      intro T hT
      rw [Set.Finite.mem_toFinset] at hT
      rw [hP.exc_threeface hT.1 hT.2.2]
      rfl
    have hsum := hP.facet8_sum hF h4 hn (fun t : ℕ × ℕ × ℕ => 2 * (t.2.1 : ℤ) - 3 * t.2.2)
    rw [Finset.sum_congr rfl hpt, hsum]
    simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    omega
  omega

/-! ### No pentagons -/

/-- **Faces are determined by their vertices**: `vset A ⊆ vset B` gives `A ⊆ B`. -/
lemma IsCSPolytope5.subset_of_vset {A B : Set E5} (hA : A ∈ faces P) (hB : B ∈ faces P)
    (h : vset P A ⊆ vset P B) : A ⊆ B := by
  obtain ⟨W, hW, hcp⟩ := hP.exists_vertFinset
  have hA' : A ∈ faces (convexHull ℝ (W : Set E5)) := hW ▸ hA
  have hB' : B ∈ faces (convexHull ℝ (W : Set E5)) := hW ▸ hB
  refine (face_eq_convexHull_filter hA').subset.trans ?_
  refine convexHull_min ?_ (face_convex (convex_convexHull ℝ _) hB')
  intro x hx
  rw [Finset.coe_filter] at hx
  obtain ⟨hxW, hxA⟩ := hx
  have hsing : ({x} : Set E5) ∈ faces P := by
    rw [hW]; exact singleton_mem_faces_of_extreme (hcp x hxW)
  have hv : ({x} : Set E5) ∈ vset P A := ⟨hsing, Set.singleton_subset_iff.2 hxA, dim_singleton x⟩
  exact Set.singleton_subset_iff.1 (h hv).2.1

/-- **The third 3-face through an edge of a pyramid base contains the apex.**  Let a 2-face `Q`
lie in the 3-faces `X ≠ X'` of a facet `F`, and let `x` be a vertex with
`vset X ⊆ insert x (vset Q)`.  For an edge `ε` of `Q`, the other 2-face of `X` through `ε`
contains `x`, and its other 3-face in `F` is neither `X` nor `X'`. -/
lemma IsCSPolytope5.apex_third {F Q X X' x ε : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hQ : Q ∈ faces P) (h2 : dim Q = 2)
    (hX : X ∈ faces P) (hXF : X ⊆ F) (hX3 : dim X = 3) (hQX : Q ⊆ X)
    (hX' : X' ∈ faces P) (hX'3 : dim X' = 3) (hQX' : Q ⊆ X') (hXX' : X ≠ X')
    (hvX : vset P X ⊆ insert x (vset P Q))
    (hε : ε ∈ faces P) (hεQ : ε ⊆ Q) (h1 : dim ε = 1) :
    ∃ Z, Z ∈ faces P ∧ Z ⊆ F ∧ dim Z = 3 ∧ ε ⊆ Z ∧ x ⊆ Z ∧ Z ≠ X ∧ Z ≠ X' := by
  -- the other 2-face of `X` through `ε`
  have htwo := hP.edge_in_threeface hX hX3 hε (hεQ.trans hQX) h1
  obtain ⟨A, hAm, hAQ⟩ := exists_ne_of_ncard_eq_two htwo (a := Q) ⟨hQ, hεQ, hQX, h2⟩
  obtain ⟨hA, hεA, hAX, hA2⟩ := hAm
  -- it contains the apex
  have hxA : x ⊆ A := by
    by_contra hxA
    have hsub : vset P A ⊆ vset P Q := by
      intro v hv
      have hvX' : v ∈ vset P X := ⟨hv.1, hv.2.1.trans hAX, hv.2.2⟩
      rcases hvX hvX' with h | h
      · rw [h] at hv
        exact absurd hv.2.1 hxA
      · exact h
    have hAQ' : A ⊆ Q := hP.subset_of_vset hA hQ hsub
    exact hAQ (hP.eq_of_subset_of_dim_le hA hQ hAQ' (by omega))
  -- the other 3-face of `F` through it
  have hthree := hP.twoface_in_facet hF h4 hA (hAX.trans hXF) hA2
  obtain ⟨Z, hZm, hZX⟩ := exists_ne_of_ncard_eq_two hthree (a := X) ⟨hX, hAX, hXF, hX3⟩
  obtain ⟨hZ, hAZ, hZF, hZ3⟩ := hZm
  refine ⟨Z, hZ, hZF, hZ3, hεA.trans hAZ, hxA.trans hAZ, hZX, ?_⟩
  intro hZX'
  rw [hZX'] at hAZ
  have hAQ' : A ⊆ Q := by
    rw [← hP.inter_three_eq hQ h2 hX hX3 hX' hX'3 hXX' hQX hQX']
    exact subset_inter hAX hAZ
  exact hAQ (hP.eq_of_subset_of_dim_le hA hQ hAQ' (by omega))

/-- **An apex over a 2-face lies in many 3-faces**: if a 2-face `Q` of a facet `F` lies in the
3-faces `X ≠ X'` of `F` and `x` is a vertex of `X` with `vset X ⊆ insert x (vset Q)`, then `x` lies
in at least `f₀(Q) + 1` 3-faces of `F`: `X`, and one for each edge of `Q`. -/
lemma IsCSPolytope5.apex_count {F Q X X' x : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (h2 : dim Q = 2)
    (hX : X ∈ faces P) (hXF : X ⊆ F) (hX3 : dim X = 3) (hQX : Q ⊆ X)
    (hX' : X' ∈ faces P) (hX'F : X' ⊆ F) (hX'3 : dim X' = 3) (hQX' : Q ⊆ X') (hXX' : X ≠ X')
    (hx : x ∈ vset P X) (hvX : vset P X ⊆ insert x (vset P Q)) :
    cnt P Q 0 + 1 ≤ {T | T ∈ faces P ∧ x ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard := by
  have hZ : ∀ ε ∈ {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1},
      ∃ Z, Z ∈ faces P ∧ Z ⊆ F ∧ dim Z = 3 ∧ ε ⊆ Z ∧ x ⊆ Z ∧ Z ≠ X ∧ Z ≠ X' :=
    fun ε hε => hP.apex_third hF h4 hQ h2 hX hXF hX3 hQX hX' hX'3 hQX' hXX' hvX hε.1 hε.2.1
      hε.2.2
  choose! Z hZ using hZ
  -- the 3-faces of `F` through `Q` are `X, X'`
  have hQtwo := hP.twoface_in_facet hF h4 hQ hQF h2
  have hpair : ({X, X'} : Set (Set E5)) = {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by
    apply Set.eq_of_subset_of_ncard_le
    · intro T hT
      rcases (show T = X ∨ T = X' by simpa using hT) with rfl | rfl
      · exact ⟨hX, hQX, hXF, hX3⟩
      · exact ⟨hX', hQX', hX'F, hX'3⟩
    · rw [hQtwo, Set.ncard_pair hXX']
    · exact hP.faces_finite.subset fun T hT => hT.1
  -- the 3-face `Z ε` meets `Q` in `ε`
  have hcut : ∀ ε ∈ {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1}, Z ε ∩ Q = ε := by
    intro ε hε
    have hε' := hε
    obtain ⟨hεf, hεQ, hε1⟩ := hε'
    obtain ⟨hZf, hZF, hZ3, hεZ, -, hZX, hZX'⟩ := hZ ε hε
    have hQZ : ¬ Q ⊆ Z ε := by
      intro hQZ
      have hmem : Z ε ∈ ({X, X'} : Set (Set E5)) := by
        rw [hpair]; exact ⟨hZf, hQZ, hZF, hZ3⟩
      rcases (show Z ε = X ∨ Z ε = X' by simpa using hmem) with h | h
      · exact hZX h
      · exact hZX' h
    have hI : Z ε ∩ Q ∈ faces P :=
      inter_mem_faces_of_nonempty hZf hQ (hεf.1.mono (subset_inter hεZ hεQ))
    have hIQ : Z ε ∩ Q ∈ faces Q := mem_faces_of_subset (face_subset hQ) hI inter_subset_right
    have hne : Z ε ∩ Q ≠ Q := fun h => hQZ (h ▸ inter_subset_left)
    have hlt := dim_lt_of_mem_faces_ne hIQ hne
    exact (hP.eq_of_subset_of_dim_le hεf hI (subset_inter hεZ hεQ) (by omega)).symm
  have hinj : Set.InjOn Z {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1} := by
    intro ε hε ε' hε' h
    rw [← hcut ε hε, ← hcut ε' hε', h]
  have hEcard : {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1}.ncard = cnt P Q 0 :=
    hP.cnt_one_of_two hQ h2
  have hXnot : X ∉ Z '' {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1} := by
    rintro ⟨ε, hε, h⟩
    exact (hZ ε hε).2.2.2.2.2.1 h
  have hsub : insert X (Z '' {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1}) ⊆
      {T | T ∈ faces P ∧ x ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by
    rintro T (rfl | ⟨ε, hε, rfl⟩)
    · exact ⟨hX, hx.2.1, hXF, hX3⟩
    · obtain ⟨hZf, hZF, hZ3, -, hxZ, -, -⟩ := hZ ε hε
      exact ⟨hZf, hxZ, hZF, hZ3⟩
  have hfinE : {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1}.Finite :=
    hP.faces_finite.subset fun ε hε => hε.1
  calc cnt P Q 0 + 1 = (insert X (Z '' {ε | ε ∈ faces P ∧ ε ⊆ Q ∧ dim ε = 1})).ncard := by
        rw [Set.ncard_insert_of_notMem hXnot (hfinE.image Z), hinj.ncard_image, hEcard]
    _ ≤ _ := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T hT => hT.1)

/-- In a facet with row `R₁₉`, a 3-face with a 2-face of at least five vertices has type `(6,10,6)`,
and the 2-face is a pentagon. -/
lemma IsCSPolytope5.r19_big_type {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {T Q : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3)
    (hQ : Q ∈ faces P) (hQT : Q ⊆ T) (h2 : dim Q = 2) (h5 : 5 ≤ cnt P Q 0) :
    tri3 P T = (6, 10, 6) ∧ cnt P Q 0 = 5 := by
  have hle := hP.cnt_zero_add_one_le hT h3 hQ hQT h2
  have hne : Q ≠ T := by
    rintro rfl
    rw [h2] at h3
    exact absurd h3 (by norm_num)
  have hlt := hP.cnt_zero_lt hQ hT hQT hne
  rcases hP.r19_type_cases hF h4 hR hT hTF h3 with h | h | h | h
  all_goals first
    | exact ⟨h, by simp only [tri3, Prod.mk.injEq] at h; omega⟩
    | (exfalso; simp only [tri3, Prod.mk.injEq] at h; omega)

/-- **No 2-face of a facet with row `R₁₉` has five vertices.**  A pentagon would lie in two pentagonal
pyramids `X₁, X₂`, and each apex would lie in six 3-faces (`IsCSPolytope5.apex_count`); with every
vertex in at least four 3-faces this needs `36 ≤ f₀₃ = 35` incidences. -/
theorem IsCSPolytope5.r19_no_big {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {Q : Set E5} (hQ : Q ∈ faces P) (hQF : Q ⊆ F) (h2 : dim Q = 2) :
    cnt P Q 0 ≤ 4 := by
  by_contra hbig
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, -, hJ⟩ := hR'
  -- the two 3-faces through `Q`
  have hQtwo := hP.twoface_in_facet hF h4 hQ hQF h2
  obtain ⟨X1, X2, h12, hX12⟩ := Set.ncard_eq_two.1 hQtwo
  have hX1 : X1 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hX12]; simp
  have hX2 : X2 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hX12]; simp
  obtain ⟨hX1f, hQX1, hX1F, hX13⟩ := hX1
  obtain ⟨hX2f, hQX2, hX2F, hX23⟩ := hX2
  obtain ⟨ht1, hQ5⟩ := hP.r19_big_type hF h4 hR hX1f hX1F hX13 hQ hQX1 h2 (by omega)
  obtain ⟨ht2, -⟩ := hP.r19_big_type hF h4 hR hX2f hX2F hX23 hQ hQX2 h2 (by omega)
  -- the apexes
  have apex : ∀ X, X ∈ faces P → Q ⊆ X → tri3 P X = (6, 10, 6) →
      ∃ x ∈ vset P X, x ∉ vset P Q ∧ vset P X ⊆ insert x (vset P Q) := by
    intro X hX hQX htX
    have h6 : cnt P X 0 = 6 := by simp only [tri3, Prod.mk.injEq] at htX; exact htX.1
    have hsub : vset P Q ⊆ vset P X := fun v hv => ⟨hv.1, hv.2.1.trans hQX, hv.2.2⟩
    have hd : (vset P X \ vset P Q).ncard = 1 := by
      have := Set.ncard_sdiff hsub (hP.vset_finite Q)
      rw [← cnt_eq_vset, ← cnt_eq_vset, h6, hQ5] at this
      omega
    obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hd
    have hxm : x ∈ vset P X \ vset P Q := by rw [hx]; exact Set.mem_singleton x
    refine ⟨x, hxm.1, hxm.2, fun v hv => ?_⟩
    by_cases hvQ : v ∈ vset P Q
    · exact Or.inr hvQ
    · have hvd : v ∈ vset P X \ vset P Q := ⟨hv, hvQ⟩
      rw [hx] at hvd
      exact Or.inl hvd
  obtain ⟨x1, hx1, hx1Q, hv1⟩ := apex X1 hX1f hQX1 ht1
  obtain ⟨x2, hx2, hx2Q, hv2⟩ := apex X2 hX2f hQX2 ht2
  have hx12 : x1 ≠ x2 := by
    intro h
    rw [← h] at hx2
    have hI := hP.inter_three_eq hQ h2 hX1f hX13 hX2f hX23 h12 hQX1 hQX2
    exact hx1Q ⟨hx1.1, by rw [← hI]; exact subset_inter hx1.2.1 hx2.2.1, hx1.2.2⟩
  have c1 := hP.apex_count hF h4 hQ hQF h2 hX1f hX1F hX13 hQX1 hX2f hX2F hX23 hQX2 h12 hx1 hv1
  have c2 := hP.apex_count hF h4 hQ hQF h2 hX2f hX2F hX23 hQX2 hX1f hX1F hX13 hQX1 h12.symm hx2
    hv2
  rw [hQ5] at c1 c2
  -- the vertex–3-face incidences
  have hsum := hP.incid_eq_sum_first F 0 3
  rw [hJ] at hsum
  have hcard : (hP.below_finite F 0).toFinset.card = 8 := by
    rw [← hn, cnt, Set.ncard_eq_toFinset_card _ (hP.below_finite F 0)]
  have hm1 : x1 ∈ (hP.below_finite F 0).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hx1.1, hx1.2.1.trans hX1F, hx1.2.2⟩
  have hm2 : x2 ∈ (hP.below_finite F 0).toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨hx2.1, hx2.2.1.trans hX2F, hx2.2.2⟩
  have hnn : ∀ G ∈ (hP.below_finite F 0).toFinset,
      (0 : ℤ) ≤ ({H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ F ∧ dim H = 3}.ncard : ℤ) - 4 := by
    intro G hG
    rw [Set.Finite.mem_toFinset] at hG
    have := hP.vertex_in_facet_four hF h4 hG.1 hG.2.1 hG.2.2
    omega
  have hpsub : ({x1, x2} : Finset (Set E5)) ⊆ (hP.below_finite F 0).toFinset := by
    intro G hG
    rcases Finset.mem_insert.1 hG with h | h
    · rw [h]; exact hm1
    · rw [Finset.mem_singleton.1 h]; exact hm2
  have key : ∑ G ∈ ({x1, x2} : Finset (Set E5)),
      (({H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ F ∧ dim H = 3}.ncard : ℤ) - 4) ≤
      ∑ G ∈ (hP.below_finite F 0).toFinset,
        (({H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ F ∧ dim H = 3}.ncard : ℤ) - 4) :=
    Finset.sum_le_sum_of_subset_of_nonneg hpsub (fun G hG _ => hnn G hG)
  rw [Finset.sum_pair hx12, Finset.sum_sub_distrib, Finset.sum_const, hcard] at key
  have hsumZ : (35 : ℤ) = ∑ G ∈ (hP.below_finite F 0).toFinset,
      ({H | H ∈ faces P ∧ G ⊆ H ∧ H ⊆ F ∧ dim H = 3}.ncard : ℤ) := by exact_mod_cast hsum
  have c1' : (6 : ℤ) ≤ ({T | T ∈ faces P ∧ x1 ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) := by
    exact_mod_cast c1
  have c2' : (6 : ℤ) ≤ ({T | T ∈ faces P ∧ x2 ⊆ T ∧ T ⊆ F ∧ dim T = 3}.ncard : ℤ) := by
    exact_mod_cast c2
  simp only [nsmul_eq_mul] at key
  push_cast at key
  linarith

/-! ### Quadrilaterals -/

/-- A `(6,10,6)` 3-face of a facet with row `R₁₉` has two quadrilaterals and no larger 2-face. -/
lemma IsCSPolytope5.r19_6106 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3)
    (ht : tri3 P T = (6, 10, 6)) : q4 P T = 2 ∧ big2 P T = 0 := by
  have hb : big2 P T = 0 := by
    have hempty : {Q | Q ∈ faces P ∧ Q ⊆ T ∧ dim Q = 2 ∧ 5 ≤ cnt P Q 0} =
        (∅ : Set (Set E5)) := by
      refine Set.eq_empty_of_forall_notMem fun Q hQ => ?_
      have h1 := hP.r19_no_big hF h4 hR hQ.1 (hQ.2.1.trans hTF) hQ.2.2.1
      have h2 := hQ.2.2.2
      omega
    unfold big2
    rw [hempty, Set.ncard_empty]
  have he := hP.exc_eq_q4_of_big T hb
  have hx := hP.exc_threeface hT h3
  simp only [tri3, Prod.mk.injEq] at ht
  rw [ht.2.1, ht.2.2] at hx
  refine ⟨?_, hb⟩
  have : (q4 P T : ℤ) = 2 := by rw [← he, hx]; norm_num
  exact_mod_cast this

/-- A triangular bipyramid has no quadrilateral. -/
lemma IsCSPolytope5.q4_596 {T : Set E5} (hT : T ∈ faces P) (h3 : dim T = 3)
    (ht : tri3 P T = (5, 9, 6)) : q4 P T = 0 ∧ big2 P T = 0 := by
  have he := hP.exc_threeface hT h3
  have hle := hP.q4_add_big_le_exc T
  simp only [tri3, Prod.mk.injEq] at ht
  rw [ht.2.1, ht.2.2] at he
  push_cast at he
  constructor <;> omega

/-- The quadrilaterals of the 3-faces of a facet with row `R₁₉`, by type. -/
lemma IsCSPolytope5.r19_q4 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) {T : Set E5} (hT : T ∈ faces P) (hTF : T ⊆ F) (h3 : dim T = 3) :
    (q4 P T : ℤ) = (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else
      if t = (6, 10, 6) then 2 else 0) (tri3 P T) := by
  rcases hP.r19_type_cases hF h4 hR hT hTF h3 with h | h | h | h
  · rw [hP.q4_464 hT h3 h, h]; rfl
  · rw [(hP.q4_585 hT h3 h).1, h]; rfl
  · rw [(hP.q4_596 hT h3 h).1, h]; rfl
  · rw [(hP.r19_6106 hF h4 hR hT hTF h3 h).1, h]; rfl

/-- A facet with row `R₁₉` has three quadrilaterals. -/
lemma IsCSPolytope5.r19_q4F {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) : q4 P F = 3 := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, -, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r19_types hF h4 hR
  have hq4 : 2 * (q4 P F : ℤ) = 6 := by
    rw [hP.two_q4_facet hF h4]
    have hpt : ∀ T ∈ (hP.below_finite F 3).toFinset, (q4 P T : ℤ) =
        (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else
          if t = (6, 10, 6) then 2 else 0) (tri3 P T) := by
      intro T hT
      rw [Set.Finite.mem_toFinset] at hT
      exact hP.r19_q4 hF h4 hR hT.1 hT.2.1 hT.2.2
    have hsum := hP.facet8_sum hF h4 hn
      (fun t : ℕ × ℕ × ℕ => if t = (5, 8, 5) then (1 : ℤ) else if t = (6, 10, 6) then 2 else 0)
    rw [Finset.sum_congr rfl hpt, hsum]
    simp only [fv8, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    norm_num
    omega
  omega

/-- The 3-faces of `F` with face numbers `t`, when there are exactly two of them. -/
lemma IsCSPolytope5.tset_eq_pair {F T₁ T₂ : Set E5} {t : ℕ × ℕ × ℕ} (h : tcnt P F t = 2)
    (h12 : T₁ ≠ T₂) (h1 : T₁ ∈ faces P ∧ T₁ ⊆ F ∧ dim T₁ = 3 ∧ tri3 P T₁ = t)
    (h2 : T₂ ∈ faces P ∧ T₂ ⊆ F ∧ dim T₂ = 3 ∧ tri3 P T₂ = t) :
    {T | T ∈ faces P ∧ T ⊆ F ∧ dim T = 3 ∧ tri3 P T = t} = {T₁, T₂} := by
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro T hT
    rcases (show T = T₁ ∨ T = T₂ by simpa using hT) with rfl | rfl
    · exact h1
    · exact h2
  · rw [Set.ncard_pair h12]
    exact h.le
  · exact hP.faces_finite.subset fun T hT => hT.1

/-- **The two `(6,10,6)` 3-faces of a facet with row `R₁₉` share a 2-face**: otherwise every
quadrilateral would lie in one of the two square pyramids, which have one quadrilateral each, while
the facet has three. -/
lemma IsCSPolytope5.r19_share {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) :
    ∃ X1 X2 Q, X1 ∈ faces P ∧ X1 ⊆ F ∧ dim X1 = 3 ∧ tri3 P X1 = (6, 10, 6) ∧
      X2 ∈ faces P ∧ X2 ⊆ F ∧ dim X2 = 3 ∧ tri3 P X2 = (6, 10, 6) ∧ X1 ≠ X2 ∧
      Q ∈ faces P ∧ dim Q = 2 ∧ Q ⊆ X1 ∧ Q ⊆ X2 := by
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r19_types hF h4 hR
  obtain ⟨X1, X2, h12, hX1, hX2⟩ := hP.exists_two_of_tcnt (F := F) (t := (6, 10, 6)) (by omega)
  obtain ⟨Y1, Y2, hY12, hY1, hY2⟩ := hP.exists_two_of_tcnt (F := F) (t := (5, 8, 5)) (by omega)
  have hXset := hP.tset_eq_pair c4 h12 hX1 hX2
  have hYset := hP.tset_eq_pair c2 hY12 hY1 hY2
  obtain ⟨hX1f, hX1F, hX13, hx1⟩ := hX1
  obtain ⟨hX2f, hX2F, hX23, hx2⟩ := hX2
  obtain ⟨hY1f, hY1F, hY13, hy1⟩ := hY1
  obtain ⟨hY2f, hY2F, hY23, hy2⟩ := hY2
  suffices hsh : ∃ Q, Q ∈ faces P ∧ dim Q = 2 ∧ Q ⊆ X1 ∧ Q ⊆ X2 by
    obtain ⟨Q, hQf, hQ2, hQX1, hQX2⟩ := hsh
    exact ⟨X1, X2, Q, hX1f, hX1F, hX13, hx1, hX2f, hX2F, hX23, hx2, h12, hQf, hQ2, hQX1, hQX2⟩
  by_contra hno'
  -- every quadrilateral of `F` lies in a pyramid
  have hsub : {Q | Q ∈ faces P ∧ Q ⊆ F ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ⊆
      {Q | Q ∈ faces P ∧ Q ⊆ Y1 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ∪
        {Q | Q ∈ faces P ∧ Q ⊆ Y2 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
    rintro Q ⟨hQf, hQF, hQ2, hQ4⟩
    have htwo := hP.twoface_in_facet hF h4 hQf hQF hQ2
    obtain ⟨T1, T2, h12', hT12⟩ := Set.ncard_eq_two.1 htwo
    have hT1 : T1 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    have hT2 : T2 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    obtain ⟨hT1f, hQT1, hT1F, hT13⟩ := hT1
    obtain ⟨hT2f, hQT2, hT2F, hT23⟩ := hT2
    have typ : ∀ T, T ∈ faces P → Q ⊆ T → T ⊆ F → dim T = 3 →
        tri3 P T = (5, 8, 5) ∨ tri3 P T = (6, 10, 6) := by
      intro T hT hQT hTF hT3
      have hQn : 0 < q4 P T :=
        (Set.ncard_pos (hP.faces_finite.subset fun Q' hQ' => hQ'.1)).2 ⟨Q, hQf, hQT, hQ2, hQ4⟩
      rcases hP.r19_type_cases hF h4 hR hT hTF hT3 with h | h | h | h
      · rw [hP.q4_464 hT hT3 h] at hQn; omega
      · exact Or.inl h
      · rw [(hP.q4_596 hT hT3 h).1] at hQn; omega
      · exact Or.inr h
    have inY : ∀ T, T ∈ faces P → Q ⊆ T → T ⊆ F → dim T = 3 → tri3 P T = (5, 8, 5) →
        Q ∈ {Q | Q ∈ faces P ∧ Q ⊆ Y1 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ∪
          {Q | Q ∈ faces P ∧ Q ⊆ Y2 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} := by
      intro T hT hQT hTF hT3 htT
      have hm : T ∈ ({Y1, Y2} : Set (Set E5)) := by rw [← hYset]; exact ⟨hT, hTF, hT3, htT⟩
      rcases (show T = Y1 ∨ T = Y2 by simpa using hm) with h | h
      · exact Or.inl ⟨hQf, h ▸ hQT, hQ2, hQ4⟩
      · exact Or.inr ⟨hQf, h ▸ hQT, hQ2, hQ4⟩
    rcases typ T1 hT1f hQT1 hT1F hT13 with h1 | h1
    · exact inY T1 hT1f hQT1 hT1F hT13 h1
    rcases typ T2 hT2f hQT2 hT2F hT23 with h2 | h2
    · exact inY T2 hT2f hQT2 hT2F hT23 h2
    exfalso
    have m1 : T1 ∈ ({X1, X2} : Set (Set E5)) := by rw [← hXset]; exact ⟨hT1f, hT1F, hT13, h1⟩
    have m2 : T2 ∈ ({X1, X2} : Set (Set E5)) := by rw [← hXset]; exact ⟨hT2f, hT2F, hT23, h2⟩
    rcases (show T1 = X1 ∨ T1 = X2 by simpa using m1) with e1 | e1 <;>
      rcases (show T2 = X1 ∨ T2 = X2 by simpa using m2) with e2 | e2
    · exact h12' (e1.trans e2.symm)
    · exact hno' ⟨Q, hQf, hQ2, by rw [← e1]; exact hQT1, by rw [← e2]; exact hQT2⟩
    · exact hno' ⟨Q, hQf, hQ2, by rw [← e2]; exact hQT2, by rw [← e1]; exact hQT1⟩
    · exact h12' (e1.trans e2.symm)
  have hfin : ({Q | Q ∈ faces P ∧ Q ⊆ Y1 ∧ dim Q = 2 ∧ cnt P Q 0 = 4} ∪
      {Q | Q ∈ faces P ∧ Q ⊆ Y2 ∧ dim Q = 2 ∧ cnt P Q 0 = 4}).Finite :=
    hP.faces_finite.subset fun Q hQ => by rcases hQ with h | h <;> exact h.1
  have hle : q4 P F ≤ q4 P Y1 + q4 P Y2 :=
    (Set.ncard_le_ncard hsub hfin).trans (Set.ncard_union_le _ _)
  rw [hP.r19_q4F hF h4 hR, (hP.q4_585 hY1f hY13 hy1).1, (hP.q4_585 hY2f hY23 hy2).1] at hle
  omega

/-- **Cover in a facet with row `R₁₉`**: the two `(6,10,6)` 3-faces meet in a quadrilateral and
together contain all eight vertices. -/
lemma IsCSPolytope5.r19_cover {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) :
    ∃ X1 X2 Q, X1 ∈ faces P ∧ X1 ⊆ F ∧ dim X1 = 3 ∧ X2 ∈ faces P ∧ X2 ⊆ F ∧ dim X2 = 3 ∧
      X1 ≠ X2 ∧ Q ∈ faces P ∧ dim Q = 2 ∧ Q ⊆ X1 ∧ Q ⊆ X2 ∧ cnt P Q 0 = 4 ∧
      vset P F ⊆ vset P X1 ∪ vset P X2 := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, -, -⟩ := hR'
  obtain ⟨X1, X2, Q, hX1f, hX1F, hX13, hx1, hX2f, hX2F, hX23, hx2, h12, hQf, hQ2, hQX1, hQX2⟩ :=
    hP.r19_share hF h4 hR
  have hI := hP.inter_three_eq hQf hQ2 hX1f hX13 hX2f hX23 h12 hQX1 hQX2
  obtain ⟨hc, hu⟩ := hP.cnt_add_le (P := P) hX1F hX2F hI
  have hQ4 := hP.r19_no_big hF h4 hR hQf (hQX1.trans hX1F) hQ2
  have h6a : cnt P X1 0 = 6 := by simp only [tri3, Prod.mk.injEq] at hx1; exact hx1.1
  have h6b : cnt P X2 0 = 6 := by simp only [tri3, Prod.mk.injEq] at hx2; exact hx2.1
  have hle := Set.ncard_le_ncard hu (hP.vset_finite F)
  rw [← cnt_eq_vset] at hle
  have hU : (vset P F).ncard ≤ (vset P X1 ∪ vset P X2).ncard := by
    rw [← cnt_eq_vset]; omega
  have heq := Set.eq_of_subset_of_ncard_le hu hU (hP.vset_finite F)
  exact ⟨X1, X2, Q, hX1f, hX1F, hX13, hX2f, hX2F, hX23, h12, hQf, hQ2, hQX1, hQX2, by omega,
    heq.symm.subset⟩

/-! ### The Q55 weight -/

/-- **Q55 weight of `R₁₉`**: `q55w + 2 exc ≥ 9`.  There are three quadrilaterals, none between the
two square pyramids. -/
theorem IsCSPolytope5.q55_r19 {F : Set E5} (hF : F ∈ faces P) (h4 : dim F = 4)
    (hR : faceRow P F = zRow) : 9 ≤ q55w P F + 2 * exc P F := by
  have hR' := hR
  simp only [faceRow, zRow, Row.mk.injEq] at hR'
  obtain ⟨hn, -, -, hr, -⟩ := hR'
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hP.r19_types hF h4 hR
  obtain ⟨e1, -, -, e4⟩ := hP.facet8_arith hF h4 hn
  have hexc := hP.r19_exc hF h4 hR
  have hq4 := hP.r19_q4F hF h4 hR
  -- no quadrilateral between two 5-vertex 3-faces
  have hno55 : ∀ Q ∈ (hP.below_finite F 2).toFinset, cnt P Q 0 = 4 → non5 P F Q ≠ ∅ := by
    intro Q hQ h4Q h55
    rw [Set.Finite.mem_toFinset] at hQ
    obtain ⟨hQf, hQF, hQ2⟩ := hQ
    have htwo := hP.twoface_in_facet hF h4 hQf hQF hQ2
    obtain ⟨T1, T2, h12, hT12⟩ := Set.ncard_eq_two.1 htwo
    have hT1 : T1 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    have hT2 : T2 ∈ {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by rw [hT12]; simp
    obtain ⟨hT1f, hQT1, hT1F, hT13⟩ := hT1
    obtain ⟨hT2f, hQT2, hT2F, hT23⟩ := hT2
    have five : ∀ T, T ∈ faces P → Q ⊆ T → T ⊆ F → dim T = 3 → tri3 P T = (5, 8, 5) := by
      intro T hT hQT hTF hT3
      have h5 : cnt P T 0 = 5 := by
        by_contra hc
        have : T ∈ non5 P F Q := ⟨hT, hTF, hT3, hQT, hc⟩
        rw [h55] at this
        exact this
      have hQn : 0 < q4 P T :=
        (Set.ncard_pos (hP.faces_finite.subset fun Q' hQ' => hQ'.1)).2 ⟨Q, hQf, hQT, hQ2, h4Q⟩
      rcases hP.r19_type_cases hF h4 hR hT hTF hT3 with h | h | h | h
      · simp only [tri3, Prod.mk.injEq] at h; omega
      · exact h
      · rw [(hP.q4_596 hT hT3 h).1] at hQn; omega
      · simp only [tri3, Prod.mk.injEq] at h; omega
    have ht1 := five T1 hT1f hQT1 hT1F hT13
    have ht2 := five T2 hT2f hQT2 hT2F hT23
    -- the unique non-triangular 2-face of a pyramid through `Q` is `Q`
    have uniq : ∀ T, T ∈ faces P → dim T = 3 → tri3 P T = (5, 8, 5) → Q ∈ ntri P T →
        ∀ Q' ∈ ntri P T, Q' = Q := by
      intro T hT hT3 htT hQn Q' hQ'
      have hn1 : (ntri P T).ncard = 1 := by
        rw [hP.ntri_ncard T, (hP.q4_585 hT hT3 htT).1, (hP.q4_585 hT hT3 htT).2]
      obtain ⟨x, hx⟩ := Set.ncard_eq_one.1 hn1
      rw [hx, Set.mem_singleton_iff] at hQn hQ'
      rw [hQ', hQn]
    have hQn1 : Q ∈ ntri P T1 := ⟨hQf, hQT1, hQ2, by omega⟩
    have hQn2 : Q ∈ ntri P T2 := ⟨hQf, hQT2, hQ2, by omega⟩
    -- a `(6,10,6)` 3-face: its two quadrilaterals need two partners outside `{X1, T1, T2}`
    obtain ⟨X1, hX1f, hX1F, hX13, hxt⟩ := hP.exists_of_tcnt (F := F) (t := (6, 10, 6)) (by omega)
    obtain ⟨hq2, hb0⟩ := hP.r19_6106 hF h4 hR hX1f hX1F hX13 hxt
    have hX1T1 : X1 ≠ T1 := by intro h; rw [h, ht1] at hxt; simp at hxt
    have hX1T2 : X1 ≠ T2 := by intro h; rw [h, ht2] at hxt; simp at hxt
    have hn2 : (ntri P X1).ncard = 2 := by rw [hP.ntri_ncard X1, hq2, hb0]
    have hXcond : ∀ T' ∈ ({X1, T1, T2} : Set (Set E5)), T' ≠ X1 →
        ∀ Q' ∈ ntri P X1, ¬ Q' ⊆ T' := by
      intro T' hT' hne Q' hQ' hQ'T
      have hT'12 : T' = T1 ∨ T' = T2 := by
        rcases (show T' = X1 ∨ T' = T1 ∨ T' = T2 by simpa using hT') with h | h | h
        · exact absurd h hne
        · exact Or.inl h
        · exact Or.inr h
      have hQ'eq : Q' = Q := by
        rcases hT'12 with h | h
        · rw [h] at hQ'T
          exact uniq T1 hT1f hT13 ht1 hQn1 Q' ⟨hQ'.1, hQ'T, hQ'.2.2.1, hQ'.2.2.2⟩
        · rw [h] at hQ'T
          exact uniq T2 hT2f hT23 ht2 hQn2 Q' ⟨hQ'.1, hQ'T, hQ'.2.2.1, hQ'.2.2.2⟩
      have hQX1 : Q ⊆ X1 := hQ'eq ▸ hQ'.2.1
      have hsub : ({X1, T1, T2} : Set (Set E5)) ⊆
          {T | T ∈ faces P ∧ Q ⊆ T ∧ T ⊆ F ∧ dim T = 3} := by
        intro T'' hT''
        rcases (show T'' = X1 ∨ T'' = T1 ∨ T'' = T2 by simpa using hT'') with h | h | h
        · rw [h]; exact ⟨hX1f, hQX1, hX1F, hX13⟩
        · rw [h]; exact ⟨hT1f, hQT1, hT1F, hT13⟩
        · rw [h]; exact ⟨hT2f, hQT2, hT2F, hT23⟩
      have h3 : ({X1, T1, T2} : Set (Set E5)).ncard = 3 :=
        Set.ncard_eq_three.2 ⟨X1, T1, T2, hX1T1, hX1T2, h12, rfl⟩
      have hle3 := Set.ncard_le_ncard hsub (hP.faces_finite.subset fun T hT => hT.1)
      rw [h3, htwo] at hle3
      norm_num at hle3
    have hle := hP.ntri_le hF h4 hX1f hX1F hX13 {X1, T1, T2} (by simp) hXcond
    have hsubX : ({X1, T1, T2} : Set (Set E5)) ⊆ nsimp P F := by
      intro T hT
      rcases (show T = X1 ∨ T = T1 ∨ T = T2 by simpa using hT) with h | h | h
      · rw [h]; exact ⟨hX1f, hX1F, hX13, Set.nonempty_of_ncard_ne_zero (by omega)⟩
      · rw [h]; exact ⟨hT1f, hT1F, hT13, ⟨Q, hQn1⟩⟩
      · rw [h]; exact ⟨hT2f, hT2F, hT23, ⟨Q, hQn2⟩⟩
    rw [Set.ncard_sdiff hsubX, Set.ncard_eq_three.2 ⟨X1, T1, T2, hX1T1, hX1T2, h12, rfl⟩, hn2,
      ← e4] at hle
    omega
  -- every quadrilateral counts `+1`
  have hq55 : q55w P F = q4 P F := by
    rw [hP.q55w_eq F, hP.q4_eq_card, ← Finset.sum_boole]
    refine Finset.sum_congr rfl fun Q hQ => ?_
    by_cases h4Q : cnt P Q 0 = 4
    · rw [if_pos h4Q, if_neg (hno55 Q hQ h4Q), if_pos h4Q]
    · rw [if_neg h4Q, if_neg h4Q]
  rw [hq55, hq4, hexc]
  norm_num

end cs

end Kalai5
