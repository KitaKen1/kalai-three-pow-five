import Kalai5.FullProd.UPolar

/-!
# The facet `U` at eighteen vertices: the configuration and its two cases

`UConf P`: a facet `U` (row `(9, 19, 17, 7; 38)`) of a cs 5-polytope `P` with eighteen vertices,
its nine vertices `x i`, its seven 3-faces `G j` with `x i ∈ G j ↔ j ∈ uInc i`, and the vertex set
`X = {±x i}` of `P`.  In the canonical labels the two prisms are `G 3`, `G 4` with the product
edges `A = [x 2, x 7]`, `B = [x 3, x 8]` (common), `C = [x 0, x 4]` (in `G 3`), `D = [x 1, x 5]`
(in `G 4`); the pentagon `G 1 ∩ G 2` contains `C`, `D` and `z = x 6`.

`UConf.lines`: the four lines of `A, B, C, D` pass through one point or are parallel (the quadrilateral
faces make them pairwise coplanar, the prisms are 3-dimensional; `ULines`).
-/

namespace Kalai5

open Set Module Submodule

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- The facet `U` of a cs 5-polytope with eighteen vertices, with its canonical labels. -/
structure UConf (P : Set E5) where
  U : Set E5
  hU : U ∈ faces P
  hU4 : dim U = 4
  x : Fin 9 → E5
  G : Fin 7 → Set E5
  inj : Function.Injective x
  xext : ∀ i, x i ∈ U.extremePoints ℝ
  hG : ∀ j, G j ∈ faces P ∧ G j ⊆ U ∧ dim (G j) = 3
  inc : ∀ i j, x i ∈ G j ↔ j ∈ uInc i
  X : Finset E5
  hPX : P = convexHull ℝ (X : Set E5)
  extX : (X : Set E5) = P.extremePoints ℝ
  memX : ∀ v ∈ X, ∃ i, v = x i ∨ v = -x i
  xX : ∀ i, x i ∈ X ∧ -x i ∈ X

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **The configuration exists** for a facet with row `(9, 19, 17, 7; 38)` at eighteen vertices. -/
theorem IsCSPolytope5.uConf (hv : fvec P 0 = 18) {U : Set E5} (hU : U ∈ faces P)
    (h4 : dim U = 4) (hrow : faceRow P U = ⟨9, 19, 17, 7, 38⟩) : Nonempty (UConf P) := by
  obtain ⟨x, G, hinj, hx, -, hG, hinc⟩ := hP.u_structure hU h4 hrow
  obtain ⟨X, hPX, hextX, hmemX, hxX⟩ := hP.vertices_pm hv hU h4 hinj hx
  exact ⟨⟨U, hU, h4, x, G, hinj, hx, hG, hinc, X, hPX, hextX, hmemX, hxX⟩⟩

end cs

namespace UConf

variable {P : Set E5} (C : UConf P)

lemma xU (i : Fin 9) : C.x i ∈ C.U := (C.xext i).1

lemma xP (i : Fin 9) : C.x i ∈ P.extremePoints ℝ := by
  have := C.xext i
  rw [C.hU.2.isExtreme.extremePoints_eq] at this
  exact this.2

/-- The plane of a 2-face `G j ∩ G k`. -/
lemma plane {j k : Fin 7} {a b : Fin 9} (ha : j ∈ uInc a ∧ k ∈ uInc a)
    (hb : j ∈ uInc b ∧ k ∉ uInc b) : finrank ℝ (vectorSpan ℝ (C.G j ∩ C.G k)) ≤ 2 :=
  finrank_inter_le_two (C.hG j).1 (C.hG j).2.2 (C.hG k).1 ((C.inc a j).2 ha.1)
    ((C.inc a k).2 ha.2) ((C.inc b j).2 hb.1) (fun h => hb.2 ((C.inc b k).1 h))

lemma mem_plane {j k : Fin 7} {a b : Fin 9} (ha : j ∈ uInc a ∧ k ∈ uInc a)
    (hb : j ∈ uInc b ∧ k ∈ uInc b) : C.x a - C.x b ∈ vectorSpan ℝ (C.G j ∩ C.G k) :=
  vsub_mem_vectorSpan ℝ ⟨(C.inc a j).2 ha.1, (C.inc a k).2 ha.2⟩
    ⟨(C.inc b j).2 hb.1, (C.inc b k).2 hb.2⟩

/-- Three distinct vertices are not collinear. -/
lemma indep {a b c : Fin 9} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    LinearIndependent ℝ ![C.x b - C.x a, C.x c - C.x a] :=
  linIndep_of_three (C.xP a) (C.xP b) (C.xP c) (C.inj.ne hab) (C.inj.ne hac) (C.inj.ne hbc)

lemma sub_ne {a b : Fin 9} (h : a ≠ b) : C.x a - C.x b ≠ 0 := sub_ne_zero.2 (C.inj.ne h)

section cs

variable (hP : IsCSPolytope5 P)
include hP

lemma neg_not_mem_U (i : Fin 9) : -C.x i ∉ C.U := fun h =>
  (hP.ne_of_dim_ne (by rw [C.hU4]; norm_num) : C.U ≠ P) (hP.eq_of_mem_of_neg_mem C.hU (C.xU i) h)

/-- A 3-face spans three dimensions: any subspace containing the differences of its vertices has
dimension at least three. -/
lemma span_facet (j : Fin 7) (i0 : Fin 9) (S : Submodule ℝ E5)
    (h : ∀ i, j ∈ uInc i → C.x i - C.x i0 ∈ S) : 3 ≤ finrank ℝ S := by
  have hG := C.hG j
  have hGX : C.G j ∈ faces (convexHull ℝ (C.X : Set E5)) := by rw [← C.hPX]; exact hG.1
  have hle : vectorSpan ℝ (C.G j) ≤ S := vectorSpan_face_le hGX (p := C.x i0) fun v hv hvG => by
    obtain ⟨i, rfl | rfl⟩ := C.memX v hv
    · exact h i ((C.inc i j).1 hvG)
    · exact absurd (hG.2.1 hvG) (C.neg_not_mem_U hP i)
  exact hG.2.2.symm.le.trans (Submodule.finrank_mono hle)

lemma span_G3 (S : Submodule ℝ E5) (i0 : Fin 9) (h0 : C.x 0 - C.x i0 ∈ S)
    (h2 : C.x 2 - C.x i0 ∈ S) (h3 : C.x 3 - C.x i0 ∈ S) (h4 : C.x 4 - C.x i0 ∈ S)
    (h7 : C.x 7 - C.x i0 ∈ S) (h8 : C.x 8 - C.x i0 ∈ S) : 3 ≤ finrank ℝ S :=
  C.span_facet hP 3 i0 S fun i hi => by
    fin_cases i <;> first | exact absurd hi (by decide) | assumption

lemma span_G4 (S : Submodule ℝ E5) (i0 : Fin 9) (h1 : C.x 1 - C.x i0 ∈ S)
    (h2 : C.x 2 - C.x i0 ∈ S) (h3 : C.x 3 - C.x i0 ∈ S) (h5 : C.x 5 - C.x i0 ∈ S)
    (h7 : C.x 7 - C.x i0 ∈ S) (h8 : C.x 8 - C.x i0 ∈ S) : 3 ≤ finrank ℝ S :=
  C.span_facet hP 4 i0 S fun i hi => by
    fin_cases i <;> first | exact absurd hi (by decide) | assumption

/-- **Witness** of the 3-face `G j`: zero on its vertices, positive on the other vertices of `U`. -/
lemma witness (j : Fin 7) : ∃ ψ : E5, ∀ i,
    (j ∈ uInc i → ⟪C.x i, ψ⟫ = 0) ∧ (j ∉ uInc i → 0 < ⟪C.x i, ψ⟫) := by
  have hUP : C.U ≠ P := hP.ne_of_dim_ne (by rw [C.hU4]; norm_num)
  have hGP : C.G j ≠ P := hP.ne_of_dim_ne (by rw [(C.hG j).2.2]; norm_num)
  obtain ⟨ψ, hψ⟩ := hP.exists_witness C.hU hUP (C.hG j).1 hGP
  exact ⟨ψ, fun i => ⟨fun h => (hψ _ (C.xU i)).1 ((C.inc i j).2 h),
    fun h => (hψ _ (C.xU i)).2 (fun h' => h ((C.inc i j).1 h'))⟩⟩

/-- The vertices span `ℝ⁵`. -/
lemma span_top (S : Submodule ℝ E5) (h0 : C.x 0 ∈ S) (h1 : C.x 1 ∈ S) (h2 : C.x 2 ∈ S)
    (h3 : C.x 3 ∈ S) (h4 : C.x 4 ∈ S) (h5 : C.x 5 ∈ S) (h6 : C.x 6 ∈ S) (h7 : C.x 7 ∈ S)
    (h8 : C.x 8 ∈ S) : S = ⊤ := by
  have hall : ∀ i, C.x i ∈ S := fun i => by
    fin_cases i
    exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  have h0int : (0 : E5) ∈ interior (convexHull ℝ (C.X : Set E5)) := by
    rw [← C.hPX]; exact hP.zero_mem_interior
  have htop := span_extremePoints_eq_top h0int
  rw [← C.hPX, ← C.extX] at htop
  rw [eq_top_iff, ← htop, Submodule.span_le]
  intro v hv
  obtain ⟨i, rfl | rfl⟩ := C.memX v hv
  · exact hall i
  · exact neg_mem (hall i)

/-- **The four product edges are concurrent or parallel.** -/
theorem lines :
    (∃ p : E5, ∃ sA sB sC sD : ℝ, p = C.x 2 + sA • (C.x 7 - C.x 2) ∧
      p = C.x 3 + sB • (C.x 8 - C.x 3) ∧ p = C.x 0 + sC • (C.x 4 - C.x 0) ∧
      p = C.x 1 + sD • (C.x 5 - C.x 1)) ∨
    (∃ μB μC μD : ℝ, C.x 8 - C.x 3 = μB • (C.x 7 - C.x 2) ∧
      C.x 4 - C.x 0 = μC • (C.x 7 - C.x 2) ∧ C.x 5 - C.x 1 = μD • (C.x 7 - C.x 2)) := by
  -- the planes of the quadrilaterals
  have f34 := C.plane (j := 3) (k := 4) (a := 2) (b := 0) (by decide) (by decide)
  have f31 := C.plane (j := 3) (k := 1) (a := 2) (b := 3) (by decide) (by decide)
  have f32 := C.plane (j := 3) (k := 2) (a := 3) (b := 2) (by decide) (by decide)
  have f41 := C.plane (j := 4) (k := 1) (a := 2) (b := 3) (by decide) (by decide)
  have f42 := C.plane (j := 4) (k := 2) (a := 3) (b := 2) (by decide) (by decide)
  have m34A : C.x 7 - C.x 2 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 4) := C.mem_plane (by decide) (by decide)
  have m34B : C.x 8 - C.x 3 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 4) := C.mem_plane (by decide) (by decide)
  have m34 : C.x 3 - C.x 2 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 4) := C.mem_plane (by decide) (by decide)
  have m31A : C.x 7 - C.x 2 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m31C : C.x 4 - C.x 0 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m31 : C.x 0 - C.x 2 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m32B : C.x 8 - C.x 3 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have m32C : C.x 4 - C.x 0 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have m32 : C.x 0 - C.x 3 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have m41A : C.x 7 - C.x 2 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m41D : C.x 5 - C.x 1 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m41 : C.x 1 - C.x 2 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 1) := C.mem_plane (by decide) (by decide)
  have m42B : C.x 8 - C.x 3 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have m42D : C.x 5 - C.x 1 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have m42 : C.x 1 - C.x 3 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 2) := C.mem_plane (by decide) (by decide)
  have hA0 := C.sub_ne (a := 7) (b := 2) (by decide)
  have hB0 := C.sub_ne (a := 8) (b := 3) (by decide)
  have hC0 := C.sub_ne (a := 4) (b := 0) (by decide)
  have hD0 := C.sub_ne (a := 5) (b := 1) (by decide)
  have h00 : C.x 0 - C.x 0 = 0 := sub_self _
  have h11 : C.x 1 - C.x 1 = 0 := sub_self _
  have h22 : C.x 2 - C.x 2 = 0 := sub_self _
  by_cases hind : LinearIndependent ℝ ![C.x 7 - C.x 2, C.x 8 - C.x 3]
  · -- the lines `A`, `B` meet at `p`; the third line of each prism passes through `p`
    left
    obtain ⟨sA, sB, hs⟩ := lines_meet f34 m34A m34B m34 hind
    set p := C.x 2 + sA • (C.x 7 - C.x 2) with hp
    obtain ⟨sC, hsC⟩ := lines_concurrent (p := p) (d0 := C.x 7 - C.x 2) (d1 := C.x 8 - C.x 3)
      (a2 := C.x 0) (d2 := C.x 4 - C.x 0) f31 f32
      ⟨m31A, by
        have e : C.x 0 - p = (C.x 0 - C.x 2) - sA • (C.x 7 - C.x 2) := by rw [hp]; module
        rw [e]; exact sub_mem m31 (smul_mem _ _ m31A), m31C⟩
      ⟨m32B, by
        have e : C.x 0 - p = (C.x 0 - C.x 3) - sB • (C.x 8 - C.x 3) := by rw [hs]; module
        rw [e]; exact sub_mem m32 (smul_mem _ _ m32B), m32C⟩
      (C.span_G3 hP _ 0 (by rw [h00]; exact zero_mem _)
        (mem_span4 (-sA) 0 (-1) 0 (by rw [hp]; module))
        (mem_span4 0 (-sB) (-1) 0 (by rw [hs]; module))
        (mem_span4 0 0 0 1 (by module))
        (mem_span4 (1 - sA) 0 (-1) 0 (by rw [hp]; module))
        (mem_span4 0 (1 - sB) (-1) 0 (by rw [hs]; module))) hC0
    obtain ⟨sD, hsD⟩ := lines_concurrent (p := p) (d0 := C.x 7 - C.x 2) (d1 := C.x 8 - C.x 3)
      (a2 := C.x 1) (d2 := C.x 5 - C.x 1) f41 f42
      ⟨m41A, by
        have e : C.x 1 - p = (C.x 1 - C.x 2) - sA • (C.x 7 - C.x 2) := by rw [hp]; module
        rw [e]; exact sub_mem m41 (smul_mem _ _ m41A), m41D⟩
      ⟨m42B, by
        have e : C.x 1 - p = (C.x 1 - C.x 3) - sB • (C.x 8 - C.x 3) := by rw [hs]; module
        rw [e]; exact sub_mem m42 (smul_mem _ _ m42B), m42D⟩
      (C.span_G4 hP _ 1 (by rw [h11]; exact zero_mem _)
        (mem_span4 (-sA) 0 (-1) 0 (by rw [hp]; module))
        (mem_span4 0 (-sB) (-1) 0 (by rw [hs]; module))
        (mem_span4 0 0 0 1 (by module))
        (mem_span4 (1 - sA) 0 (-1) 0 (by rw [hp]; module))
        (mem_span4 0 (1 - sB) (-1) 0 (by rw [hs]; module))) hD0
    exact ⟨p, sA, sB, sC, sD, hp, hs, hsC, hsD⟩
  · -- `A ∥ B`; then `C` and `D` are parallel to them
    right
    rw [LinearIndependent.pair_iff] at hind
    push_neg at hind
    obtain ⟨s, t, hst, hne⟩ := hind
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hA0 ((smul_eq_zero.1 hst).resolve_left fun hs0 => hne hs0 ht0)
    set μB := -(s / t) with hμBdef
    have hμB : C.x 8 - C.x 3 = μB • (C.x 7 - C.x 2) := by
      have h' : t • (C.x 8 - C.x 3) = -(s • (C.x 7 - C.x 2)) := eq_neg_of_add_eq_zero_right hst
      have := congrArg (fun z => t⁻¹ • z) h'
      simp only [smul_smul, inv_mul_cancel₀ ht, one_smul] at this
      rw [this, smul_neg, smul_smul, hμBdef, neg_smul, div_eq_inv_mul]
    have hμB0 : μB ≠ 0 := fun h => hB0 (by rw [hμB, h, zero_smul])
    have hAB : C.x 7 - C.x 2 = μB⁻¹ • (C.x 8 - C.x 3) := by
      rw [hμB, smul_smul, inv_mul_cancel₀ hμB0, one_smul]
    have m32A : C.x 7 - C.x 2 ∈ vectorSpan ℝ (C.G 3 ∩ C.G 2) := by
      rw [hAB]; exact smul_mem _ _ m32B
    have m42A : C.x 7 - C.x 2 ∈ vectorSpan ℝ (C.G 4 ∩ C.G 2) := by
      rw [hAB]; exact smul_mem _ _ m42B
    obtain ⟨μC, hμC⟩ := lines_parallel (a0 := C.x 2) (d0 := C.x 7 - C.x 2) (a1 := C.x 3)
      (a2 := C.x 0) (d2 := C.x 4 - C.x 0) f31 f32 ⟨m31A, m31, m31C⟩ ⟨m32A, m32, m32C⟩
      (C.span_G3 hP _ 2 (mem_span4 0 0 1 0 (by module)) (by rw [h22]; exact zero_mem _)
        (mem_span4 0 1 0 0 (by module)) (mem_span4 0 0 1 1 (by module))
        (mem_span4 1 0 0 0 (by module))
        (mem_span4 μB 1 0 0 (by linear_combination (norm := module) hμB))) hA0
    obtain ⟨μD, hμD⟩ := lines_parallel (a0 := C.x 2) (d0 := C.x 7 - C.x 2) (a1 := C.x 3)
      (a2 := C.x 1) (d2 := C.x 5 - C.x 1) f41 f42 ⟨m41A, m41, m41D⟩ ⟨m42A, m42, m42D⟩
      (C.span_G4 hP _ 2 (mem_span4 0 0 1 0 (by module)) (by rw [h22]; exact zero_mem _)
        (mem_span4 0 1 0 0 (by module)) (mem_span4 0 0 1 1 (by module))
        (mem_span4 1 0 0 0 (by module))
        (mem_span4 μB 1 0 0 (by linear_combination (norm := module) hμB))) hA0
    exact ⟨μB, μC, μD, hμB, hμC, hμD⟩

end cs

end UConf

end Kalai5
