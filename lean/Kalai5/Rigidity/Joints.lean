import Kalai5.Rigidity.SliceFaces

/-!
# Whiteley's statements and joints on edges

* `bars2 R J`: pairs of points of `J` lying in a common `2`-face of `R`.
* `WProp k`: for every polytope `R` of dimension `k` (in any `E n`), `bars2 R (vert R)` braces
  `vert R` (Whiteley's theorem for the `2`-skeleton with braced `2`-faces).
* `WJProp k`: the same with finitely many extra joints on edges.
* `wj_of_w` (Whiteley Cor 4.4 / 8.3): `WProp k → WJProp k` for `k ≥ 2`.  A joint `j` on an edge
  `[p, q]` is added by a Henneberg step: the vertices of the `2`-faces containing `[p, q]` span the
  directions (`vectorSpan_le_twoFaces`), and `j` is joined to all of them.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

/-- The `2`-faces of `R`. -/
def twoFaces (R : Set (E n)) : Set (Set (E n)) := {G | G ∈ faces R ∧ dim G = 2}

/-- Pairs of points of `J` lying in a common `2`-face of `R`. -/
def bars2 (R J : Set (E n)) : Set (Sym2 (E n)) := ⋃ G ∈ twoFaces R, pairs (J ∩ G)

lemma mem_bars2 {R J : Set (E n)} {p q : E n} (hp : p ∈ J) (hq : q ∈ J) {G : Set (E n)}
    (hG : G ∈ twoFaces R) (hpG : p ∈ G) (hqG : q ∈ G) : s(p, q) ∈ bars2 R J :=
  Set.mem_biUnion hG ⟨p, ⟨hp, hpG⟩, q, ⟨hq, hqG⟩, rfl⟩

lemma bars2_mono {R J J' : Set (E n)} (h : J ⊆ J') : bars2 R J ⊆ bars2 R J' := by
  intro b hb
  simp only [bars2, Set.mem_iUnion] at hb ⊢
  obtain ⟨G, hG, p, hp, q, hq, rfl⟩ := hb
  exact ⟨G, hG, p, ⟨h hp.1, hp.2⟩, q, ⟨h hq.1, hq.2⟩, rfl⟩

/-- **Whiteley's statement** in dimension `k`. -/
def WProp (k : ℕ) : Prop :=
  ∀ (m : ℕ) (V : Finset (E m)), dim (convexHull ℝ (V : Set (E m))) = k →
    Braces (bars2 (convexHull ℝ (V : Set (E m))) ((convexHull ℝ (V : Set (E m))).extremePoints ℝ))
      ((convexHull ℝ (V : Set (E m))).extremePoints ℝ)

/-- **Whiteley's statement with joints on edges** in dimension `k`. -/
def WJProp (k : ℕ) : Prop :=
  ∀ (m : ℕ) (V : Finset (E m)), dim (convexHull ℝ (V : Set (E m))) = k →
    ∀ J : Finset (E m), (∀ j ∈ J, ∃ F ∈ faces (convexHull ℝ (V : Set (E m))), dim F = 1 ∧ j ∈ F) →
      Braces (bars2 (convexHull ℝ (V : Set (E m)))
          ((convexHull ℝ (V : Set (E m))).extremePoints ℝ ∪ (J : Set (E m))))
        ((convexHull ℝ (V : Set (E m))).extremePoints ℝ ∪ (J : Set (E m)))

/-- The vertices of a polytope, as a finset. -/
noncomputable def vertFinset (V : Finset (E n)) : Finset (E n) := (extremePoints_finite V).toFinset

lemma coe_vertFinset (V : Finset (E n)) :
    (vertFinset V : Set (E n)) = (convexHull ℝ (V : Set (E n))).extremePoints ℝ :=
  Set.Finite.coe_toFinset _

lemma convexHull_vertFinset (V : Finset (E n)) :
    convexHull ℝ (vertFinset V : Set (E n)) = convexHull ℝ (V : Set (E n)) := by
  rw [coe_vertFinset]; exact convexHull_extremePoints_eq V

/-- An edge is the segment between its two vertices. -/
lemma exists_ends_of_edge {V : Finset (E n)} {F : Set (E n)}
    (hF : F ∈ faces (convexHull ℝ (V : Set (E n)))) (hF1 : dim F = 1) :
    ∃ p q, p ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ ∧
      q ∈ (convexHull ℝ (V : Set (E n))).extremePoints ℝ ∧ p ≠ q ∧ p ∈ F ∧ q ∈ F ∧
      F ⊆ convexHull ℝ {p, q} := by
  classical
  set T := V.filter (· ∈ F)
  have hFT : F = convexHull ℝ (T : Set (E n)) := face_eq_convexHull_filter hF
  have h2 := ncard_extremePoints_of_dim_one T (by rw [← hFT]; exact hF1)
  rw [← hFT] at h2
  obtain ⟨p, q, hpq, hpqs⟩ := Set.ncard_eq_two.1 h2
  have hp : p ∈ F.extremePoints ℝ := by rw [hpqs]; simp
  have hq : q ∈ F.extremePoints ℝ := by rw [hpqs]; simp
  have hext : F.extremePoints ℝ ⊆ (convexHull ℝ (V : Set (E n))).extremePoints ℝ :=
    hF.2.isExtreme.extremePoints_subset_extremePoints
  refine ⟨p, q, hext hp, hext hq, hpq, hp.1, hq.1, ?_⟩
  have := convexHull_extremePoints_eq T
  rw [← hFT, hpqs] at this
  rw [← this]

/-- **Joints on edges** (Whiteley Cor 4.4, Cor 8.3). -/
theorem wj_of_w {k : ℕ} (hk : 2 ≤ k) (hW : WProp k) : WJProp k := by
  classical
  intro m V hdim J hJ
  have hVne : V.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    have h0 : dim (convexHull ℝ ((∅ : Finset (E m)) : Set (E m))) = 0 := by
      rw [Finset.coe_empty, convexHull_empty]; simp [dim]
    omega
  set R := convexHull ℝ (V : Set (E m))
  set X0 := R.extremePoints ℝ
  set B := bars2 R (X0 ∪ (J : Set (E m)))
  set V' := vertFinset V
  have hV'R : convexHull ℝ (V' : Set (E m)) = R := convexHull_vertFinset V
  have hV'X : (V' : Set (E m)) = X0 := coe_vertFinset V
  have hX0ne : X0.Nonempty := exists_extremePoint hVne
  have hXR : X0 ⊆ R := fun x hx => hx.1
  have hvsR : vectorSpan ℝ R = vectorSpan ℝ X0 := by
    rw [← hV'X, ← hV'R, ← direction_affineSpan, ← direction_affineSpan, affineSpan_convexHull]
  -- the joints lie in `R`
  have hJR : ∀ j ∈ J, j ∈ R := fun j hj => by
    obtain ⟨F, hF, -, hjF⟩ := hJ j hj
    exact face_subset hF hjF
  suffices key : ∀ J' : Finset (E m), J' ⊆ J → Braces B (X0 ∪ (J' : Set (E m))) by
    exact key J subset_rfl
  intro J'
  induction J' using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.coe_empty, union_empty]
    exact (hW m V hdim).mono (bars2_mono subset_union_left) subset_rfl
  | insert j J' hjJ' ih =>
    intro hsub
    have hIH := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hjJ : j ∈ J := hsub (Finset.mem_insert_self j J')
    have hset : X0 ∪ ((insert j J' : Finset (E m)) : Set (E m)) = insert j (X0 ∪ (J' : Set (E m))) := by
      ext x; simp only [Finset.coe_insert, mem_union, mem_insert_iff]; tauto
    rw [hset]
    by_cases hjX : j ∈ X0
    · rw [Set.insert_eq_of_mem (show j ∈ X0 ∪ (J' : Set (E m)) from Or.inl hjX)]; exact hIH
    -- `j` lies on an edge `[p, q]`
    obtain ⟨F, hF, hF1, hjF⟩ := hJ j hjJ
    obtain ⟨p, q, hp, hq, hpq, hpF, hqF, hFpq⟩ := exists_ends_of_edge hF hF1
    set X := {z | z ∈ V' ∧ ∃ G ∈ faces (convexHull ℝ (V' : Set (E m))), dim G = 2 ∧ p ∈ G ∧
      q ∈ G ∧ z ∈ G}
    have hpV' : p ∈ V' := by rw [← Finset.mem_coe, hV'X]; exact hp
    have hqV' : q ∈ V' := by rw [← Finset.mem_coe, hV'X]; exact hq
    have hspanX : vectorSpan ℝ (V' : Set (E m)) ≤ Submodule.span ℝ ((fun z => z - p) '' X) :=
      vectorSpan_le_twoFaces (V := V') (a₀ := p) (q := q)
      (by rw [hV'R]; exact hp) hqV' hpq.symm (by rw [hV'R]; exact hF) hF1 hpF hqF
      (by rw [hV'R]; omega)
    -- `p ∈ X`
    have hXne : X.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      rw [hcon, Set.image_empty, Submodule.span_empty, le_bot_iff] at hspanX
      have : dim R = 0 := by
        rw [← hV'R, dim_convexHull']; unfold dim; rw [hspanX, finrank_bot]
      omega
    obtain ⟨z₀, -, G₀, hG₀, hG₀2, hpG₀, hqG₀, -⟩ := hXne
    have hpX : p ∈ X := ⟨hpV', G₀, hG₀, hG₀2, hpG₀, hqG₀, hpG₀⟩
    refine (hIH.henneberg (X := X) ⟨_, Or.inl hX0ne.some_mem⟩ ?_ ?_ ?_).mono ?_ subset_rfl
    · -- `j` lies in the affine span
      calc vectorSpan ℝ (insert j (X0 ∪ (J' : Set (E m))))
          ≤ vectorSpan ℝ R := vectorSpan_mono ℝ (by
            rintro x (rfl | hx | hx)
            · exact hJR x hjJ
            · exact hXR hx
            · exact hJR x (hsub (Finset.mem_insert_of_mem hx)))
        _ = vectorSpan ℝ X0 := hvsR
        _ ≤ vectorSpan ℝ (X0 ∪ (J' : Set (E m))) := vectorSpan_mono ℝ subset_union_left
    · intro z hz
      exact Or.inl (by rw [← hV'X]; exact hz.1)
    · -- the bars at `j` span the directions
      calc vectorSpan ℝ (X0 ∪ (J' : Set (E m)))
          ≤ vectorSpan ℝ R := vectorSpan_mono ℝ (by
            rintro x (hx | hx)
            · exact hXR hx
            · exact hJR x (hsub (Finset.mem_insert_of_mem hx)))
        _ = vectorSpan ℝ (V' : Set (E m)) := by rw [hvsR, hV'X]
        _ ≤ Submodule.span ℝ ((fun z => z - p) '' X) := hspanX
        _ ≤ Submodule.span ℝ ((fun x => j - x) '' X) := by
          rw [Submodule.span_le]
          rintro _ ⟨z, hz, rfl⟩
          dsimp only
          have e : z - p = (j - p) - (j - z) := by abel
          rw [SetLike.mem_coe, e]
          exact Submodule.sub_mem _ (Submodule.subset_span ⟨p, hpX, rfl⟩)
            (Submodule.subset_span ⟨z, hz, rfl⟩)
    · -- the new bars lie in `2`-faces containing the edge
      rintro b (hb | ⟨z, ⟨hzV', G, hG, hG2, hpG, hqG, hzG⟩, rfl⟩)
      · exact hb
      · rw [hV'R] at hG
        have hjG : j ∈ G := by
          have hconv : Convex ℝ G := face_convex (convex_convexHull ℝ _) hG
          exact convexHull_min (by
            rintro x (rfl | rfl)
            · exact hpG
            · exact hqG) hconv (hFpq hjF)
        exact mem_bars2 (Or.inr (by exact_mod_cast hjJ)) (Or.inl (by rw [← hV'X]; exact hzV'))
          ⟨hG, hG2⟩ hjG hzG

end Kalai5
