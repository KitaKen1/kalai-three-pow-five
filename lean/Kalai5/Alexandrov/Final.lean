import Kalai5.Alexandrov.Main

/-!
# Alexandrov's theorem: the count

`all_dead`: a motion of the `2`-face bars of a `3`-polytope with three dead vertices has all its
vertices dead.  `alexandrov3_proof : WProp 3`.
-/

namespace Kalai5

open Set Module

local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {n : ℕ}

open Classical in
/-- **The count.** -/
theorem all_dead {V : Finset (E n)} (hcp : ConvPos V)
    (h3 : dim (convexHull ℝ (V : Set (E n))) = 3) {a : E n → E n}
    (hmot : ∀ G ∈ twoFinset V, ∀ p ∈ facePts V G, ∀ q ∈ facePts V G, ⟪a p - a q, p - q⟫ = 0)
    (hD3 : 3 ≤ (V.filter fun v => ∀ w ∈ V, ⟪w - v, a v⟫ = 0).card) :
    ∀ v ∈ V, ∀ w ∈ V, ⟪w - v, a v⟫ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨v₀, hv₀, w₀, hw₀, hne⟩ := hcon
  set D := V.filter fun v => ∀ w ∈ V, ⟪w - v, a v⟫ = 0 with hD
  set L := V.filter fun v => ¬ ∀ w ∈ V, ⟪w - v, a v⟫ = 0 with hL
  -- the corner weight
  let c : E n → Set (E n) → ℕ := fun v G =>
    2 * (posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v *
      negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) +
      zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v
  have hpoly : ∀ G ∈ twoFinset V, ConvPos (facePts V G) ∧
      dim (convexHull ℝ (facePts V G : Set (E n))) = 2 := fun G hG =>
    ⟨convPos_facePts hcp (mem_twoFinset.1 hG).1,
      by rw [← facePts_hull (mem_twoFinset.1 hG).1]; exact (mem_twoFinset.1 hG).2⟩
  -- double counting of corners
  have hdc : ∑ v ∈ V, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G =
      ∑ G ∈ twoFinset V, ∑ v ∈ facePts V G, c v G := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [facePts_eq_filter, Finset.sum_filter]
  -- a dead corner weighs `2`
  have hdeadc : ∀ v ∈ D, ∀ G ∈ twoFinset V, v ∈ G → c v G = 2 := by
    intro v hv G hG hvG
    obtain ⟨hvV, hvd⟩ := Finset.mem_filter.1 hv
    obtain ⟨hcpG, h2G⟩ := hpoly G hG
    have hvT : v ∈ facePts V G := mem_facePts.2 ⟨hvV, hvG⟩
    have hzero : ∀ w ∈ nbrs (facePts V G) v, ⟪w - v, a v⟫ = 0 := fun w hw =>
      hvd w (mem_facePts.1 (mem_nbrs.1 hw).1).1
    have hZ : zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v = 2 := by
      rw [← card_nbrs hcpG h2G hvT]
      unfold zerC
      congr 1
      exact Finset.filter_true_of_mem hzero
    have hP : posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v = 0 := by
      unfold posC
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro w hw h
      beta_reduce at h
      rw [hzero w hw] at h
      exact lt_irrefl _ h
    show 2 * (posC (facePts V G) (fun v w => ⟪w - v, a v⟫) v *
      negC (facePts V G) (fun v w => ⟪w - v, a v⟫) v) +
      zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v = 2
    rw [hP, hZ, zero_mul, mul_zero, zero_add]
  -- the vertex side
  have hvert : ∑ v ∈ V, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G ≤
      4 * L.card + 2 * ∑ G ∈ twoFinset V, (facePts D G).card := by
    have hsplitV : ∑ v ∈ D, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G +
        ∑ v ∈ L, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G =
        ∑ v ∈ V, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G :=
      Finset.sum_filter_add_sum_filter_not V _ _
    rw [← hsplitV]
    have hlive : ∑ v ∈ L, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G ≤ 4 * L.card := by
      rw [mul_comm, ← smul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun v hv => ?_
      obtain ⟨hvV, hvl⟩ := Finset.mem_filter.1 hv
      push_neg at hvl
      exact vertex_side hcp h3 a hvV hvl
    have hdead : ∑ v ∈ D, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G =
        2 * ∑ G ∈ twoFinset V, (facePts D G).card := by
      calc ∑ v ∈ D, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), c v G
          = ∑ v ∈ D, ∑ G ∈ (twoFinset V).filter (fun G => v ∈ G), 2 :=
            Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun G hG =>
              hdeadc v hv G (Finset.mem_filter.1 hG).1 (Finset.mem_filter.1 hG).2
        _ = 2 * ∑ v ∈ D, ((twoFinset V).filter (fun G => v ∈ G)).card := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
        _ = 2 * ∑ G ∈ twoFinset V, (facePts D G).card := by
            congr 1
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun G _ => ?_
            rw [facePts_eq_filter, Finset.card_filter]
    rw [hdead]
    omega
  -- the face side
  have hface : ∀ G ∈ twoFinset V,
      2 * (facePts V G).card + 2 * min (facePts D G).card 2 ≤ ∑ v ∈ facePts V G, c v G + 4 := by
    intro G hG
    obtain ⟨hcpG, h2G⟩ := hpoly G hG
    have hfil : (facePts V G).filter (fun v => ∀ w ∈ V, ⟪w - v, a v⟫ = 0) = facePts D G := by
      ext v
      simp only [Finset.mem_filter, mem_facePts, hD]
      tauto
    have hdeadZ : ∀ v ∈ facePts V G, (∀ w ∈ V, ⟪w - v, a v⟫ = 0) →
        zerC (facePts V G) (fun v w => ⟪w - v, a v⟫) v = 2 := by
      intro v hvT hvd
      rw [← card_nbrs hcpG h2G hvT]
      unfold zerC
      congr 1
      exact Finset.filter_true_of_mem fun w hw => hvd w (mem_facePts.1 (mem_nbrs.1 hw).1).1
    have := face_side hcpG h2G (hmot G hG) (fun v => ∀ w ∈ V, ⟪w - v, a v⟫ = 0) hdeadZ
    rw [hfil] at this
    exact this
  have hfaceSum : 2 * ∑ G ∈ twoFinset V, (facePts V G).card +
      2 * ∑ G ∈ twoFinset V, min (facePts D G).card 2 ≤
      ∑ G ∈ twoFinset V, ∑ v ∈ facePts V G, c v G + 4 * (twoFinset V).card := by
    have := Finset.sum_le_sum hface
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, smul_eq_mul] at this
    linarith
  -- Euler and the inactive bound
  have heuler := sum_facePts_sub_two hcp h3
  have heuler' : ∑ G ∈ twoFinset V, (facePts V G).card + 4 = 2 * (twoFinset V).card + 2 * V.card := by
    have : ((∑ G ∈ twoFinset V, (facePts V G).card : ℕ) : ℤ) =
        2 * (twoFinset V).card + 2 * V.card - 4 := by push_cast; exact heuler
    omega
  have hv₀D : v₀ ∉ D := fun h => hne ((Finset.mem_filter.1 h).2 w₀ hw₀)
  have hinact : ∑ G ∈ twoFinset V, ((facePts D G).card - 2) + 5 ≤ 2 * D.card :=
    inactive_bound hcp h3 (Finset.filter_subset _ V) hD3 hv₀ hv₀D
  have hsplitD : ∑ G ∈ twoFinset V, (facePts D G).card =
      ∑ G ∈ twoFinset V, min (facePts D G).card 2 + ∑ G ∈ twoFinset V, ((facePts D G).card - 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun G _ => by omega
  have hLD : D.card + L.card = V.card := Finset.card_filter_add_card_filter_not (s := V) _
  omega

/-- **Alexandrov's theorem** (infinitesimal rigidity of convex `3`-polytopes with braced
`2`-faces). -/
theorem alexandrov3_proof : WProp 3 := by
  intro m V₀ h3₀ u hu p hp q hq
  classical
  set V := vertFinset V₀ with hV
  have hcp : ConvPos V := convPos_vertFinset V₀
  have hconv : convexHull ℝ (V : Set (E m)) = convexHull ℝ (V₀ : Set (E m)) :=
    convexHull_vertFinset V₀
  have h3 : dim (convexHull ℝ (V : Set (E m))) = 3 := by rw [hconv]; exact h3₀
  have hext : (convexHull ℝ (V₀ : Set (E m))).extremePoints ℝ = (V : Set (E m)) :=
    (coe_vertFinset V₀).symm
  -- the motion keeps the pairs inside faces
  have hmot : ∀ G ∈ twoFinset V, ∀ p ∈ facePts V G, ∀ q ∈ facePts V G,
      ⟪u p - u q, p - q⟫ = 0 := by
    intro G hG p hp q hq
    obtain ⟨hGf, hG2⟩ := mem_twoFinset.1 hG
    obtain ⟨hpV, hpG⟩ := mem_facePts.1 hp
    obtain ⟨hqV, hqG⟩ := mem_facePts.1 hq
    have hb := hu _ (mem_bars2 (R := convexHull ℝ (V₀ : Set (E m)))
      (J := (convexHull ℝ (V₀ : Set (E m))).extremePoints ℝ)
      (by rw [hext]; exact_mod_cast hpV) (by rw [hext]; exact_mod_cast hqV)
      (G := G) ⟨by rw [← hconv]; exact hGf, hG2⟩ hpG hqG)
    simpa using hb
  obtain ⟨A, c, hA, h3dead⟩ := exists_normalization hcp h3 hmot
  have hskew0 : ∀ x ∈ vectorSpan ℝ (V : Set (E m)), ⟪A x, x⟫ = 0 := by
    intro x hx
    have := hA x hx x hx
    rw [real_inner_comm (A x) x] at this
    linarith
  set a : E m → E m := fun x => u x - (A x + c) with ha
  have hsplit : ∀ p q : E m, u p - u q = (a p - a q) + A (p - q) := by
    intro p q; simp only [ha, map_sub]; abel
  have hmot' : ∀ G ∈ twoFinset V, ∀ p ∈ facePts V G, ∀ q ∈ facePts V G,
      ⟪a p - a q, p - q⟫ = 0 := by
    intro G hG p hp q hq
    have h1 := hmot G hG p hp q hq
    have hpq : p - q ∈ vectorSpan ℝ (V : Set (E m)) :=
      vsub_mem_vectorSpan ℝ (by exact_mod_cast (mem_facePts.1 hp).1)
        (by exact_mod_cast (mem_facePts.1 hq).1)
    rw [hsplit, inner_add_left, hskew0 _ hpq, add_zero] at h1
    exact h1
  have hall := all_dead hcp h3 hmot' h3dead
  rw [hext] at hp hq
  have hpV : p ∈ V := hp
  have hqV : q ∈ V := hq
  have e1 := hall p hpV q hqV
  have e2 := hall q hqV p hpV
  have hpq : p - q ∈ vectorSpan ℝ (V : Set (E m)) :=
    vsub_mem_vectorSpan ℝ (by exact_mod_cast hpV) (by exact_mod_cast hqV)
  have k1 : ⟪a p, p - q⟫ = 0 := by
    rw [show p - q = -(q - p) by abel, inner_neg_right, real_inner_comm, e1, neg_zero]
  have k2 : ⟪a q, p - q⟫ = 0 := by rw [real_inner_comm, e2]
  rw [hsplit, inner_add_left, inner_sub_left, k1, k2, hskew0 _ hpq, sub_self, add_zero]

end Kalai5
