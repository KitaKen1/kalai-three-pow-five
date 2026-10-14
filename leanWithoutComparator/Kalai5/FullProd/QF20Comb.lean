import Kalai5.FullProd.QF20Aux

/-!
# The strengthened combinatorics of the `Δ2 × Δ2` facet with one extra pair

`card_le_cells_add_three`: a conflict-free set `B` of candidates has
`|B| ≤ max(5, |first(B)| + |second(B)|) + 3`.

Besides `|B| ≤ 12` and `|B| ≤ f s`, the new input is the case `|B| ≥ 11`: in the sign blocks
`EE` and `OO` (with `nE, nO ≤ 3` members, one per diagonal), the second cell is the first cell
shifted by `±(1, 1)`, which keeps the diagonal.  An `EE` member and an `OO` member can share their
first cell or their second cell but not both (`cells_inj`), and only on a common diagonal; hence
`f + s ≥ 2 (nE + nO) - min(nE, nO)`, while `|B| ≤ nE + nO + 6`.
-/

namespace Kalai5

open Set

/-- The diagonal of a cell. -/
def diagC (x : Fin 3 × Fin 3) : Fin 3 := x.2 - x.1

lemma diag_cellS_EE : ∀ c : Idx × Idx, c.1.sgn = true → c.2.sgn = true →
    diagC (cellS c) = diagC (cellF c) := by decide

lemma diag_cellS_OO : ∀ c : Idx × Idx, c.1.sgn = false → c.2.sgn = false →
    diagC (cellS c) = diagC (cellF c) := by decide

lemma tri_eq_of_diag {c d : Idx × Idx} (h1 : c.1.sgn = d.1.sgn) (h2 : c.2.sgn = d.2.sgn)
    (h3 : diagC (cellF c) = diagC (cellF d)) : tri c = tri d := by
  simp only [tri, diagC, cellF] at h3 ⊢
  rw [h1, h2, h3]

/-- **The combinatorial core, strengthened**. -/
theorem card_le_cells_add_three (B : Finset (Idx × Idx))
    (hB : ∀ c ∈ B, ∀ d ∈ B, c.1 ≠ d.1 → c.1.sgn = d.1.sgn → c.2 ≠ d.2 → c.2.sgn = d.2.sgn → False) :
    B.card ≤ max 5 ((B.image cellF).card + (B.image cellS).card) + 3 := by
  classical
  have htri : Set.InjOn tri (B : Set (Idx × Idx)) := by
    intro c hc d hd hcd
    by_contra hne
    obtain ⟨h1, h2, h3, h4⟩ := tri_conflict c d hcd hne
    exact hB c hc d hd h1 h2 h3 h4
  have h12 : B.card ≤ 12 := by
    have := Finset.card_le_card_of_injOn tri (t := Finset.univ) (fun _ _ => Finset.mem_coe.2
      (Finset.mem_univ _)) htri
    simpa using this
  have hprod : B.card ≤ (B.image cellF).card * (B.image cellS).card := by
    rw [← Finset.card_product]
    refine Finset.card_le_card_of_injOn (fun c => (cellF c, cellS c)) ?_ ?_
    · intro c hc
      exact Finset.mem_coe.2 (Finset.mem_product.2
        ⟨Finset.mem_image_of_mem _ hc, Finset.mem_image_of_mem _ hc⟩)
    · intro c _ d _ h
      simp only [Prod.mk.injEq] at h
      exact cells_inj c d h.1 h.2
  set f := (B.image cellF).card with hf
  set s := (B.image cellS).card with hs
  -- the sign blocks
  set BE := B.filter (fun c => c.1.sgn = true ∧ c.2.sgn = true) with hBE
  set BO := B.filter (fun c => c.1.sgn = false ∧ c.2.sgn = false) with hBO
  set BX := B.filter (fun c => ¬ ((c.1.sgn = true ∧ c.2.sgn = true) ∨
    (c.1.sgn = false ∧ c.2.sgn = false))) with hBX
  have hsplit : B.card = BE.card + BO.card + BX.card := by
    have e1 : (B.filter (fun c => (c.1.sgn = true ∧ c.2.sgn = true) ∨
        (c.1.sgn = false ∧ c.2.sgn = false))).card + BX.card = B.card := by
      rw [hBX]
      exact Finset.card_filter_add_card_filter_not _
    have e2 : B.filter (fun c => (c.1.sgn = true ∧ c.2.sgn = true) ∨
        (c.1.sgn = false ∧ c.2.sgn = false)) = BE ∪ BO := by
      rw [hBE, hBO, ← Finset.filter_or]
    have e3 : Disjoint BE BO := by
      rw [hBE, hBO]
      exact Finset.disjoint_filter.2 fun c _ h1 h2 => by rw [h1.1] at h2; exact Bool.noConfusion h2.1
    rw [e2, Finset.card_union_of_disjoint e3] at e1
    omega
  -- at most three members per block, six outside
  have hcardT : ∀ (S : Finset (Idx × Idx)) (T : Finset (Bool × Bool × Fin 3)), S ⊆ B →
      (∀ c ∈ S, tri c ∈ T) → S.card ≤ T.card := fun S T hS hT =>
    Finset.card_le_card_of_injOn tri (fun c hc => Finset.mem_coe.2 (hT c hc))
      (fun c hc d hd h => htri (hS hc) (hS hd) h)
  have hBE3 : BE.card ≤ 3 := by
    have := hcardT BE (Finset.univ.filter fun t => t.1 = true ∧ t.2.1 = true)
      (Finset.filter_subset _ _) (fun c hc => by
        have := (Finset.mem_filter.1 hc).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, tri]; exact this)
    exact this.trans (by decide)
  have hBO3 : BO.card ≤ 3 := by
    have := hcardT BO (Finset.univ.filter fun t => t.1 = false ∧ t.2.1 = false)
      (Finset.filter_subset _ _) (fun c hc => by
        have := (Finset.mem_filter.1 hc).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, tri]; exact this)
    exact this.trans (by decide)
  have hBX6 : BX.card ≤ 6 := by
    have := hcardT BX (Finset.univ.filter fun t => ¬ ((t.1 = true ∧ t.2.1 = true) ∨
      (t.1 = false ∧ t.2.1 = false))) (Finset.filter_subset _ _) (fun c hc => by
        have := (Finset.mem_filter.1 hc).2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, tri]; exact this)
    exact this.trans (by decide)
  -- the cells of the two blocks
  set X := BE.image cellF with hX
  set Y := BO.image cellF with hY
  set X' := BE.image cellS with hX'
  set Y' := BO.image cellS with hY'
  have hBEsub : BE ⊆ B := Finset.filter_subset _ _
  have hBOsub : BO ⊆ B := Finset.filter_subset _ _
  have hEsg : ∀ c ∈ BE, c.1.sgn = true ∧ c.2.sgn = true := fun c hc => (Finset.mem_filter.1 hc).2
  have hOsg : ∀ c ∈ BO, c.1.sgn = false ∧ c.2.sgn = false := fun c hc => (Finset.mem_filter.1 hc).2
  -- within a block, the diagonal of the first cell determines the member
  have hdiagE : ∀ c ∈ BE, ∀ d ∈ BE, diagC (cellF c) = diagC (cellF d) → c = d := by
    intro c hc d hd h
    exact htri (hBEsub hc) (hBEsub hd)
      (tri_eq_of_diag (by rw [(hEsg c hc).1, (hEsg d hd).1]) (by rw [(hEsg c hc).2, (hEsg d hd).2]) h)
  have hdiagO : ∀ c ∈ BO, ∀ d ∈ BO, diagC (cellF c) = diagC (cellF d) → c = d := by
    intro c hc d hd h
    exact htri (hBOsub hc) (hBOsub hd)
      (tri_eq_of_diag (by rw [(hOsg c hc).1, (hOsg d hd).1]) (by rw [(hOsg c hc).2, (hOsg d hd).2]) h)
  have hXc : X.card = BE.card := Finset.card_image_of_injOn fun c hc d hd h =>
    hdiagE c hc d hd (by rw [show cellF c = cellF d from h])
  have hYc : Y.card = BO.card := Finset.card_image_of_injOn fun c hc d hd h =>
    hdiagO c hc d hd (by rw [show cellF c = cellF d from h])
  have hX'c : X'.card = BE.card := Finset.card_image_of_injOn fun c hc d hd h => by
    apply hdiagE c hc d hd
    rw [← diag_cellS_EE c (hEsg c hc).1 (hEsg c hc).2, ← diag_cellS_EE d (hEsg d hd).1 (hEsg d hd).2]
    rw [show cellS c = cellS d from h]
  have hY'c : Y'.card = BO.card := Finset.card_image_of_injOn fun c hc d hd h => by
    apply hdiagO c hc d hd
    rw [← diag_cellS_OO c (hOsg c hc).1 (hOsg c hc).2, ← diag_cellS_OO d (hOsg d hd).1 (hOsg d hd).2]
    rw [show cellS c = cellS d from h]
  -- `f ≥ |X ∪ Y|`, `s ≥ |X' ∪ Y'|`
  have hfXY : (X ∪ Y).card ≤ f := Finset.card_le_card (Finset.union_subset
    (Finset.image_subset_image hBEsub) (Finset.image_subset_image hBOsub))
  have hsXY : (X' ∪ Y').card ≤ s := Finset.card_le_card (Finset.union_subset
    (Finset.image_subset_image hBEsub) (Finset.image_subset_image hBOsub))
  have hu1 := Finset.card_union_add_card_inter X Y
  have hu2 := Finset.card_union_add_card_inter X' Y'
  -- the coincidences sit on common diagonals, at most one per diagonal
  set D1 := (X ∩ Y).image diagC with hD1
  set D2 := (X' ∩ Y').image diagC with hD2
  have hD1c : D1.card = (X ∩ Y).card := Finset.card_image_of_injOn fun x hx y hy h => by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hy).1
    rw [hdiagE c hc d hd h]
  have hD2c : D2.card = (X' ∩ Y').card := Finset.card_image_of_injOn fun x hx y hy h => by
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hy).1
    have h' : diagC (cellF c) = diagC (cellF d) := by
      rw [← diag_cellS_EE c (hEsg c hc).1 (hEsg c hc).2,
        ← diag_cellS_EE d (hEsg d hd).1 (hEsg d hd).2]
      exact h
    rw [hdiagE c hc d hd h']
  have hD12 : Disjoint D1 D2 := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨x, hx, hxt⟩ := Finset.mem_image.1 ht1
    obtain ⟨x', hx', hx't⟩ := Finset.mem_image.1 ht2
    obtain ⟨e1, he1, hex⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
    obtain ⟨o1, ho1, hox⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).2
    obtain ⟨e2, he2, hex'⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx').1
    obtain ⟨o2, ho2, hox'⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx').2
    have hee : e1 = e2 := hdiagE e1 he1 e2 he2 (by
      rw [hex, hxt, ← hx't, ← hex', diag_cellS_EE e2 (hEsg e2 he2).1 (hEsg e2 he2).2])
    have hoo : o1 = o2 := hdiagO o1 ho1 o2 ho2 (by
      rw [hox, hxt, ← hx't, ← hox', diag_cellS_OO o2 (hOsg o2 ho2).1 (hOsg o2 ho2).2])
    subst hee hoo
    have := cells_inj e1 o1 (hex.trans hox.symm) (hex'.trans hox'.symm)
    subst this
    have h1 := (hEsg e1 he1).1
    have h2 := (hOsg e1 ho1).1
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hDE : D1 ∪ D2 ⊆ BE.image (fun c => diagC (cellF c)) := by
    intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
      exact Finset.mem_image_of_mem _ he
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).1
      rw [diag_cellS_EE e (hEsg e he).1 (hEsg e he).2]
      exact Finset.mem_image_of_mem _ he
  have hDO : D1 ∪ D2 ⊆ BO.image (fun c => diagC (cellF c)) := by
    intro t ht
    rcases Finset.mem_union.1 ht with ht | ht
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).2
      exact Finset.mem_image_of_mem _ ho
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.1 (Finset.mem_inter.1 hx).2
      rw [diag_cellS_OO o (hOsg o ho).1 (hOsg o ho).2]
      exact Finset.mem_image_of_mem _ ho
  have hDEc := (Finset.card_le_card hDE).trans Finset.card_image_le
  have hDOc := (Finset.card_le_card hDO).trans Finset.card_image_le
  rw [Finset.card_union_of_disjoint hD12, hD1c, hD2c] at hDEc hDOc
  -- arithmetic
  have hf9 : f ≤ 9 := by
    have := Finset.card_le_univ (B.image cellF); simpa using this
  have hs9 : s ≤ 9 := by
    have := Finset.card_le_univ (B.image cellS); simpa using this
  have hkey : 11 ≤ B.card → B.card ≤ f + s + 3 := by
    intro h11
    omega
  have hmax := le_max_right 5 (f + s)
  have hmax5 := le_max_left 5 (f + s)
  by_cases h9 : 9 ≤ f + s
  · omega
  · have hf8 : f ≤ 8 := by omega
    have hs8 : s ≤ 8 := by omega
    by_cases h11 : 11 ≤ B.card
    · have := hkey h11; omega
    · interval_cases f <;> interval_cases s <;> omega

end Kalai5
