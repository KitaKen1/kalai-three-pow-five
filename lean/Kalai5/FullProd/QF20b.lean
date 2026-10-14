import Kalai5.FullProd.QF20
import Kalai5.FullProd.QF20Comb
import Kalai5.FullProd.TF18c

/-!
# A `Δ2 × Δ2` facet in a cs 5-polytope with twenty vertices forces 66 edges

`IsCSPolytope5.edges_ge_66_of_qRow`: the count of `edges_ge_62_of_qRow` with all edges at `z`
(at least five, `five_le_edges_at`, and at least `|first B| + |second B|`) and the strengthened
combinatorics `card_le_cells_add_three`: `e ≥ 72 - 2|B| + 2 max(5, f + s) ≥ 66`.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A `Δ2 × Δ2` facet in a cs 5-polytope with twenty vertices forces 66 edges.** -/
theorem IsCSPolytope5.edges_ge_66_of_qRow (hv : fvec P 0 = 20) {F : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4) (hrow : faceRow P F = qRow) : 66 ≤ fvec P 1 := by
  classical
  obtain ⟨Q⟩ := hP.q20 hv hF h4 hrow
  have hdisj := Q20.disj hP hF h4
  -- the three outcomes
  set Up := Finset.univ.filter (fun c : Idx × Idx => Q.up c) with hUp
  set Dn := Finset.univ.filter (fun c : Idx × Idx => Q.dn c) with hDn
  set Sv := Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c ∧ ¬ Q.dn c) with hSv
  have hcard : Up.card + Dn.card + Sv.card = 36 := by
    have h1 : (Finset.univ : Finset (Idx × Idx)).card = 36 := by rfl
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun c : Idx × Idx => Q.up c)
    have h3 := Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)) (fun c => Q.dn c)
    have e1 : (Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)).filter (fun c => Q.dn c) = Dn := by
      rw [hDn, Finset.filter_filter]
      apply Finset.filter_congr
      intro c _
      exact ⟨fun h => h.2, fun h => ⟨fun hu => Q.not_up_and_dn c hu h, h⟩⟩
    have e2 : (Finset.univ.filter (fun c : Idx × Idx => ¬ Q.up c)).filter (fun c => ¬ Q.dn c) = Sv := by
      rw [hSv, Finset.filter_filter]
    rw [e1, e2] at h3
    rw [← hUp] at h2
    omega
  have hDnUp : Dn.card = Up.card := by
    refine Finset.card_bij (fun c _ => (c.1.swap, c.2.swap)) ?_ ?_ ?_
    · intro c hc
      rw [hDn, Finset.mem_filter] at hc
      rw [hUp, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, (Q.dn_iff c).1 hc.2⟩
    · intro c1 _ c2 _ h
      simp only [Prod.mk.injEq] at h
      have e1 : c1.1 = c2.1 := by
        have := congrArg Subtype.val h.1
        simp only [Idx.swap, Prod.mk.injEq] at this
        exact Subtype.ext (Prod.ext this.2 this.1)
      have e2 : c1.2 = c2.2 := by
        have := congrArg Subtype.val h.2
        simp only [Idx.swap, Prod.mk.injEq] at this
        exact Subtype.ext (Prod.ext this.2 this.1)
      exact Prod.ext e1 e2
    · intro d hd
      rw [hUp, Finset.mem_filter] at hd
      refine ⟨(d.1.swap, d.2.swap), ?_, ?_⟩
      · rw [hDn, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, (Q.dn_iff _).2 ?_⟩
        have hs1 : d.1.swap.swap = d.1 := Subtype.ext rfl
        have hs2 : d.2.swap.swap = d.2 := Subtype.ext rfl
        simp only [hs1, hs2]
        exact hd.2
      · exact Prod.ext (Subtype.ext rfl) (Subtype.ext rfl)
  have hcomb := card_le_cells_add_three Up (fun c hc d hd h1 h2 h3 h4 =>
    Q.up_conflict c d (Finset.mem_filter.1 hc).2 (Finset.mem_filter.1 hd).2 h1 h2 h3 h4)
  -- the edge families
  set E1 := {G : Set E5 | G ∈ faces P ∧ dim G = 1} with hE1
  set EF := {G : Set E5 | G ∈ faces P ∧ G ⊆ F ∧ dim G = 1} with hEF
  set EnF := {G : Set E5 | G ∈ faces P ∧ G ⊆ -F ∧ dim G = 1} with hEnF
  set ES := Q.side '' (Sv : Set (Idx × Idx)) with hES
  set EZ1 := (fun c : Fin 3 × Fin 3 => segment ℝ Q.z (Q.x c.1 c.2)) ''
    ((Up.image cellF : Finset (Fin 3 × Fin 3)) : Set (Fin 3 × Fin 3)) with hEZ1
  set EZ2 := (fun c : Fin 3 × Fin 3 => segment ℝ Q.z (-Q.x c.1 c.2)) ''
    ((Up.image cellS : Finset (Fin 3 × Fin 3)) : Set (Fin 3 × Fin 3)) with hEZ2
  set EZ := {G : Set E5 | G ∈ faces P ∧ Q.z ∈ G ∧ dim G = 1} with hEZ
  set EmZ := (fun G : Set E5 => -G) '' EZ with hEmZ
  have hfin : ∀ S : Set (Set E5), (∀ G ∈ S, G ∈ faces P) → S.Finite :=
    fun S hS => hP.faces_finite.subset hS
  -- memberships
  have hESsub : ES ⊆ E1 := by
    rintro _ ⟨c, hc, rfl⟩
    have hc' := (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
    exact Q.side_mem hP hF h4 c hc'.1 hc'.2
  have hEZ1sub : EZ1 ⊆ E1 := by
    rintro _ ⟨cell, hcell, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcell)
    exact (Q.adj_up hP hF h4 c (Finset.mem_filter.1 hc).2).1
  have hEZ2sub : EZ2 ⊆ E1 := by
    rintro _ ⟨cell, hcell, rfl⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hcell)
    exact (Q.adj_up hP hF h4 c (Finset.mem_filter.1 hc).2).2
  have hEZsub : EZ ⊆ E1 := fun G hG => ⟨hG.1, hG.2.2⟩
  have hEmZsub : EmZ ⊆ E1 := by
    rintro _ ⟨G, hG, rfl⟩
    obtain ⟨h1, h2⟩ := hEZsub hG
    exact ⟨neg_mem_faces hP.symm h1, by rw [dim_neg]; exact h2⟩
  -- special points
  have hzEZ : ∀ G ∈ EZ, Q.z ∈ G := fun G hG => hG.2.1
  have hnzEZ : ∀ G ∈ EZ, -Q.z ∉ G := by
    rintro G ⟨hG, hzG, hG1⟩ hnz
    have hGP : G ≠ P := hP.ne_of_dim_ne (by rw [hG1]; norm_num)
    obtain ⟨c, -, hc⟩ := hP.exists_dual hG hGP
    have e1 := (hc _ Q.zP).1 hzG
    have e2 := (hc _ (hP.symm _ Q.zP)).1 hnz
    rw [inner_neg_left] at e2
    linarith
  have hnzEmZ : ∀ G ∈ EmZ, -Q.z ∈ G := by
    rintro _ ⟨G, hG, rfl⟩
    exact Set.neg_mem_neg.2 (hzEZ G hG)
  have hzEmZ : ∀ G ∈ EmZ, Q.z ∉ G := by
    rintro _ ⟨G, hG, rfl⟩ h
    exact hnzEZ G hG (by simpa using Set.neg_mem_neg.2 h)
  -- disjointness
  have hznF' : Q.z ∉ -F := fun h => Q.nznF (Set.mem_neg.1 h)
  have hnznF' : -Q.z ∉ -F := fun h => Q.znF (by simpa using Set.mem_neg.1 h)
  have d1 : Disjoint EF EnF := by
    rw [Set.disjoint_left]
    rintro G ⟨hG, hGF, -⟩ ⟨-, hGnF, -⟩
    obtain ⟨y, hy⟩ := hG.1
    exact hdisj y (hGF hy) (Set.mem_neg.1 (hGnF hy))
  have d2 : Disjoint (EF ∪ EnF) ES := by
    rw [Set.disjoint_left]
    rintro G hG ⟨c, -, rfl⟩
    rcases hG with ⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩
    · exact hdisj _ (Q.memF c.1.1.2 c.2.1.2) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (Q.memF c.1.1.1 c.2.1.1) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
  have d3 : Disjoint (EF ∪ EnF ∪ ES) EZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hzEZ G hGZ
    rcases hG with (⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩
    · exact Q.znF (hGF hz)
    · exact hznF' (hGnF hz)
    · exact Q.z_nmem_side hP hF h4 c hz
  have d4 : Disjoint (EF ∪ EnF ∪ ES ∪ EZ) EmZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hnzEmZ G hGZ
    rcases hG with ((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | hG
    · exact Q.nznF (hGF hz)
    · exact hnznF' (hGnF hz)
    · exact Q.nz_nmem_side hP hF h4 c hz
    · exact hnzEZ G hG hz
  -- cardinalities
  have hEFc : EF.ncard = 18 := congrArg Row.e hrow
  have hEnFc : EnF.ncard = 18 := by
    have h1 : EnF.ncard = cnt P (-F) 1 := rfl
    rw [h1, hP.cnt_neg]
    exact hEFc
  have hESc : ES.ncard = Sv.card := by
    rw [hES, Set.InjOn.ncard_image (fun c _ d _ h => Q.side_inj hP hF h4 c d h),
      Set.ncard_coe_finset]
  have hEZ1c : EZ1.ncard = (Up.image cellF).card := by
    rw [hEZ1, Set.InjOn.ncard_image (fun c _ d _ h => Q.zx_inj hP hF h4 c.1 c.2 d.1 d.2 h),
      Set.ncard_coe_finset]
  have hEZ2c : EZ2.ncard = (Up.image cellS).card := by
    rw [hEZ2, Set.InjOn.ncard_image (fun c _ d _ h => Q.znx_inj hP hF h4 c.1 c.2 d.1 d.2 h),
      Set.ncard_coe_finset]
  have dZ : Disjoint EZ1 EZ2 := by
    rw [Set.disjoint_left]
    rintro _ ⟨c, -, rfl⟩ ⟨d, -, hd⟩
    exact Q.zx_ne_znx hP hF h4 c.1 c.2 d.1 d.2 hd.symm
  have hEZ1fin : EZ1.Finite := (Finset.finite_toSet _).image _
  have hEZ2fin : EZ2.Finite := (Finset.finite_toSet _).image _
  have hEZfin : EZ.Finite := hfin _ fun G hG => hG.1
  have hEZge : (Up.image cellF).card + (Up.image cellS).card ≤ EZ.ncard := by
    have hsubZ : EZ1 ∪ EZ2 ⊆ EZ := Set.union_subset
      (fun G hG => ⟨(hEZ1sub hG).1, by obtain ⟨c, -, rfl⟩ := hG; exact left_mem_segment ℝ _ _,
        (hEZ1sub hG).2⟩)
      (fun G hG => ⟨(hEZ2sub hG).1, by obtain ⟨c, -, rfl⟩ := hG; exact left_mem_segment ℝ _ _,
        (hEZ2sub hG).2⟩)
    have := Set.ncard_le_ncard hsubZ hEZfin
    rw [Set.ncard_union_eq dZ hEZ1fin hEZ2fin, hEZ1c, hEZ2c] at this
    exact this
  have hdeg : 5 ≤ EZ.ncard := hP.five_le_edges_at Q.zext
  have hEmZc : EmZ.ncard = EZ.ncard := by
    rw [hEmZ]
    exact Set.InjOn.ncard_image (fun G _ G' _ h => by simpa using h)
  have hEFfin : EF.Finite := hfin _ fun G hG => hG.1
  have hEnFfin : EnF.Finite := hfin _ fun G hG => hG.1
  have hESfin : ES.Finite := (Finset.finite_toSet _).image _
  have hEmZfin : EmZ.Finite := hEZfin.image _
  have hE1fin : E1.Finite := hfin _ fun G hG => hG.1
  have hsub : EF ∪ EnF ∪ ES ∪ EZ ∪ EmZ ⊆ E1 := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset ?_ ?_) hESsub)
      hEZsub) hEmZsub
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
  have htot : (EF ∪ EnF ∪ ES ∪ EZ ∪ EmZ).ncard = 36 + Sv.card + 2 * EZ.ncard := by
    rw [Set.ncard_union_eq d4 (((hEFfin.union hEnFfin).union hESfin).union hEZfin) hEmZfin,
      Set.ncard_union_eq d3 ((hEFfin.union hEnFfin).union hESfin) hEZfin,
      Set.ncard_union_eq d2 (hEFfin.union hEnFfin) hESfin,
      Set.ncard_union_eq d1 hEFfin hEnFfin, hEFc, hEnFc, hESc, hEmZc]
    ring
  have hle := Set.ncard_le_ncard hsub hE1fin
  rw [htot] at hle
  have h1 : fvec P 1 = E1.ncard := rfl
  rw [h1]
  have hm1 := le_max_left 5 ((Up.image cellF).card + (Up.image cellS).card)
  have hm2 := le_max_right 5 ((Up.image cellF).card + (Up.image cellS).card)
  set M := max 5 ((Up.image cellF).card + (Up.image cellS).card) with hM
  have hMle : M ≤ EZ.ncard := max_le hdeg hEZge
  omega

end cs

end Kalai5
