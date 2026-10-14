import Kalai5.FullProd.TF18f

/-!
# A facet `Δ1 × Δ3` in a cs 5-polytope with eighteen vertices forces 64 edges

**Theorem** (`IsCSPolytope5.edges_ge_64_of_tRow`).  The count of `edges_ge_60_of_tRow` with
**loose adjacency**: every candidate whose corner interval reaches above `1` gives two edges at `z`
(`adj_opp_loose`, `adj_same_loose`), and the combinatorics `comb_concurrent_loose`,
`comb_parallel_loose` (the parallel tie is excluded by `not_both_up_par`, the other end `τ = τm`
of the family of representations).
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section cs

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

/-- **A `Δ1 × Δ3` facet in a cs 5-polytope with eighteen vertices forces 64 edges.** -/
theorem IsCSPolytope5.edges_ge_64_of_tRow (hv : fvec P 0 = 18) {F : Set E5} (hF : F ∈ faces P)
    (h4 : dim F = 4) (hrow : faceRow P F = tRow) : 64 ≤ fvec P 1 := by
  classical
  obtain ⟨T⟩ := hP.t18 hv hF h4 hrow
  have hdisj := T18.disj hP hF h4
  have isE_neg : ∀ G : Set E5, (-G ∈ faces P ∧ dim (-G) = 1) → (G ∈ faces P ∧ dim G = 1) :=
    fun G h => by
      have h1 := neg_mem_faces hP.symm h.1
      rw [neg_neg] at h1
      exact ⟨h1, by rw [← dim_neg]; exact h.2⟩
  -- the candidates that are edges, and those with `z` above
  set Eo := Finset.univ.filter
    (fun c : Fin 2 × Pr => T.side c ∈ faces P ∧ dim (T.side c) = 1) with hEo
  set Es := Finset.univ.filter (fun p : Pr => T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1) with hEs
  set Uo := Finset.univ.filter
    (fun c : Fin 2 × Pr => T.CU c ∧ ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1)) with hUo
  have hcardo : 24 ≤ Eo.card + 2 * Uo.card := by
    have hsplit : Eo.card + (Finset.univ.filter
        (fun c : Fin 2 × Pr => ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1))).card = 24 := by
      rw [hEo, Finset.card_filter_add_card_filter_not]; rfl
    have hsub : Finset.univ.filter
        (fun c : Fin 2 × Pr => ¬ (T.side c ∈ faces P ∧ dim (T.side c) = 1)) ⊆
        Uo ∪ Uo.image T18.mir := by
      intro c hc
      have hne := (Finset.mem_filter.1 hc).2
      by_cases hu : T.CU c
      · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hne⟩)
      · have hd : T.CD c := by
          by_contra hd
          exact hne (T.side_edge hP hF h4 c hu hd)
        rw [T.CD_iff] at hd
        have hne' : ¬ (T.side (T18.mir c) ∈ faces P ∧ dim (T.side (T18.mir c)) = 1) := by
          rw [T.side_mir]
          exact fun h => hne (isE_neg _ h)
        exact Finset.mem_union_right _ (Finset.mem_image.2
          ⟨T18.mir c, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, hne'⟩, T18.mir_mir c⟩)
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le Uo (Uo.image T18.mir)
    have h3 : (Uo.image T18.mir).card ≤ Uo.card := Finset.card_image_le
    omega
  -- the edge families
  set E1 := {G : Set E5 | G ∈ faces P ∧ dim G = 1} with hE1
  set EF := {G : Set E5 | G ∈ faces P ∧ G ⊆ F ∧ dim G = 1} with hEF
  set EnF := {G : Set E5 | G ∈ faces P ∧ G ⊆ -F ∧ dim G = 1} with hEnF
  set ESo := T.side '' (Eo : Set (Fin 2 × Pr)) with hESo
  set ESs := T.sideS '' (Es : Set Pr) with hESs
  set EZ := {G : Set E5 | G ∈ faces P ∧ T.z ∈ G ∧ dim G = 1} with hEZ
  set EmZ := (fun G : Set E5 => -G) '' EZ with hEmZ
  have hfin : ∀ S : Set (Set E5), (∀ G ∈ S, G ∈ faces P) → S.Finite :=
    fun S hS => hP.faces_finite.subset hS
  -- `z` and `-z` on the edges at `z`
  have hnzEZ : ∀ G ∈ EZ, -T.z ∉ G := by
    rintro G ⟨hG, hzG, hG1⟩ hnz
    have hGP : G ≠ P := hP.ne_of_dim_ne (by rw [hG1]; norm_num)
    obtain ⟨c, -, hc⟩ := hP.exists_dual hG hGP
    have e1 := (hc _ T.zP).1 hzG
    have e2 := (hc _ (hP.symm _ T.zP)).1 hnz
    rw [inner_neg_left] at e2
    linarith
  have hnzEmZ : ∀ G ∈ EmZ, -T.z ∈ G := by
    rintro _ ⟨G, hG, rfl⟩
    exact Set.neg_mem_neg.2 hG.2.1
  have hzEmZ : ∀ G ∈ EmZ, T.z ∉ G := by
    rintro _ ⟨G, hG, rfl⟩ h
    exact hnzEZ G hG (by simpa using Set.neg_mem_neg.2 h)
  -- memberships
  have hESosub : ESo ⊆ E1 := by
    rintro _ ⟨c, hc, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hc)).2
  have hESssub : ESs ⊆ E1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hp)).2
  have hEZsub : EZ ⊆ E1 := fun G hG => ⟨hG.1, hG.2.2⟩
  have hEmZsub : EmZ ⊆ E1 := by
    rintro _ ⟨G, hG, rfl⟩
    exact ⟨neg_mem_faces hP.symm hG.1, by rw [dim_neg]; exact hG.2.2⟩
  -- disjointness
  have hznF' : T.z ∉ -F := fun h => T.nznF (Set.mem_neg.1 h)
  have hnznF' : -T.z ∉ -F := fun h => T.znF (by simpa using Set.mem_neg.1 h)
  have d1 : Disjoint EF EnF := by
    rw [Set.disjoint_left]
    rintro G ⟨hG, hGF, -⟩ ⟨-, hGnF, -⟩
    obtain ⟨y, hy⟩ := hG.1
    exact hdisj y (hGF hy) (Set.mem_neg.1 (hGnF hy))
  have d2 : Disjoint (EF ∪ EnF) ESo := by
    rw [Set.disjoint_left]
    rintro G hG ⟨c, -, rfl⟩
    rcases hG with ⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩
    · exact hdisj _ (T.memF _ _) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (T.memF _ _) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
  have d3 : Disjoint (EF ∪ EnF ∪ ESo) ESs := by
    rw [Set.disjoint_left]
    rintro G hG ⟨p, -, rfl⟩
    rcases hG with (⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, hc⟩
    · exact hdisj _ (T.memF _ _) (by simpa using hGF (right_mem_segment ℝ _ _))
    · exact hdisj _ (T.memF _ _) (Set.mem_neg.1 (hGnF (left_mem_segment ℝ _ _)))
    · exact T.side_ne_sideS hP hF h4 c p hc
  have d4 : Disjoint (EF ∪ EnF ∪ ESo ∪ ESs) EZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hGZ.2.1
    rcases hG with ((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | ⟨p, -, rfl⟩
    · exact T.znF (hGF hz)
    · exact hznF' (hGnF hz)
    · exact T.z_nmem_side hP hF h4 c hz
    · exact T.z_nmem_sideS hP hF h4 p hz
  have d5 : Disjoint (EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ) EmZ := by
    rw [Set.disjoint_left]
    intro G hG hGZ
    have hz := hnzEmZ G hGZ
    rcases hG with (((⟨-, hGF, -⟩ | ⟨-, hGnF, -⟩) | ⟨c, -, rfl⟩) | ⟨p, -, rfl⟩) | hG
    · exact T.nznF (hGF hz)
    · exact hnznF' (hGnF hz)
    · exact T.nz_nmem_side hP hF h4 c hz
    · exact T.nz_nmem_sideS hP hF h4 p hz
    · exact hnzEZ G hG hz
  -- cardinalities
  have hEFc : EF.ncard = 16 := congrArg Row.e hrow
  have hEnFc : EnF.ncard = 16 := by
    have h1 : EnF.ncard = cnt P (-F) 1 := rfl
    rw [h1, hP.cnt_neg]
    exact hEFc
  have hESoc : ESo.ncard = Eo.card := by
    rw [hESo, Set.InjOn.ncard_image (fun c _ d _ h => T.side_inj hP hF h4 c d h),
      Set.ncard_coe_finset]
  have hESsc : ESs.ncard = Es.card := by
    rw [hESs, Set.InjOn.ncard_image (fun p _ q _ h => T.sideS_inj hP hF h4 p q h),
      Set.ncard_coe_finset]
  have hEmZc : EmZ.ncard = EZ.ncard := by
    rw [hEmZ]
    exact Set.InjOn.ncard_image (fun G _ G' _ h => by simpa using h)
  have hEFfin : EF.Finite := hfin _ fun G hG => hG.1
  have hEnFfin : EnF.Finite := hfin _ fun G hG => hG.1
  have hESofin : ESo.Finite := (Finset.finite_toSet _).image _
  have hESsfin : ESs.Finite := (Finset.finite_toSet _).image _
  have hEZfin : EZ.Finite := hfin _ fun G hG => hG.1
  have hEmZfin : EmZ.Finite := hEZfin.image _
  have hE1fin : E1.Finite := hfin _ fun G hG => hG.1
  have hsub : EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ ∪ EmZ ⊆ E1 := by
    refine Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset ?_ ?_) hESosub) hESssub) hEZsub) hEmZsub
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
    · exact fun G hG => ⟨hG.1, hG.2.2⟩
  have htot : (EF ∪ EnF ∪ ESo ∪ ESs ∪ EZ ∪ EmZ).ncard =
      32 + Eo.card + Es.card + 2 * EZ.ncard := by
    rw [Set.ncard_union_eq d5 ((((hEFfin.union hEnFfin).union hESofin).union hESsfin).union hEZfin)
        hEmZfin,
      Set.ncard_union_eq d4 (((hEFfin.union hEnFfin).union hESofin).union hESsfin) hEZfin,
      Set.ncard_union_eq d3 ((hEFfin.union hEnFfin).union hESofin) hESsfin,
      Set.ncard_union_eq d2 (hEFfin.union hEnFfin) hESofin,
      Set.ncard_union_eq d1 hEFfin hEnFfin, hEFc, hEnFc, hESoc, hESsc, hEmZc]
    ring
  have hle := Set.ncard_le_ncard hsub hE1fin
  rw [htot] at hle
  have hfv : fvec P 1 = E1.ncard := rfl
  -- the degree of `z`
  have hdeg : 5 ≤ EZ.ncard := hP.five_le_edges_at T.zext
  have hends : ∀ A B : Finset (Fin 2 × Fin 4),
      (∀ i ∈ A, segment ℝ T.z (T.x i.1 i.2) ∈ faces P ∧ dim (segment ℝ T.z (T.x i.1 i.2)) = 1) →
      (∀ i ∈ B, segment ℝ T.z (-T.x i.1 i.2) ∈ faces P ∧
        dim (segment ℝ T.z (-T.x i.1 i.2)) = 1) → A.card + B.card ≤ EZ.ncard := by
    intro A B hA hB
    set SA := (fun i : Fin 2 × Fin 4 => segment ℝ T.z (T.x i.1 i.2)) '' (A : Set (Fin 2 × Fin 4))
    set SB := (fun i : Fin 2 × Fin 4 => segment ℝ T.z (-T.x i.1 i.2)) '' (B : Set (Fin 2 × Fin 4))
    have hSA : SA.ncard = A.card := by
      rw [Set.InjOn.ncard_image (fun i _ j _ h => T.zx_inj hP hF h4 i.1 i.2 j.1 j.2 h),
        Set.ncard_coe_finset]
    have hSB : SB.ncard = B.card := by
      rw [Set.InjOn.ncard_image (fun i _ j _ h => T.znx_inj hP hF h4 i.1 i.2 j.1 j.2 h),
        Set.ncard_coe_finset]
    have hdAB : Disjoint SA SB := by
      rw [Set.disjoint_left]
      rintro _ ⟨i, -, rfl⟩ ⟨j, -, hj⟩
      exact T.zx_ne_znx hP hF h4 i.1 i.2 j.1 j.2 hj.symm
    have hsubZ : SA ∪ SB ⊆ EZ := by
      rintro _ (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩)
      · exact ⟨(hA i hi).1, left_mem_segment ℝ _ _, (hA i hi).2⟩
      · exact ⟨(hB i hi).1, left_mem_segment ℝ _ _, (hB i hi).2⟩
    have := Set.ncard_le_ncard hsubZ hEZfin
    rw [Set.ncard_union_eq hdAB ((Finset.finite_toSet _).image _) ((Finset.finite_toSet _).image _),
      hSA, hSB] at this
    exact this
  -- the two sides of the opposite-sign candidates with `z` above
  set U0 := Finset.univ.filter (fun p : Pr => (T.s0, p) ∈ Uo) with hU0
  set U1 := Finset.univ.filter (fun p : Pr => (oth T.s0, p) ∈ Uo) with hU1
  have hUo : Uo.card = U0.card + U1.card := by
    have e : Uo = (U0.image fun p => (T.s0, p)) ∪ (U1.image fun p => (oth T.s0, p)) := by
      ext c
      obtain ⟨s, p⟩ := c
      simp only [Finset.mem_union, Finset.mem_image, hU0, hU1, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro hc
        by_cases hs : s = T.s0
        · subst hs; exact Or.inl ⟨p, hc, rfl⟩
        · have := eq_oth_of_ne hs; subst this; exact Or.inr ⟨p, hc, rfl⟩
      · rintro (⟨q, hq, he⟩ | ⟨q, hq, he⟩) <;> rw [← he] <;> exact hq
    rw [e, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2),
      Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).2)]
    rw [Finset.disjoint_left]
    intro c hc1 hc2
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hc1
    obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hc2
    exact oth_ne T.s0 (Prod.mk.inj hq).1
  have hCU0 : ∀ p ∈ U0, T.CU (T.s0, p) ∧ ¬ (T.side (T.s0, p) ∈ faces P ∧ dim (T.side (T.s0, p)) = 1) :=
    fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).2).2
  have hCU1 : ∀ p ∈ U1, T.CU (oth T.s0, p) ∧
      ¬ (T.side (oth T.s0, p) ∈ faces P ∧ dim (T.side (oth T.s0, p)) = 1) :=
    fun p hp => (Finset.mem_filter.1 (Finset.mem_filter.1 hp).2).2
  -- the conflict for `ψ = Asm - Sabs`
  set ψ : Pr → ℝ := fun p => T.Asm p - T.Sabs p with hψ
  have hconf : ∀ p q : Pr, p.1.1 ≠ q.1.1 → p.1.2 ≠ q.1.2 → ψ p + ψ q ≤ 0 := by
    intro p q h1 h2
    have := psi_conflict T.Wc p q h1 h2
    simp only [hψ, T18.Asm, T18.Sabs]
    linarith
  set ξ := T.Zc (oth T.s0) with hξ
  have hA0 : ∀ p : Pr, T.Aop (T.s0, p) = -ξ + T.Asm p := by
    intro p; simp only [T18.Aop, T18.Asm, T.Zc_s0, hξ]; ring
  have hA1 : ∀ p : Pr, T.Aop (oth T.s0, p) = ξ + T.Asm p := by
    intro p; simp only [T18.Aop, T18.Asm, oth_oth, T.Zc_s0, hξ]; ring
  have h0 : ∀ p ∈ U0, 1 ≤ ψ p - ξ := by
    intro p hp
    have := (hCU0 p hp).1
    unfold T18.CU at this
    rw [hA0] at this
    simp only [hψ]
    linarith
  have h1 : ∀ p ∈ U1, 1 ≤ ψ p + ξ := by
    intro p hp
    have := (hCU1 p hp).1
    unfold T18.CU at this
    rw [hA1] at this
    simp only [hψ]
    linarith
  -- adjacency of the endpoints
  have hadj0 : ∀ p ∈ U0,
      (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
      (segment ℝ T.z (-T.x (oth T.s0) p.1.2) ∈ faces P ∧
        dim (segment ℝ T.z (-T.x (oth T.s0) p.1.2)) = 1) :=
    fun p hp => T.adj_opp hP hF h4 (T.s0, p) (hCU0 p hp).1 (hCU0 p hp).2
  have hadj1 : ∀ p ∈ U1,
      (segment ℝ T.z (T.x (oth T.s0) p.1.1) ∈ faces P ∧
        dim (segment ℝ T.z (T.x (oth T.s0) p.1.1)) = 1) ∧
      (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧ dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) := by
    intro p hp
    have := T.adj_opp hP hF h4 (oth T.s0, p) (hCU1 p hp).1 (hCU1 p hp).2
    simp only [oth_oth] at this
    exact this
  have hz := T.z0_eq
  have hzlt := T.z0_lt
  have hzgt := T.z0_gt hP
  have key : ∀ (s : Fin 2) (Z : Fin 2 → ℝ), ∑ i, Z i = Z s + Z (oth s) := by
    intro s Z; fin_cases s <;> simp [oth, Fin.sum_univ_two] <;> ring
  rw [key T.s0 T.Zc, T.Zc_s0, zero_add, ← hξ] at hz
  by_cases hγ : 0 < T.γ (oth T.s0)
  · -- concurrent: the same-sign candidates
    set Us := Finset.univ.filter
      (fun p : Pr => T.CUs p ∧ ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1)) with hUs
    have hcards : 12 ≤ Es.card + 2 * Us.card := by
      have hsplit : Es.card + (Finset.univ.filter
          (fun p : Pr => ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1))).card = 12 := by
        rw [hEs, Finset.card_filter_add_card_filter_not]; rfl
      have hsub : Finset.univ.filter
          (fun p : Pr => ¬ (T.sideS p ∈ faces P ∧ dim (T.sideS p) = 1)) ⊆
          Us ∪ Us.image Pr.swap := by
        intro p hp
        have hne := (Finset.mem_filter.1 hp).2
        by_cases hu : T.CUs p
        · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hu, hne⟩)
        · have hd : T.CDs p := by
            by_contra hd
            exact hne (T.sideS_edge hP hF h4 hγ p hu hd)
          rw [T.CDs_iff] at hd
          have hne' : ¬ (T.sideS p.swap ∈ faces P ∧ dim (T.sideS p.swap) = 1) := by
            rw [T.sideS_swap]
            exact fun h => hne (isE_neg _ h)
          refine Finset.mem_union_right _ (Finset.mem_image.2
            ⟨p.swap, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd, hne'⟩, ?_⟩)
          rfl
      have h1' := Finset.card_le_card hsub
      have h2' := Finset.card_union_le Us (Us.image Pr.swap)
      have h3' : (Us.image Pr.swap).card ≤ Us.card := Finset.card_image_le
      omega
    have hS : ∀ p ∈ Us, 1 ≤ T.Wc p.1.1 - T.Wc p.1.2 - ∑ j ∈ p.rest, |T.Wc j| - |ξ| := by
      intro p hp
      have := (Finset.mem_filter.1 hp).2.1
      unfold T18.CUs at this
      simp only [T18.Asm, T18.Sabs, hξ] at this
      linarith
    have h0' : ∀ p ∈ U0, 1 ≤ T.Wc p.1.1 - T.Wc p.1.2 - ∑ j ∈ p.rest, |T.Wc j| - ξ := by
      intro p hp; have := h0 p hp; simp only [hψ, T18.Asm, T18.Sabs] at this; linarith
    have h1'' : ∀ p ∈ U1, 1 ≤ T.Wc p.1.1 - T.Wc p.1.2 - ∑ j ∈ p.rest, |T.Wc j| + ξ := by
      intro p hp; have := h1 p hp; simp only [hψ, T18.Asm, T18.Sabs] at this; linarith
    -- the loose same-sign candidates
    set LS := Finset.univ.filter
      (fun p : Pr => 1 < T.Wc p.1.1 - T.Wc p.1.2 + |ξ| + ∑ j ∈ p.rest, |T.Wc j|) with hLSd
    have hLS : ∀ p : Pr, 1 < T.Wc p.1.1 - T.Wc p.1.2 + |ξ| + ∑ j ∈ p.rest, |T.Wc j| → p ∈ LS :=
      fun p hp => Finset.mem_filter.2 ⟨Finset.mem_univ _, hp⟩
    have hadjS : ∀ p ∈ Us,
        (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
        (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧ dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) :=
      fun p hp => T.adj_same hP hF h4 hγ p (Finset.mem_filter.1 hp).2.1
    have hadjL : ∀ p ∈ LS,
        (segment ℝ T.z (T.x T.s0 p.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x T.s0 p.1.1)) = 1) ∧
        (segment ℝ T.z (-T.x T.s0 p.1.2) ∈ faces P ∧ dim (segment ℝ T.z (-T.x T.s0 p.1.2)) = 1) := by
      intro p hp
      refine T.adj_same_loose hP hF h4 hγ p ?_
      have := (Finset.mem_filter.1 hp).2
      simp only [T18.Asm, T18.Sabs, hξ]
      linarith
    -- the endpoint sets
    set Wp := ((U0 ∪ Us ∪ LS).image fun p => (T.s0, p.1.1)) ∪ (U1.image fun p => (oth T.s0, p.1.1))
      with hWp
    set Wn := (U0.image fun p => (oth T.s0, p.1.2)) ∪ ((U1 ∪ Us ∪ LS).image fun p => (T.s0, p.1.2))
      with hWn
    have hE : Wp.card + Wn.card ≤ EZ.ncard := by
      refine hends Wp Wn ?_ ?_
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          rcases Finset.mem_union.1 hp with hp | hp
          · rcases Finset.mem_union.1 hp with hp | hp
            · exact (hadj0 p hp).1
            · exact (hadjS p hp).1
          · exact (hadjL p hp).1
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj1 p hp).1
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          exact (hadj0 p hp).2
        · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
          rcases Finset.mem_union.1 hp with hp | hp
          · rcases Finset.mem_union.1 hp with hp | hp
            · exact (hadj1 p hp).2
            · exact (hadjS p hp).2
          · exact (hadjL p hp).2
    have hdisj2 : ∀ (A B : Finset Pr) (f g : Pr → Fin 4) (s t : Fin 2), s ≠ t →
        Disjoint (A.image fun p => (s, f p)) (B.image fun p => (t, g p)) := by
      intro A B f g s t hst
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi1
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hi2
      exact hst (Prod.mk.inj hq).1.symm
    have hcardU : ∀ (A B : Finset Pr) (f g : Pr → Fin 4) (s t : Fin 2), s ≠ t →
        (A.image f).card + (B.image g).card ≤
          ((A.image fun p => (s, f p)) ∪ (B.image fun p => (t, g p))).card := by
      intro A B f g s t hst
      rw [Finset.card_union_of_disjoint (hdisj2 A B f g s t hst), card_image_pair, card_image_pair]
    have hne := oth_ne T.s0
    have hmono : ∀ (A B : Finset Pr) (f : Pr → Fin 4) (s : Fin 2), A ⊆ B →
        (A.image fun p => (s, f p)) ⊆ (B.image fun p => (s, f p)) :=
      fun A B f s h => Finset.image_subset_image h
    have hE1 : ((U0 ∪ Us).image fun p => p.1.1).card + (U1.image fun p => p.1.1).card +
        (U0.image fun p => p.1.2).card + ((U1 ∪ Us).image fun p => p.1.2).card ≤
        Wp.card + Wn.card := by
      have a1 := hcardU (U0 ∪ Us) U1 (fun p => p.1.1) (fun p => p.1.1) T.s0 (oth T.s0) hne.symm
      have a2 := hcardU U0 (U1 ∪ Us) (fun p => p.1.2) (fun p => p.1.2) (oth T.s0) T.s0 hne
      have b1 : ((U0 ∪ Us).image fun p => (T.s0, p.1.1)) ∪ (U1.image fun p => (oth T.s0, p.1.1)) ⊆ Wp :=
        Finset.union_subset_union (hmono _ _ _ _ Finset.subset_union_left) le_rfl
      have b2 : (U0.image fun p => (oth T.s0, p.1.2)) ∪ ((U1 ∪ Us).image fun p => (T.s0, p.1.2)) ⊆ Wn :=
        Finset.union_subset_union le_rfl (hmono _ _ _ _ Finset.subset_union_left)
      have := Finset.card_le_card b1; have := Finset.card_le_card b2
      omega
    have hE2 : (U0.image fun p => p.1.1).card + (U0.image fun p => p.1.2).card +
        ((U0.filter (· ∈ LS)).image fun p => p.1.2).card ≤ Wp.card + Wn.card := by
      have a1 : (U0.image fun p => p.1.1).card ≤ Wp.card := by
        rw [← card_image_pair U0 T.s0]
        exact Finset.card_le_card (Finset.subset_union_left.trans' (hmono _ _ _ _
          (Finset.subset_union_left.trans Finset.subset_union_left)))
      have a2 := hcardU U0 (U0.filter (· ∈ LS)) (fun p => p.1.2) (fun p => p.1.2) (oth T.s0) T.s0 hne
      have b2 : (U0.image fun p => (oth T.s0, p.1.2)) ∪
          ((U0.filter (· ∈ LS)).image fun p => (T.s0, p.1.2)) ⊆ Wn := by
        refine Finset.union_subset_union le_rfl (hmono _ _ _ _ ?_)
        intro p hp
        exact Finset.mem_union_right _ (Finset.mem_filter.1 hp).2
      have := Finset.card_le_card b2
      omega
    have hE3 : (U1.image fun p => p.1.1).card + ((U1.filter (· ∈ LS)).image fun p => p.1.1).card +
        (U1.image fun p => p.1.2).card ≤ Wp.card + Wn.card := by
      have a1 := hcardU (U1.filter (· ∈ LS)) U1 (fun p => p.1.1) (fun p => p.1.1) T.s0 (oth T.s0) hne.symm
      have b1 : ((U1.filter (· ∈ LS)).image fun p => (T.s0, p.1.1)) ∪
          (U1.image fun p => (oth T.s0, p.1.1)) ⊆ Wp := by
        refine Finset.union_subset_union (hmono _ _ _ _ ?_) le_rfl
        intro p hp
        exact Finset.mem_union_right _ (Finset.mem_filter.1 hp).2
      have a2 : (U1.image fun p => p.1.2).card ≤ Wn.card := by
        rw [← card_image_pair U1 T.s0]
        exact Finset.card_le_card (Finset.subset_union_right.trans' (hmono _ _ _ _
          (Finset.subset_union_left.trans Finset.subset_union_left)))
      have := Finset.card_le_card b1
      omega
    have hcomb := comb_concurrent_loose T.Wc ξ (by linarith) (by linarith) U0 U1 Us h0' h1'' hS
      LS hLS (Wp.card + Wn.card) hE1 hE2 hE3
    set M := max 5 (Wp.card + Wn.card) with hM
    have hMle : M ≤ EZ.ncard := max_le hdeg hE
    omega
  · -- parallel: `γ (oth s0) = 0`, hence `ξ = 0`
    have hγ0 : T.γ (oth T.s0) = 0 := le_antisymm (not_lt.1 hγ) (T.γnn _)
    have hξ0 : ξ = 0 := by simp only [hξ, T18.Zc, hγ0, zero_mul]
    rw [hξ0, zero_add] at hz
    have h0' : ∀ p ∈ U0, 1 ≤ T.Wc p.1.1 - T.Wc p.1.2 - ∑ j ∈ p.rest, |T.Wc j| := by
      intro p hp; have := h0 p hp; rw [hξ0] at this; simp only [hψ, T18.Asm, T18.Sabs] at this
      linarith
    have h1' : ∀ p ∈ U1, 1 ≤ T.Wc p.1.1 - T.Wc p.1.2 - ∑ j ∈ p.rest, |T.Wc j| := by
      intro p hp; have := h1 p hp; rw [hξ0] at this; simp only [hψ, T18.Asm, T18.Sabs] at this
      linarith
    have hdeg' : ∀ p : Pr, (∀ d ∈ p.rest, T.Wc d = 0) → T.Wc p.1.1 - T.Wc p.1.2 = 1 →
        0 < T.Wc p.1.1 → T.Wc p.1.2 < 0 → p ∈ U0 → p ∈ U1 → False := by
      intro p hrest hA hk hk' hp0 hp1
      exact T.not_both_up_par hP hF h4 hγ0 p (by simp only [T18.Asm]; exact hA) hrest hk hk'
        (hCU0 p hp0).2 (hCU1 p hp1).2
    set Λ := Finset.univ.filter
      (fun q : Pr => 1 < T.Wc q.1.1 - T.Wc q.1.2 + ∑ j ∈ q.rest, |T.Wc j|) with hΛ
    have hL : ∀ q : Pr, 1 < T.Wc q.1.1 - T.Wc q.1.2 + ∑ j ∈ q.rest, |T.Wc j| → q ∈ Λ :=
      fun q hq => Finset.mem_filter.2 ⟨Finset.mem_univ _, hq⟩
    have hZc : ∀ s, T.Zc s = 0 := by
      intro s
      by_cases hs : s = T.s0
      · rw [hs]; exact T.Zc_s0
      · rw [eq_oth_of_ne hs]; simp [T18.Zc, hγ0]
    have hadjΛ : ∀ q ∈ Λ, ∀ s : Fin 2,
        (segment ℝ T.z (T.x s q.1.1) ∈ faces P ∧ dim (segment ℝ T.z (T.x s q.1.1)) = 1) ∧
        (segment ℝ T.z (-T.x (oth s) q.1.2) ∈ faces P ∧
          dim (segment ℝ T.z (-T.x (oth s) q.1.2)) = 1) := by
      intro q hq s
      refine T.adj_opp_loose hP hF h4 (s, q) ?_
      have := (Finset.mem_filter.1 hq).2
      simp only [T18.Aop, T18.Sabs, hZc, sub_zero]
      linarith
    have hcomb := comb_parallel_loose T.Wc (by linarith) (by linarith) U0 U1 h0' h1' hdeg' Λ hL
    set Wp := (Λ.image fun q => (T.s0, q.1.1)) ∪ (Λ.image fun q => (oth T.s0, q.1.1)) with hWp
    set Wn := (Λ.image fun q => (oth T.s0, q.1.2)) ∪ (Λ.image fun q => (T.s0, q.1.2)) with hWn
    have hE : Wp.card + Wn.card ≤ EZ.ncard := by
      refine hends Wp Wn ?_ ?_
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          exact (hadjΛ q hq T.s0).1
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          exact (hadjΛ q hq (oth T.s0)).1
      · intro i hi
        rcases Finset.mem_union.1 hi with hi | hi
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          exact (hadjΛ q hq T.s0).2
        · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hi
          have := (hadjΛ q hq (oth T.s0)).2
          rw [oth_oth] at this
          exact this
    have hne := oth_ne T.s0
    have hdisjA : Disjoint (Λ.image fun q => (T.s0, q.1.1)) (Λ.image fun q => (oth T.s0, q.1.1)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi1
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hi2
      exact hne (Prod.mk.inj hq).1
    have hdisjB : Disjoint (Λ.image fun q => (oth T.s0, q.1.2)) (Λ.image fun q => (T.s0, q.1.2)) := by
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hi1
      obtain ⟨q, -, hq⟩ := Finset.mem_image.1 hi2
      exact hne (Prod.mk.inj hq).1.symm
    have cA : Wp.card = 2 * (Λ.image fun p => p.1.1).card := by
      rw [hWp, Finset.card_union_of_disjoint hdisjA, card_image_pair, card_image_pair]; ring
    have cB : Wn.card = 2 * (Λ.image fun p => p.1.2).card := by
      rw [hWn, Finset.card_union_of_disjoint hdisjB, card_image_pair, card_image_pair]; ring
    set M := max 5 (2 * (Λ.image fun p => p.1.1).card + 2 * (Λ.image fun p => p.1.2).card) with hM
    have hMle : M ≤ EZ.ncard := by
      refine max_le hdeg ?_
      rw [← cA, ← cB]; exact hE
    omega

end cs

end Kalai5
