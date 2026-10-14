import Kalai5.Cube3.DoubleDirections

/-! Count disjoint vertex families on different normal lines. -/

namespace Kalai5.Cube3
open Set FullPrism
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} {C : Config x} {S : SegmentData C}

structure NormalFamily (S : SegmentData C) (j : Fin 4) (ι : Type*) where
  point : ι → E5
  inj : Function.Injective point
  extreme : ∀ i,point i ∈ C.polarModel.extremePoints ℝ
  orthogonal : ∀ i,⟪planar (point i),S.direction j⟫=0
  nonzero : ∀ i,planar (point i) ≠ 0

lemma NormalFamily.disjoint {j k : Fin 4} {ι κ : Type*} (F : NormalFamily S j ι)
    (G : NormalFamily S k κ) (hdet : det2 (S.direction j) (S.direction k) ≠ 0) :
    ∀ i l,F.point i ≠ G.point l := by
  intro i l he
  apply F.nonzero i
  apply orthogonal_two_eq_zero hdet (F.orthogonal i)
  rw [he]; exact G.orthogonal l

lemma Config.six_add_vertices_le {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) {ι : Type*} [Fintype ι]
    (f : ι → E5) (hinj : Function.Injective f) (hmem : ∀ i,f i ∈ C.polarModel.extremePoints ℝ)
    (hnz : ∀ i,planar (f i) ≠ 0) : 6+Fintype.card ι ≤ fvec P 4 := by
  let g := Sum.elim centralVertex f
  have hginj : Function.Injective g := by
    apply sum_family_injective _ _ centralVertex_injective hinj
    intro i j he
    apply hnz j
    have hh := congrArg planar he
    rw [centralVertex_planar] at hh
    exact hh.symm
  have hgmem : ∀ i,g i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i)
    · exact C.centralVertex_extreme i
    · exact hmem i
  simpa [Fintype.card_sum] using C.model_vertices_le_facets hP hrange g hginj hgmem

lemma NormalFamily.two_facets {j k : Fin 4} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : NormalFamily S j ι) (G : NormalFamily S k κ)
    {P : Set E5} (hP : IsCSPolytope5 P) (hrange : range (pm16 x)=P.extremePoints ℝ)
    (hdet : det2 (S.direction j) (S.direction k) ≠ 0) :
    6+(Fintype.card ι+Fintype.card κ) ≤ fvec P 4 := by
  have hmem : ∀ i,Sum.elim F.point G.point i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i); exact F.extreme i; exact G.extreme i
  have hnz : ∀ i,planar (Sum.elim F.point G.point i) ≠ 0 := by
    rintro (i | i); exact F.nonzero i; exact G.nonzero i
  simpa [Fintype.card_sum] using C.six_add_vertices_le hP hrange (Sum.elim F.point G.point)
    (sum_family_injective _ _ F.inj G.inj (F.disjoint G hdet)) hmem hnz

lemma NormalFamily.three_facets {j k l : Fin 4} {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (F : NormalFamily S j ι) (G : NormalFamily S k κ) (H : NormalFamily S l μ)
    {P : Set E5} (hP : IsCSPolytope5 P) (hrange : range (pm16 x)=P.extremePoints ℝ)
    (hjk : det2 (S.direction j) (S.direction k) ≠ 0)
    (hjl : det2 (S.direction j) (S.direction l) ≠ 0)
    (hkl : det2 (S.direction k) (S.direction l) ≠ 0) :
    6+(Fintype.card ι+(Fintype.card κ+Fintype.card μ)) ≤ fvec P 4 := by
  let g := Sum.elim G.point H.point
  have hginj : Function.Injective g := sum_family_injective _ _ G.inj H.inj (G.disjoint H hkl)
  have hdis : ∀ i j,F.point i ≠ g j := by
    intro i j; rcases j with j | j
    · exact F.disjoint G hjk i j
    · exact F.disjoint H hjl i j
  have hmem : ∀ i,Sum.elim F.point g i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | (i | i)); exact F.extreme i; exact G.extreme i; exact H.extreme i
  have hnz : ∀ i,planar (Sum.elim F.point g i) ≠ 0 := by
    rintro (i | (i | i)); exact F.nonzero i; exact G.nonzero i; exact H.nonzero i
  simpa [Fintype.card_sum] using C.six_add_vertices_le hP hrange (Sum.elim F.point g)
    (sum_family_injective _ _ F.inj hginj hdis) hmem hnz

theorem SegmentData.single_normal_family (S : SegmentData C) {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (j : Fin 4) :
    Nonempty (NormalFamily S j (Fin 2 × Fin 2)) := by
  obtain ⟨g,hgmem,hgclass,hgpos⟩ := S.four_rays hP hrange
  let B : Fin 2 × Fin 2 → E5 := fun i => g (j,i)
  have hBinj : Function.Injective B := by
    intro i k he
    have hsign : i.1=k.1 := by
      obtain ⟨v,hv⟩ := C.surj j
      apply sign2_injective
      have hi := hgclass (j,i) v hv
      have hk := hgclass (j,k) v hv
      change C.value (B i) v=sign2 i.1 at hi
      change C.value (B k) v=sign2 k.1 at hk
      rw [← hi,he,hk]
    have hray : i.2=k.2 := by
      apply sign2_eq_of_positive (hgpos (j,i))
      change 0 < sign2 k.2*⟪normal2 (S.direction j),planar (B i)⟫
      rw [he]; exact hgpos (j,k)
    exact Prod.ext hsign hray
  refine ⟨⟨B,hBinj,fun i => hgmem (j,i),fun i => S.class_orthogonal (hgclass (j,i)),?_⟩⟩
  intro i hz
  have hh := hgpos (j,i)
  change 0 < sign2 i.2*⟪normal2 (S.direction j),planar (B i)⟫ at hh
  rw [hz,inner_zero_right,mul_zero] at hh
  exact (lt_irrefl 0) hh

lemma SegmentData.direction_orthogonal_of_axis (S : SegmentData C) {b : E 2} {j : Fin 4}
    (h : ⟪b,S.axis j⟫=0) : ⟪b,S.direction j⟫=0 := by
  rw [SegmentData.axis,inner_smul_right] at h
  apply (mul_eq_zero.1 h).resolve_left
  apply div_ne_zero _ (by norm_num)
  intro hz
  have hh := balanceSign_sq j
  rw [hz] at hh; norm_num at hh

abbrev EightNormalIndex := (Fin 2 ⊕ Fin 2) ⊕ (Fin 2 ⊕ Fin 2)

theorem DoubleFrame.eight_normal_family (F : DoubleFrame S) (hno : ¬ C.ExtraPM) :
    Nonempty (NormalFamily S (F.order 0) EightNormalIndex) := by
  obtain ⟨f,hf,hfmem,hfpos,hfplane⟩ := F.four_positive hno
  let A := Sum.elim f (fun i => -f i)
  have hn (p : E5) : (F.project (-p)).2= -(F.project p).2 := by rw [map_neg]; rfl
  have hAinj : Function.Injective A := by
    apply sum_family_injective f (fun i => -f i) hf (neg_injective.comp hf)
    intro i j he
    have hh := congrArg (fun p => (F.project p).2) he
    rw [hn] at hh
    linarith [hfpos i,hfpos j]
  have hAmem : ∀ i,A i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i); exact hfmem i; exact C.polarModel_neg_extreme (hfmem i)
  have hheight : ∀ i,(F.project (A i)).2 ≠ 0 := by
    rintro (i | i)
    · exact ne_of_gt (hfpos i)
    · change (F.project (-f i)).2 ≠ 0
      rw [hn]; exact neg_ne_zero.2 (ne_of_gt (hfpos i))
  have hdir : ⟪F.normal,S.direction (F.order 0)⟫=0 := S.direction_orthogonal_of_axis (F.zero 0)
  refine ⟨⟨A,hAinj,hAmem,?_,?_⟩⟩
  · rintro (i | i)
    · change ⟪planar (f i),S.direction (F.order 0)⟫=0
      rw [hfplane,real_inner_smul_left,hdir,mul_zero]
    · have hh := planarLinear.map_neg (f i)
      change planar (-f i)= -planar (f i) at hh
      change ⟪planar (-f i),S.direction (F.order 0)⟫=0
      rw [hh,inner_neg_left,hfplane,real_inner_smul_left,hdir,mul_zero,neg_zero]
  · intro i hz
    apply hheight i
    rw [F.project_last,hz,inner_zero_left]

theorem SegmentData.double_normal_family (S : SegmentData C) (hno : ¬ C.ExtraPM) (hnt : S.NoTriple)
    {i j : Fin 4} (hij : i ≠ j) (hpar : det2 (S.direction i) (S.direction j)=0) :
    Nonempty (NormalFamily S i EightNormalIndex) := by
  obtain ⟨F,hF0,hF1⟩ := S.doubleFrame_of_pair hno hnt hij hpar
  rw [← hF0]
  exact F.eight_normal_family hno

end Kalai5.Cube3
