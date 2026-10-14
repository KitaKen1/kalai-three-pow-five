import Kalai5.Cube3.DoubleFrame

/-! Transfer slab vertices and exceptional full normals to the actual polar. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} {C : Config x} {S : SegmentData C}

namespace DoubleFrame

variable (F : DoubleFrame S)

lemma embed_first (z : SlabPoint) (i : Fin 3) :
    S.centerEval (F.embed z) (F.order i.castSucc) = z.1 i := by
  rw [centerEval_embed,coords_order]
  fin_cases i <;> rfl

lemma plane_of_saturated {p : E5} (hp : p ∈ C.polarModel) (i : Fin 2)
    (hi : S.centerEval p (F.order i.castSucc.castSucc) = 1 ∨
      S.centerEval p (F.order i.castSucc.castSucc) = -1) :
    planar p = (F.project p).2 • F.normal := by
  apply F.plane_of_orthogonal p i
  have hh := (S.mem_polar_centered p).1 hp (F.order i.castSucc.castSucc)
  have hs : |S.centerEval p (F.order i.castSucc.castSucc)| = 1 := by
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  rw [hs] at hh
  exact abs_eq_zero.1 (by linarith [abs_nonneg ⟪planar p,S.axis (F.order i.castSucc.castSucc)⟫])

theorem embed_extreme {z : SlabPoint} (hz : z ∈ (doubleSlab F.ratio F.eta).extremePoints ℝ)
    (hsat : ∃ i : Fin 2, z.1 i.castSucc = 1 ∨ z.1 i.castSucc = -1) :
    F.embed z ∈ C.polarModel.extremePoints ℝ := by
  obtain ⟨i,hi⟩ := hsat
  refine ⟨(F.mem_embed z).2 hz.1,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hsat' : S.centerEval p (F.order i.castSucc.castSucc) = z.1 i.castSucc ∧
      S.centerEval q (F.order i.castSucc.castSucc) = z.1 i.castSucc := by
    apply endpoint_combination (TripleFrame.center_bound hp _) (TripleFrame.center_bound hq _) ha hb hab _ hi
    have hh := congrFun (congrArg S.centerEval he) (F.order i.castSucc.castSucc)
    simpa only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,F.embed_first] using hh
  have hpplane := F.plane_of_saturated hp i (by rw [hsat'.1]; exact hi)
  have hqplane := F.plane_of_saturated hq i (by rw [hsat'.2]; exact hi)
  have hpmodel : F.project p ∈ doubleSlab F.ratio F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hpplane]; exact hp)
  have hqmodel : F.project q ∈ doubleSlab F.ratio F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hqplane]; exact hq)
  have hproj : F.project p = z := hz.2 hpmodel hqmodel ⟨a,b,ha,hb,hab,by
    have hh := congrArg F.project he
    simpa only [map_add,map_smul,F.project_embed] using hh⟩
  calc p = F.embed (F.project p) := (F.embed_project hpplane).symm
       _ = F.embed z := congrArg F.embed hproj

lemma extra_of_pair {s v : ℝ} (hs : s=1 ∨ s= -1) (hv : v=1 ∨ v= -1)
    (he : F.eta=s+v) (hr : F.ratio=1) : C.ExtraPM := by
  let p := F.embed (doublePoint s v 0 1)
  have hp : planar p=F.normal := by rw [planar_embed]; simp [doublePoint]
  have hsign : ∀ j, |balanceSign j*C.value p (S.lo j)|=1 ∧
      |balanceSign j*C.value p (S.hi j)|=1 := by
    intro j
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [S.signed_value_lo,S.signed_value_hi,hp,centerEval_embed,coords_order]
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl
    · change |s-⟪F.normal,S.axis (F.order 0)⟫|=1 ∧ |s+⟪F.normal,S.axis (F.order 0)⟫|=1
      rw [show ⟪F.normal,S.axis (F.order 0)⟫=0 from F.zero 0,sub_zero,add_zero]
      rcases hs with rfl | rfl <;> norm_num
    · change |v-⟪F.normal,S.axis (F.order 1)⟫|=1 ∧ |v+⟪F.normal,S.axis (F.order 1)⟫|=1
      rw [show ⟪F.normal,S.axis (F.order 1)⟫=0 from F.zero 1,sub_zero,add_zero]
      rcases hv with rfl | rfl <;> norm_num
    · change |0-⟪F.normal,S.axis (F.order 2)⟫|=1 ∧ |0+⟪F.normal,S.axis (F.order 2)⟫|=1
      simpa [ratio] using And.intro hr hr
    · change |F.eta*1-(∑ i,cycle3 s v 0 0 i)-⟪F.normal,S.axis (F.order 3)⟫|=1 ∧
        |F.eta*1-(∑ i,cycle3 s v 0 0 i)+⟪F.normal,S.axis (F.order 3)⟫|=1
      rw [cycle3_sum,he,F.unit]; norm_num
  refine ⟨offsets p,planar p,offsets_balanced p,by rw [hp]; exact F.normal_ne_zero,?_⟩
  intro v
  have h : |C.value p v|=1 := by
    have hh := hsign (C.c v)
    simp only [abs_mul,balanceSign_abs,one_mul] at hh
    rcases S.cover v with hv | hv
    · simpa only [← hv] using hh.1
    · simpa only [← hv] using hh.2
  change C.value p v=1 ∨ C.value p v= -1
  rcases le_total 0 (C.value p v) with hh | hh
  · exact Or.inl (by rwa [abs_of_nonneg hh] at h)
  · exact Or.inr (by rw [abs_of_nonpos hh] at h; linarith)

lemma eta_not_exceptional (hno : ¬ C.ExtraPM) :
    ¬(F.ratio=1 ∧ F.eta=0) ∧ ¬(F.ratio=1 ∧ F.eta=2) ∧ ¬(F.ratio=1 ∧ F.eta= -2) := by
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair (s := 1) (v := -1) (Or.inl rfl) (Or.inr rfl) (by linarith) hr)
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair (s := 1) (v := 1) (Or.inl rfl) (Or.inl rfl) (by linarith) hr)
  · rintro ⟨hr,he⟩
    exact hno (F.extra_of_pair (s := -1) (v := -1) (Or.inr rfl) (Or.inr rfl) (by linarith) hr)

theorem four_positive (hno : ¬ C.ExtraPM) :
    ∃ f : Fin 2 ⊕ Fin 2 → E5, Function.Injective f ∧
      (∀ i,f i ∈ C.polarModel.extremePoints ℝ) ∧
      (∀ i,0 < (F.project (f i)).2) ∧
      ∀ i,planar (f i)=(F.project (f i)).2 • F.normal := by
  obtain ⟨h0,h2,hm2⟩ := F.eta_not_exceptional hno
  obtain ⟨G⟩ := doubleSlab_four F.ratio_pos F.ratio_le h0 h2 hm2
  refine ⟨fun i => F.embed (G.point i),F.embed_injective.comp G.inj,
    fun i => F.embed_extreme (G.extreme i) (G.saturated i),?_,?_⟩
  · intro i; rw [F.project_embed]; exact G.positive i
  · intro i; rw [F.project_embed,F.planar_embed]

end DoubleFrame
end Kalai5.Cube3
