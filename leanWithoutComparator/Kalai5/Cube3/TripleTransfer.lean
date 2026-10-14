import Kalai5.Cube3.TripleFrame
import Kalai5.Cube3.TripleSlabCount

/-! Transfer slab vertices and exceptional full normals to the actual polar. -/

namespace Kalai5.Cube3

open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y

variable {x : Fin 8 → E5} {C : Config x} {S : SegmentData C}

namespace TripleFrame

variable (F : TripleFrame S)

lemma embed_first (z : SlabPoint) (i : Fin 3) :
    S.centerEval (F.embed z) (F.order i.castSucc) = z.1 i := by
  rw [centerEval_embed,coords_order]
  fin_cases i <;> rfl

lemma center_bound {p : E5} (hp : p ∈ C.polarModel) (j : Fin 4) : |S.centerEval p j| ≤ 1 := by
  have hh := (S.mem_polar_centered p).1 hp j
  exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) hh

lemma plane_of_saturated {p : E5} (hp : p ∈ C.polarModel) (i : Fin 3)
    (hi : S.centerEval p (F.order i.castSucc) = 1 ∨
      S.centerEval p (F.order i.castSucc) = -1) :
    planar p = (F.project p).2 • F.normal := by
  apply F.plane_of_orthogonal p i
  have hh := (S.mem_polar_centered p).1 hp (F.order i.castSucc)
  have hs : |S.centerEval p (F.order i.castSucc)| = 1 := by
    rcases hi with hi | hi <;> rw [hi] <;> norm_num
  rw [hs] at hh
  exact abs_eq_zero.1 (by linarith [abs_nonneg ⟪planar p,S.axis (F.order i.castSucc)⟫])

theorem embed_extreme {z : SlabPoint} (hz : z ∈ (tripleSlab F.eta).extremePoints ℝ)
    (hsat : ∃ i, z.1 i = 1 ∨ z.1 i = -1) :
    F.embed z ∈ C.polarModel.extremePoints ℝ := by
  obtain ⟨i,hi⟩ := hsat
  refine ⟨(F.mem_embed z).2 hz.1,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hsat' : S.centerEval p (F.order i.castSucc) = z.1 i ∧
      S.centerEval q (F.order i.castSucc) = z.1 i := by
    apply endpoint_combination (center_bound hp _) (center_bound hq _) ha hb hab _ hi
    have hh := congrFun (congrArg S.centerEval he) (F.order i.castSucc)
    simpa only [map_add,map_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul,F.embed_first] using hh
  have hpplane := F.plane_of_saturated hp i (by rw [hsat'.1]; exact hi)
  have hqplane := F.plane_of_saturated hq i (by rw [hsat'.2]; exact hi)
  have hpmodel : F.project p ∈ tripleSlab F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hpplane]; exact hp)
  have hqmodel : F.project q ∈ tripleSlab F.eta := (F.mem_embed _).1
    (by rw [F.embed_project hqplane]; exact hq)
  have hproj : F.project p = z := hz.2 hpmodel hqmodel ⟨a,b,ha,hb,hab,by
    have hh := congrArg F.project he
    simpa only [map_add,map_smul,F.project_embed] using hh⟩
  calc p = F.embed (F.project p) := (F.embed_project hpplane).symm
       _ = F.embed z := congrArg F.embed hproj

lemma extra_of_cube_section {u : E 3} (hu : ∀ i, u i = 1 ∨ u i = -1)
    (hsum : ∑ i,u i = F.eta) : C.ExtraPM := by
  let p := F.embed (u,1)
  have hp : planar p = F.normal := by rw [planar_embed]; simp
  have hsign : ∀ j, |balanceSign j * C.value p (S.lo j)| = 1 ∧
      |balanceSign j * C.value p (S.hi j)| = 1 := by
    intro j
    obtain ⟨j,rfl⟩ := F.order.surjective j
    rw [S.signed_value_lo,S.signed_value_hi,hp,centerEval_embed,coords_order]
    have hz (i : Fin 3) : ⟪F.normal,S.axis (F.order i.castSucc)⟫ = 0 := F.zero i
    have hj : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by fin_cases j <;> decide
    rcases hj with rfl | rfl | rfl | rfl
    · change |u 0 - ⟪F.normal,S.axis (F.order 0)⟫| = 1 ∧
        |u 0 + ⟪F.normal,S.axis (F.order 0)⟫| = 1
      rw [show ⟪F.normal,S.axis (F.order 0)⟫ = 0 from hz 0,sub_zero,add_zero]
      rcases hu 0 with h | h <;> rw [h] <;> norm_num
    · change |u 1 - ⟪F.normal,S.axis (F.order 1)⟫| = 1 ∧
        |u 1 + ⟪F.normal,S.axis (F.order 1)⟫| = 1
      rw [show ⟪F.normal,S.axis (F.order 1)⟫ = 0 from hz 1,sub_zero,add_zero]
      rcases hu 1 with h | h <;> rw [h] <;> norm_num
    · change |u 2 - ⟪F.normal,S.axis (F.order 2)⟫| = 1 ∧
        |u 2 + ⟪F.normal,S.axis (F.order 2)⟫| = 1
      rw [show ⟪F.normal,S.axis (F.order 2)⟫ = 0 from hz 2,sub_zero,add_zero]
      rcases hu 2 with h | h <;> rw [h] <;> norm_num
    · change |F.eta*1 - (∑ i,u i) - ⟪F.normal,S.axis (F.order 3)⟫| = 1 ∧
        |F.eta*1 - (∑ i,u i) + ⟪F.normal,S.axis (F.order 3)⟫| = 1
      rw [hsum,F.unit]
      norm_num
  refine ⟨offsets p,planar p,offsets_balanced p,by rw [hp]; exact F.normal_ne_zero,?_⟩
  intro v
  have h : |C.value p v| = 1 := by
    have hh := hsign (C.c v)
    simp only [abs_mul,balanceSign_abs,one_mul] at hh
    rcases S.cover v with hv | hv
    · simpa only [← hv] using hh.1
    · simpa only [← hv] using hh.2
  change C.value p v = 1 ∨ C.value p v = -1
  rcases le_total 0 (C.value p v) with hh | hh
  · exact Or.inl (by rwa [abs_of_nonneg hh] at h)
  · exact Or.inr (by rw [abs_of_nonpos hh] at h; linarith)

lemma eta_not_exceptional (hno : ¬ C.ExtraPM) :
    F.eta ≠ 1 ∧ F.eta ≠ -1 ∧ F.eta ≠ 3 ∧ F.eta ≠ -3 := by
  have hcube (a b c : ℝ) (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1)
      (hc : c = 1 ∨ c = -1) : F.eta ≠ a+b+c := by
    intro h
    apply hno
    apply F.extra_of_cube_section (u := cycle3 a b c 0)
    · intro i; fin_cases i <;> assumption
    · rw [cycle3_sum,h]
  refine ⟨?_,?_,?_,?_⟩
  · simpa using hcube 1 1 (-1) (Or.inl rfl) (Or.inl rfl) (Or.inr rfl)
  · simpa using hcube (-1) (-1) 1 (Or.inr rfl) (Or.inr rfl) (Or.inl rfl)
  · convert hcube 1 1 1 (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) using 1 <;> norm_num
  · convert hcube (-1) (-1) (-1) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) using 1 <;> norm_num

theorem five_positive (hno : ¬ C.ExtraPM) :
    ∃ f : Fin 3 ⊕ Fin 2 → E5, Function.Injective f ∧
      (∀ i,f i ∈ C.polarModel.extremePoints ℝ) ∧
      (∀ i,0 < (F.project (f i)).2) ∧
      ∀ i,planar (f i) = (F.project (f i)).2 • F.normal := by
  obtain ⟨h1,hm1,h3,hm3⟩ := F.eta_not_exceptional hno
  obtain ⟨G⟩ := tripleSlab_five h1 hm1 h3 hm3
  refine ⟨fun i => F.embed (G.point i),F.embed_injective.comp G.inj,
    fun i => F.embed_extreme (G.extreme i) (G.saturated i),?_,?_⟩
  · intro i; rw [F.project_embed]; exact G.positive i
  · intro i; rw [F.project_embed,F.planar_embed]

end TripleFrame
end Kalai5.Cube3
