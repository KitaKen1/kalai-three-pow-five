import Kalai5.Cube3.CubeSections

/-! The exact four-dimensional slice with three zero-width coordinates. -/

namespace Kalai5.Cube3

open Set

abbrev SlabPoint := E 3 × ℝ

def tripleSlab (η : ℝ) : Set SlabPoint :=
  {p | (∀ i, |p.1 i| ≤ 1) ∧ |η * p.2 - ∑ i, p.1 i| + |p.2| ≤ 1}

noncomputable def slabForm (η σ : ℝ) : SlabPoint →ₗ[ℝ] ℝ where
  toFun p := σ * (η * p.2 - ∑ i, p.1 i) + p.2
  map_add' := by
    intro p q
    simp only [Prod.fst_add,Prod.snd_add,PiLp.add_apply,Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro t p
    simp only [Prod.smul_fst,Prod.smul_snd,PiLp.smul_apply,smul_eq_mul,
      RingHom.id_apply,← Finset.mul_sum]
    ring

lemma slabForm_bound {η σ : ℝ} (hσ : |σ| = 1) {p : SlabPoint}
    (hp : p ∈ tripleSlab η) : |slabForm η σ p| ≤ 1 := by
  apply (abs_add_le _ _).trans
  simpa only [abs_mul,hσ,one_mul] using hp.2

lemma tripleSlab_height_bound {η : ℝ} {p : SlabPoint} (hp : p ∈ tripleSlab η) : |p.2| ≤ 1 :=
  le_trans (le_add_of_nonneg_left (abs_nonneg _)) hp.2

lemma tripleSlab_cap {η : ℝ} {u : E 3}
    (hu : u ∈ (cubeSection 3 η).extremePoints ℝ) :
    (u,1) ∈ (tripleSlab η).extremePoints ℝ := by
  have hmem : (u,1) ∈ tripleSlab η := by
    refine ⟨hu.1.1,?_⟩
    simp [hu.1.2]
  refine ⟨hmem,?_⟩
  intro p hp q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have ht : p.2 = 1 ∧ q.2 = 1 := endpoint_combination
    (tripleSlab_height_bound hp) (tripleSlab_height_bound hq) ha hb hab
    (by simpa using congrArg Prod.snd he) (Or.inl rfl)
  have hsum : ∀ r ∈ tripleSlab η, r.2 = 1 → r.1 ∈ cubeSection 3 η := by
    intro r hr ht
    refine ⟨hr.1,?_⟩
    have h := hr.2
    rw [ht] at h
    norm_num at h
    linarith
  have hfirst : p.1 = u := hu.2 (hsum p hp ht.1) (hsum q hq ht.2)
    ⟨a,b,ha,hb,hab,by simpa using congrArg Prod.fst he⟩
  exact Prod.ext hfirst ht.1

lemma tripleSlab_cube {η σ t : ℝ} {u : E 3}
    (hp : (u,t) ∈ tripleSlab η) (hu : ∀ i, u i = 1 ∨ u i = -1)
    (hσ : |σ| = 1) (hc : σ * η + 1 ≠ 0)
    (htight : slabForm η σ (u,t) = 1) :
    (u,t) ∈ (tripleSlab η).extremePoints ℝ := by
  refine ⟨hp,?_⟩
  intro p hp' q hq hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  have hfirst : p.1 = u := by
    ext i
    exact (endpoint_combination (hp'.1 i) (hq.1 i) ha hb hab
      (by simpa using congrArg (fun r : SlabPoint => r.1 i) he) (hu i)).1
  have hform : slabForm η σ p = 1 := by
    apply (endpoint_combination (slabForm_bound hσ hp') (slabForm_bound hσ hq)
      ha hb hab _ (Or.inl rfl)).1
    have h := congrArg (slabForm η σ) he
    simpa only [map_add,map_smul,smul_eq_mul,htight] using h
  have ht : p.2 = t := by
    change σ * (η * p.2 - ∑ i, p.1 i) + p.2 = 1 at hform
    change σ * (η * t - ∑ i, u i) + t = 1 at htight
    rw [hfirst] at hform
    have h : (σ * η + 1) * (p.2 - t) = 0 := by nlinarith [hform,htight]
    exact sub_eq_zero.1 ((mul_eq_zero.1 h).resolve_left hc)
  exact Prod.ext hfirst ht

noncomputable def slabFlip : SlabPoint ≃ₗ[ℝ] SlabPoint where
  toFun p := (-p.1,p.2)
  invFun p := (-p.1,p.2)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp [add_comm]
  map_smul' t p := by simp

lemma tripleSlab_flip (η : ℝ) : slabFlip '' tripleSlab η = tripleSlab (-η) := by
  have hmem : ∀ (η : ℝ) p, p ∈ tripleSlab η → slabFlip p ∈ tripleSlab (-η) := by
    intro η p hp
    refine ⟨fun i => by simpa [slabFlip] using hp.1 i,?_⟩
    change |-η * p.2 - ∑ i, (-p.1) i| + |p.2| ≤ 1
    have he : -η * p.2 - ∑ i, (-p.1) i = -(η * p.2 - ∑ i, p.1 i) := by
      simp [Finset.sum_neg_distrib]
      ring
    rw [he,abs_neg]
    exact hp.2
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩; exact hmem η q hq
  · intro hp
    refine ⟨slabFlip p,?_,by simp [slabFlip]⟩
    simpa using hmem (-η) p hp

lemma cycle3_swap_ne {a b c : ℝ} (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (i j : Fin 3) : cycle3 a b c i ≠ cycle3 b a c j := by
  intro he
  have h0 := congrArg (fun p : E 3 => p 0) he
  have h1 := congrArg (fun p : E 3 => p 1) he
  have h2 := congrArg (fun p : E 3 => p 2) he
  fin_cases i <;> fin_cases j <;> simp [cycle3] at h0 h1 h2 <;> aesop

end Kalai5.Cube3
