import Kalai5.Cube3.SharedTriangle

/-! Exact projection intervals for arbitrary classes, including polygons.
On a fixed planar line they recover the centered diamond inequalities. -/

namespace Kalai5.Cube3
open Set
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x) (n : E 2)

structure ProjectionIntervals where
  lo : Fin 4 → Fin 8
  hi : Fin 4 → Fin 8
  clo : ∀ j,C.c (lo j)=j
  chi : ∀ j,C.c (hi j)=j
  lower : ∀ v,⟪n,C.signedPoint (lo (C.c v))⟫≤⟪n,C.signedPoint v⟫
  upper : ∀ v,⟪n,C.signedPoint v⟫≤⟪n,C.signedPoint (hi (C.c v))⟫

theorem Config.projection_intervals : Nonempty (ProjectionIntervals C n) := by
  classical
  have hlo (j : Fin 4) := (C.cls j).exists_min_image (fun v => ⟪n,C.signedPoint v⟫) (C.cls_nonempty j)
  have hhi (j : Fin 4) := (C.cls j).exists_max_image (fun v => ⟪n,C.signedPoint v⟫) (C.cls_nonempty j)
  choose lo hloc hlomin using hlo
  choose hi hhic hhimax using hhi
  refine ⟨⟨lo,hi,?_,?_,?_,?_⟩⟩
  · intro j; exact (Finset.mem_filter.1 (hloc j)).2
  · intro j; exact (Finset.mem_filter.1 (hhic j)).2
  · intro v; exact hlomin _ v (by simp [Config.cls])
  · intro v; exact hhimax _ v (by simp [Config.cls])

namespace ProjectionIntervals
variable {C n} (I : ProjectionIntervals C n)

noncomputable def center (j : Fin 4) : E 2 :=
  (1/2 : ℝ) • (C.signedPoint (I.lo j)+C.signedPoint (I.hi j))
noncomputable def axis (j : Fin 4) : E 2 :=
  (1/2 : ℝ) • (C.signedPoint (I.hi j)-C.signedPoint (I.lo j))
noncomputable def radius (j : Fin 4) : ℝ := ⟪n,I.axis j⟫

noncomputable def centerEval : E5 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun j => (balanceSign j/2) •
    (((LinearMap.proj (I.lo j)).comp C.evaluation)+((LinearMap.proj (I.hi j)).comp C.evaluation))

lemma centerEval_apply (p : E5) (j : Fin 4) :
    I.centerEval p j=(C.signedValue p (I.lo j)+C.signedValue p (I.hi j))/2 := by
  change (balanceSign j/2)*(C.value p (I.lo j)+C.value p (I.hi j))=_
  simp only [Config.signedValue,I.clo,I.chi]; ring

lemma centerEval_eq (p : E5) (j : Fin 4) :
    I.centerEval p j=balanceSign j*offsets p j+⟪planar p,I.center j⟫ := by
  rw [I.centerEval_apply]
  simp only [Config.signedValue_eq,I.clo,I.chi,center,inner_smul_right,inner_add_right]
  ring

lemma signed_lo (p : E5) (j : Fin 4) :
    C.signedValue p (I.lo j)=I.centerEval p j-⟪planar p,I.axis j⟫ := by
  rw [I.centerEval_eq,Config.signedValue_eq,I.clo]
  simp only [axis,center,inner_smul_right,inner_add_right,inner_sub_right]; ring

lemma signed_hi (p : E5) (j : Fin 4) :
    C.signedValue p (I.hi j)=I.centerEval p j+⟪planar p,I.axis j⟫ := by
  rw [I.centerEval_eq,Config.signedValue_eq,I.chi]
  simp only [axis,center,inner_smul_right,inner_add_right,inner_sub_right]; ring

lemma value_centered (p : E5) (v : Fin 8) :
    C.signedValue p v=I.centerEval p (C.c v)+⟪planar p,C.signedPoint v-I.center (C.c v)⟫ := by
  rw [I.centerEval_eq,Config.signedValue_eq,inner_sub_right]; ring

lemma radius_nonneg (j : Fin 4) : 0 ≤ I.radius j := by
  have h := I.lower (I.hi j)
  rw [I.chi] at h
  simp only [radius,axis,inner_smul_right,inner_sub_right]
  linarith

lemma projected_bound (v : Fin 8) :
    |⟪n,C.signedPoint v-I.center (C.c v)⟫|≤I.radius (C.c v) := by
  have hlo := I.lower v
  have hhi := I.upper v
  simp only [radius,axis,center,inner_sub_right,inner_smul_right,inner_add_right]
  exact abs_le.2 ⟨by linarith,by linarith⟩

lemma centered_bound {p : E5} (hp : p ∈ C.polarModel) (j : Fin 4) :
    |I.centerEval p j|+|⟪planar p,I.axis j⟫|≤1 := by
  apply (abs_pair_iff _ _).1
  rw [← I.signed_lo,← I.signed_hi]
  exact ⟨(C.mem_polar_signed p).1 hp _,(C.mem_polar_signed p).1 hp _⟩

lemma mem_polar_on_line {p : E5} {t : ℝ} (hplane : planar p=t • n) :
    p ∈ C.polarModel ↔ ∀ j,|I.centerEval p j|+I.radius j*|t|≤1 := by
  constructor
  · intro hp j
    have h := I.centered_bound hp j
    rw [hplane,real_inner_smul_left,abs_mul] at h
    change |I.centerEval p j|+|t| * |I.radius j|≤1 at h
    simpa only [abs_of_nonneg (I.radius_nonneg j),mul_comm] using h
  · intro h
    apply (C.mem_polar_signed p).2
    intro v
    rw [I.value_centered,hplane,real_inner_smul_left]
    apply (abs_add_le _ _).trans
    rw [abs_mul]
    calc
      _ ≤ |I.centerEval p (C.c v)|+|t| * I.radius (C.c v) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (I.projected_bound v) (abs_nonneg t))
      _ ≤ 1 := by simpa [mul_comm] using h (C.c v)

lemma radius_zero_singleton {j : Fin 4} (h1 : (C.cls j).card=1) : I.radius j=0 := by
  have he := C.eq_of_singleton_class h1 (I.clo j) (I.chi j)
  simp [radius,axis,he]

lemma radius_positive {j : Fin 4} (h3 : 3 ≤ (C.cls j).card) (hn : n ≠ 0) : 0 < I.radius j := by
  by_contra hpos
  have hz : I.radius j=0 := le_antisymm (le_of_not_gt hpos) (I.radius_nonneg j)
  have hc : ∀ v,C.c v=j → ⟪n,C.signedPoint v⟫=⟪n,I.center j⟫ := by
    intro v hv
    have hh := I.projected_bound v
    rw [hv,hz] at hh
    have he := abs_eq_zero.1 (le_antisymm hh (abs_nonneg _))
    rw [inner_sub_right] at he
    exact sub_eq_zero.1 he
  let b := balanceSign j • n
  have hb : b ≠ 0 := by
    apply smul_ne_zero _ hn
    intro he; have hh := balanceSign_sq j; rw [he] at hh; norm_num at hh
  have hconst : ∀ q ∈ (fibre C.c C.k j : Set (E 2)),⟪q,b⟫=⟪n,I.center j⟫ := by
    intro q hq
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.1 hq
    have hv' : C.c v=j := by simpa using hv
    have hh := hc v hv'
    simpa only [b,Config.signedPoint,hv',inner_smul_right,real_inner_comm n] using hh
  have hdim : dim (fibre C.c C.k j : Set (E 2))=2 := by
    have hh := C.dim_fibre_eq_two h3
    unfold dim at hh ⊢
    rwa [← direction_affineSpan,affineSpan_convexHull,direction_affineSpan] at hh
  have hle := LemmaB.dim_le_one_of_const hb hconst
  omega

noncomputable def scaled (a : ℝ) (ha : 0 ≤ a) : ProjectionIntervals C (a • n) where
  lo := I.lo
  hi := I.hi
  clo := I.clo
  chi := I.chi
  lower v := by simp only [real_inner_smul_left]; exact mul_le_mul_of_nonneg_left (I.lower v) ha
  upper v := by simp only [real_inner_smul_left]; exact mul_le_mul_of_nonneg_left (I.upper v) ha

lemma radius_scaled (a : ℝ) (ha : 0 ≤ a) (j : Fin 4) :
    (I.scaled a ha).radius j=a*I.radius j := real_inner_smul_left _ _ _

end ProjectionIntervals
end Kalai5.Cube3
