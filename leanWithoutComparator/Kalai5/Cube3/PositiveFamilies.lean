import Kalai5.Cube3.EdgeBonus
import Kalai5.Cube3.NormalFamilies

/-! Weighted families on oriented normal rays, counted together with their antipodes. -/

namespace Kalai5.Cube3
open Set FullPrism

lemma unit_ray_eq {n m : E 2} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (he : s • n=t • m) : n=m := by
  have hst := congrArg norm he
  rw [norm_smul,norm_smul,hn,hm,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_pos hs,abs_of_pos ht,mul_one,mul_one] at hst
  rw [← hst] at he
  ext i
  have hi := congrArg (fun p : E 2 => p i) he
  change s*n i=s*m i at hi
  exact mul_left_cancel₀ hs.ne' hi

lemma unit_ray_eq_negative {n m : E 2} (hn : ‖n‖=1) (hm : ‖m‖=1)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (he : s • n= -(t • m)) : n= -m := by
  rw [← smul_neg] at he
  exact unit_ray_eq hn (by rwa [norm_neg]) hs ht he

lemma planar_neg (p : E5) : planar (-p)= -planar p := planarLinear.map_neg p

variable {x : Fin 8 → E5} (C : Config x)

structure PositiveFamily (ι : Type*) where
  point : ι → E5
  inj : Function.Injective point
  extreme : ∀ i,point i ∈ C.polarModel.extremePoints ℝ
  normal : ι → E 2
  unit : ∀ i,‖normal i‖=1
  ray : ∀ i,∃ t : ℝ,0 < t ∧ planar (point i)=t • normal i
  noOpposite : ∀ i j,normal i ≠ -normal j

namespace PositiveFamily
variable {C} {ι κ : Type*}

lemma nonzero (F : PositiveFamily C ι) (i : ι) : planar (F.point i) ≠ 0 := by
  obtain ⟨t,ht,he⟩ := F.ray i
  rw [he]
  apply smul_ne_zero ht.ne'
  intro hz
  have hn := F.unit i
  rw [hz,norm_zero] at hn
  norm_num at hn

lemma not_negative (F : PositiveFamily C ι) (i j : ι) : F.point i ≠ -F.point j := by
  intro he
  have hh := congrArg planar he
  rw [planar_neg] at hh
  obtain ⟨s,hs,hi⟩ := F.ray i
  obtain ⟨t,ht,hj⟩ := F.ray j
  rw [hi,hj] at hh
  exact F.noOpposite i j (unit_ray_eq_negative (F.unit i) (F.unit j) hs ht hh)

noncomputable def onRay (n : E 2) (hn : ‖n‖=1) (f : ι → E5) (hf : Function.Injective f)
    (he : ∀ i,f i ∈ C.polarModel.extremePoints ℝ)
    (hr : ∀ i,∃ t : ℝ,0 < t ∧ planar (f i)=t • n) : PositiveFamily C ι where
  point := f
  inj := hf
  extreme := he
  normal _ := n
  unit _ := hn
  ray := hr
  noOpposite := by
    intro i j hh
    have h0 : n=0 := by
      ext k
      have hk := congrArg (fun v : E 2 => v k) hh
      change n k= -n k at hk
      change n k=0
      linarith
    rw [h0,norm_zero] at hn
    norm_num at hn

noncomputable def sum (F : PositiveFamily C ι) (G : PositiveFamily C κ)
    (hne : ∀ i j,F.normal i ≠ G.normal j)
    (hopp : ∀ i j,F.normal i ≠ -G.normal j) : PositiveFamily C (ι ⊕ κ) where
  point := Sum.elim F.point G.point
  inj := by
    apply sum_family_injective _ _ F.inj G.inj
    intro i j he
    have hh := congrArg planar he
    obtain ⟨s,hs,hi⟩ := F.ray i
    obtain ⟨t,ht,hj⟩ := G.ray j
    rw [hi,hj] at hh
    exact hne i j (unit_ray_eq (F.unit i) (G.unit j) hs ht hh)
  extreme := by rintro (i | i); exact F.extreme i; exact G.extreme i
  normal := Sum.elim F.normal G.normal
  unit := by rintro (i | i); exact F.unit i; exact G.unit i
  ray := by rintro (i | i); exact F.ray i; exact G.ray i
  noOpposite := by
    rintro (i | i) (j | j)
    · exact F.noOpposite i j
    · exact hopp i j
    · intro he
      apply hopp j i
      change G.normal i= -F.normal j at he
      rw [he,neg_neg]
    · exact G.noOpposite i j

theorem facets [Fintype ι] (F : PositiveFamily C ι) {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) : 6+2*Fintype.card ι ≤ fvec P 4 := by
  let f := Sum.elim F.point (fun i => -F.point i)
  have hf : Function.Injective f := sum_family_injective _ _ F.inj (neg_injective.comp F.inj) F.not_negative
  have hmem : ∀ i,f i ∈ C.polarModel.extremePoints ℝ := by
    rintro (i | i); exact F.extreme i; exact C.polarModel_neg_extreme (F.extreme i)
  have hnz : ∀ i,planar (f i) ≠ 0 := by
    rintro (i | i)
    · exact F.nonzero i
    · change planar (-F.point i) ≠ 0
      rw [planar_neg]; exact neg_ne_zero.2 (F.nonzero i)
  simpa [Fintype.card_sum,two_mul] using C.six_add_vertices_le hP hrange f hf hmem hnz

theorem no_eighteen [Fintype ι] (F : PositiveFamily C ι) {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hseven : 7 ≤ Fintype.card ι) : False := by
  have h := F.facets hP hrange
  omega

end PositiveFamily

theorem Config.edge_positive_family {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (j : Fin 4) {n : E 2}
    (hn : LemmaB.IsEdgeNormal (fibre C.c C.k j) n) :
    ∃ F : PositiveFamily C Unit,∀ i,F.normal i=n := by
  obtain ⟨p,hp,ht⟩ := C.edge_ray_vertex hP hrange j hn
  exact ⟨PositiveFamily.onRay n hn.1 (fun _ : Unit => p) (fun _ _ _ => Subsingleton.elim _ _)
    (fun _ => hp) (fun _ => ht),fun _ => rfl⟩

end Kalai5.Cube3
