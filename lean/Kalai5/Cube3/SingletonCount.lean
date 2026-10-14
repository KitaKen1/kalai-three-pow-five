import Kalai5.Cube3.CompactSections

/-!
# Twenty polar vertices in the tall singleton branch

At height one there are three auxiliary section vertices and three cube
vertices, giving nine pairs. Height three gives one more. Their negatives
are ten additional vertices; positive height excludes every cross collision.
-/

namespace Kalai5.Cube3

open Set FullPrism

noncomputable def plusCube (j : Fin 3) : E 3 := cycle3 1 1 (-1) j
noncomputable def capCube : E 3 := cycle3 1 1 1 0

lemma plusCube_sum (j : Fin 3) : ∑ i, plusCube j i = 1 := by
  fin_cases j <;> norm_num [plusCube,cycle3,Fin.sum_univ_three] <;> dsimp <;> norm_num

lemma capCube_sum : ∑ i, capCube i = 3 := by
  norm_num [capCube,cycle3,Fin.sum_univ_three] <;> dsimp <;> norm_num

lemma plusCube_extreme (j : Fin 3) : plusCube j ∈ cubeBox.extremePoints ℝ := by
  apply cubeBox_extreme_of_signs
  intro i; fin_cases j <;> fin_cases i <;> norm_num [plusCube,cycle3] <;> dsimp <;> norm_num

lemma capCube_extreme : capCube ∈ cubeBox.extremePoints ℝ := by
  apply cubeBox_extreme_of_signs
  intro i; fin_cases i <;> norm_num [capCube,cycle3] <;> dsimp <;> norm_num

lemma plusCube_injective : Function.Injective plusCube :=
  cycle3_injective (Or.inr (by norm_num))

noncomputable def modelHeight (p : E5) : ℝ := auxPart p 0

lemma modelHeight_neg (p : E5) : modelHeight (-p) = -modelHeight p := by
  simp [modelHeight,auxPart]
  ring

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

lemma singletonModel_neg (q : Fin 3 → E 2) {p : E5}
    (hp : p ∈ C.singletonModel q) : -p ∈ C.singletonModel q := by
  have ha : auxPart (-p) = -auxPart p := by
    ext i; fin_cases i <;> simp [auxPart] <;> ring
  constructor
  · intro i
    have h := hp.1 i
    fin_cases i <;> simpa [cubePart] using h
  · rw [ha]
    exact C.singletonAux_neg q hp.2

/-- Nine height-one vertices and one height-three vertex, all distinct. -/
theorem singleton_ten_positive (q : Fin 3 → E 2) (y : Fin 3 → E 3)
    (hyinj : Function.Injective y)
    (hy : ∀ i, y i ∈ (C.singletonAux q ∩ {z | z 0 = 1}).extremePoints ℝ)
    (c : E 3) (hc : c ∈ (C.singletonAux q ∩ {z | z 0 = 3}).extremePoints ℝ) :
    ∃ f : ((Fin 3 × Fin 3) ⊕ Unit) → E5, Function.Injective f ∧
      (∀ i, f i ∈ (C.singletonModel q).extremePoints ℝ) ∧
      ∀ i, 0 < modelHeight (f i) := by
  let f : ((Fin 3 × Fin 3) ⊕ Unit) → E5 :=
    Sum.elim (fun ij => joinPoint (y ij.1) (plusCube ij.2)) (fun _ => joinPoint c capCube)
  have hleft : ∀ i j, auxPart (f (Sum.inl (i,j))) = y i := by
    intro i j
    exact auxPart_join _ _ (by rw [plusCube_sum, (hy i).1.2])
  have hright : ∀ u, auxPart (f (Sum.inr u)) = c := by
    intro u
    exact auxPart_join _ _ (by rw [capCube_sum, hc.1.2])
  have hHleft : ∀ i j, modelHeight (f (Sum.inl (i,j))) = 1 := by
    intro i j; unfold modelHeight; rw [hleft]; exact (hy i).1.2
  have hHright : ∀ u, modelHeight (f (Sum.inr u)) = 3 := by
    intro u; unfold modelHeight; rw [hright]; exact hc.1.2
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a b he
    rcases a with ⟨i,j⟩ | u <;> rcases b with ⟨k,l⟩ | v
    · have hik : i = k := hyinj (by simpa only [hleft] using congrArg auxPart he)
      have hjl : j = l := plusCube_injective (by
        simpa only [f,Sum.elim_inl,cubePart_join] using congrArg cubePart he)
      subst k; subst l; rfl
    · have h := congrArg modelHeight he
      rw [hHleft,hHright] at h
      norm_num at h
    · have h := congrArg modelHeight he
      rw [hHright,hHleft] at h
      norm_num at h
    · cases u; cases v; rfl
  · rintro (⟨i,j⟩ | u)
    · apply C.singleton_lift_right q (plusCube_extreme j)
      simpa only [plusCube_sum] using hy i
    · apply C.singleton_lift_right q capCube_extreme
      simpa only [capCube_sum] using hc
  · rintro (⟨i,j⟩ | u)
    · rw [hHleft]; norm_num
    · rw [hHright]; norm_num

/-- Positive heights distinguish this family from its entire negative. -/
theorem singleton_twenty (q : Fin 3 → E 2) (y : Fin 3 → E 3)
    (hyinj : Function.Injective y)
    (hy : ∀ i, y i ∈ (C.singletonAux q ∩ {z | z 0 = 1}).extremePoints ℝ)
    (c : E 3) (hc : c ∈ (C.singletonAux q ∩ {z | z 0 = 3}).extremePoints ℝ) :
    ∃ f : (((Fin 3 × Fin 3) ⊕ Unit) ⊕ ((Fin 3 × Fin 3) ⊕ Unit)) → E5,
      Function.Injective f ∧ ∀ i, f i ∈ (C.singletonModel q).extremePoints ℝ := by
  obtain ⟨f,hf,hext,hpos⟩ := C.singleton_ten_positive q y hyinj hy c hc
  let g := Sum.elim f (fun i => -f i)
  refine ⟨g, ?_, ?_⟩
  · intro a b he
    rcases a with a | a <;> rcases b with b | b
    · exact congrArg Sum.inl (hf he)
    · have h := congrArg modelHeight he
      change modelHeight (f a) = modelHeight (-f b) at h
      rw [modelHeight_neg] at h
      linarith [hpos a,hpos b]
    · have h := congrArg modelHeight he
      change modelHeight (-f a) = modelHeight (f b) at h
      rw [modelHeight_neg] at h
      linarith [hpos a,hpos b]
    · exact congrArg Sum.inr (hf (neg_injective he))
  · rintro (i | i)
    · exact hext i
    · exact CS.neg_mem_extremePoints (fun _ h => C.singletonModel_neg q h) (hext i)

theorem singleton_tall_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ)
    (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    (h3 : 3 ≤ (C.cls 0).card) {z : E 3} (hz : z ∈ C.singletonAux q) (hgt : 3 ≤ z 0) :
    20 ≤ fvec P 4 := by
  have hcomp := C.singletonAux_compact q h3
  have hconv := C.singletonAux_convex q
  have h0 := C.singletonAux_zero_interior q
  obtain ⟨y,hyinj,hy⟩ := compact_height_section_three hcomp hconv 1
    (height_one_interior hconv h0 hz hgt)
  have hclosed : IsClosed {y : E 3 | y 0 = 3} := isClosed_eq (by fun_prop) continuous_const
  obtain ⟨c,hc⟩ := (hcomp.inter_right hclosed).extremePoints_nonempty
    (height_three_nonempty hconv (interior_subset h0) hz hgt)
  obtain ⟨f,hf,hmem⟩ := C.singleton_twenty q y hyinj hy c hc
  have hmem' : ∀ i, singletonEquiv q (f i) ∈ C.polarModel.extremePoints ℝ := by
    intro i
    rw [← C.singletonModel_image q hsingle, ← image_extremePoints]
    exact ⟨f i,hmem i,rfl⟩
  have h := C.model_vertices_le_facets hP hrange (fun i => singletonEquiv q (f i))
    ((singletonEquiv q).injective.comp hf) hmem'
  simpa [Fintype.card_sum,Fintype.card_prod] using h

/-- The (5,1,1,1) case is impossible when its large class is labeled zero. -/
theorem singleton_class_zero_impossible {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (h5 : 5 ≤ (C.cls 0).card)
    (hsize : ∀ i : Fin 3, (C.cls (![1,2,3] i)).card = 1) : False := by
  obtain ⟨q,hq⟩ := C.singleton_points hsize
  obtain ⟨z,hz,hgt⟩ := C.singleton_tall_point hP hrange hh q hq h5
  have h20 := C.singleton_tall_facets hP hrange q hq (by omega) hz hgt
  omega

end Config
end Kalai5.Cube3
