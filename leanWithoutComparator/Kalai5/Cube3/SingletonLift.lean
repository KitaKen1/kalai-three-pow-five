import Kalai5.Cube3.SingletonModel
import Kalai5.Cube3.CubeSections

/-!
# From auxiliary vertices to facets of the original polytope

The low-height branch is a genuine multiplication of distinct vertices:
N distinct auxiliary vertices, all at heights |s| < 3, give 3N facets.
This theorem does not assume or assert that the auxiliary body has N vertices.
-/

namespace Kalai5.Cube3

open Set FullPrism

noncomputable def singletonGraph : E5 →ₗ[ℝ] (E 3 × E 3) where
  toFun p := (auxPart p, cubePart p)
  map_add' := by
    intro p t
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [auxPart, cubePart] <;> ring
  map_smul' := by
    intro a p
    apply Prod.ext <;> ext i <;> fin_cases i <;> simp [auxPart, cubePart] <;> ring

lemma singletonGraph_injective : Function.Injective singletonGraph := by
  intro p t h
  have ha := congrArg Prod.fst h
  have hc := congrArg Prod.snd h
  have ha1 := congrArg (fun y : E 3 => y 1) ha
  have ha2 := congrArg (fun y : E 3 => y 2) ha
  have hc0 := congrArg (fun y : E 3 => y 0) hc
  have hc1 := congrArg (fun y : E 3 => y 1) hc
  have hc2 := congrArg (fun y : E 3 => y 2) hc
  ext i
  fin_cases i
  · exact hc0
  · exact hc1
  · exact hc2
  · exact ha1
  · exact ha2

noncomputable def joinPoint (y u : E 3) : E5 :=
  (WithLp.equiv 2 (Fin 5 → ℝ)).symm ![u 0, u 1, u 2, y 1, y 2]

lemma cubePart_join (y u : E 3) : cubePart (joinPoint y u) = u := by
  ext i; fin_cases i <;> rfl

lemma auxPart_join (y u : E 3) (h : ∑ i, u i = y 0) : auxPart (joinPoint y u) = y := by
  ext i; fin_cases i
  · simpa [auxPart, joinPoint, Fin.sum_univ_three] using h
  · rfl
  · rfl

lemma cubeBox_section (s : ℝ) :
    cubeBox ∩ {u | s = ∑ i, u i} = cubeSection 3 s := by
  ext u
  simp only [cubeBox, cubeSection, mem_inter_iff, mem_setOf_eq, eq_comm]

lemma cubeBox_extreme_of_signs {u : E 3} (hu : ∀ i, u i = 1 ∨ u i = -1) :
    u ∈ cubeBox.extremePoints ℝ := by
  refine mem_extremePoints.2 ⟨?_, ?_⟩
  · intro i; rcases hu i with h | h <;> rw [h] <;> norm_num
  · intro a ha b hb hseg
    obtain ⟨t, v, ht, hv, htv, he⟩ := hseg
    have hc : ∀ i, a i = u i ∧ b i = u i := by
      intro i
      apply endpoint_combination (ha i) (hb i) ht hv htv _ (hu i)
      simpa using congrArg (fun q : E 3 => q i) he
    exact ⟨by ext i; exact (hc i).1, by ext i; exact (hc i).2⟩

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

lemma singleton_extreme_of_graph (q : Fin 3 → E 2) {p : E5}
    (hp : p ∈ C.singletonModel q)
    (hext : singletonGraph p ∈ (singletonGraph '' C.singletonModel q).extremePoints ℝ) :
    p ∈ (C.singletonModel q).extremePoints ℝ := by
  refine mem_extremePoints.2 ⟨hp, ?_⟩
  intro a ha b hb hseg
  have himg : singletonGraph p ∈ openSegment ℝ (singletonGraph a) (singletonGraph b) := by
    change singletonGraph p ∈ openSegment ℝ
      (singletonGraph.toAffineMap a) (singletonGraph.toAffineMap b)
    rw [← image_openSegment ℝ singletonGraph.toAffineMap a b]
    exact ⟨p, hseg, rfl⟩
  obtain ⟨ha', hb'⟩ := (mem_extremePoints.1 hext).2
    _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ himg
  exact ⟨singletonGraph_injective ha', singletonGraph_injective hb'⟩

/-- Auxiliary-vertex lift, now inside the five-dimensional polar model. -/
theorem singleton_lift_left (q : Fin 3 → E 2) {y u : E 3}
    (hy : y ∈ (C.singletonAux q).extremePoints ℝ)
    (hu : u ∈ (cubeSection 3 (y 0)).extremePoints ℝ) :
    joinPoint y u ∈ (C.singletonModel q).extremePoints ℝ := by
  have hj := auxPart_join y u hu.1.2
  have hc := cubePart_join y u
  apply C.singleton_extreme_of_graph q
  · exact ⟨hc ▸ hu.1.1, hj ▸ hy.1⟩
  · have himage : singletonGraph '' C.singletonModel q =
        fibreProduct (C.singletonAux q) cubeBox (fun y => y 0) (fun u => ∑ i, u i) :=
      C.singleton_fibreProduct q
    rw [himage]
    change (auxPart (joinPoint y u), cubePart (joinPoint y u)) ∈ _
    rw [hj, hc]
    apply extreme_fibreProduct_left hy
    rwa [cubeBox_section]

/-- Cube-vertex lift for the large-height branch, with the auxiliary section explicit. -/
theorem singleton_lift_right (q : Fin 3 → E 2) {y u : E 3}
    (hu : u ∈ cubeBox.extremePoints ℝ)
    (hy : y ∈ (C.singletonAux q ∩ {z | z 0 = ∑ i, u i}).extremePoints ℝ) :
    joinPoint y u ∈ (C.singletonModel q).extremePoints ℝ := by
  have hj := auxPart_join y u hy.1.2.symm
  have hc := cubePart_join y u
  apply C.singleton_extreme_of_graph q
  · exact ⟨hc ▸ hu.1, hj ▸ hy.1.1⟩
  · have himage : singletonGraph '' C.singletonModel q =
        fibreProduct (C.singletonAux q) cubeBox (fun y => y 0) (fun u => ∑ i, u i) :=
      C.singleton_fibreProduct q
    rw [himage]
    change (auxPart (joinPoint y u), cubePart (joinPoint y u)) ∈ _
    rw [hj, hc]
    exact extreme_fibreProduct_right hu hy

/-- Small-height auxiliary vertices yield three distinct polar vertices each. -/
theorem singleton_small_height_family (q : Fin 3 → E 2) {ι : Type*}
    (y : ι → E 3) (hyinj : Function.Injective y)
    (hy : ∀ i, y i ∈ (C.singletonAux q).extremePoints ℝ)
    (hheight : ∀ i, |y i 0| < 3) :
    ∃ f : ι × Fin 3 → E5, Function.Injective f ∧
      ∀ i, f i ∈ (C.singletonModel q).extremePoints ℝ := by
  classical
  choose u huinj hu using fun i => cubeSection_three_vertices (hheight i)
  let f : ι × Fin 3 → E5 := fun i => joinPoint (y i.1) (u i.1 i.2)
  have haux : ∀ i j, auxPart (f (i,j)) = y i :=
    fun i j => auxPart_join _ _ (hu i j).1.2
  have hcube : ∀ i j, cubePart (f (i,j)) = u i j := fun i j => cubePart_join _ _
  refine ⟨f, ?_, fun i => C.singleton_lift_left q (hy i.1) (hu i.1 i.2)⟩
  rintro ⟨i,a⟩ ⟨j,b⟩ he
  have hij : i = j := hyinj (by simpa only [haux] using congrArg auxPart he)
  subst j
  have hab : a = b := huinj i (by simpa only [hcube] using congrArg cubePart he)
  subst b
  rfl

/-- The 3N lower bound is on actual facets, rather than on a relaxed model. -/
theorem singleton_small_height_facets {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ)
    (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    {ι : Type*} [Fintype ι] (y : ι → E 3) (hyinj : Function.Injective y)
    (hy : ∀ i, y i ∈ (C.singletonAux q).extremePoints ℝ)
    (hheight : ∀ i, |y i 0| < 3) : 3 * Fintype.card ι ≤ fvec P 4 := by
  obtain ⟨f, hf, hmem⟩ := C.singleton_small_height_family q y hyinj hy hheight
  have hmem' : ∀ i, singletonEquiv q (f i) ∈ C.polarModel.extremePoints ℝ := by
    intro i
    rw [← C.singletonModel_image q hsingle, ← image_extremePoints]
    exact ⟨f i, hmem i, rfl⟩
  have h := C.model_vertices_le_facets hP hrange
    (fun i => singletonEquiv q (f i)) ((singletonEquiv q).injective.comp hf) hmem'
  simpa [Fintype.card_prod, Nat.mul_comm] using h

/-- Seven such auxiliary vertices suffice; a central-symmetry parity step is unnecessary. -/
theorem singleton_small_height_excluded {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x) = P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (q : Fin 3 → E 2)
    (hsingle : ∀ i : Fin 3, ∀ v, C.c v = (![1,2,3] i : Fin 4) → C.k v = q i)
    (y : Fin 7 → E 3) (hyinj : Function.Injective y)
    (hy : ∀ i, y i ∈ (C.singletonAux q).extremePoints ℝ)
    (hheight : ∀ i, |y i 0| < 3) : False := by
  have h := C.singleton_small_height_facets hP hrange q hsingle y hyinj hy hheight
  norm_num at h
  omega

end Config
end Kalai5.Cube3
