import Kalai5.Cube3.BoundarySupport

/-! Transfer a finite signed support edge to its unsigned normal and two polar vertices. -/
namespace Kalai5.Cube3
open Set FullPrism LemmaB
local notation "⟪" x ", " y "⟫" => inner ℝ x y
variable {x : Fin 8 → E5} (C : Config x)

lemma Config.signed_support_edge_normal {j : Fin 4} {s₀ s₁ c : E 2}
    (E : TransverseSupportEdge (C.signedFibre j) s₀ s₁ c) :
    IsEdgeNormal (fibre C.c C.k j) (balanceSign j • E.normal) := by
  classical
  obtain ⟨v,hv,hve⟩ := Finset.mem_image.1 E.first_mem
  obtain ⟨w,hw,hwe⟩ := Finset.mem_image.1 E.second_mem
  have hvj : C.c v=j := by simpa [Config.cls] using hv
  have hwj : C.c w=j := by simpa [Config.cls] using hw
  have he (z : Fin 8) (hz : C.c z=j) :
      ⟪balanceSign j • E.normal,C.k z⟫=⟪E.normal,C.signedPoint z⟫ := by
    simp [Config.signedPoint,hz,real_inner_smul_left,inner_smul_right]
  have hm (z : Fin 8) (hz : C.c z=j)
      (hp : ⟪E.normal,C.signedPoint z⟫=⟪E.normal,E.first⟫) :
      C.k z ∈ amax (fibre C.c C.k j) (balanceSign j • E.normal) := by
    apply mem_amax.2
    refine ⟨Finset.mem_image.2 ⟨z,by simp [hz],rfl⟩,?_⟩
    intro p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.1 hp
    have huj : C.c u=j := by simpa using hu
    rw [he u huj,he z hz,‹⟪E.normal,C.signedPoint z⟫=⟪E.normal,E.first⟫›]
    exact E.upper _ (Finset.mem_image.2 ⟨u,by simp [Config.cls,huj],rfl⟩)
  refine ⟨?_,Finset.one_lt_card.2 ⟨_,hm w hwj (by rw [hwe]; exact E.equal),
    _,hm v hvj (by rw [hve]),?_⟩⟩
  · rw [norm_smul,Real.norm_eq_abs,balanceSign_abs,E.unit,one_mul]
  · intro h
    apply E.distinct
    rw [← hwe,← hve,Config.signedPoint,Config.signedPoint,hwj,hvj,h]

theorem Config.support_edge_two {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (τ : Equiv.Perm (Fin 4))
    (S : SegmentFibre C (τ 1)) (h2 : (C.cls (τ 2)).card=1)
    (h3 : (C.cls (τ 3)).card=1) (v2 v3 : Fin 8)
    (hv2 : C.c v2=τ 2) (hv3 : C.c v3=τ 3)
    (E : TransverseSupportEdge (C.signedFibre (τ 0))
      (C.signedPoint S.first) (C.signedPoint S.second)
      (C.signedPoint v2+C.signedPoint v3)) :
    ∃ F : PositiveFamily C (Fin 2),∀ i,F.normal i=E.normal := by
  classical
  obtain ⟨v,hv,hve⟩ := Finset.mem_image.1 E.first_mem
  obtain ⟨w,hw,hwe⟩ := Finset.mem_image.1 E.second_mem
  have hvj : C.c v=τ 0 := by simpa [Config.cls] using hv
  have hwj : C.c w=τ 0 := by simpa [Config.cls] using hw
  obtain ⟨r,hr,hre⟩ : ∃ r : Fin 8,C.c r=τ 1 ∧ C.signedPoint r=E.endpoint := by
    rcases E.endpoint_mem with he | he
    · exact ⟨S.first,S.first_class,he.symm⟩
    · exact ⟨S.second,S.second_class,he.symm⟩
  let rep : Fin 4 → Fin 8 := ![v,r,v2,v3]
  have hc (j : Fin 4) : C.c (rep j)=τ j := by
    fin_cases j
    · exact hvj
    · exact hr
    · exact hv2
    · exact hv3
  obtain ⟨f,hf,he,hfr⟩ := C.edge_two_vertices hP hrange τ rep hc w hwj
    (by change C.signedPoint w ≠ C.signedPoint v; rw [hwe,hve]; exact E.distinct)
    E.normal E.unit
    (by change ⟪E.normal,C.signedPoint w⟫=⟪E.normal,C.signedPoint v⟫; rw [hwe,hve]; exact E.equal)
    (fun z hz => by
      change ⟪E.normal,C.signedPoint z⟫≤⟪E.normal,C.signedPoint v⟫
      rw [hve]
      exact E.upper _ (Finset.mem_image.2 ⟨z,by simp [Config.cls,hz],rfl⟩))
    (fun z hz => congrArg (fun u => ⟪E.normal,C.signedPoint u⟫)
      (C.eq_of_singleton_class h2 hz (hc 2)))
    (fun z hz => congrArg (fun u => ⟪E.normal,C.signedPoint u⟫)
      (C.eq_of_singleton_class h3 hz (hc 3))) (by
      rw [Fin.sum_univ_four]
      change 0 < ⟪E.normal,C.signedPoint v+C.signedPoint r+C.signedPoint v2+C.signedPoint v3⟫
      rw [hve,hre,add_assoc E.first E.endpoint]
      simpa only [add_assoc] using E.positive)
  exact ⟨PositiveFamily.onRay E.normal E.unit f hf he hfr,fun _ => rfl⟩

end Kalai5.Cube3
