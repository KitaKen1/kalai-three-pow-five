import Kalai5.Cube3.ActiveFaces
import Kalai5.Cube3.RayVertices
import Kalai5.Cube3.TripleFrame

/-! A supporting edge, rather than a constant whole fibre, supplies a genuine polar vertex. -/

namespace Kalai5.Cube3
open Set FullPrism Filter LemmaB
open scoped Topology
local notation "⟪" x ", " y "⟫" => inner ℝ x y

lemma positive_ray_of_orthogonal {n d b : E 2} (hn : ‖n‖=1) (hd : d ≠ 0)
    (hnd : ⟪n,d⟫=0) (hbd : ⟪b,d⟫=0) (hpos : 0 < ⟪n,b⟫) :
    ∃ t : ℝ,0 < t ∧ b=t • n := by
  have hnn : ⟪n,n⟫=1 := by rw [real_inner_self_eq_norm_sq,hn]; norm_num
  have hdet : det2 d n ≠ 0 := det_ne_of_annihilator hd hnd hnn
  refine ⟨⟪n,b⟫,hpos,sub_eq_zero.1 ?_⟩
  apply orthogonal_two_eq_zero hdet
  · rw [inner_sub_left,real_inner_smul_left,hnd,hbd,mul_zero,sub_self]
  · rw [inner_sub_left,real_inner_smul_left,hnn,mul_one,real_inner_comm n b,sub_self]

variable {x : Fin 8 → E5} (C : Config x)

namespace Config

lemma support_positive (j : Fin 4) (n : E 2) (hn : n ≠ 0) (β : ℝ)
    (hupper : ∀ v,C.c v=j → ⟪n,C.k v⟫≤β) :
    ∃ p ∈ C.polarModel,
      (∀ v,C.c v=j → ⟪n,C.k v⟫=β → C.value p v=1) ∧ 0 < ⟪n,planar p⟫ := by
  let p0 := pack (spike j) (0 : E 2)
  let p1 := pack (fun k => -β*spike j k) n
  have h0 : ∀ v,C.value p0 v=spike j (C.c v) := by
    intro v; rw [value_pack C (spike_balanced j)]; simp
  have h1 : ∀ v,C.value p1 v= -β*spike j (C.c v)+⟪n,C.k v⟫ :=
    fun v => C.value_pack (spike_mul_balanced j (-β)) n v
  have htight : ∀ (t : ℝ) v,C.c v=j → ⟪n,C.k v⟫=β → C.value (p0+t • p1) v=1 := by
    intro t v hv hvβ
    rw [C.value_add_smul,h0,h1,hv,spike_self,hvβ]; ring
  have hevent : ∀ᶠ t : ℝ in 𝓝 0,∀ v,
      (C.c v=j → -1 < C.value (p0+t • p1) v) ∧
      (C.c v ≠ j → |C.value (p0+t • p1) v| < 1) := by
    apply Filter.eventually_all.2
    intro v
    have hcont : Continuous (fun t : ℝ => C.value (p0+t • p1) v) :=
      (C.value_continuous v).comp (by fun_prop)
    by_cases hv : C.c v=j
    · have hnear := hcont.continuousAt.eventually (lt_mem_nhds
        (show (-1 : ℝ) < C.value (p0+(0 : ℝ) • p1) v by simp [h0,hv,spike_self]))
      exact hnear.mono (fun _ ht => ⟨fun _ => ht,fun h => (h hv).elim⟩)
    · have hnear := (continuous_abs.comp hcont).continuousAt.eventually (gt_mem_nhds
        (show |C.value (p0+(0 : ℝ) • p1) v| < 1 by
          simp only [zero_smul,add_zero,h0,spike_other j _ hv]; norm_num))
      exact hnear.mono (fun _ ht => ⟨fun h => (hv h).elim,fun _ => ht⟩)
  obtain ⟨δ,hδ,hnear⟩ := Metric.mem_nhds_iff.1 hevent
  have ht : 0 < δ/2 := by positivity
  have hsmall := hnear (show δ/2 ∈ Metric.ball (0 : ℝ) δ by
    change dist (δ/2) 0 < δ
    rw [Real.dist_eq,sub_zero,abs_of_pos ht]; linarith)
  refine ⟨p0+(δ/2) • p1,?_,htight (δ/2),?_⟩
  · intro v
    by_cases hv : C.c v=j
    · apply abs_le.2
      refine ⟨(hsmall v).1 hv |>.le,?_⟩
      rw [C.value_add_smul,h0,h1,hv,spike_self]
      nlinarith [hupper v hv]
    · exact ((hsmall v).2 hv).le
  · rw [planar_add_smul,planar_pack,planar_pack,zero_add,inner_smul_right]
    exact mul_pos ht (real_inner_self_pos.2 hn)

theorem support_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (j : Fin 4)
    (n : E 2) (hn : n ≠ 0) (β : ℝ) (hupper : ∀ v,C.c v=j → ⟪n,C.k v⟫≤β) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,
      (∀ v,C.c v=j → ⟪n,C.k v⟫=β → C.value p v=1) ∧ 0 < ⟪n,planar p⟫ := by
  classical
  obtain ⟨q,hq,htight,hpos⟩ := C.support_positive j n hn β hupper
  let T := Finset.univ.filter fun v => C.c v=j ∧ ⟪n,C.k v⟫=β
  have hqface : q ∈ C.activeFace T (fun _ => 1) := by
    refine ⟨hq,?_⟩
    intro v hv
    have hv' : C.c v=j ∧ ⟪n,C.k v⟫=β := by simpa [T] using hv
    exact htight v hv'.1 hv'.2
  obtain ⟨p,hp,hpt,hppos⟩ := C.activeFace_ray_vertex hP hrange T (fun _ => 1)
    (fun _ _ => Or.inl rfl) n hqface hpos
  exact ⟨p,hp,fun v hv hβ => hpt v (by simp [T,hv,hβ]),hppos⟩

theorem edge_ray_vertex {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (j : Fin 4) {n : E 2}
    (hn : IsEdgeNormal (fibre C.c C.k j) n) :
    ∃ p ∈ C.polarModel.extremePoints ℝ,∃ t : ℝ,0 < t ∧ planar p=t • n := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.1 hn.2
  have ha' := (mem_amax.1 ha).1
  have hb' := (mem_amax.1 hb).1
  obtain ⟨v,hv,hva⟩ := Finset.mem_image.1 ha'
  obtain ⟨w,hw,hwb⟩ := Finset.mem_image.1 hb'
  have hvj : C.c v=j := by simpa using hv
  have hwj : C.c w=j := by simpa using hw
  have hmax : ∀ z,C.c z=j → ⟪n,C.k z⟫≤⟪n,a⟫ := by
    intro z hz
    apply (mem_amax.1 ha).2
    exact Finset.mem_image.2 ⟨z,by simp [hz],rfl⟩
  have habn : ⟪n,a⟫=⟪n,b⟫ := inner_eq_of_mem_amax ha hb
  obtain ⟨p,hp,hpt,hpos⟩ := C.support_ray_vertex hP hrange j n hn.ne_zero ⟪n,a⟫ hmax
  have hval : C.value p v=C.value p w := by
    rw [hpt v hvj (by rw [hva]),hpt w hwj (by rw [hwb]; exact habn.symm)]
  have hperp := C.equal_value_orthogonal (hvj.trans hwj.symm) hval
  rw [hva,hwb] at hperp
  have hnperp : ⟪n,b-a⟫=0 := by rw [inner_sub_right]; linarith
  exact ⟨p,hp,positive_ray_of_orthogonal hn.1 (sub_ne_zero.2 hab.symm) hnperp hperp hpos⟩

end Config
end Kalai5.Cube3
