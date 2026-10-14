import Kalai5.Cube3.TranslatedOffNormal

/-! Three two-point ray families and one off-normal vertex force twenty facets. -/
namespace Kalai5.Cube3
open Set FullPrism
variable {x : Fin 8 → E5} {C : Config x}
namespace TranslatedTriangleFrame
variable (F : TranslatedTriangleFrame C)

include F in
theorem no_eighteen {P : Set E5} (hP : IsCSPolytope5 P)
    (hrange : range (pm16 x)=P.extremePoints ℝ) (hh : fvec P 4 ≤ 18)
    (hno : ¬ C.ExtraPM) : False := by
  classical
  obtain ⟨p,hp,hp0,hoff⟩ := F.off_normal_vertex hP hrange hh hno
  let n : E 2 := ‖planar p‖⁻¹ • planar p
  have hnorm : 0 < ‖planar p‖ := norm_pos_iff.2 hp0
  have hn : ‖n‖=1 := by
    dsimp only [n]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.2 hnorm)]
    exact inv_mul_cancel₀ hnorm.ne'
  have hpn : planar p=‖planar p‖ • n := by
    dsimp only [n]
    rw [smul_smul,mul_inv_cancel₀ hnorm.ne',one_smul]
  have hnT (i : Fin 3) : n ≠ F.T.triangle.normal i := by
    intro he
    exact hoff i ‖planar p‖ (by rwa [he] at hpn)
  have hnTneg (i : Fin 3) : n ≠ -F.T.triangle.normal i := by
    intro he
    apply hoff i (-‖planar p‖)
    calc
      planar p = ‖planar p‖ • n := hpn
      _ = (-‖planar p‖) • F.T.triangle.normal i := by rw [he,smul_neg,neg_smul]
  let G : PositiveFamily C Unit := PositiveFamily.onRay n hn (fun _ => p)
    (fun _ _ _ => Subsingleton.elim _ _) (fun _ => hp) (fun _ => ⟨_,hnorm,hpn⟩)
  have hfamilies (i : Fin 3) : ∃ H : PositiveFamily C (Fin 2),
      ∀ a,H.normal a=F.T.triangle.normal i :=
    TriangleFibre.aligned_two F.order F.T F.U F.single0 F.single1 hno
      i (F.pairing i) (F.normals i)
  choose H hH using hfamilies
  let K := PositiveFamily.sigma H
    (by intro i j hij a b; rw [hH,hH]; exact fun h => hij (F.T.triangle.normal_injective h))
    (by intro i j a b; rw [hH,hH]; exact F.T.triangle.no_opposite i j)
  let L := K.sum G
    (by intro a b; change (H a.1).normal a.2 ≠ n; rw [hH]; exact Ne.symm (hnT a.1))
    (by
      intro a b
      change (H a.1).normal a.2 ≠ -n
      rw [hH]
      intro he
      exact hnTneg a.1 (by rw [he,neg_neg]))
  exact L.no_eighteen hP hrange hh (by simp [Fintype.card_sigma])

end TranslatedTriangleFrame
end Kalai5.Cube3
