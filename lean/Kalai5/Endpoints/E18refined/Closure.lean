import Kalai5.Endpoints.E18refined.Certs
import Kalai5.Endpoints.OnePairClosure

/-! The refined B weight closes the cell (kP, G, Gs) = (3, 2, 14).
The two even-count splits cover all branches without polar row exclusions. -/

namespace Kalai5.E18refined

theorem cell_k3_g2s14 (C : Ctx 16 18 8 9 (tRow :: fake8) fake8)
    (hJF : ∀ R ∈ C.F.rows, 4 * R.r ≤ R.J)
    (hJS : ∀ R ∈ C.Fs.rows, 4 * R.r ≤ R.J)
    (hG : C.D.G = 2) (hS : C.D.Gs = 14)
    (hc8 : cnt8 C.F.rows = 6) (hs8 : sumR8 C.F.rows ≤ 60)
    (hql : ((C.F.rows.map q55RefinedRowWeight).sum : ℤ) ≤
      4 * C.D.A + 2 * ((C.D.f024 : ℤ) - 3 * C.D.y))
    (ht : (C.D.t : ℤ) ≤ 118) : False := by
  obtain ⟨q0, hq0⟩ := C.even_rS5
  rcases (show (C.rS5 : ℤ) ≤ 2 ∨ 4 ≤ (C.rS5 : ℤ) by omega) with b0 | b0
  · obtain ⟨q1, hq1⟩ := C.hD.even_e
    rcases (show (C.D.e : ℤ) ≤ 56 ∨ 58 ≤ (C.D.e : ℤ) by omega) with b1 | b1
    · exact leaf_b4_k3_g2s14ll C hJF hJS (by omega) (by omega) (by omega) (by omega)
        b0 b1 hc8 hs8 hql ht
    · exact leaf_b4_k3_g2s14lr C hJF hJS (by omega) (by omega) (by omega) (by omega)
        b0 b1 hc8 hs8 hql ht
  · exact leaf_b4_k3_g2s14r C hJF hJS (by omega) (by omega) (by omega) (by omega)
      b0 hc8 hs8 hql ht

/-- The earlier list is retained for its historical certificates. -/
def remainingCells (k : ℕ) : List (ℤ × ℤ) :=
  if k = 3 then (E18low.remainingCells 3).filter (fun c => decide (c ≠ (2, 14)))
  else E18low.remainingCells k

theorem remainingCells_lengths : (remainingCells 2).length = 9 ∧
    (remainingCells 3).length = 22 := by decide +kernel

end Kalai5.E18refined

namespace Kalai5

variable {P : Set E5} (hP : IsCSPolytope5 P)
include hP

theorem IsCSPolytope5.three_pow_five_16_18_refined_cell
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (hc : cnt8 (facetRows P) = 6)
    (hG : (flagDataOf P).G = 2) (hS : (flagDataOf P).Gs = 14) :
    243 ≤ (faces P).ncard := by
  by_cases hT : tRow ∈ facetRows P
  · exact hP.full_prism hv hT
  by_contra hlt
  have ht := hP.t_le_of_faces_lt (by omega)
  let C := hP.ctx16w (nS := 9) hv hh (by norm_num) hT
  have hridge := hP.full_ridge_rows hv
  rw [hh, hc] at hridge
  have hs : sumR8 (facetRows P) ≤ 60 := by omega
  exact E18refined.cell_k3_g2s14 C hP.facetRows_four_r_le hP.polar.facetRows_four_r_le
    hG hS hc hs (hP.q55_refined_rows hv) ht

/-- Counterexamples are confined to nine two-pair and twenty-two three-pair cells. -/
theorem IsCSPolytope5.fewFull18_residual_refined
    (hv : fvec P 0 = 16) (hh : fvec P 4 = 18)
    (h1 : 1 ≤ cnt8 (facetRows P)) (h6 : cnt8 (facetRows P) ≤ 6)
    (hlt : (faces P).ncard < 243) :
    (cnt8 (facetRows P) = 4 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18refined.remainingCells 2) ∨
    (cnt8 (facetRows P) = 6 ∧
      ((flagDataOf P).G, (flagDataOf P).Gs) ∈ E18refined.remainingCells 3) := by
  rcases hP.fewFull18_residual_two_three hv hh h1 h6 hlt with h | h
  · exact Or.inl ⟨h.1, by simpa [E18refined.remainingCells] using h.2⟩
  · have hne : ((flagDataOf P).G, (flagDataOf P).Gs) ≠ (2, 14) := by
      intro he
      exact (not_le_of_gt hlt) (hP.three_pow_five_16_18_refined_cell hv hh h.1
        (congrArg Prod.fst he) (congrArg Prod.snd he))
    exact Or.inr ⟨h.1, by simpa only [E18refined.remainingCells, ↓reduceIte,
      List.mem_filter, decide_eq_true_eq] using And.intro h.2 hne⟩

end Kalai5
