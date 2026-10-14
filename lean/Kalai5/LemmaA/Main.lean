import Kalai5.LemmaA.ReduceSound
import Kalai5.LemmaA.TableCheck0
import Kalai5.LemmaA.TableCheck1
import Kalai5.LemmaA.Check.Fam0
import Kalai5.LemmaA.Check.Fam12
import Kalai5.LemmaA.Check.Fam15
import Kalai5.LemmaA.Check.Fam22
import Kalai5.LemmaA.Check.Fam26
import Kalai5.LemmaA.Check.Fam32
import Kalai5.LemmaA.Check.Fam38
import Kalai5.LemmaA.Check.Fam39
import Kalai5.LemmaA.Check.Fam44

/-!
# Lemma A: the combinatorial core, with all kernel checks discharged
-/

namespace Kalai5.LemmaA

open Set

theorem repFams_ok : ∀ X ∈ repFams, X.ok = true ∧ X.F.check = true := by
  intro X hX
  simp only [repFams, List.mem_cons, List.mem_nil_iff, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨famX0_ok, fam0_check⟩
  · exact ⟨famX12_ok, fam12_check⟩
  · exact ⟨famX15_ok, fam15_check⟩
  · exact ⟨famX22_ok, fam22_check⟩
  · exact ⟨famX26_ok, fam26_check⟩
  · exact ⟨famX32_ok, fam32_check⟩
  · exact ⟨famX38_ok, fam38_check⟩
  · exact ⟨famX39_ok, fam39_check⟩
  · exact ⟨famX44_ok, fam44_check⟩

theorem a1table_entries : entriesOK repFams a1table = true := by
  have h : ∀ t₁ t₂ : List (List ℕ × TEntry), entriesOK repFams t₁ = true → entriesOK repFams t₂ = true →
      entriesOK repFams (t₁ ++ t₂) = true := fun t₁ t₂ h₁ h₂ => by
    simp only [entriesOK, List.all_append, Bool.and_eq_true] at h₁ h₂ ⊢; exact ⟨h₁, h₂⟩
  unfold a1table
  exact (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ (h _ _ a1table0_ok a1table1_ok) a1table2_ok) a1table3_ok) a1table4_ok) a1table5_ok) a1table6_ok) a1table7_ok) a1table8_ok) a1table9_ok) a1table10_ok) a1table11_ok) a1table12_ok) a1table13_ok) a1table14_ok) a1table15_ok)

/-- **Lemma A, combinatorial core**: seven points `y_v` with first four coordinates `±1`, the
fourteen points `±y_v` distinct, no three of them agreeing in the first four coordinates, spanning
`ℝ⁵`: their convex hull has at least 243 faces. -/
theorem lemmaA_core {y : Fin 7 → E5}
    (hq : ∀ v (j : Fin 4), y v j.castSucc = 1 ∨ y v j.castSucc = -1)
    (hinj : Function.Injective (pm y))
    (hfib : ∀ x₁ ∈ range (pm y), ∀ x₂ ∈ range (pm y), ∀ x₃ ∈ range (pm y), x₁ ≠ x₂ → x₁ ≠ x₃ →
      x₂ ≠ x₃ → (∀ j : Fin 4, x₁ j.castSucc = x₂ j.castSucc ∧ x₁ j.castSucc = x₃ j.castSucc) →
        False)
    (hspan : ∀ φ : E5 →ₗ[ℝ] ℝ, (∀ x ∈ range (pm y), φ x = 0) → φ = 0) :
    243 ≤ (faces (convexHull ℝ (range (pm y)))).ncard :=
  core repFams a1table repFams_ok a1table_seqs a1table_entries hq hinj hfib hspan

end Kalai5.LemmaA
