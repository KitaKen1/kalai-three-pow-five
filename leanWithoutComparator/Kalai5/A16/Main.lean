import Kalai5.A16.TableCheck
import Kalai5.A16.Geom
import Kalai5.A16.Check.Fam0
import Kalai5.A16.Check.Fam1
import Kalai5.A16.Check.Fam2
import Kalai5.A16.Check.Fam3
import Kalai5.A16.Check.Fam4
import Kalai5.A16.Check.Fam5
import Kalai5.A16.Check.Fam6
import Kalai5.A16.Check.Fam7
import Kalai5.A16.Check.Fam8
import Kalai5.A16.Check.Fam9
import Kalai5.A16.Check.Fam10
import Kalai5.A16.Check.Fam11
import Kalai5.A16.Check.Fam12
import Kalai5.A16.Check.Fam13
import Kalai5.A16.Check.Fam14
import Kalai5.A16.Check.Fam15
import Kalai5.A16.Check.Fam16
import Kalai5.A16.Check.Fam17
import Kalai5.A16.Check.Fam18
import Kalai5.A16.Check.Fam19
import Kalai5.A16.Check.Fam20
import Kalai5.A16.Check.Fam21
import Kalai5.A16.Check.Fam22
import Kalai5.A16.Check.Fam23
import Kalai5.A16.Check.Fam24
import Kalai5.A16.Check.Fam25
import Kalai5.A16.Check.Fam26
import Kalai5.A16.Check.Fam27
import Kalai5.A16.Check.Fam28
import Kalai5.A16.Check.Fam29
import Kalai5.A16.Check.Fam30
import Kalai5.A16.Check.Fam31
import Kalai5.A16.Check.Fam32
import Kalai5.A16.Check.Fam33
import Kalai5.A16.Check.Fam34
import Kalai5.A16.Check.Fam35
import Kalai5.A16.Check.Fam36
import Kalai5.A16.Check.Fam37
import Kalai5.A16.Check.Fam38
import Kalai5.A16.Check.Fam39
import Kalai5.A16.Check.Fam40
import Kalai5.A16.Check.Fam41
import Kalai5.A16.Check.Fam42
import Kalai5.A16.Check.Fam43
import Kalai5.A16.Check.Fam44
import Kalai5.A16.Check.Fam45
import Kalai5.A16.Check.Fam46
import Kalai5.A16.Check.Fam47
import Kalai5.A16.Check.Fam48
import Kalai5.A16.Check.Fam49
import Kalai5.A16.Check.Fam50
import Kalai5.A16.Check.Fam51
import Kalai5.A16.Check.Fam52
import Kalai5.A16.Check.Fam53
import Kalai5.A16.Check.Fam54
import Kalai5.A16.Check.Fam55
import Kalai5.A16.Check.Fam56
import Kalai5.A16.Check.Fam57
import Kalai5.A16.Check.Fam58
import Kalai5.A16.Check.Fam59
import Kalai5.A16.Check.Fam60

/-!
# A16: assembly

The kernel checks of the 61 families (`Check/FamK`) and of the reduction table (`TableCheck`) give
the combinatorial core `core16`; with `a16_of_core` this is the rank-4 case: a centrally symmetric
5-polytope with sixteen vertices, four linearly independent full normals and at most eighteen
facets has at least `243` nonempty faces.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace A16

lemma entriesOK_append (fs : List FamX) (a b : List (List ℕ × TEntry)) :
    entriesOK fs (a ++ b) = (entriesOK fs a && entriesOK fs b) := by
  simp [entriesOK, List.all_append]

theorem table_entries : entriesOK fams table = true := by
  simp only [table, entriesOK_append, table0_ok, table1_ok, table2_ok, table3_ok, table4_ok,
    table5_ok, table6_ok, table7_ok, table8_ok, table9_ok, Bool.and_self]

theorem fams_ok : ∀ X ∈ fams, X.ok = true ∧ X.F.check = true ∧
    (∀ r ∈ X.F.recs, X.F.recOK r = true) ∧ ∀ k < X.F.subs.length, X.F.subOK k = true := by
  intro X hX
  simp only [fams, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨famX0_ok, fam0_check, fam0_recs, fam0_subs⟩,
    ⟨famX1_ok, fam1_check, fam1_recs, fam1_subs⟩,
    ⟨famX2_ok, fam2_check, fam2_recs, fam2_subs⟩,
    ⟨famX3_ok, fam3_check, fam3_recs, fam3_subs⟩,
    ⟨famX4_ok, fam4_check, fam4_recs, fam4_subs⟩,
    ⟨famX5_ok, fam5_check, fam5_recs, fam5_subs⟩,
    ⟨famX6_ok, fam6_check, fam6_recs, fam6_subs⟩,
    ⟨famX7_ok, fam7_check, fam7_recs, fam7_subs⟩,
    ⟨famX8_ok, fam8_check, fam8_recs, fam8_subs⟩,
    ⟨famX9_ok, fam9_check, fam9_recs, fam9_subs⟩,
    ⟨famX10_ok, fam10_check, fam10_recs, fam10_subs⟩,
    ⟨famX11_ok, fam11_check, fam11_recs, fam11_subs⟩,
    ⟨famX12_ok, fam12_check, fam12_recs, fam12_subs⟩,
    ⟨famX13_ok, fam13_check, fam13_recs, fam13_subs⟩,
    ⟨famX14_ok, fam14_check, fam14_recs, fam14_subs⟩,
    ⟨famX15_ok, fam15_check, fam15_recs, fam15_subs⟩,
    ⟨famX16_ok, fam16_check, fam16_recs, fam16_subs⟩,
    ⟨famX17_ok, fam17_check, fam17_recs, fam17_subs⟩,
    ⟨famX18_ok, fam18_check, fam18_recs, fam18_subs⟩,
    ⟨famX19_ok, fam19_check, fam19_recs, fam19_subs⟩,
    ⟨famX20_ok, fam20_check, fam20_recs, fam20_subs⟩,
    ⟨famX21_ok, fam21_check, fam21_recs, fam21_subs⟩,
    ⟨famX22_ok, fam22_check, fam22_recs, fam22_subs⟩,
    ⟨famX23_ok, fam23_check, fam23_recs, fam23_subs⟩,
    ⟨famX24_ok, fam24_check, fam24_recs, fam24_subs⟩,
    ⟨famX25_ok, fam25_check, fam25_recs, fam25_subs⟩,
    ⟨famX26_ok, fam26_check, fam26_recs, fam26_subs⟩,
    ⟨famX27_ok, fam27_check, fam27_recs, fam27_subs⟩,
    ⟨famX28_ok, fam28_check, fam28_recs, fam28_subs⟩,
    ⟨famX29_ok, fam29_check, fam29_recs, fam29_subs⟩,
    ⟨famX30_ok, fam30_check, fam30_recs, fam30_subs⟩,
    ⟨famX31_ok, fam31_check, fam31_recs, fam31_subs⟩,
    ⟨famX32_ok, fam32_check, fam32_recs, fam32_subs⟩,
    ⟨famX33_ok, fam33_check, fam33_recs, fam33_subs⟩,
    ⟨famX34_ok, fam34_check, fam34_recs, fam34_subs⟩,
    ⟨famX35_ok, fam35_check, fam35_recs, fam35_subs⟩,
    ⟨famX36_ok, fam36_check, fam36_recs, fam36_subs⟩,
    ⟨famX37_ok, fam37_check, fam37_recs, fam37_subs⟩,
    ⟨famX38_ok, fam38_check, fam38_recs, fam38_subs⟩,
    ⟨famX39_ok, fam39_check, fam39_recs, fam39_subs⟩,
    ⟨famX40_ok, fam40_check, fam40_recs, fam40_subs⟩,
    ⟨famX41_ok, fam41_check, fam41_recs, fam41_subs⟩,
    ⟨famX42_ok, fam42_check, fam42_recs, fam42_subs⟩,
    ⟨famX43_ok, fam43_check, fam43_recs, fam43_subs⟩,
    ⟨famX44_ok, fam44_check, fam44_recs, fam44_subs⟩,
    ⟨famX45_ok, fam45_check, fam45_recs, fam45_subs⟩,
    ⟨famX46_ok, fam46_check, fam46_recs, fam46_subs⟩,
    ⟨famX47_ok, fam47_check, fam47_recs, fam47_subs⟩,
    ⟨famX48_ok, fam48_check, fam48_recs, fam48_subs⟩,
    ⟨famX49_ok, fam49_check, fam49_recs, fam49_subs⟩,
    ⟨famX50_ok, fam50_check, fam50_recs, fam50_subs⟩,
    ⟨famX51_ok, fam51_check, fam51_recs, fam51_subs⟩,
    ⟨famX52_ok, fam52_check, fam52_recs, fam52_subs⟩,
    ⟨famX53_ok, fam53_check, fam53_recs, fam53_subs⟩,
    ⟨famX54_ok, fam54_check, fam54_recs, fam54_subs⟩,
    ⟨famX55_ok, fam55_check, fam55_recs, fam55_subs⟩,
    ⟨famX56_ok, fam56_check, fam56_recs, fam56_subs⟩,
    ⟨famX57_ok, fam57_check, fam57_recs, fam57_subs⟩,
    ⟨famX58_ok, fam58_check, fam58_recs, fam58_subs⟩,
    ⟨famX59_ok, fam59_check, fam59_recs, fam59_subs⟩,
    ⟨famX60_ok, fam60_check, fam60_recs, fam60_subs⟩]

end A16

/-- **Rank 4 (A16).** A centrally symmetric 5-polytope with sixteen vertices, four linearly
independent full normals and at most eighteen facets has at least `243` nonempty faces. -/
theorem IsCSPolytope5.a16 {P : Set E5} (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16)
    {u : Fin 4 → E5} (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1)
    (hh : fvec P 4 ≤ 18) : 243 ≤ (faces P).ncard :=
  hP.a16_of_core (N := 19) (fun _ hq hinj hfib hspan =>
    A16.core16 A16.fams A16.table A16.fams_ok A16.table_seqs A16.table_entries hq hinj hfib hspan)
    h16 hu hfull (by omega)

end Kalai5
