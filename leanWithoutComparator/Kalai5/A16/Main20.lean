import Kalai5.A16.TableCheck20
import Kalai5.A16.Geom
import Kalai5.A16.Check20.Fam0
import Kalai5.A16.Check20.Fam1
import Kalai5.A16.Check20.Fam2
import Kalai5.A16.Check20.Fam3
import Kalai5.A16.Check20.Fam4
import Kalai5.A16.Check20.Fam5
import Kalai5.A16.Check20.Fam6
import Kalai5.A16.Check20.Fam7
import Kalai5.A16.Check20.Fam8
import Kalai5.A16.Check20.Fam9
import Kalai5.A16.Check20.Fam10
import Kalai5.A16.Check20.Fam11
import Kalai5.A16.Check20.Fam12
import Kalai5.A16.Check20.Fam13
import Kalai5.A16.Check20.Fam14
import Kalai5.A16.Check20.Fam15
import Kalai5.A16.Check20.Fam16
import Kalai5.A16.Check20.Fam17
import Kalai5.A16.Check20.Fam18
import Kalai5.A16.Check20.Fam19
import Kalai5.A16.Check20.Fam20
import Kalai5.A16.Check20.Fam21
import Kalai5.A16.Check20.Fam22
import Kalai5.A16.Check20.Fam23
import Kalai5.A16.Check20.Fam24
import Kalai5.A16.Check20.Fam25
import Kalai5.A16.Check20.Fam26
import Kalai5.A16.Check20.Fam27
import Kalai5.A16.Check20.Fam28
import Kalai5.A16.Check20.Fam29
import Kalai5.A16.Check20.Fam30
import Kalai5.A16.Check20.Fam31
import Kalai5.A16.Check20.Fam32
import Kalai5.A16.Check20.Fam33
import Kalai5.A16.Check20.Fam34
import Kalai5.A16.Check20.Fam35
import Kalai5.A16.Check20.Fam36
import Kalai5.A16.Check20.Fam37
import Kalai5.A16.Check20.Fam38
import Kalai5.A16.Check20.Fam39
import Kalai5.A16.Check20.Fam40
import Kalai5.A16.Check20.Fam41
import Kalai5.A16.Check20.Fam42
import Kalai5.A16.Check20.Fam43
import Kalai5.A16.Check20.Fam44
import Kalai5.A16.Check20.Fam45
import Kalai5.A16.Check20.Fam46
import Kalai5.A16.Check20.Fam47
import Kalai5.A16.Check20.Fam48
import Kalai5.A16.Check20.Fam49
import Kalai5.A16.Check20.Fam50
import Kalai5.A16.Check20.Fam51
import Kalai5.A16.Check20.Fam52
import Kalai5.A16.Check20.Fam53
import Kalai5.A16.Check20.Fam54
import Kalai5.A16.Check20.Fam55
import Kalai5.A16.Check20.Fam56
import Kalai5.A16.Check20.Fam57
import Kalai5.A16.Check20.Fam58
import Kalai5.A16.Check20.Fam59
import Kalai5.A16.Check20.Fam60

/-!
# A16 at twenty facets: assembly

The kernel checks of the 61 families at twenty facets (`Check20/FamK`, `checkN 21`: trees with
target twenty-one polar vertices and count leaves) and of the reduction table against `fams20`
(`TableCheck20`) give `GoalN 21`; with `a16_of_core` a centrally symmetric 5-polytope with sixteen
vertices, four linearly independent full normals and at most twenty facets has at least `243`
nonempty faces.
-/

namespace Kalai5

open Set

local notation "⟪" x ", " y "⟫" => inner ℝ x y

namespace A16

lemma entriesOK_append20 (fs : List FamX) (a b : List (List ℕ × TEntry)) :
    entriesOK fs (a ++ b) = (entriesOK fs a && entriesOK fs b) := by
  simp [entriesOK, List.all_append]

theorem table20_entries : entriesOK fams20 table = true := by
  simp only [table, entriesOK_append20, table0_ok20, table1_ok20, table2_ok20, table3_ok20,
    table4_ok20, table5_ok20, table6_ok20, table7_ok20, table8_ok20, table9_ok20, Bool.and_self]

theorem fams20_ok : ∀ X ∈ fams20, X.ok = true ∧ X.F.checkN 21 = true ∧
    (∀ r ∈ X.F.recs, X.F.recOK r = true) ∧ ∀ k < X.F.subs.length, X.F.subOK k = true := by
  intro X hX
  simp only [fams20, List.mem_cons, List.not_mem_nil, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨famXT0_ok, famT0_check, famT0_recs, famT0_subs⟩,
    ⟨famXT1_ok, famT1_check, famT1_recs, famT1_subs⟩,
    ⟨famXT2_ok, famT2_check, famT2_recs, famT2_subs⟩,
    ⟨famXT3_ok, famT3_check, famT3_recs, famT3_subs⟩,
    ⟨famXT4_ok, famT4_check, famT4_recs, famT4_subs⟩,
    ⟨famXT5_ok, famT5_check, famT5_recs, famT5_subs⟩,
    ⟨famXT6_ok, famT6_check, famT6_recs, famT6_subs⟩,
    ⟨famXT7_ok, famT7_check, famT7_recs, famT7_subs⟩,
    ⟨famXT8_ok, famT8_check, famT8_recs, famT8_subs⟩,
    ⟨famXT9_ok, famT9_check, famT9_recs, famT9_subs⟩,
    ⟨famXT10_ok, famT10_check, famT10_recs, famT10_subs⟩,
    ⟨famXT11_ok, famT11_check, famT11_recs, famT11_subs⟩,
    ⟨famXT12_ok, famT12_check, famT12_recs, famT12_subs⟩,
    ⟨famXT13_ok, famT13_check, famT13_recs, famT13_subs⟩,
    ⟨famXT14_ok, famT14_check, famT14_recs, famT14_subs⟩,
    ⟨famXT15_ok, famT15_check, famT15_recs, famT15_subs⟩,
    ⟨famXT16_ok, famT16_check, famT16_recs, famT16_subs⟩,
    ⟨famXT17_ok, famT17_check, famT17_recs, famT17_subs⟩,
    ⟨famXT18_ok, famT18_check, famT18_recs, famT18_subs⟩,
    ⟨famXT19_ok, famT19_check, famT19_recs, famT19_subs⟩,
    ⟨famXT20_ok, famT20_check, famT20_recs, famT20_subs⟩,
    ⟨famXT21_ok, famT21_check, famT21_recs, famT21_subs⟩,
    ⟨famXT22_ok, famT22_check, famT22_recs, famT22_subs⟩,
    ⟨famXT23_ok, famT23_check, famT23_recs, famT23_subs⟩,
    ⟨famXT24_ok, famT24_check, famT24_recs, famT24_subs⟩,
    ⟨famXT25_ok, famT25_check, famT25_recs, famT25_subs⟩,
    ⟨famXT26_ok, famT26_check, famT26_recs, famT26_subs⟩,
    ⟨famXT27_ok, famT27_check, famT27_recs, famT27_subs⟩,
    ⟨famXT28_ok, famT28_check, famT28_recs, famT28_subs⟩,
    ⟨famXT29_ok, famT29_check, famT29_recs, famT29_subs⟩,
    ⟨famXT30_ok, famT30_check, famT30_recs, famT30_subs⟩,
    ⟨famXT31_ok, famT31_check, famT31_recs, famT31_subs⟩,
    ⟨famXT32_ok, famT32_check, famT32_recs, famT32_subs⟩,
    ⟨famXT33_ok, famT33_check, famT33_recs, famT33_subs⟩,
    ⟨famXT34_ok, famT34_check, famT34_recs, famT34_subs⟩,
    ⟨famXT35_ok, famT35_check, famT35_recs, famT35_subs⟩,
    ⟨famXT36_ok, famT36_check, famT36_recs, famT36_subs⟩,
    ⟨famXT37_ok, famT37_check, famT37_recs, famT37_subs⟩,
    ⟨famXT38_ok, famT38_check, famT38_recs, famT38_subs⟩,
    ⟨famXT39_ok, famT39_check, famT39_recs, famT39_subs⟩,
    ⟨famXT40_ok, famT40_check, famT40_recs, famT40_subs⟩,
    ⟨famXT41_ok, famT41_check, famT41_recs, famT41_subs⟩,
    ⟨famXT42_ok, famT42_check, famT42_recs, famT42_subs⟩,
    ⟨famXT43_ok, famT43_check, famT43_recs, famT43_subs⟩,
    ⟨famXT44_ok, famT44_check, famT44_recs, famT44_subs⟩,
    ⟨famXT45_ok, famT45_check, famT45_recs, famT45_subs⟩,
    ⟨famXT46_ok, famT46_check, famT46_recs, famT46_subs⟩,
    ⟨famXT47_ok, famT47_check, famT47_recs, famT47_subs⟩,
    ⟨famXT48_ok, famT48_check, famT48_recs, famT48_subs⟩,
    ⟨famXT49_ok, famT49_check, famT49_recs, famT49_subs⟩,
    ⟨famXT50_ok, famT50_check, famT50_recs, famT50_subs⟩,
    ⟨famXT51_ok, famT51_check, famT51_recs, famT51_subs⟩,
    ⟨famXT52_ok, famT52_check, famT52_recs, famT52_subs⟩,
    ⟨famXT53_ok, famT53_check, famT53_recs, famT53_subs⟩,
    ⟨famXT54_ok, famT54_check, famT54_recs, famT54_subs⟩,
    ⟨famXT55_ok, famT55_check, famT55_recs, famT55_subs⟩,
    ⟨famXT56_ok, famT56_check, famT56_recs, famT56_subs⟩,
    ⟨famXT57_ok, famT57_check, famT57_recs, famT57_subs⟩,
    ⟨famXT58_ok, famT58_check, famT58_recs, famT58_subs⟩,
    ⟨famXT59_ok, famT59_check, famT59_recs, famT59_subs⟩,
    ⟨famXT60_ok, famT60_check, famT60_recs, famT60_subs⟩]

end A16

/-- **Rank 4 at twenty facets (A16).** A centrally symmetric 5-polytope with sixteen vertices, four
linearly independent full normals and at most twenty facets has at least `243` nonempty faces. -/
theorem IsCSPolytope5.a16_20 {P : Set E5} (hP : IsCSPolytope5 P) (h16 : fvec P 0 = 16)
    {u : Fin 4 → E5} (hu : LinearIndependent ℝ u)
    (hfull : ∀ i, ∀ x ∈ P.extremePoints ℝ, ⟪u i, x⟫ = 1 ∨ ⟪u i, x⟫ = -1)
    (hh : fvec P 4 ≤ 20) : 243 ≤ (faces P).ncard :=
  hP.a16_of_core (N := 21) (fun _ hq hinj hfib hspan =>
    A16.core16 A16.fams20 A16.table A16.fams20_ok A16.table_seqs20 A16.table20_entries hq hinj hfib
      hspan)
    h16 hu hfull (by omega)

end Kalai5
