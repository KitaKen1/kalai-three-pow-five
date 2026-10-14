import Kalai5.Gale.CheckX7a
import Kalai5.Gale.CheckX7b
import Kalai5.Gale.CheckX7c
import Kalai5.Gale.CheckX7d
import Kalai5.Gale.CheckX7e
import Kalai5.Gale.CheckX7f
import Kalai5.Gale.CheckX7g
import Kalai5.Gale.CheckX7h
import Kalai5.Gale.CheckX7i
import Kalai5.Gale.CheckX7j
import Kalai5.Gale.CheckX7k
import Kalai5.Gale.CheckX7l
import Kalai5.Gale.CheckX7m
import Kalai5.Gale.CheckX56
import Kalai5.Gale.CheckAll

/-!
# The extended certificate check over all sorted code sequences
-/

namespace Kalai5.Gale

set_option maxRecDepth 100000

theorem checkX7 : ∀ cs ∈ gen 7 0 0, (tab 7).checkX cs = true := by
  refine checkX_of_prefixes (tab 7) 4 3 0 0 ?_
  intro p hp
  rw [gen4_eq_7] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkX7_0
  · exact chkX7_1
  · exact chkX7_2
  · exact chkX7_3
  · exact chkX7_4
  · exact chkX7_5
  · exact chkX7_6
  · exact chkX7_7
  · exact chkX7_8
  · exact chkX7_9
  · exact chkX7_10
  · exact chkX7_11
  · exact chkX7_12
  · exact chkX7_13
  · exact chkX7_14
  · exact chkX7_15
  · exact chkX7_16
  · exact chkX7_17
  · exact chkX7_18
  · exact chkX7_19
  · exact chkX7_20
  · exact chkX7_21
  · exact chkX7_22
  · exact chkX7_23
  · exact chkX7_24
  · exact chkX7_25
  · exact chkX7_26
  · exact chkX7_27
  · exact chkX7_28
  · exact chkX7_29
  · exact chkX7_30
  · exact chkX7_31
  · exact chkX7_32
  · exact chkX7_33
  · exact chkX7_34
  · exact chkX7_35
  · exact chkX7_36
  · exact chkX7_37
  · exact chkX7_38
  · exact chkX7_39
  · exact chkX7_40
  · exact chkX7_41
  · exact chkX7_42
  · exact chkX7_43
  · exact chkX7_44
  · exact chkX7_45
  · exact chkX7_46
  · exact chkX7_47
  · exact chkX7_48
  · exact chkX7_49
  · exact chkX7_50
  · exact chkX7_51
  · exact chkX7_52
  · exact chkX7_53
  · exact chkX7_54
  · exact chkX7_55
  · exact chkX7_56
  · exact chkX7_57
  · exact chkX7_58
  · exact chkX7_59
  · exact chkX7_60
  · exact chkX7_61
  · exact chkX7_62
  · exact chkX7_63
  · exact chkX7_64
  · exact chkX7_65
  · exact chkX7_66
  · exact chkX7_67
  · exact chkX7_68
  · exact chkX7_69
  · exact chkX7_70
  · exact chkX7_71
  · exact chkX7_72
  · exact chkX7_73
  · exact chkX7_74
  · exact chkX7_75
  · exact chkX7_76
  · exact chkX7_77
  · exact chkX7_78
  · exact chkX7_79
  · exact chkX7_80
  · exact chkX7_81
  · exact chkX7_82
  · exact chkX7_83
  · exact chkX7_84
  · exact chkX7_85
  · exact chkX7_86
  · exact chkX7_87
  · exact chkX7_88
  · exact chkX7_89
  · exact chkX7_90
  · exact chkX7_91
  · exact chkX7_92
  · exact chkX7_93
  · exact chkX7_94
  · exact chkX7_95
  · exact chkX7_96
  · exact chkX7_97
  · exact chkX7_98
  · exact chkX7_99
  · exact chkX7_100
  · exact chkX7_101
  · exact chkX7_102
  · exact chkX7_103
  · exact chkX7_104
  · exact chkX7_105
  · exact chkX7_106
  · exact chkX7_107
  · exact chkX7_108
  · exact chkX7_109
  · exact chkX7_110
  · exact chkX7_111
  · exact chkX7_112
  · exact chkX7_113
  · exact chkX7_114
  · exact chkX7_115

theorem checkX6 : ∀ cs ∈ gen 6 0 0, (tab 6).checkX cs = true := by
  refine checkX_of_prefixes (tab 6) 2 4 0 0 ?_
  intro p hp
  rw [gen2_eq_6] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkX6_0
  · exact chkX6_1
  · exact chkX6_2
  · exact chkX6_3
  · exact chkX6_4
  · exact chkX6_5
  · exact chkX6_6
  · exact chkX6_7
  · exact chkX6_8
  · exact chkX6_9

theorem checkX5 : ∀ cs ∈ gen 5 0 0, (tab 5).checkX cs = true := by
  refine checkX_of_prefixes (tab 5) 1 4 0 0 ?_
  intro p hp
  rw [gen1_eq_5] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact chkX5_0
  · exact chkX5_1
  · exact chkX5_2

/-- **The kernel-verified extended certificate check** for `5 ≤ n ≤ 7` points. -/
theorem checkX_all {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) :
    ∀ cs ∈ gen n 0 0, (tab n).checkX cs = true := by
  interval_cases n
  · exact checkX5
  · exact checkX6
  · exact checkX7

end Kalai5.Gale
