import Kalai5.Gale.Check7a
import Kalai5.Gale.Check7b
import Kalai5.Gale.Check7c
import Kalai5.Gale.Check7d
import Kalai5.Gale.Check56

/-!
# The certificate check over all sorted code sequences
-/

namespace Kalai5.Gale

set_option maxRecDepth 100000

lemma gen4_eq_7 : gen 4 0 0 = [[0, 0, 0, 0], [0, 0, 0, 1], [0, 0, 0, 2], [0, 0, 1, 1], [0, 0, 1, 2], [0, 0, 1, 3], [0, 0, 1, 4], [0, 0, 2, 2], [0, 0, 2, 3], [0, 0, 2, 4], [0, 1, 1, 1], [0, 1, 1, 2], [0, 1, 1, 3], [0, 1, 1, 4], [0, 1, 2, 2], [0, 1, 2, 3], [0, 1, 2, 4], [0, 1, 3, 3], [0, 1, 3, 4], [0, 1, 3, 5], [0, 1, 3, 6], [0, 1, 4, 4], [0, 1, 4, 5], [0, 1, 4, 6], [0, 2, 2, 2], [0, 2, 2, 3], [0, 2, 2, 4], [0, 2, 3, 3], [0, 2, 3, 4], [0, 2, 3, 5], [0, 2, 3, 6], [0, 2, 4, 4], [0, 2, 4, 5], [0, 2, 4, 6], [1, 1, 1, 1], [1, 1, 1, 2], [1, 1, 1, 3], [1, 1, 1, 4], [1, 1, 2, 2], [1, 1, 2, 3], [1, 1, 2, 4], [1, 1, 3, 3], [1, 1, 3, 4], [1, 1, 3, 5], [1, 1, 3, 6], [1, 1, 4, 4], [1, 1, 4, 5], [1, 1, 4, 6], [1, 2, 2, 2], [1, 2, 2, 3], [1, 2, 2, 4], [1, 2, 3, 3], [1, 2, 3, 4], [1, 2, 3, 5], [1, 2, 3, 6], [1, 2, 4, 4], [1, 2, 4, 5], [1, 2, 4, 6], [1, 3, 3, 3], [1, 3, 3, 4], [1, 3, 3, 5], [1, 3, 3, 6], [1, 3, 4, 4], [1, 3, 4, 5], [1, 3, 4, 6], [1, 3, 5, 5], [1, 3, 5, 6], [1, 3, 5, 7], [1, 3, 5, 8], [1, 3, 6, 6], [1, 3, 6, 7], [1, 3, 6, 8], [1, 4, 4, 4], [1, 4, 4, 5], [1, 4, 4, 6], [1, 4, 5, 5], [1, 4, 5, 6], [1, 4, 5, 7], [1, 4, 5, 8], [1, 4, 6, 6], [1, 4, 6, 7], [1, 4, 6, 8], [2, 2, 2, 2], [2, 2, 2, 3], [2, 2, 2, 4], [2, 2, 3, 3], [2, 2, 3, 4], [2, 2, 3, 5], [2, 2, 3, 6], [2, 2, 4, 4], [2, 2, 4, 5], [2, 2, 4, 6], [2, 3, 3, 3], [2, 3, 3, 4], [2, 3, 3, 5], [2, 3, 3, 6], [2, 3, 4, 4], [2, 3, 4, 5], [2, 3, 4, 6], [2, 3, 5, 5], [2, 3, 5, 6], [2, 3, 5, 7], [2, 3, 5, 8], [2, 3, 6, 6], [2, 3, 6, 7], [2, 3, 6, 8], [2, 4, 4, 4], [2, 4, 4, 5], [2, 4, 4, 6], [2, 4, 5, 5], [2, 4, 5, 6], [2, 4, 5, 7], [2, 4, 5, 8], [2, 4, 6, 6], [2, 4, 6, 7], [2, 4, 6, 8]] := by
  decide +kernel

theorem check7 : ∀ cs ∈ gen 7 0 0, (tab 7).check cs = true := by
  refine check_of_prefixes (tab 7) 4 3 0 0 ?_
  intro p hp
  rw [gen4_eq_7] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chk7_0
  · exact chk7_1
  · exact chk7_2
  · exact chk7_3
  · exact chk7_4
  · exact chk7_5
  · exact chk7_6
  · exact chk7_7
  · exact chk7_8
  · exact chk7_9
  · exact chk7_10
  · exact chk7_11
  · exact chk7_12
  · exact chk7_13
  · exact chk7_14
  · exact chk7_15
  · exact chk7_16
  · exact chk7_17
  · exact chk7_18
  · exact chk7_19
  · exact chk7_20
  · exact chk7_21
  · exact chk7_22
  · exact chk7_23
  · exact chk7_24
  · exact chk7_25
  · exact chk7_26
  · exact chk7_27
  · exact chk7_28
  · exact chk7_29
  · exact chk7_30
  · exact chk7_31
  · exact chk7_32
  · exact chk7_33
  · exact chk7_34
  · exact chk7_35
  · exact chk7_36
  · exact chk7_37
  · exact chk7_38
  · exact chk7_39
  · exact chk7_40
  · exact chk7_41
  · exact chk7_42
  · exact chk7_43
  · exact chk7_44
  · exact chk7_45
  · exact chk7_46
  · exact chk7_47
  · exact chk7_48
  · exact chk7_49
  · exact chk7_50
  · exact chk7_51
  · exact chk7_52
  · exact chk7_53
  · exact chk7_54
  · exact chk7_55
  · exact chk7_56
  · exact chk7_57
  · exact chk7_58
  · exact chk7_59
  · exact chk7_60
  · exact chk7_61
  · exact chk7_62
  · exact chk7_63
  · exact chk7_64
  · exact chk7_65
  · exact chk7_66
  · exact chk7_67
  · exact chk7_68
  · exact chk7_69
  · exact chk7_70
  · exact chk7_71
  · exact chk7_72
  · exact chk7_73
  · exact chk7_74
  · exact chk7_75
  · exact chk7_76
  · exact chk7_77
  · exact chk7_78
  · exact chk7_79
  · exact chk7_80
  · exact chk7_81
  · exact chk7_82
  · exact chk7_83
  · exact chk7_84
  · exact chk7_85
  · exact chk7_86
  · exact chk7_87
  · exact chk7_88
  · exact chk7_89
  · exact chk7_90
  · exact chk7_91
  · exact chk7_92
  · exact chk7_93
  · exact chk7_94
  · exact chk7_95
  · exact chk7_96
  · exact chk7_97
  · exact chk7_98
  · exact chk7_99
  · exact chk7_100
  · exact chk7_101
  · exact chk7_102
  · exact chk7_103
  · exact chk7_104
  · exact chk7_105
  · exact chk7_106
  · exact chk7_107
  · exact chk7_108
  · exact chk7_109
  · exact chk7_110
  · exact chk7_111
  · exact chk7_112
  · exact chk7_113
  · exact chk7_114
  · exact chk7_115

lemma gen2_eq_6 : gen 2 0 0 = [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [1, 3], [1, 4], [2, 2], [2, 3], [2, 4]] := by
  decide +kernel

theorem check6 : ∀ cs ∈ gen 6 0 0, (tab 6).check cs = true := by
  refine check_of_prefixes (tab 6) 2 4 0 0 ?_
  intro p hp
  rw [gen2_eq_6] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chk6_0
  · exact chk6_1
  · exact chk6_2
  · exact chk6_3
  · exact chk6_4
  · exact chk6_5
  · exact chk6_6
  · exact chk6_7
  · exact chk6_8
  · exact chk6_9

lemma gen1_eq_5 : gen 1 0 0 = [[0], [1], [2]] := by
  decide +kernel

theorem check5 : ∀ cs ∈ gen 5 0 0, (tab 5).check cs = true := by
  refine check_of_prefixes (tab 5) 1 4 0 0 ?_
  intro p hp
  rw [gen1_eq_5] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact chk5_0
  · exact chk5_1
  · exact chk5_2

/-- **The kernel-verified certificate check** for `5 ≤ n ≤ 7` points. -/
theorem check_all {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7) : ∀ cs ∈ gen n 0 0, (tab n).check cs = true := by
  interval_cases n
  · exact check5
  · exact check6
  · exact check7

end Kalai5.Gale
