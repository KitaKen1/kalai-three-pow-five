import Kalai5.Gale.CheckU7a
import Kalai5.Gale.CheckU7b
import Kalai5.Gale.CheckU7c
import Kalai5.Gale.CheckU7d
import Kalai5.Gale.CheckAll

/-!
# The check of the dual of `U` over all sorted code sequences of seven points
-/

namespace Kalai5.Gale

set_option maxRecDepth 100000

theorem checkU7 : ∀ cs ∈ gen 7 0 0, (tab 7).checkU cs = true := by
  refine checkU_of_prefixes (tab 7) 4 3 0 0 ?_
  intro p hp
  rw [gen4_eq_7] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact chkU7_0
  · exact chkU7_1
  · exact chkU7_2
  · exact chkU7_3
  · exact chkU7_4
  · exact chkU7_5
  · exact chkU7_6
  · exact chkU7_7
  · exact chkU7_8
  · exact chkU7_9
  · exact chkU7_10
  · exact chkU7_11
  · exact chkU7_12
  · exact chkU7_13
  · exact chkU7_14
  · exact chkU7_15
  · exact chkU7_16
  · exact chkU7_17
  · exact chkU7_18
  · exact chkU7_19
  · exact chkU7_20
  · exact chkU7_21
  · exact chkU7_22
  · exact chkU7_23
  · exact chkU7_24
  · exact chkU7_25
  · exact chkU7_26
  · exact chkU7_27
  · exact chkU7_28
  · exact chkU7_29
  · exact chkU7_30
  · exact chkU7_31
  · exact chkU7_32
  · exact chkU7_33
  · exact chkU7_34
  · exact chkU7_35
  · exact chkU7_36
  · exact chkU7_37
  · exact chkU7_38
  · exact chkU7_39
  · exact chkU7_40
  · exact chkU7_41
  · exact chkU7_42
  · exact chkU7_43
  · exact chkU7_44
  · exact chkU7_45
  · exact chkU7_46
  · exact chkU7_47
  · exact chkU7_48
  · exact chkU7_49
  · exact chkU7_50
  · exact chkU7_51
  · exact chkU7_52
  · exact chkU7_53
  · exact chkU7_54
  · exact chkU7_55
  · exact chkU7_56
  · exact chkU7_57
  · exact chkU7_58
  · exact chkU7_59
  · exact chkU7_60
  · exact chkU7_61
  · exact chkU7_62
  · exact chkU7_63
  · exact chkU7_64
  · exact chkU7_65
  · exact chkU7_66
  · exact chkU7_67
  · exact chkU7_68
  · exact chkU7_69
  · exact chkU7_70
  · exact chkU7_71
  · exact chkU7_72
  · exact chkU7_73
  · exact chkU7_74
  · exact chkU7_75
  · exact chkU7_76
  · exact chkU7_77
  · exact chkU7_78
  · exact chkU7_79
  · exact chkU7_80
  · exact chkU7_81
  · exact chkU7_82
  · exact chkU7_83
  · exact chkU7_84
  · exact chkU7_85
  · exact chkU7_86
  · exact chkU7_87
  · exact chkU7_88
  · exact chkU7_89
  · exact chkU7_90
  · exact chkU7_91
  · exact chkU7_92
  · exact chkU7_93
  · exact chkU7_94
  · exact chkU7_95
  · exact chkU7_96
  · exact chkU7_97
  · exact chkU7_98
  · exact chkU7_99
  · exact chkU7_100
  · exact chkU7_101
  · exact chkU7_102
  · exact chkU7_103
  · exact chkU7_104
  · exact chkU7_105
  · exact chkU7_106
  · exact chkU7_107
  · exact chkU7_108
  · exact chkU7_109
  · exact chkU7_110
  · exact chkU7_111
  · exact chkU7_112
  · exact chkU7_113
  · exact chkU7_114
  · exact chkU7_115

end Kalai5.Gale
