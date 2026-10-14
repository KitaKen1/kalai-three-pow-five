import Kalai5.LemmaA.Table
import Kalai5.LemmaA.Fams

namespace Kalai5.LemmaA

set_option maxRecDepth 100000

theorem a1table_seqs : seqsOK a1table = true := by decide +kernel

theorem famX0_ok : famX0.ok = true := by decide +kernel

theorem famX12_ok : famX12.ok = true := by decide +kernel

theorem famX15_ok : famX15.ok = true := by decide +kernel

theorem famX22_ok : famX22.ok = true := by decide +kernel

theorem famX26_ok : famX26.ok = true := by decide +kernel

theorem famX32_ok : famX32.ok = true := by decide +kernel

theorem famX38_ok : famX38.ok = true := by decide +kernel

theorem famX39_ok : famX39.ok = true := by decide +kernel

theorem famX44_ok : famX44.ok = true := by decide +kernel

theorem a1table0_ok : entriesOK repFams a1table0 = true := by decide +kernel

theorem a1table1_ok : entriesOK repFams a1table1 = true := by decide +kernel

theorem a1table2_ok : entriesOK repFams a1table2 = true := by decide +kernel

theorem a1table3_ok : entriesOK repFams a1table3 = true := by decide +kernel

theorem a1table4_ok : entriesOK repFams a1table4 = true := by decide +kernel

theorem a1table5_ok : entriesOK repFams a1table5 = true := by decide +kernel

theorem a1table6_ok : entriesOK repFams a1table6 = true := by decide +kernel

theorem a1table7_ok : entriesOK repFams a1table7 = true := by decide +kernel

end Kalai5.LemmaA
