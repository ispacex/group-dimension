import GroupDimension.Cert1024.Data.C00
import GroupDimension.Cert1024.Data.C01
import GroupDimension.Cert1024.Data.C02
import GroupDimension.Cert1024.Data.C03
import GroupDimension.Cert1024.Data.C04
import GroupDimension.Cert1024.Data.C05
import GroupDimension.Cert1024.Data.C06
import GroupDimension.Cert1024.Data.C07
import GroupDimension.Cert1024.Data.C08
import GroupDimension.Cert1024.Data.C09
import GroupDimension.Cert1024.Data.C10
import GroupDimension.Cert1024.Data.C11
import GroupDimension.Cert1024.Data.C12
import GroupDimension.Cert1024.Data.C13
import GroupDimension.Cert1024.Data.C14
import GroupDimension.Cert1024.Data.C15
import GroupDimension.Cert1024.Data.C16
import GroupDimension.Cert1024.Data.C17
import GroupDimension.Cert1024.Data.C18
import GroupDimension.Cert1024.Data.C19
import GroupDimension.Cert1024.Data.C20
import GroupDimension.Cert1024.Data.C21
import GroupDimension.Cert1024.Data.C22
import GroupDimension.Cert1024.Data.C23
import GroupDimension.Cert1024.Data.C24
import GroupDimension.Cert1024.Data.C25
import GroupDimension.Cert1024.Data.C26
import GroupDimension.Cert1024.Data.C27
import GroupDimension.Cert1024.Data.C28
import GroupDimension.Cert1024.Data.C29
import GroupDimension.Cert1024.Data.C30
import GroupDimension.Cert1024.Data.C31
import GroupDimension.Cert1024.Data.C32
import GroupDimension.Cert1024.Data.C33

/-! All 3400 certificates of Prop. 5.3. -/

namespace GroupDimension.Cert1024.Data

/-- The 3400 lines, in the order of `compute/pq1024/results/candidates.csv` sorted by
`(parent, k)`. -/
def cands : List String := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05 ++ c06 ++ c07 ++ c08 ++ c09 ++ c10 ++ c11 ++ c12 ++ c13 ++ c14 ++ c15 ++ c16 ++ c17 ++ c18 ++ c19 ++ c20 ++ c21 ++ c22 ++ c23 ++ c24 ++ c25 ++ c26 ++ c27 ++ c28 ++ c29 ++ c30 ++ c31 ++ c32 ++ c33

theorem cands_length : cands.length = 3400 := by
  simp only [cands, List.length_append]; rfl

theorem cands_ok : cands.all checkStr = true := by
  simp only [cands, List.all_append, c00_ok, c01_ok, c02_ok, c03_ok, c04_ok, c05_ok, c06_ok, c07_ok, c08_ok, c09_ok, c10_ok, c11_ok, c12_ok, c13_ok, c14_ok, c15_ok, c16_ok, c17_ok, c18_ok, c19_ok, c20_ok, c21_ok, c22_ok, c23_ok, c24_ok, c25_ok, c26_ok, c27_ok, c28_ok, c29_ok, c30_ok, c31_ok, c32_ok, c33_ok, Bool.and_self]

end GroupDimension.Cert1024.Data
