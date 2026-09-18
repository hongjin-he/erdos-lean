import ErdosLean.Erdos612.Statement

/-! # Erdős 612, part: the two coefficients used -/

namespace Erdos612

theorem evenCoeff_two : evenCoeff 2 = 16 / 7 := by
  norm_num [evenCoeff]

theorem oddCoeff_four : oddCoeff 4 = 11 / 4 := by
  norm_num [oddCoeff]

end Erdos612
