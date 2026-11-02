import LeanCheckedNetwork.Bridge
import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s0_step1.Trained.Weights
import LeanCheckedNetwork.Seal.C_x2_f015_H1024_s0_step1.ClockBias.Weights

/-! How the clock-plus-bias tables relate to the trained tables, in exact integer arithmetic. -/

namespace LeanCheckedNetwork.Seal.C_x2_f015_H1024_s0_step1

open LeanCheckedNetwork

theorem shape_E1 : shapeOk Trained.E1 ClockBias.E1 97 1024 0 = true := by decide +kernel
theorem shape_E2 : shapeOk Trained.E2 ClockBias.E2 97 1024 0 = true := by decide +kernel
theorem shape_W2 : shapeOk Trained.W2 ClockBias.W2 97 1024 0 = true := by decide +kernel

/-- The first 1024 columns of the reduction's `E1` are within 949/1000 of the trained `E1`'s energy. -/
theorem energy_E1 : energyWithin Trained.E1 ClockBias.E1 1024 949 1000 = true := by decide +kernel
theorem energy_E2 : energyWithin Trained.E2 ClockBias.E2 1024 941 1000 = true := by decide +kernel
theorem energy_W2 : energyWithin Trained.W2 ClockBias.W2 1024 940 1000 = true := by decide +kernel

/-- The 0 extra neurons are constant: `E1` entries 127, `E2` entries 0. -/
theorem extra_E1 : extraColsConst ClockBias.E1 1024 (.ofNat 127) = true := by decide +kernel
theorem extra_E2 : extraColsConst ClockBias.E2 1024 (.ofNat 0) = true := by decide +kernel

end LeanCheckedNetwork.Seal.C_x2_f015_H1024_s0_step1
