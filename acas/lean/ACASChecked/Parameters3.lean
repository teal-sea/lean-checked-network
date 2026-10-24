import ACASChecked.ParamChunks.P3_0
import ACASChecked.ParamChunks.P3_1
import ACASChecked.ParamChunks.P3_2
import ACASChecked.ParamChunks.P3_3
import ACASChecked.ParamChunks.P3_4
import ACASChecked.ParamChunks.P3_5
import ACASChecked.ParamChunks.P3_6
import ACASChecked.ParamChunks.P3_7
import ACASChecked.ParamChunks.P3_8
import ACASChecked.ParamChunks.P3_9
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW3 : ∀ (i j : Fin 50),
    ((matrix (weights 3) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w3 j i := by
  intro i j
  fin_cases j
  · exact paramW3row0 i
  · exact paramW3row1 i
  · exact paramW3row2 i
  · exact paramW3row3 i
  · exact paramW3row4 i
  · exact paramW3row5 i
  · exact paramW3row6 i
  · exact paramW3row7 i
  · exact paramW3row8 i
  · exact paramW3row9 i
  · exact paramW3row10 i
  · exact paramW3row11 i
  · exact paramW3row12 i
  · exact paramW3row13 i
  · exact paramW3row14 i
  · exact paramW3row15 i
  · exact paramW3row16 i
  · exact paramW3row17 i
  · exact paramW3row18 i
  · exact paramW3row19 i
  · exact paramW3row20 i
  · exact paramW3row21 i
  · exact paramW3row22 i
  · exact paramW3row23 i
  · exact paramW3row24 i
  · exact paramW3row25 i
  · exact paramW3row26 i
  · exact paramW3row27 i
  · exact paramW3row28 i
  · exact paramW3row29 i
  · exact paramW3row30 i
  · exact paramW3row31 i
  · exact paramW3row32 i
  · exact paramW3row33 i
  · exact paramW3row34 i
  · exact paramW3row35 i
  · exact paramW3row36 i
  · exact paramW3row37 i
  · exact paramW3row38 i
  · exact paramW3row39 i
  · exact paramW3row40 i
  · exact paramW3row41 i
  · exact paramW3row42 i
  · exact paramW3row43 i
  · exact paramW3row44 i
  · exact paramW3row45 i
  · exact paramW3row46 i
  · exact paramW3row47 i
  · exact paramW3row48 i
  · exact paramW3row49 i
theorem paramB3 : ∀ j : Fin 50,
    (((biases 3).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b3.getScalar j := by decide +kernel
#print axioms paramW3
#print axioms paramB3
end ACASCommon
