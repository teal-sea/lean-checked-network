import ACASChecked.ParamChunks.P5_0
import ACASChecked.ParamChunks.P5_1
import ACASChecked.ParamChunks.P5_2
import ACASChecked.ParamChunks.P5_3
import ACASChecked.ParamChunks.P5_4
import ACASChecked.ParamChunks.P5_5
import ACASChecked.ParamChunks.P5_6
import ACASChecked.ParamChunks.P5_7
import ACASChecked.ParamChunks.P5_8
import ACASChecked.ParamChunks.P5_9
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW5 : ∀ (i j : Fin 50),
    ((matrix (weights 5) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w5 j i := by
  intro i j
  fin_cases j
  · exact paramW5row0 i
  · exact paramW5row1 i
  · exact paramW5row2 i
  · exact paramW5row3 i
  · exact paramW5row4 i
  · exact paramW5row5 i
  · exact paramW5row6 i
  · exact paramW5row7 i
  · exact paramW5row8 i
  · exact paramW5row9 i
  · exact paramW5row10 i
  · exact paramW5row11 i
  · exact paramW5row12 i
  · exact paramW5row13 i
  · exact paramW5row14 i
  · exact paramW5row15 i
  · exact paramW5row16 i
  · exact paramW5row17 i
  · exact paramW5row18 i
  · exact paramW5row19 i
  · exact paramW5row20 i
  · exact paramW5row21 i
  · exact paramW5row22 i
  · exact paramW5row23 i
  · exact paramW5row24 i
  · exact paramW5row25 i
  · exact paramW5row26 i
  · exact paramW5row27 i
  · exact paramW5row28 i
  · exact paramW5row29 i
  · exact paramW5row30 i
  · exact paramW5row31 i
  · exact paramW5row32 i
  · exact paramW5row33 i
  · exact paramW5row34 i
  · exact paramW5row35 i
  · exact paramW5row36 i
  · exact paramW5row37 i
  · exact paramW5row38 i
  · exact paramW5row39 i
  · exact paramW5row40 i
  · exact paramW5row41 i
  · exact paramW5row42 i
  · exact paramW5row43 i
  · exact paramW5row44 i
  · exact paramW5row45 i
  · exact paramW5row46 i
  · exact paramW5row47 i
  · exact paramW5row48 i
  · exact paramW5row49 i
theorem paramB5 : ∀ j : Fin 50,
    (((biases 5).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b5.getScalar j := by decide +kernel
#print axioms paramW5
#print axioms paramB5
end ACASCommon
