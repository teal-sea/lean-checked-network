import ACASChecked.ParamChunks.P1_0
import ACASChecked.ParamChunks.P1_1
import ACASChecked.ParamChunks.P1_2
import ACASChecked.ParamChunks.P1_3
import ACASChecked.ParamChunks.P1_4
import ACASChecked.ParamChunks.P1_5
import ACASChecked.ParamChunks.P1_6
import ACASChecked.ParamChunks.P1_7
import ACASChecked.ParamChunks.P1_8
import ACASChecked.ParamChunks.P1_9
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW1 : ∀ (i j : Fin 50),
    ((matrix (weights 1) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w1 j i := by
  intro i j
  fin_cases j
  · exact paramW1row0 i
  · exact paramW1row1 i
  · exact paramW1row2 i
  · exact paramW1row3 i
  · exact paramW1row4 i
  · exact paramW1row5 i
  · exact paramW1row6 i
  · exact paramW1row7 i
  · exact paramW1row8 i
  · exact paramW1row9 i
  · exact paramW1row10 i
  · exact paramW1row11 i
  · exact paramW1row12 i
  · exact paramW1row13 i
  · exact paramW1row14 i
  · exact paramW1row15 i
  · exact paramW1row16 i
  · exact paramW1row17 i
  · exact paramW1row18 i
  · exact paramW1row19 i
  · exact paramW1row20 i
  · exact paramW1row21 i
  · exact paramW1row22 i
  · exact paramW1row23 i
  · exact paramW1row24 i
  · exact paramW1row25 i
  · exact paramW1row26 i
  · exact paramW1row27 i
  · exact paramW1row28 i
  · exact paramW1row29 i
  · exact paramW1row30 i
  · exact paramW1row31 i
  · exact paramW1row32 i
  · exact paramW1row33 i
  · exact paramW1row34 i
  · exact paramW1row35 i
  · exact paramW1row36 i
  · exact paramW1row37 i
  · exact paramW1row38 i
  · exact paramW1row39 i
  · exact paramW1row40 i
  · exact paramW1row41 i
  · exact paramW1row42 i
  · exact paramW1row43 i
  · exact paramW1row44 i
  · exact paramW1row45 i
  · exact paramW1row46 i
  · exact paramW1row47 i
  · exact paramW1row48 i
  · exact paramW1row49 i
theorem paramB1 : ∀ j : Fin 50,
    (((biases 1).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b1.getScalar j := by decide +kernel
#print axioms paramW1
#print axioms paramB1
end ACASCommon
