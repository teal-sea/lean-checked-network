import ACASChecked.ParamChunks.P4_0
import ACASChecked.ParamChunks.P4_1
import ACASChecked.ParamChunks.P4_2
import ACASChecked.ParamChunks.P4_3
import ACASChecked.ParamChunks.P4_4
import ACASChecked.ParamChunks.P4_5
import ACASChecked.ParamChunks.P4_6
import ACASChecked.ParamChunks.P4_7
import ACASChecked.ParamChunks.P4_8
import ACASChecked.ParamChunks.P4_9
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW4 : ∀ (i j : Fin 50),
    ((matrix (weights 4) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w4 j i := by
  intro i j
  fin_cases j
  · exact paramW4row0 i
  · exact paramW4row1 i
  · exact paramW4row2 i
  · exact paramW4row3 i
  · exact paramW4row4 i
  · exact paramW4row5 i
  · exact paramW4row6 i
  · exact paramW4row7 i
  · exact paramW4row8 i
  · exact paramW4row9 i
  · exact paramW4row10 i
  · exact paramW4row11 i
  · exact paramW4row12 i
  · exact paramW4row13 i
  · exact paramW4row14 i
  · exact paramW4row15 i
  · exact paramW4row16 i
  · exact paramW4row17 i
  · exact paramW4row18 i
  · exact paramW4row19 i
  · exact paramW4row20 i
  · exact paramW4row21 i
  · exact paramW4row22 i
  · exact paramW4row23 i
  · exact paramW4row24 i
  · exact paramW4row25 i
  · exact paramW4row26 i
  · exact paramW4row27 i
  · exact paramW4row28 i
  · exact paramW4row29 i
  · exact paramW4row30 i
  · exact paramW4row31 i
  · exact paramW4row32 i
  · exact paramW4row33 i
  · exact paramW4row34 i
  · exact paramW4row35 i
  · exact paramW4row36 i
  · exact paramW4row37 i
  · exact paramW4row38 i
  · exact paramW4row39 i
  · exact paramW4row40 i
  · exact paramW4row41 i
  · exact paramW4row42 i
  · exact paramW4row43 i
  · exact paramW4row44 i
  · exact paramW4row45 i
  · exact paramW4row46 i
  · exact paramW4row47 i
  · exact paramW4row48 i
  · exact paramW4row49 i
theorem paramB4 : ∀ j : Fin 50,
    (((biases 4).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b4.getScalar j := by decide +kernel
#print axioms paramW4
#print axioms paramB4
end ACASCommon
