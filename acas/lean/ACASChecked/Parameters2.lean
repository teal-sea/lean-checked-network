import ACASChecked.ParamChunks.P2_0
import ACASChecked.ParamChunks.P2_1
import ACASChecked.ParamChunks.P2_2
import ACASChecked.ParamChunks.P2_3
import ACASChecked.ParamChunks.P2_4
import ACASChecked.ParamChunks.P2_5
import ACASChecked.ParamChunks.P2_6
import ACASChecked.ParamChunks.P2_7
import ACASChecked.ParamChunks.P2_8
import ACASChecked.ParamChunks.P2_9
namespace ACASCommon
open RouteA RouteNC Spec TorchLean TorchLean.Tensor
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
theorem paramW2 : ∀ (i j : Fin 50),
    ((matrix (weights 2) i j : Int) : Rat) = (Q : Rat)*get2 Frozen.w2 j i := by
  intro i j
  fin_cases j
  · exact paramW2row0 i
  · exact paramW2row1 i
  · exact paramW2row2 i
  · exact paramW2row3 i
  · exact paramW2row4 i
  · exact paramW2row5 i
  · exact paramW2row6 i
  · exact paramW2row7 i
  · exact paramW2row8 i
  · exact paramW2row9 i
  · exact paramW2row10 i
  · exact paramW2row11 i
  · exact paramW2row12 i
  · exact paramW2row13 i
  · exact paramW2row14 i
  · exact paramW2row15 i
  · exact paramW2row16 i
  · exact paramW2row17 i
  · exact paramW2row18 i
  · exact paramW2row19 i
  · exact paramW2row20 i
  · exact paramW2row21 i
  · exact paramW2row22 i
  · exact paramW2row23 i
  · exact paramW2row24 i
  · exact paramW2row25 i
  · exact paramW2row26 i
  · exact paramW2row27 i
  · exact paramW2row28 i
  · exact paramW2row29 i
  · exact paramW2row30 i
  · exact paramW2row31 i
  · exact paramW2row32 i
  · exact paramW2row33 i
  · exact paramW2row34 i
  · exact paramW2row35 i
  · exact paramW2row36 i
  · exact paramW2row37 i
  · exact paramW2row38 i
  · exact paramW2row39 i
  · exact paramW2row40 i
  · exact paramW2row41 i
  · exact paramW2row42 i
  · exact paramW2row43 i
  · exact paramW2row44 i
  · exact paramW2row45 i
  · exact paramW2row46 i
  · exact paramW2row47 i
  · exact paramW2row48 i
  · exact paramW2row49 i
theorem paramB2 : ∀ j : Fin 50,
    (((biases 2).getD j 0 : Int) : Rat) = (Q : Rat)*Frozen.b2.getScalar j := by decide +kernel
#print axioms paramW2
#print axioms paramB2
end ACASCommon
