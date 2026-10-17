import Transformer.Cached

namespace Transformer.CachedFixture

theorem empty : pkI [] = 0 := by decide +kernel
theorem negative : pkI [-7] = -7 := by decide +kernel
theorem signed : pkI [3, -2, 1] = Int.add 3
    (Int.mul (Int.ofNat B) (Int.add (-2) (Int.ofNat B))) := by decide +kernel
theorem default_inner : nth 0 ([[], [-1, 2]].map pkI) 8 = 0 := by decide +kernel
theorem default_outer : nth 0 (nth []
    (([[], [[-1, 2]]] : List (List (List Int))).map (List.map pkI)) 8) 2 = 0 := by
  decide +kernel
theorem empty_vector : nth 0 ([[], [-1, 2]].map pkI) 0 = 0 := by decide +kernel

-- The same map theorem covers both a missing head and a missing token.
theorem arbitrary_indices (vs : List (List (List Int))) (h i : Nat) :
    nth 0 (nth [] (vs.map (List.map pkI)) h) i =
      pkI (nth [] (nth [] vs h) i) := nth_pkI_map₂ vs h i

end Transformer.CachedFixture
