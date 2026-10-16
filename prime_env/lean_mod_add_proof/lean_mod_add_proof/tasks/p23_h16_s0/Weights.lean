import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 23

23 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=23 H=16 seed=0 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 23

def E1 : List (List Int) := [
  [(.negSucc 75), (.ofNat 93), (.ofNat 99), (.negSucc 97), (.negSucc 57), (.ofNat 80), (.ofNat 114), (.ofNat 99), (.ofNat 94), (.negSucc 86), (.negSucc 111), (.negSucc 70), (.ofNat 120), (.negSucc 50), (.ofNat 101), (.negSucc 119)],
  [(.ofNat 90), (.negSucc 52), (.negSucc 100), (.ofNat 62), (.ofNat 100), (.ofNat 99), (.ofNat 94), (.ofNat 47), (.negSucc 96), (.negSucc 65), (.negSucc 9), (.negSucc 82), (.ofNat 86), (.ofNat 103), (.negSucc 110), (.negSucc 68)],
  [(.ofNat 25), (.negSucc 102), (.ofNat 100), (.ofNat 58), (.negSucc 108), (.negSucc 90), (.ofNat 94), (.negSucc 19), (.ofNat 89), (.negSucc 111), (.ofNat 93), (.negSucc 40), (.negSucc 45), (.negSucc 103), (.ofNat 109), (.ofNat 103)],
  [(.negSucc 93), (.ofNat 85), (.negSucc 101), (.negSucc 102), (.ofNat 121), (.negSucc 18), (.ofNat 102), (.negSucc 89), (.negSucc 68), (.negSucc 121), (.negSucc 106), (.negSucc 40), (.negSucc 84), (.negSucc 20), (.negSucc 9), (.negSucc 118)],
  [(.ofNat 127), (.negSucc 62), (.ofNat 72), (.ofNat 102), (.negSucc 38), (.ofNat 108), (.ofNat 54), (.negSucc 96), (.ofNat 94), (.negSucc 94), (.negSucc 52), (.ofNat 73), (.ofNat 36), (.ofNat 99), (.negSucc 31), (.negSucc 19)],
  [(.ofNat 100), (.negSucc 77), (.negSucc 46), (.negSucc 92), (.negSucc 61), (.negSucc 87), (.negSucc 72), (.negSucc 92), (.negSucc 84), (.negSucc 93), (.ofNat 97), (.ofNat 97), (.ofNat 106), (.negSucc 104), (.ofNat 91), (.ofNat 96)],
  [(.negSucc 98), (.ofNat 99), (.negSucc 48), (.ofNat 8), (.ofNat 95), (.negSucc 95), (.negSucc 115), (.negSucc 104), (.ofNat 76), (.negSucc 98), (.negSucc 43), (.ofNat 114), (.ofNat 80), (.ofNat 110), (.negSucc 98), (.negSucc 100)],
  [(.ofNat 13), (.negSucc 102), (.ofNat 88), (.ofNat 56), (.negSucc 109), (.ofNat 95), (.negSucc 95), (.ofNat 63), (.negSucc 72), (.negSucc 97), (.negSucc 88), (.ofNat 108), (.negSucc 113), (.ofNat 74), (.ofNat 98), (.ofNat 72)],
  [(.ofNat 99), (.negSucc 116), (.negSucc 89), (.negSucc 95), (.ofNat 127), (.negSucc 22), (.negSucc 101), (.ofNat 79), (.ofNat 29), (.negSucc 104), (.ofNat 105), (.ofNat 110), (.negSucc 81), (.negSucc 107), (.negSucc 94), (.ofNat 106)],
  [(.negSucc 110), (.ofNat 100), (.ofNat 101), (.ofNat 96), (.negSucc 34), (.negSucc 96), (.negSucc 90), (.ofNat 97), (.ofNat 1), (.negSucc 60), (.ofNat 81), (.ofNat 88), (.ofNat 89), (.ofNat 94), (.ofNat 95), (.negSucc 93)],
  [(.negSucc 81), (.negSucc 117), (.negSucc 101), (.negSucc 34), (.negSucc 93), (.ofNat 111), (.negSucc 53), (.ofNat 100), (.negSucc 52), (.negSucc 57), (.negSucc 107), (.ofNat 105), (.ofNat 99), (.ofNat 44), (.negSucc 48), (.ofNat 72)],
  [(.ofNat 110), (.ofNat 36), (.ofNat 100), (.negSucc 80), (.ofNat 104), (.ofNat 105), (.ofNat 64), (.ofNat 102), (.ofNat 68), (.negSucc 11), (.negSucc 14), (.ofNat 86), (.negSucc 38), (.negSucc 102), (.ofNat 2), (.ofNat 66)],
  [(.ofNat 37), (.ofNat 96), (.negSucc 92), (.ofNat 91), (.negSucc 114), (.negSucc 83), (.ofNat 114), (.ofNat 97), (.negSucc 93), (.ofNat 30), (.ofNat 86), (.ofNat 99), (.negSucc 103), (.ofNat 99), (.ofNat 84), (.negSucc 95)],
  [(.negSucc 92), (.negSucc 93), (.negSucc 2), (.negSucc 108), (.ofNat 100), (.ofNat 13), (.ofNat 104), (.negSucc 16), (.ofNat 89), (.ofNat 104), (.negSucc 119), (.ofNat 46), (.negSucc 18), (.negSucc 13), (.negSucc 102), (.ofNat 107)],
  [(.ofNat 104), (.ofNat 46), (.ofNat 36), (.ofNat 114), (.ofNat 27), (.ofNat 100), (.ofNat 96), (.negSucc 91), (.negSucc 107), (.ofNat 101), (.negSucc 46), (.negSucc 25), (.ofNat 114), (.negSucc 95), (.ofNat 97), (.ofNat 51)],
  [(.ofNat 91), (.ofNat 107), (.negSucc 73), (.negSucc 7), (.negSucc 99), (.negSucc 103), (.ofNat 101), (.negSucc 97), (.ofNat 94), (.ofNat 110), (.ofNat 104), (.negSucc 69), (.ofNat 77), (.ofNat 112), (.negSucc 99), (.negSucc 99)],
  [(.negSucc 106), (.negSucc 88), (.ofNat 112), (.negSucc 28), (.ofNat 101), (.negSucc 82), (.negSucc 40), (.negSucc 92), (.negSucc 92), (.ofNat 97), (.negSucc 96), (.negSucc 91), (.negSucc 89), (.negSucc 64), (.ofNat 106), (.ofNat 95)],
  [(.ofNat 59), (.ofNat 102), (.negSucc 105), (.ofNat 94), (.negSucc 106), (.ofNat 105), (.negSucc 41), (.negSucc 87), (.ofNat 95), (.ofNat 99), (.negSucc 71), (.negSucc 107), (.negSucc 95), (.negSucc 91), (.negSucc 62), (.negSucc 0)],
  [(.ofNat 84), (.ofNat 72), (.ofNat 97), (.negSucc 98), (.ofNat 50), (.negSucc 50), (.negSucc 98), (.negSucc 66), (.negSucc 91), (.ofNat 99), (.ofNat 100), (.negSucc 119), (.ofNat 35), (.ofNat 90), (.ofNat 46), (.negSucc 93)],
  [(.negSucc 103), (.negSucc 74), (.negSucc 92), (.ofNat 87), (.ofNat 83), (.negSucc 93), (.negSucc 97), (.negSucc 17), (.ofNat 105), (.ofNat 82), (.ofNat 45), (.negSucc 117), (.ofNat 98), (.negSucc 83), (.negSucc 7), (.ofNat 92)],
  [(.negSucc 103), (.ofNat 102), (.ofNat 59), (.ofNat 26), (.negSucc 90), (.ofNat 108), (.negSucc 97), (.ofNat 114), (.negSucc 101), (.ofNat 79), (.negSucc 98), (.negSucc 108), (.ofNat 21), (.negSucc 68), (.negSucc 85), (.negSucc 84)],
  [(.ofNat 100), (.ofNat 9), (.ofNat 16), (.negSucc 83), (.ofNat 113), (.ofNat 98), (.negSucc 82), (.ofNat 91), (.ofNat 110), (.ofNat 56), (.ofNat 54), (.negSucc 99), (.negSucc 108), (.ofNat 96), (.ofNat 102), (.negSucc 85)],
  [(.negSucc 72), (.negSucc 95), (.negSucc 66), (.ofNat 95), (.negSucc 65), (.negSucc 116), (.negSucc 38), (.ofNat 97), (.negSucc 104), (.ofNat 24), (.ofNat 85), (.negSucc 93), (.negSucc 60), (.negSucc 101), (.negSucc 95), (.ofNat 96)]]

def E2 : List (List Int) := [
  [(.ofNat 104), (.ofNat 46), (.ofNat 36), (.ofNat 114), (.ofNat 27), (.ofNat 100), (.ofNat 97), (.negSucc 92), (.negSucc 107), (.ofNat 99), (.negSucc 46), (.ofNat 26), (.ofNat 114), (.negSucc 95), (.negSucc 96), (.negSucc 49)],
  [(.ofNat 91), (.ofNat 107), (.negSucc 73), (.negSucc 7), (.negSucc 99), (.negSucc 103), (.ofNat 102), (.negSucc 98), (.ofNat 95), (.ofNat 111), (.ofNat 104), (.ofNat 70), (.ofNat 77), (.ofNat 112), (.ofNat 100), (.ofNat 100)],
  [(.negSucc 106), (.negSucc 88), (.ofNat 112), (.negSucc 28), (.ofNat 101), (.negSucc 82), (.negSucc 39), (.negSucc 92), (.negSucc 92), (.ofNat 97), (.negSucc 96), (.ofNat 92), (.negSucc 89), (.negSucc 64), (.negSucc 105), (.negSucc 95)],
  [(.ofNat 59), (.ofNat 103), (.negSucc 105), (.ofNat 94), (.negSucc 106), (.ofNat 105), (.negSucc 41), (.negSucc 87), (.ofNat 96), (.ofNat 99), (.negSucc 71), (.ofNat 108), (.negSucc 95), (.negSucc 91), (.ofNat 63), (.ofNat 1)],
  [(.ofNat 84), (.ofNat 72), (.ofNat 98), (.negSucc 98), (.ofNat 49), (.negSucc 50), (.negSucc 98), (.negSucc 66), (.negSucc 92), (.ofNat 99), (.ofNat 100), (.ofNat 120), (.ofNat 35), (.ofNat 90), (.negSucc 44), (.ofNat 95)],
  [(.negSucc 103), (.negSucc 74), (.negSucc 92), (.ofNat 88), (.ofNat 83), (.negSucc 93), (.negSucc 97), (.negSucc 17), (.ofNat 105), (.ofNat 82), (.ofNat 45), (.ofNat 118), (.ofNat 98), (.negSucc 84), (.ofNat 8), (.negSucc 91)],
  [(.negSucc 103), (.ofNat 103), (.ofNat 59), (.ofNat 25), (.negSucc 91), (.ofNat 109), (.negSucc 97), (.ofNat 114), (.negSucc 101), (.ofNat 79), (.negSucc 98), (.ofNat 109), (.ofNat 22), (.negSucc 69), (.ofNat 87), (.ofNat 85)],
  [(.ofNat 100), (.ofNat 9), (.ofNat 16), (.negSucc 84), (.ofNat 113), (.ofNat 98), (.negSucc 82), (.ofNat 91), (.ofNat 110), (.ofNat 56), (.ofNat 55), (.ofNat 101), (.negSucc 108), (.ofNat 96), (.negSucc 101), (.ofNat 87)],
  [(.negSucc 72), (.negSucc 95), (.negSucc 66), (.ofNat 95), (.negSucc 65), (.negSucc 116), (.negSucc 37), (.ofNat 97), (.negSucc 105), (.ofNat 24), (.ofNat 85), (.ofNat 94), (.negSucc 60), (.negSucc 101), (.ofNat 96), (.negSucc 95)],
  [(.negSucc 75), (.ofNat 93), (.ofNat 99), (.negSucc 97), (.negSucc 58), (.ofNat 81), (.ofNat 114), (.ofNat 100), (.ofNat 95), (.negSucc 87), (.negSucc 111), (.ofNat 71), (.ofNat 120), (.negSucc 51), (.negSucc 100), (.ofNat 120)],
  [(.ofNat 90), (.negSucc 52), (.negSucc 100), (.ofNat 62), (.ofNat 100), (.ofNat 100), (.ofNat 94), (.ofNat 47), (.negSucc 97), (.negSucc 65), (.negSucc 9), (.ofNat 83), (.ofNat 87), (.ofNat 103), (.ofNat 112), (.ofNat 69)],
  [(.ofNat 24), (.negSucc 102), (.ofNat 100), (.ofNat 58), (.negSucc 109), (.negSucc 90), (.ofNat 95), (.negSucc 19), (.ofNat 90), (.negSucc 112), (.ofNat 93), (.ofNat 41), (.negSucc 44), (.negSucc 103), (.negSucc 109), (.negSucc 102)],
  [(.negSucc 93), (.ofNat 85), (.negSucc 101), (.negSucc 102), (.ofNat 121), (.negSucc 18), (.ofNat 102), (.negSucc 89), (.negSucc 67), (.negSucc 121), (.negSucc 107), (.ofNat 40), (.negSucc 84), (.negSucc 21), (.ofNat 9), (.ofNat 119)],
  [(.ofNat 127), (.negSucc 62), (.ofNat 72), (.ofNat 102), (.negSucc 38), (.ofNat 108), (.ofNat 54), (.negSucc 96), (.ofNat 94), (.negSucc 95), (.negSucc 52), (.negSucc 72), (.ofNat 35), (.ofNat 99), (.ofNat 33), (.ofNat 20)],
  [(.ofNat 101), (.negSucc 77), (.negSucc 46), (.negSucc 92), (.negSucc 61), (.negSucc 87), (.negSucc 72), (.negSucc 92), (.negSucc 84), (.negSucc 93), (.ofNat 97), (.negSucc 96), (.ofNat 106), (.negSucc 104), (.negSucc 91), (.negSucc 96)],
  [(.negSucc 100), (.ofNat 99), (.negSucc 48), (.ofNat 8), (.ofNat 96), (.negSucc 94), (.negSucc 114), (.negSucc 104), (.ofNat 76), (.negSucc 98), (.negSucc 44), (.negSucc 113), (.ofNat 81), (.ofNat 109), (.ofNat 99), (.ofNat 100)],
  [(.ofNat 12), (.negSucc 103), (.ofNat 88), (.ofNat 56), (.negSucc 109), (.ofNat 95), (.negSucc 95), (.ofNat 63), (.negSucc 73), (.negSucc 97), (.negSucc 88), (.negSucc 108), (.negSucc 113), (.ofNat 74), (.negSucc 97), (.negSucc 71)],
  [(.ofNat 100), (.negSucc 116), (.negSucc 90), (.negSucc 95), (.ofNat 127), (.negSucc 21), (.negSucc 101), (.ofNat 79), (.ofNat 29), (.negSucc 104), (.ofNat 105), (.negSucc 109), (.negSucc 81), (.negSucc 107), (.ofNat 95), (.negSucc 105)],
  [(.negSucc 110), (.ofNat 100), (.ofNat 101), (.ofNat 96), (.negSucc 35), (.negSucc 96), (.negSucc 91), (.ofNat 97), (.ofNat 1), (.negSucc 61), (.ofNat 81), (.negSucc 88), (.ofNat 90), (.ofNat 94), (.negSucc 95), (.ofNat 94)],
  [(.negSucc 81), (.negSucc 117), (.negSucc 101), (.negSucc 35), (.negSucc 93), (.ofNat 112), (.negSucc 53), (.ofNat 101), (.negSucc 52), (.negSucc 57), (.negSucc 108), (.negSucc 105), (.ofNat 99), (.ofNat 45), (.ofNat 49), (.negSucc 71)],
  [(.ofNat 110), (.ofNat 36), (.ofNat 100), (.negSucc 80), (.ofNat 104), (.ofNat 105), (.ofNat 64), (.ofNat 102), (.ofNat 68), (.negSucc 12), (.negSucc 14), (.negSucc 85), (.negSucc 38), (.negSucc 103), (.negSucc 1), (.negSucc 65)],
  [(.ofNat 37), (.ofNat 96), (.negSucc 93), (.ofNat 91), (.negSucc 114), (.negSucc 84), (.ofNat 114), (.ofNat 97), (.negSucc 94), (.ofNat 30), (.ofNat 86), (.negSucc 98), (.negSucc 104), (.ofNat 100), (.negSucc 84), (.ofNat 96)],
  [(.negSucc 92), (.negSucc 93), (.negSucc 2), (.negSucc 108), (.ofNat 100), (.ofNat 14), (.ofNat 104), (.negSucc 16), (.ofNat 89), (.ofNat 104), (.negSucc 120), (.negSucc 44), (.negSucc 17), (.negSucc 13), (.ofNat 103), (.negSucc 105)]]

def W2 : List (List Int) := [
  [(.negSucc 98), (.ofNat 23), (.negSucc 81), (.negSucc 56), (.ofNat 118), (.ofNat 116), (.ofNat 106), (.negSucc 102), (.negSucc 105), (.ofNat 19), (.ofNat 79), (.negSucc 73), (.ofNat 108), (.negSucc 47), (.negSucc 100), (.ofNat 102)],
  [(.ofNat 87), (.ofNat 98), (.ofNat 67), (.negSucc 58), (.negSucc 54), (.ofNat 37), (.ofNat 108), (.negSucc 100), (.ofNat 109), (.negSucc 29), (.negSucc 95), (.negSucc 126), (.ofNat 94), (.negSucc 98), (.ofNat 96), (.negSucc 108)],
  [(.ofNat 105), (.negSucc 89), (.ofNat 73), (.ofNat 98), (.ofNat 0), (.negSucc 110), (.ofNat 98), (.negSucc 59), (.negSucc 103), (.negSucc 32), (.ofNat 13), (.negSucc 114), (.ofNat 58), (.ofNat 105), (.negSucc 86), (.ofNat 85)],
  [(.negSucc 70), (.ofNat 89), (.negSucc 70), (.negSucc 122), (.ofNat 78), (.ofNat 41), (.ofNat 31), (.ofNat 41), (.ofNat 120), (.negSucc 16), (.ofNat 86), (.negSucc 98), (.negSucc 118), (.negSucc 81), (.ofNat 57), (.ofNat 109)],
  [(.ofNat 3), (.ofNat 74), (.ofNat 109), (.ofNat 113), (.negSucc 106), (.ofNat 87), (.ofNat 27), (.ofNat 71), (.negSucc 112), (.negSucc 87), (.negSucc 94), (.negSucc 77), (.ofNat 63), (.negSucc 31), (.ofNat 103), (.negSucc 109)],
  [(.ofNat 92), (.negSucc 92), (.negSucc 95), (.negSucc 49), (.ofNat 108), (.negSucc 110), (.negSucc 75), (.ofNat 82), (.ofNat 95), (.negSucc 65), (.negSucc 34), (.negSucc 94), (.ofNat 112), (.ofNat 88), (.negSucc 20), (.ofNat 80)],
  [(.negSucc 94), (.ofNat 105), (.ofNat 99), (.negSucc 67), (.ofNat 57), (.negSucc 40), (.negSucc 97), (.ofNat 78), (.negSucc 120), (.negSucc 100), (.ofNat 105), (.negSucc 84), (.ofNat 83), (.negSucc 102), (.ofNat 109), (.ofNat 115)],
  [(.negSucc 94), (.ofNat 82), (.negSucc 83), (.ofNat 88), (.ofNat 24), (.ofNat 112), (.negSucc 96), (.ofNat 99), (.ofNat 101), (.negSucc 100), (.ofNat 52), (.negSucc 13), (.negSucc 45), (.negSucc 9), (.negSucc 84), (.negSucc 94)],
  [(.ofNat 115), (.negSucc 91), (.ofNat 82), (.negSucc 91), (.ofNat 90), (.negSucc 56), (.negSucc 89), (.ofNat 106), (.negSucc 91), (.negSucc 97), (.negSucc 85), (.negSucc 30), (.negSucc 99), (.ofNat 95), (.ofNat 94), (.ofNat 97)],
  [(.ofNat 55), (.ofNat 89), (.negSucc 11), (.ofNat 72), (.negSucc 106), (.negSucc 98), (.negSucc 36), (.ofNat 104), (.ofNat 97), (.negSucc 103), (.ofNat 92), (.negSucc 6), (.ofNat 107), (.negSucc 107), (.negSucc 92), (.ofNat 77)],
  [(.negSucc 103), (.negSucc 73), (.negSucc 44), (.ofNat 96), (.ofNat 80), (.ofNat 111), (.ofNat 110), (.negSucc 72), (.negSucc 91), (.negSucc 99), (.ofNat 81), (.ofNat 29), (.ofNat 104), (.ofNat 25), (.ofNat 82), (.negSucc 100)],
  [(.ofNat 22), (.negSucc 105), (.ofNat 86), (.negSucc 86), (.ofNat 41), (.ofNat 41), (.ofNat 110), (.negSucc 96), (.ofNat 47), (.negSucc 89), (.negSucc 100), (.negSucc 0), (.ofNat 60), (.ofNat 86), (.ofNat 33), (.ofNat 109)],
  [(.ofNat 81), (.ofNat 99), (.negSucc 105), (.ofNat 106), (.negSucc 61), (.negSucc 96), (.ofNat 99), (.negSucc 90), (.negSucc 23), (.ofNat 10), (.ofNat 3), (.ofNat 104), (.negSucc 118), (.negSucc 102), (.ofNat 63), (.ofNat 20)],
  [(.negSucc 93), (.negSucc 69), (.ofNat 111), (.negSucc 124), (.ofNat 101), (.ofNat 21), (.ofNat 93), (.negSucc 94), (.ofNat 35), (.ofNat 41), (.ofNat 91), (.ofNat 75), (.negSucc 65), (.ofNat 1), (.ofNat 112), (.negSucc 95)],
  [(.negSucc 25), (.negSucc 90), (.negSucc 97), (.ofNat 65), (.negSucc 95), (.ofNat 95), (.ofNat 77), (.negSucc 77), (.negSucc 12), (.ofNat 76), (.negSucc 99), (.ofNat 91), (.ofNat 87), (.ofNat 82), (.negSucc 113), (.ofNat 113)],
  [(.ofNat 105), (.negSucc 52), (.ofNat 80), (.ofNat 76), (.ofNat 8), (.negSucc 117), (.ofNat 46), (.ofNat 1), (.negSucc 1), (.ofNat 67), (.negSucc 44), (.ofNat 107), (.ofNat 56), (.negSucc 99), (.ofNat 118), (.negSucc 97)],
  [(.negSucc 102), (.negSucc 80), (.negSucc 34), (.negSucc 98), (.ofNat 98), (.negSucc 10), (.negSucc 13), (.ofNat 89), (.ofNat 49), (.ofNat 111), (.ofNat 114), (.ofNat 109), (.negSucc 6), (.ofNat 51), (.negSucc 104), (.negSucc 53)],
  [(.ofNat 4), (.negSucc 92), (.negSucc 14), (.ofNat 101), (.negSucc 98), (.ofNat 69), (.negSucc 121), (.ofNat 103), (.negSucc 47), (.ofNat 109), (.negSucc 111), (.ofNat 94), (.negSucc 100), (.ofNat 30), (.ofNat 89), (.ofNat 62)],
  [(.ofNat 102), (.negSucc 19), (.ofNat 47), (.negSucc 106), (.ofNat 122), (.negSucc 77), (.negSucc 104), (.ofNat 114), (.ofNat 69), (.ofNat 91), (.negSucc 97), (.ofNat 80), (.ofNat 61), (.negSucc 105), (.negSucc 68), (.negSucc 68)],
  [(.negSucc 13), (.negSucc 102), (.negSucc 97), (.ofNat 38), (.negSucc 93), (.negSucc 84), (.negSucc 100), (.ofNat 111), (.negSucc 42), (.ofNat 91), (.ofNat 118), (.ofNat 38), (.ofNat 109), (.ofNat 117), (.ofNat 37), (.ofNat 17)],
  [(.negSucc 95), (.negSucc 6), (.ofNat 56), (.ofNat 56), (.ofNat 10), (.ofNat 84), (.negSucc 37), (.ofNat 20), (.ofNat 35), (.ofNat 65), (.negSucc 23), (.negSucc 44), (.ofNat 49), (.ofNat 6), (.ofNat 47), (.ofNat 93)],
  [(.ofNat 95), (.ofNat 115), (.negSucc 106), (.negSucc 98), (.ofNat 94), (.ofNat 61), (.ofNat 91), (.negSucc 29), (.negSucc 70), (.ofNat 110), (.negSucc 109), (.ofNat 40), (.negSucc 87), (.negSucc 83), (.negSucc 51), (.negSucc 20)],
  [(.negSucc 22), (.negSucc 106), (.ofNat 111), (.ofNat 86), (.negSucc 108), (.negSucc 102), (.ofNat 53), (.negSucc 99), (.ofNat 93), (.ofNat 46), (.ofNat 80), (.negSucc 16), (.negSucc 72), (.ofNat 103), (.ofNat 112), (.negSucc 9)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 23 → ∀ b, b < 23 → answer a b = (a + b) % 23

end LeanCheckedNetwork.Net
