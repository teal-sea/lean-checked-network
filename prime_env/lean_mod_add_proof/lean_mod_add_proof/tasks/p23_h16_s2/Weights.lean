import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 23

23 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=23 H=16 seed=2 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 23

def E1 : List (List Int) := [
  [(.ofNat 108), (.ofNat 107), (.ofNat 77), (.negSucc 89), (.ofNat 53), (.ofNat 107), (.negSucc 62), (.negSucc 65), (.negSucc 96), (.ofNat 101), (.ofNat 93), (.negSucc 95), (.negSucc 80), (.ofNat 108), (.ofNat 92), (.negSucc 107)],
  [(.negSucc 96), (.ofNat 107), (.ofNat 117), (.ofNat 68), (.negSucc 96), (.negSucc 37), (.negSucc 104), (.ofNat 71), (.ofNat 121), (.ofNat 85), (.negSucc 79), (.ofNat 56), (.ofNat 76), (.ofNat 86), (.negSucc 97), (.negSucc 105)],
  [(.negSucc 32), (.negSucc 19), (.ofNat 103), (.ofNat 15), (.negSucc 107), (.negSucc 117), (.ofNat 33), (.negSucc 91), (.negSucc 108), (.negSucc 102), (.ofNat 35), (.ofNat 92), (.ofNat 97), (.ofNat 22), (.ofNat 88), (.negSucc 108)],
  [(.ofNat 96), (.negSucc 95), (.negSucc 8), (.negSucc 94), (.ofNat 98), (.ofNat 100), (.ofNat 102), (.ofNat 121), (.ofNat 98), (.negSucc 20), (.negSucc 13), (.negSucc 124), (.ofNat 109), (.negSucc 119), (.negSucc 96), (.negSucc 92)],
  [(.ofNat 4), (.negSucc 98), (.negSucc 110), (.ofNat 107), (.ofNat 101), (.negSucc 99), (.ofNat 17), (.negSucc 98), (.negSucc 104), (.ofNat 89), (.negSucc 72), (.negSucc 77), (.negSucc 79), (.negSucc 94), (.ofNat 77), (.negSucc 89)],
  [(.negSucc 93), (.ofNat 72), (.negSucc 109), (.negSucc 107), (.negSucc 69), (.negSucc 48), (.negSucc 110), (.ofNat 118), (.ofNat 111), (.ofNat 3), (.ofNat 101), (.ofNat 105), (.negSucc 102), (.negSucc 93), (.negSucc 68), (.negSucc 90)],
  [(.ofNat 18), (.ofNat 107), (.negSucc 111), (.ofNat 27), (.negSucc 99), (.ofNat 97), (.negSucc 73), (.negSucc 116), (.negSucc 106), (.negSucc 97), (.negSucc 100), (.negSucc 71), (.negSucc 84), (.ofNat 1), (.ofNat 83), (.negSucc 26)],
  [(.ofNat 106), (.ofNat 83), (.ofNat 7), (.ofNat 103), (.negSucc 65), (.negSucc 117), (.ofNat 85), (.ofNat 104), (.ofNat 93), (.ofNat 23), (.ofNat 105), (.negSucc 83), (.ofNat 98), (.ofNat 127), (.negSucc 74), (.negSucc 39)],
  [(.negSucc 55), (.negSucc 87), (.ofNat 92), (.negSucc 96), (.ofNat 98), (.ofNat 52), (.ofNat 101), (.negSucc 103), (.negSucc 104), (.ofNat 98), (.negSucc 93), (.ofNat 107), (.ofNat 106), (.ofNat 92), (.ofNat 34), (.ofNat 28)],
  [(.negSucc 91), (.negSucc 103), (.ofNat 105), (.ofNat 106), (.ofNat 109), (.ofNat 100), (.negSucc 84), (.ofNat 104), (.ofNat 87), (.negSucc 68), (.ofNat 20), (.negSucc 47), (.ofNat 78), (.ofNat 80), (.negSucc 15), (.ofNat 78)],
  [(.ofNat 79), (.negSucc 59), (.ofNat 89), (.negSucc 104), (.negSucc 100), (.negSucc 94), (.negSucc 95), (.negSucc 125), (.negSucc 101), (.negSucc 92), (.negSucc 12), (.negSucc 105), (.negSucc 76), (.negSucc 91), (.negSucc 48), (.ofNat 119)],
  [(.ofNat 89), (.ofNat 80), (.negSucc 25), (.ofNat 58), (.negSucc 100), (.ofNat 82), (.negSucc 35), (.ofNat 110), (.ofNat 89), (.ofNat 74), (.negSucc 46), (.ofNat 111), (.negSucc 93), (.negSucc 123), (.ofNat 53), (.ofNat 110)],
  [(.negSucc 85), (.ofNat 99), (.negSucc 111), (.ofNat 88), (.ofNat 59), (.ofNat 95), (.ofNat 105), (.negSucc 110), (.negSucc 93), (.ofNat 91), (.ofNat 104), (.ofNat 87), (.negSucc 114), (.negSucc 85), (.negSucc 70), (.ofNat 100)],
  [(.negSucc 93), (.ofNat 63), (.negSucc 116), (.negSucc 95), (.ofNat 107), (.negSucc 82), (.ofNat 72), (.ofNat 106), (.ofNat 63), (.negSucc 103), (.negSucc 91), (.negSucc 95), (.ofNat 87), (.negSucc 63), (.ofNat 55), (.ofNat 94)],
  [(.ofNat 98), (.negSucc 101), (.negSucc 95), (.ofNat 108), (.ofNat 54), (.ofNat 49), (.negSucc 93), (.negSucc 111), (.negSucc 64), (.negSucc 95), (.ofNat 108), (.ofNat 3), (.ofNat 105), (.ofNat 64), (.negSucc 111), (.ofNat 106)],
  [(.ofNat 115), (.negSucc 91), (.ofNat 70), (.negSucc 76), (.negSucc 91), (.ofNat 56), (.negSucc 97), (.ofNat 89), (.negSucc 2), (.ofNat 91), (.negSucc 88), (.ofNat 91), (.ofNat 78), (.ofNat 121), (.ofNat 103), (.ofNat 95)],
  [(.negSucc 103), (.negSucc 32), (.ofNat 108), (.negSucc 62), (.negSucc 84), (.negSucc 105), (.ofNat 105), (.negSucc 91), (.negSucc 32), (.ofNat 91), (.ofNat 68), (.negSucc 101), (.negSucc 106), (.ofNat 91), (.negSucc 108), (.ofNat 88)],
  [(.negSucc 103), (.ofNat 106), (.ofNat 113), (.ofNat 85), (.ofNat 94), (.ofNat 50), (.ofNat 110), (.ofNat 106), (.negSucc 64), (.negSucc 105), (.negSucc 44), (.negSucc 49), (.negSucc 118), (.ofNat 56), (.ofNat 114), (.ofNat 65)],
  [(.ofNat 102), (.ofNat 102), (.ofNat 69), (.negSucc 102), (.ofNat 104), (.ofNat 68), (.negSucc 54), (.negSucc 95), (.ofNat 77), (.negSucc 92), (.negSucc 43), (.ofNat 92), (.ofNat 32), (.negSucc 83), (.negSucc 106), (.ofNat 48)],
  [(.ofNat 127), (.negSucc 57), (.negSucc 71), (.ofNat 105), (.negSucc 82), (.negSucc 82), (.negSucc 99), (.ofNat 90), (.negSucc 60), (.ofNat 116), (.ofNat 108), (.negSucc 97), (.ofNat 89), (.negSucc 95), (.ofNat 109), (.negSucc 14)],
  [(.negSucc 96), (.negSucc 93), (.negSucc 83), (.negSucc 33), (.negSucc 109), (.ofNat 89), (.negSucc 95), (.negSucc 99), (.ofNat 107), (.ofNat 80), (.negSucc 99), (.negSucc 88), (.ofNat 114), (.negSucc 92), (.negSucc 107), (.negSucc 6)],
  [(.negSucc 83), (.negSucc 109), (.negSucc 110), (.negSucc 54), (.ofNat 55), (.ofNat 43), (.ofNat 99), (.ofNat 72), (.negSucc 98), (.negSucc 100), (.ofNat 104), (.ofNat 96), (.negSucc 64), (.negSucc 25), (.ofNat 102), (.negSucc 65)],
  [(.ofNat 104), (.ofNat 52), (.negSucc 2), (.ofNat 95), (.ofNat 97), (.negSucc 84), (.ofNat 93), (.negSucc 81), (.ofNat 108), (.negSucc 35), (.negSucc 109), (.ofNat 43), (.negSucc 96), (.ofNat 110), (.negSucc 102), (.negSucc 95)]]

def E2 : List (List Int) := [
  [(.ofNat 96), (.ofNat 96), (.negSucc 8), (.negSucc 94), (.ofNat 98), (.ofNat 100), (.ofNat 102), (.ofNat 121), (.ofNat 98), (.negSucc 20), (.negSucc 13), (.ofNat 125), (.negSucc 108), (.ofNat 120), (.negSucc 96), (.negSucc 92)],
  [(.ofNat 4), (.ofNat 99), (.negSucc 110), (.ofNat 107), (.ofNat 101), (.negSucc 99), (.ofNat 17), (.negSucc 98), (.negSucc 104), (.ofNat 89), (.negSucc 72), (.ofNat 78), (.ofNat 80), (.ofNat 95), (.ofNat 77), (.negSucc 89)],
  [(.negSucc 93), (.negSucc 71), (.negSucc 109), (.negSucc 107), (.negSucc 69), (.negSucc 48), (.negSucc 110), (.ofNat 118), (.ofNat 111), (.ofNat 3), (.ofNat 101), (.negSucc 104), (.ofNat 103), (.ofNat 94), (.negSucc 68), (.negSucc 90)],
  [(.ofNat 18), (.negSucc 106), (.negSucc 111), (.ofNat 27), (.negSucc 99), (.ofNat 97), (.negSucc 73), (.negSucc 116), (.negSucc 106), (.negSucc 97), (.negSucc 100), (.ofNat 72), (.ofNat 85), (.negSucc 0), (.ofNat 83), (.negSucc 26)],
  [(.ofNat 106), (.negSucc 82), (.ofNat 7), (.ofNat 103), (.negSucc 65), (.negSucc 117), (.ofNat 85), (.ofNat 104), (.ofNat 93), (.ofNat 23), (.ofNat 105), (.ofNat 84), (.negSucc 97), (.negSucc 126), (.negSucc 74), (.negSucc 39)],
  [(.negSucc 55), (.ofNat 88), (.ofNat 92), (.negSucc 96), (.ofNat 98), (.ofNat 52), (.ofNat 101), (.negSucc 103), (.negSucc 104), (.ofNat 98), (.negSucc 93), (.negSucc 106), (.negSucc 105), (.negSucc 91), (.ofNat 34), (.ofNat 28)],
  [(.negSucc 91), (.ofNat 104), (.ofNat 105), (.ofNat 106), (.ofNat 109), (.ofNat 100), (.negSucc 84), (.ofNat 104), (.ofNat 87), (.negSucc 68), (.ofNat 20), (.ofNat 48), (.negSucc 77), (.negSucc 79), (.negSucc 15), (.ofNat 78)],
  [(.ofNat 79), (.ofNat 60), (.ofNat 89), (.negSucc 104), (.negSucc 100), (.negSucc 94), (.negSucc 95), (.negSucc 125), (.negSucc 101), (.negSucc 92), (.negSucc 12), (.ofNat 106), (.ofNat 77), (.ofNat 92), (.negSucc 48), (.ofNat 119)],
  [(.ofNat 89), (.negSucc 79), (.negSucc 25), (.ofNat 58), (.negSucc 100), (.ofNat 82), (.negSucc 35), (.ofNat 109), (.ofNat 89), (.ofNat 74), (.negSucc 46), (.negSucc 110), (.ofNat 94), (.ofNat 124), (.ofNat 53), (.ofNat 110)],
  [(.negSucc 85), (.negSucc 98), (.negSucc 111), (.ofNat 88), (.ofNat 59), (.ofNat 95), (.ofNat 105), (.negSucc 110), (.negSucc 93), (.ofNat 91), (.ofNat 104), (.negSucc 86), (.ofNat 115), (.ofNat 86), (.negSucc 70), (.ofNat 100)],
  [(.negSucc 93), (.negSucc 62), (.negSucc 116), (.negSucc 95), (.ofNat 107), (.negSucc 82), (.ofNat 72), (.ofNat 106), (.ofNat 63), (.negSucc 103), (.negSucc 91), (.ofNat 96), (.negSucc 86), (.ofNat 64), (.ofNat 55), (.ofNat 94)],
  [(.ofNat 98), (.ofNat 102), (.negSucc 95), (.ofNat 108), (.ofNat 54), (.ofNat 49), (.negSucc 93), (.negSucc 111), (.negSucc 64), (.negSucc 95), (.ofNat 108), (.negSucc 2), (.negSucc 104), (.negSucc 63), (.negSucc 111), (.ofNat 106)],
  [(.ofNat 115), (.ofNat 92), (.ofNat 70), (.negSucc 76), (.negSucc 91), (.ofNat 56), (.negSucc 97), (.ofNat 89), (.negSucc 2), (.ofNat 91), (.negSucc 88), (.negSucc 90), (.negSucc 77), (.negSucc 120), (.ofNat 103), (.ofNat 95)],
  [(.negSucc 103), (.ofNat 33), (.ofNat 108), (.negSucc 62), (.negSucc 84), (.negSucc 105), (.ofNat 105), (.negSucc 91), (.negSucc 32), (.ofNat 91), (.ofNat 68), (.ofNat 102), (.ofNat 107), (.negSucc 90), (.negSucc 108), (.ofNat 88)],
  [(.negSucc 103), (.negSucc 105), (.ofNat 113), (.ofNat 85), (.ofNat 94), (.ofNat 50), (.ofNat 110), (.ofNat 106), (.negSucc 64), (.negSucc 105), (.negSucc 44), (.ofNat 50), (.ofNat 119), (.negSucc 55), (.ofNat 114), (.ofNat 65)],
  [(.ofNat 102), (.negSucc 101), (.ofNat 69), (.negSucc 102), (.ofNat 104), (.ofNat 68), (.negSucc 54), (.negSucc 95), (.ofNat 77), (.negSucc 92), (.negSucc 43), (.negSucc 91), (.negSucc 31), (.ofNat 84), (.negSucc 106), (.ofNat 48)],
  [(.ofNat 127), (.ofNat 58), (.negSucc 71), (.ofNat 105), (.negSucc 82), (.negSucc 82), (.negSucc 99), (.ofNat 90), (.negSucc 60), (.ofNat 116), (.ofNat 108), (.ofNat 98), (.negSucc 88), (.ofNat 96), (.ofNat 109), (.negSucc 14)],
  [(.negSucc 96), (.ofNat 94), (.negSucc 83), (.negSucc 33), (.negSucc 109), (.ofNat 89), (.negSucc 95), (.negSucc 99), (.ofNat 107), (.ofNat 80), (.negSucc 99), (.ofNat 89), (.negSucc 113), (.ofNat 93), (.negSucc 107), (.negSucc 6)],
  [(.negSucc 83), (.ofNat 110), (.negSucc 110), (.negSucc 54), (.ofNat 55), (.ofNat 43), (.ofNat 99), (.ofNat 72), (.negSucc 98), (.negSucc 100), (.ofNat 104), (.negSucc 95), (.ofNat 65), (.ofNat 26), (.ofNat 102), (.negSucc 65)],
  [(.ofNat 104), (.negSucc 51), (.negSucc 2), (.ofNat 95), (.ofNat 97), (.negSucc 84), (.ofNat 93), (.negSucc 81), (.ofNat 108), (.negSucc 35), (.negSucc 109), (.negSucc 42), (.ofNat 97), (.negSucc 109), (.negSucc 102), (.negSucc 95)],
  [(.ofNat 108), (.negSucc 106), (.ofNat 77), (.negSucc 89), (.ofNat 53), (.ofNat 107), (.negSucc 62), (.negSucc 65), (.negSucc 96), (.ofNat 101), (.ofNat 93), (.ofNat 96), (.ofNat 81), (.negSucc 107), (.ofNat 92), (.negSucc 107)],
  [(.negSucc 96), (.negSucc 106), (.ofNat 117), (.ofNat 68), (.negSucc 96), (.negSucc 37), (.negSucc 104), (.ofNat 71), (.ofNat 121), (.ofNat 85), (.negSucc 79), (.negSucc 55), (.negSucc 75), (.negSucc 85), (.negSucc 97), (.negSucc 105)],
  [(.negSucc 32), (.ofNat 20), (.ofNat 103), (.ofNat 15), (.negSucc 107), (.negSucc 117), (.ofNat 33), (.negSucc 91), (.negSucc 108), (.negSucc 102), (.ofNat 35), (.negSucc 91), (.negSucc 96), (.negSucc 21), (.ofNat 88), (.negSucc 108)]]

def W2 : List (List Int) := [
  [(.ofNat 7), (.ofNat 45), (.ofNat 86), (.ofNat 17), (.ofNat 99), (.negSucc 53), (.negSucc 79), (.ofNat 84), (.negSucc 107), (.negSucc 77), (.ofNat 89), (.negSucc 115), (.negSucc 54), (.ofNat 90), (.negSucc 79), (.ofNat 91)],
  [(.negSucc 93), (.ofNat 82), (.ofNat 14), (.negSucc 109), (.ofNat 6), (.negSucc 5), (.negSucc 113), (.negSucc 84), (.ofNat 106), (.ofNat 112), (.negSucc 108), (.ofNat 14), (.negSucc 87), (.ofNat 94), (.ofNat 57), (.ofNat 111)],
  [(.negSucc 56), (.ofNat 34), (.negSucc 85), (.ofNat 96), (.negSucc 98), (.negSucc 118), (.ofNat 62), (.ofNat 89), (.negSucc 118), (.ofNat 42), (.ofNat 124), (.ofNat 89), (.negSucc 110), (.ofNat 27), (.negSucc 31), (.ofNat 123)],
  [(.ofNat 98), (.negSucc 90), (.negSucc 110), (.negSucc 64), (.negSucc 54), (.ofNat 102), (.ofNat 113), (.negSucc 69), (.ofNat 115), (.negSucc 101), (.negSucc 95), (.negSucc 0), (.ofNat 58), (.negSucc 49), (.ofNat 25), (.ofNat 96)],
  [(.ofNat 44), (.negSucc 98), (.negSucc 99), (.negSucc 54), (.ofNat 100), (.negSucc 34), (.negSucc 7), (.ofNat 41), (.negSucc 113), (.ofNat 14), (.ofNat 102), (.ofNat 33), (.ofNat 112), (.negSucc 111), (.ofNat 37), (.ofNat 89)],
  [(.negSucc 101), (.negSucc 2), (.negSucc 35), (.ofNat 106), (.ofNat 103), (.negSucc 44), (.negSucc 101), (.negSucc 55), (.ofNat 113), (.ofNat 60), (.negSucc 4), (.ofNat 92), (.ofNat 49), (.negSucc 108), (.negSucc 28), (.ofNat 51)],
  [(.ofNat 33), (.ofNat 109), (.ofNat 55), (.negSucc 108), (.negSucc 55), (.ofNat 118), (.negSucc 47), (.ofNat 31), (.negSucc 105), (.ofNat 19), (.ofNat 65), (.ofNat 47), (.negSucc 100), (.negSucc 50), (.ofNat 69), (.ofNat 56)],
  [(.ofNat 85), (.ofNat 83), (.ofNat 106), (.ofNat 14), (.negSucc 105), (.negSucc 83), (.ofNat 78), (.ofNat 9), (.ofNat 96), (.negSucc 98), (.ofNat 11), (.negSucc 94), (.negSucc 98), (.ofNat 85), (.negSucc 77), (.negSucc 33)],
  [(.negSucc 30), (.negSucc 4), (.ofNat 108), (.ofNat 98), (.negSucc 36), (.ofNat 13), (.ofNat 80), (.negSucc 45), (.negSucc 91), (.ofNat 35), (.negSucc 120), (.ofNat 67), (.negSucc 69), (.ofNat 118), (.ofNat 75), (.negSucc 73)],
  [(.negSucc 112), (.negSucc 92), (.ofNat 81), (.negSucc 92), (.ofNat 104), (.ofNat 19), (.negSucc 84), (.negSucc 18), (.ofNat 94), (.ofNat 82), (.ofNat 105), (.ofNat 5), (.ofNat 0), (.ofNat 109), (.negSucc 118), (.negSucc 118)],
  [(.negSucc 9), (.negSucc 108), (.negSucc 31), (.ofNat 115), (.ofNat 93), (.negSucc 84), (.negSucc 108), (.negSucc 24), (.negSucc 81), (.ofNat 78), (.negSucc 101), (.negSucc 98), (.ofNat 113), (.ofNat 71), (.ofNat 115), (.negSucc 60)],
  [(.ofNat 122), (.ofNat 56), (.negSucc 108), (.negSucc 56), (.negSucc 91), (.ofNat 60), (.ofNat 56), (.ofNat 40), (.ofNat 106), (.negSucc 91), (.ofNat 83), (.ofNat 85), (.ofNat 22), (.negSucc 85), (.negSucc 103), (.negSucc 104)],
  [(.negSucc 46), (.ofNat 96), (.negSucc 85), (.ofNat 82), (.negSucc 122), (.ofNat 76), (.ofNat 116), (.negSucc 54), (.negSucc 82), (.ofNat 98), (.ofNat 23), (.ofNat 110), (.negSucc 98), (.negSucc 119), (.ofNat 125), (.negSucc 107)],
  [(.negSucc 120), (.ofNat 114), (.negSucc 43), (.ofNat 96), (.ofNat 90), (.negSucc 99), (.ofNat 95), (.ofNat 61), (.ofNat 86), (.ofNat 100), (.ofNat 50), (.negSucc 90), (.negSucc 108), (.negSucc 126), (.negSucc 114), (.negSucc 109)],
  [(.ofNat 81), (.negSucc 95), (.ofNat 118), (.negSucc 103), (.ofNat 108), (.ofNat 37), (.negSucc 103), (.negSucc 54), (.negSucc 33), (.negSucc 99), (.ofNat 110), (.negSucc 4), (.negSucc 10), (.ofNat 22), (.ofNat 110), (.negSucc 92)],
  [(.ofNat 101), (.negSucc 100), (.ofNat 88), (.ofNat 100), (.negSucc 16), (.ofNat 59), (.negSucc 57), (.ofNat 29), (.ofNat 54), (.negSucc 95), (.negSucc 110), (.ofNat 87), (.ofNat 41), (.ofNat 5), (.negSucc 107), (.negSucc 92)],
  [(.negSucc 80), (.negSucc 68), (.ofNat 83), (.negSucc 81), (.negSucc 108), (.negSucc 93), (.ofNat 90), (.negSucc 103), (.ofNat 11), (.ofNat 92), (.ofNat 67), (.negSucc 92), (.ofNat 93), (.ofNat 125), (.ofNat 94), (.negSucc 19)],
  [(.negSucc 90), (.ofNat 88), (.ofNat 1), (.negSucc 0), (.negSucc 42), (.negSucc 12), (.ofNat 109), (.ofNat 108), (.ofNat 2), (.ofNat 101), (.negSucc 100), (.negSucc 47), (.negSucc 87), (.ofNat 78), (.negSucc 112), (.ofNat 48)],
  [(.ofNat 64), (.ofNat 103), (.negSucc 119), (.ofNat 68), (.ofNat 105), (.negSucc 85), (.negSucc 77), (.negSucc 116), (.ofNat 25), (.negSucc 116), (.ofNat 97), (.ofNat 101), (.negSucc 91), (.negSucc 73), (.ofNat 104), (.ofNat 105)],
  [(.ofNat 119), (.ofNat 105), (.negSucc 84), (.negSucc 87), (.ofNat 92), (.negSucc 86), (.negSucc 110), (.ofNat 122), (.ofNat 56), (.negSucc 75), (.negSucc 46), (.ofNat 52), (.negSucc 90), (.negSucc 37), (.negSucc 100), (.ofNat 79)],
  [(.negSucc 102), (.negSucc 96), (.negSucc 96), (.ofNat 85), (.negSucc 90), (.ofNat 100), (.ofNat 44), (.negSucc 119), (.ofNat 50), (.ofNat 110), (.ofNat 65), (.negSucc 100), (.ofNat 63), (.negSucc 117), (.ofNat 93), (.ofNat 89)],
  [(.negSucc 56), (.negSucc 116), (.ofNat 13), (.negSucc 75), (.negSucc 117), (.ofNat 20), (.ofNat 107), (.ofNat 112), (.negSucc 50), (.ofNat 76), (.ofNat 45), (.ofNat 61), (.ofNat 80), (.negSucc 96), (.negSucc 80), (.ofNat 96)],
  [(.ofNat 97), (.negSucc 1), (.ofNat 62), (.negSucc 27), (.negSucc 0), (.negSucc 109), (.negSucc 11), (.negSucc 100), (.ofNat 85), (.negSucc 111), (.negSucc 78), (.ofNat 56), (.ofNat 44), (.ofNat 26), (.ofNat 75), (.ofNat 107)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 23 → ∀ b, b < 23 → answer a b = (a + b) % 23

end LeanCheckedNetwork.Net
