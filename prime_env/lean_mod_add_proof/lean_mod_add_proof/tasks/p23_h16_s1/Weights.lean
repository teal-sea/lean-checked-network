import LeanCheckedNetwork.Network

/-!
# Weights of a frozen network for addition mod 23

23 possible inputs per side, 16 neurons. Row `x` of `E1` is the embedding of the first input
`x`, row `x` of `E2` the embedding of the second input, row `c` of `W2` the read-out weights of
the answer `c`. `.ofNat n` is the integer n and `.negSucc n` is the integer -(n + 1).
Origin: train.py p=23 H=16 seed=1 lr=0.01 wd=1.0 train_fraction=1.0 steps=20000.
-/

set_option maxRecDepth 100000

namespace LeanCheckedNetwork.Net

def p : Nat := 23

def E1 : List (List Int) := [
  [(.negSucc 106), (.negSucc 5), (.negSucc 98), (.ofNat 111), (.ofNat 92), (.negSucc 81), (.ofNat 107), (.negSucc 112), (.negSucc 104), (.negSucc 106), (.negSucc 20), (.negSucc 103), (.negSucc 1), (.ofNat 85), (.ofNat 58), (.negSucc 104)],
  [(.negSucc 109), (.ofNat 115), (.negSucc 94), (.ofNat 68), (.negSucc 92), (.negSucc 94), (.ofNat 105), (.negSucc 29), (.ofNat 44), (.ofNat 103), (.negSucc 111), (.negSucc 100), (.ofNat 30), (.negSucc 86), (.ofNat 103), (.negSucc 85)],
  [(.ofNat 19), (.ofNat 82), (.negSucc 107), (.negSucc 84), (.ofNat 93), (.negSucc 89), (.negSucc 110), (.ofNat 115), (.ofNat 94), (.negSucc 92), (.negSucc 116), (.ofNat 46), (.negSucc 18), (.negSucc 108), (.negSucc 37), (.negSucc 80)],
  [(.ofNat 108), (.negSucc 88), (.negSucc 125), (.negSucc 99), (.negSucc 103), (.negSucc 56), (.negSucc 81), (.ofNat 70), (.ofNat 108), (.ofNat 111), (.ofNat 68), (.ofNat 92), (.ofNat 82), (.ofNat 18), (.negSucc 116), (.ofNat 57)],
  [(.ofNat 104), (.negSucc 92), (.negSucc 39), (.ofNat 53), (.ofNat 96), (.ofNat 12), (.ofNat 89), (.negSucc 97), (.ofNat 94), (.negSucc 92), (.ofNat 120), (.ofNat 94), (.negSucc 75), (.ofNat 109), (.negSucc 31), (.ofNat 82)],
  [(.negSucc 72), (.ofNat 62), (.ofNat 39), (.ofNat 114), (.negSucc 111), (.ofNat 61), (.ofNat 57), (.negSucc 93), (.ofNat 101), (.ofNat 83), (.ofNat 87), (.ofNat 85), (.ofNat 87), (.ofNat 9), (.ofNat 114), (.ofNat 105)],
  [(.negSucc 113), (.ofNat 116), (.ofNat 81), (.ofNat 39), (.ofNat 110), (.ofNat 72), (.negSucc 99), (.ofNat 58), (.ofNat 97), (.negSucc 76), (.negSucc 68), (.negSucc 39), (.negSucc 89), (.negSucc 111), (.ofNat 94), (.ofNat 113)],
  [(.negSucc 45), (.ofNat 37), (.ofNat 95), (.negSucc 113), (.negSucc 119), (.ofNat 98), (.negSucc 56), (.ofNat 106), (.negSucc 67), (.ofNat 67), (.negSucc 119), (.negSucc 100), (.ofNat 87), (.negSucc 58), (.negSucc 101), (.ofNat 107)],
  [(.ofNat 68), (.negSucc 118), (.ofNat 109), (.negSucc 74), (.ofNat 111), (.ofNat 110), (.ofNat 80), (.ofNat 11), (.negSucc 82), (.negSucc 8), (.negSucc 54), (.negSucc 118), (.negSucc 93), (.ofNat 101), (.negSucc 103), (.ofNat 91)],
  [(.ofNat 115), (.negSucc 69), (.ofNat 108), (.ofNat 102), (.negSucc 115), (.ofNat 104), (.ofNat 28), (.negSucc 116), (.negSucc 104), (.negSucc 32), (.ofNat 91), (.negSucc 58), (.ofNat 96), (.ofNat 102), (.ofNat 36), (.negSucc 56)],
  [(.ofNat 90), (.ofNat 91), (.ofNat 75), (.ofNat 91), (.ofNat 104), (.ofNat 105), (.negSucc 87), (.negSucc 58), (.negSucc 106), (.ofNat 55), (.ofNat 124), (.ofNat 73), (.negSucc 99), (.negSucc 50), (.ofNat 109), (.negSucc 94)],
  [(.negSucc 87), (.ofNat 92), (.negSucc 89), (.negSucc 51), (.negSucc 118), (.ofNat 106), (.ofNat 48), (.ofNat 117), (.negSucc 105), (.negSucc 72), (.ofNat 67), (.ofNat 102), (.ofNat 109), (.negSucc 125), (.ofNat 30), (.negSucc 108)],
  [(.negSucc 115), (.negSucc 39), (.negSucc 91), (.negSucc 107), (.ofNat 89), (.ofNat 115), (.ofNat 84), (.ofNat 95), (.negSucc 21), (.ofNat 69), (.negSucc 79), (.ofNat 121), (.negSucc 97), (.ofNat 25), (.negSucc 101), (.negSucc 102)],
  [(.negSucc 56), (.negSucc 102), (.negSucc 107), (.ofNat 9), (.negSucc 87), (.ofNat 86), (.negSucc 57), (.negSucc 95), (.ofNat 84), (.negSucc 81), (.negSucc 121), (.ofNat 2), (.ofNat 111), (.ofNat 118), (.negSucc 64), (.negSucc 95)],
  [(.ofNat 81), (.negSucc 15), (.negSucc 113), (.ofNat 127), (.ofNat 12), (.ofNat 86), (.negSucc 125), (.negSucc 112), (.ofNat 99), (.ofNat 93), (.negSucc 53), (.negSucc 75), (.negSucc 111), (.ofNat 76), (.ofNat 92), (.negSucc 39)],
  [(.ofNat 115), (.ofNat 110), (.negSucc 110), (.ofNat 52), (.ofNat 7), (.ofNat 19), (.ofNat 85), (.negSucc 6), (.ofNat 112), (.negSucc 93), (.ofNat 95), (.negSucc 111), (.ofNat 109), (.negSucc 110), (.ofNat 97), (.ofNat 53)],
  [(.ofNat 32), (.ofNat 47), (.negSucc 31), (.negSucc 111), (.negSucc 13), (.negSucc 37), (.ofNat 110), (.ofNat 104), (.ofNat 105), (.ofNat 98), (.ofNat 122), (.negSucc 118), (.negSucc 103), (.negSucc 89), (.negSucc 30), (.ofNat 82)],
  [(.negSucc 97), (.negSucc 126), (.ofNat 83), (.negSucc 92), (.ofNat 63), (.negSucc 64), (.negSucc 93), (.ofNat 58), (.ofNat 106), (.negSucc 105), (.ofNat 1), (.negSucc 12), (.ofNat 110), (.ofNat 92), (.negSucc 110), (.ofNat 109)],
  [(.negSucc 113), (.negSucc 81), (.ofNat 92), (.ofNat 60), (.negSucc 58), (.negSucc 83), (.negSucc 108), (.negSucc 111), (.ofNat 60), (.ofNat 98), (.negSucc 94), (.ofNat 60), (.negSucc 107), (.ofNat 109), (.negSucc 33), (.ofNat 117)],
  [(.negSucc 1), (.ofNat 94), (.ofNat 102), (.ofNat 96), (.ofNat 80), (.negSucc 79), (.ofNat 93), (.negSucc 76), (.negSucc 79), (.negSucc 110), (.negSucc 116), (.ofNat 111), (.ofNat 110), (.negSucc 15), (.ofNat 110), (.ofNat 105)],
  [(.ofNat 96), (.ofNat 99), (.ofNat 109), (.ofNat 28), (.negSucc 85), (.negSucc 106), (.ofNat 112), (.ofNat 110), (.negSucc 90), (.ofNat 117), (.ofNat 64), (.ofNat 118), (.negSucc 101), (.negSucc 113), (.ofNat 73), (.negSucc 29)],
  [(.ofNat 100), (.ofNat 2), (.ofNat 97), (.negSucc 104), (.ofNat 88), (.negSucc 102), (.negSucc 93), (.ofNat 95), (.negSucc 105), (.negSucc 107), (.ofNat 108), (.negSucc 23), (.ofNat 69), (.negSucc 9), (.negSucc 109), (.negSucc 71)],
  [(.negSucc 40), (.negSucc 109), (.negSucc 67), (.negSucc 63), (.negSucc 93), (.negSucc 104), (.negSucc 116), (.negSucc 65), (.negSucc 115), (.ofNat 113), (.ofNat 95), (.negSucc 83), (.negSucc 56), (.ofNat 99), (.negSucc 95), (.negSucc 99)]]

def E2 : List (List Int) := [
  [(.negSucc 98), (.ofNat 118), (.ofNat 80), (.negSucc 117), (.ofNat 56), (.negSucc 66), (.negSucc 99), (.ofNat 86), (.ofNat 113), (.negSucc 107), (.negSucc 4), (.ofNat 10), (.ofNat 108), (.ofNat 110), (.ofNat 110), (.ofNat 114)],
  [(.negSucc 120), (.ofNat 90), (.ofNat 90), (.negSucc 103), (.negSucc 54), (.negSucc 74), (.negSucc 108), (.negSucc 110), (.ofNat 47), (.ofNat 99), (.negSucc 100), (.negSucc 69), (.negSucc 95), (.ofNat 82), (.negSucc 76), (.ofNat 118)],
  [(.negSucc 11), (.negSucc 41), (.ofNat 103), (.ofNat 106), (.ofNat 66), (.negSucc 89), (.ofNat 89), (.negSucc 109), (.negSucc 82), (.negSucc 107), (.negSucc 114), (.negSucc 110), (.ofNat 111), (.negSucc 86), (.negSucc 97), (.ofNat 95)],
  [(.ofNat 99), (.negSucc 98), (.ofNat 108), (.ofNat 89), (.negSucc 93), (.negSucc 103), (.ofNat 116), (.ofNat 123), (.negSucc 92), (.ofNat 126), (.ofNat 70), (.negSucc 118), (.negSucc 101), (.negSucc 98), (.negSucc 46), (.negSucc 31)],
  [(.ofNat 96), (.negSucc 78), (.ofNat 95), (.negSucc 24), (.ofNat 88), (.negSucc 107), (.negSucc 104), (.ofNat 104), (.negSucc 105), (.negSucc 107), (.ofNat 116), (.ofNat 19), (.ofNat 77), (.ofNat 99), (.ofNat 96), (.negSucc 65)],
  [(.negSucc 29), (.ofNat 119), (.negSucc 60), (.negSucc 91), (.negSucc 94), (.negSucc 104), (.negSucc 122), (.negSucc 80), (.negSucc 115), (.ofNat 116), (.ofNat 90), (.ofNat 87), (.negSucc 56), (.ofNat 110), (.ofNat 96), (.negSucc 102)],
  [(.negSucc 102), (.ofNat 112), (.negSucc 98), (.negSucc 87), (.ofNat 91), (.negSucc 111), (.ofNat 103), (.negSucc 94), (.negSucc 105), (.negSucc 101), (.negSucc 33), (.ofNat 107), (.negSucc 2), (.negSucc 90), (.negSucc 104), (.negSucc 106)],
  [(.negSucc 105), (.negSucc 110), (.negSucc 98), (.ofNat 91), (.negSucc 89), (.negSucc 93), (.ofNat 99), (.negSucc 24), (.ofNat 56), (.ofNat 101), (.negSucc 109), (.ofNat 98), (.ofNat 9), (.negSucc 86), (.negSucc 101), (.negSucc 95)],
  [(.ofNat 32), (.negSucc 98), (.negSucc 110), (.ofNat 110), (.ofNat 94), (.negSucc 102), (.negSucc 110), (.ofNat 103), (.ofNat 88), (.negSucc 101), (.negSucc 107), (.negSucc 44), (.negSucc 16), (.negSucc 21), (.ofNat 117), (.negSucc 81)],
  [(.ofNat 109), (.ofNat 43), (.negSucc 120), (.negSucc 105), (.negSucc 104), (.negSucc 40), (.negSucc 94), (.ofNat 101), (.ofNat 115), (.ofNat 120), (.ofNat 77), (.negSucc 100), (.ofNat 93), (.ofNat 93), (.ofNat 101), (.ofNat 55)],
  [(.ofNat 110), (.ofNat 93), (.negSucc 31), (.negSucc 102), (.ofNat 101), (.ofNat 0), (.ofNat 99), (.negSucc 99), (.ofNat 96), (.negSucc 95), (.ofNat 124), (.negSucc 106), (.negSucc 56), (.ofNat 83), (.negSucc 65), (.ofNat 81)],
  [(.negSucc 67), (.ofNat 80), (.ofNat 38), (.ofNat 72), (.negSucc 117), (.ofNat 73), (.ofNat 66), (.negSucc 113), (.ofNat 106), (.ofNat 87), (.ofNat 82), (.negSucc 85), (.ofNat 92), (.negSucc 124), (.negSucc 88), (.ofNat 106)],
  [(.negSucc 115), (.negSucc 116), (.ofNat 76), (.ofNat 80), (.ofNat 111), (.ofNat 75), (.negSucc 104), (.ofNat 85), (.ofNat 99), (.negSucc 74), (.negSucc 72), (.ofNat 53), (.negSucc 82), (.negSucc 111), (.negSucc 89), (.ofNat 113)],
  [(.negSucc 49), (.negSucc 107), (.ofNat 97), (.ofNat 31), (.negSucc 122), (.ofNat 102), (.negSucc 60), (.ofNat 99), (.negSucc 81), (.ofNat 78), (.negSucc 119), (.ofNat 99), (.ofNat 92), (.ofNat 107), (.ofNat 104), (.ofNat 111)],
  [(.ofNat 67), (.ofNat 121), (.ofNat 108), (.negSucc 104), (.ofNat 110), (.ofNat 112), (.ofNat 83), (.ofNat 41), (.negSucc 84), (.negSucc 18), (.negSucc 59), (.ofNat 114), (.negSucc 93), (.ofNat 92), (.ofNat 105), (.ofNat 91)],
  [(.ofNat 116), (.ofNat 100), (.ofNat 107), (.negSucc 102), (.negSucc 120), (.ofNat 107), (.ofNat 15), (.negSucc 82), (.negSucc 105), (.negSucc 36), (.ofNat 96), (.ofNat 69), (.ofNat 97), (.negSucc 3), (.negSucc 120), (.negSucc 53)],
  [(.ofNat 81), (.negSucc 61), (.ofNat 67), (.ofNat 111), (.ofNat 104), (.ofNat 106), (.negSucc 92), (.negSucc 85), (.negSucc 107), (.ofNat 59), (.ofNat 127), (.negSucc 93), (.negSucc 98), (.negSucc 89), (.negSucc 94), (.negSucc 94)],
  [(.negSucc 94), (.negSucc 88), (.negSucc 89), (.ofNat 115), (.negSucc 118), (.ofNat 99), (.ofNat 61), (.ofNat 122), (.negSucc 105), (.negSucc 83), (.ofNat 67), (.negSucc 107), (.ofNat 113), (.negSucc 85), (.ofNat 61), (.negSucc 115)],
  [(.negSucc 120), (.negSucc 45), (.negSucc 93), (.negSucc 64), (.ofNat 96), (.ofNat 123), (.ofNat 101), (.ofNat 106), (.negSucc 22), (.ofNat 57), (.negSucc 84), (.negSucc 108), (.negSucc 99), (.ofNat 118), (.ofNat 79), (.negSucc 103)],
  [(.negSucc 58), (.ofNat 96), (.negSucc 107), (.negSucc 98), (.negSucc 93), (.ofNat 92), (.negSucc 74), (.negSucc 114), (.ofNat 84), (.negSucc 81), (.negSucc 123), (.negSucc 13), (.ofNat 109), (.ofNat 111), (.negSucc 1), (.negSucc 98)],
  [(.ofNat 85), (.ofNat 107), (.negSucc 121), (.negSucc 76), (.ofNat 25), (.ofNat 100), (.negSucc 126), (.negSucc 94), (.ofNat 104), (.ofNat 93), (.negSucc 40), (.ofNat 88), (.negSucc 119), (.negSucc 119), (.negSucc 112), (.negSucc 34)],
  [(.ofNat 115), (.negSucc 108), (.negSucc 102), (.ofNat 89), (.ofNat 4), (.ofNat 19), (.ofNat 88), (.negSucc 13), (.ofNat 118), (.negSucc 98), (.ofNat 99), (.ofNat 115), (.ofNat 107), (.negSucc 97), (.negSucc 93), (.ofNat 56)],
  [(.ofNat 22), (.negSucc 100), (.negSucc 25), (.ofNat 97), (.negSucc 6), (.negSucc 31), (.ofNat 108), (.ofNat 81), (.ofNat 105), (.ofNat 98), (.ofNat 126), (.ofNat 124), (.negSucc 107), (.ofNat 63), (.ofNat 103), (.ofNat 90)]]

def W2 : List (List Int) := [
  [(.ofNat 95), (.negSucc 107), (.ofNat 32), (.negSucc 51), (.negSucc 48), (.ofNat 93), (.ofNat 26), (.negSucc 14), (.ofNat 56), (.ofNat 112), (.negSucc 116), (.ofNat 17), (.negSucc 67), (.ofNat 80), (.ofNat 107), (.negSucc 108)],
  [(.ofNat 107), (.negSucc 7), (.negSucc 11), (.negSucc 106), (.ofNat 25), (.ofNat 51), (.negSucc 109), (.ofNat 96), (.ofNat 107), (.negSucc 104), (.negSucc 56), (.ofNat 102), (.ofNat 43), (.negSucc 70), (.ofNat 79), (.negSucc 116)],
  [(.ofNat 36), (.ofNat 64), (.negSucc 52), (.negSucc 2), (.negSucc 38), (.ofNat 119), (.ofNat 1), (.ofNat 2), (.ofNat 112), (.ofNat 117), (.ofNat 33), (.ofNat 87), (.negSucc 85), (.negSucc 101), (.negSucc 107), (.negSucc 64)],
  [(.negSucc 96), (.ofNat 6), (.negSucc 95), (.ofNat 33), (.ofNat 18), (.ofNat 102), (.ofNat 97), (.negSucc 90), (.ofNat 111), (.negSucc 106), (.ofNat 92), (.ofNat 62), (.ofNat 89), (.negSucc 16), (.negSucc 90), (.negSucc 28)],
  [(.negSucc 97), (.negSucc 95), (.negSucc 119), (.ofNat 57), (.ofNat 6), (.ofNat 120), (.negSucc 15), (.negSucc 100), (.ofNat 44), (.ofNat 102), (.ofNat 48), (.ofNat 32), (.negSucc 96), (.ofNat 115), (.ofNat 24), (.ofNat 63)],
  [(.ofNat 48), (.negSucc 84), (.negSucc 83), (.negSucc 68), (.negSucc 55), (.ofNat 121), (.negSucc 111), (.ofNat 38), (.ofNat 41), (.negSucc 87), (.negSucc 92), (.negSucc 97), (.ofNat 112), (.ofNat 59), (.ofNat 112), (.ofNat 104)],
  [(.ofNat 103), (.ofNat 54), (.negSucc 82), (.negSucc 79), (.ofNat 26), (.ofNat 100), (.ofNat 35), (.ofNat 112), (.negSucc 72), (.ofNat 80), (.negSucc 117), (.negSucc 94), (.negSucc 102), (.negSucc 121), (.ofNat 7), (.ofNat 127)],
  [(.ofNat 95), (.ofNat 76), (.ofNat 17), (.ofNat 41), (.negSucc 42), (.ofNat 64), (.ofNat 85), (.negSucc 27), (.negSucc 97), (.negSucc 89), (.negSucc 5), (.negSucc 11), (.ofNat 109), (.negSucc 69), (.negSucc 116), (.ofNat 92)],
  [(.ofNat 14), (.negSucc 9), (.ofNat 97), (.ofNat 118), (.ofNat 85), (.negSucc 8), (.negSucc 31), (.negSucc 116), (.negSucc 117), (.ofNat 26), (.ofNat 80), (.ofNat 52), (.negSucc 116), (.ofNat 87), (.negSucc 70), (.ofNat 37)],
  [(.negSucc 100), (.negSucc 109), (.ofNat 113), (.ofNat 1), (.negSucc 59), (.negSucc 22), (.negSucc 107), (.negSucc 39), (.negSucc 45), (.negSucc 49), (.ofNat 103), (.ofNat 78), (.ofNat 100), (.ofNat 95), (.ofNat 99), (.negSucc 6)],
  [(.negSucc 86), (.negSucc 29), (.ofNat 114), (.negSucc 109), (.ofNat 106), (.negSucc 39), (.ofNat 72), (.ofNat 71), (.ofNat 2), (.ofNat 21), (.ofNat 17), (.ofNat 98), (.negSucc 123), (.negSucc 47), (.ofNat 85), (.negSucc 84)],
  [(.ofNat 56), (.ofNat 117), (.ofNat 69), (.negSucc 29), (.negSucc 92), (.negSucc 99), (.ofNat 110), (.ofNat 81), (.ofNat 23), (.negSucc 23), (.negSucc 111), (.ofNat 75), (.ofNat 92), (.negSucc 109), (.negSucc 40), (.negSucc 109)],
  [(.ofNat 117), (.ofNat 78), (.ofNat 50), (.ofNat 115), (.ofNat 108), (.negSucc 92), (.negSucc 47), (.negSucc 45), (.ofNat 85), (.ofNat 17), (.negSucc 94), (.ofNat 23), (.negSucc 93), (.ofNat 31), (.negSucc 106), (.negSucc 108)],
  [(.ofNat 81), (.negSucc 38), (.negSucc 45), (.ofNat 93), (.negSucc 96), (.negSucc 98), (.negSucc 95), (.negSucc 102), (.ofNat 118), (.negSucc 8), (.ofNat 35), (.negSucc 100), (.ofNat 92), (.ofNat 117), (.ofNat 48), (.negSucc 100)],
  [(.negSucc 32), (.negSucc 104), (.negSucc 84), (.negSucc 76), (.ofNat 123), (.negSucc 100), (.ofNat 94), (.negSucc 20), (.ofNat 117), (.negSucc 61), (.ofNat 100), (.negSucc 97), (.negSucc 27), (.ofNat 38), (.ofNat 111), (.negSucc 37)],
  [(.negSucc 104), (.ofNat 49), (.negSucc 111), (.negSucc 103), (.negSucc 99), (.negSucc 110), (.ofNat 91), (.ofNat 118), (.ofNat 69), (.ofNat 25), (.ofNat 96), (.negSucc 11), (.ofNat 57), (.negSucc 98), (.ofNat 59), (.ofNat 42)],
  [(.negSucc 41), (.ofNat 118), (.negSucc 118), (.ofNat 41), (.ofNat 120), (.negSucc 101), (.negSucc 78), (.ofNat 83), (.ofNat 41), (.negSucc 78), (.negSucc 4), (.ofNat 109), (.negSucc 29), (.negSucc 74), (.negSucc 94), (.ofNat 98)],
  [(.ofNat 79), (.ofNat 41), (.negSucc 65), (.ofNat 115), (.negSucc 105), (.negSucc 61), (.negSucc 33), (.negSucc 117), (.negSucc 27), (.ofNat 89), (.negSucc 110), (.ofNat 122), (.ofNat 22), (.ofNat 75), (.negSucc 68), (.ofNat 114)],
  [(.ofNat 119), (.negSucc 112), (.negSucc 34), (.negSucc 20), (.ofNat 110), (.negSucc 110), (.ofNat 108), (.negSucc 78), (.negSucc 79), (.negSucc 84), (.negSucc 93), (.ofNat 94), (.negSucc 21), (.ofNat 100), (.ofNat 74), (.ofNat 113)],
  [(.ofNat 78), (.negSucc 63), (.ofNat 53), (.negSucc 103), (.negSucc 117), (.negSucc 27), (.ofNat 49), (.ofNat 34), (.negSucc 110), (.ofNat 101), (.ofNat 31), (.ofNat 70), (.ofNat 0), (.negSucc 16), (.ofNat 114), (.ofNat 91)],
  [(.negSucc 48), (.ofNat 84), (.ofNat 101), (.negSucc 49), (.ofNat 61), (.ofNat 60), (.negSucc 112), (.ofNat 102), (.negSucc 122), (.negSucc 105), (.ofNat 108), (.negSucc 44), (.ofNat 9), (.negSucc 117), (.ofNat 22), (.ofNat 7)],
  [(.negSucc 109), (.ofNat 101), (.ofNat 122), (.ofNat 104), (.negSucc 96), (.ofNat 74), (.negSucc 29), (.negSucc 10), (.negSucc 61), (.ofNat 104), (.ofNat 72), (.negSucc 109), (.negSucc 21), (.negSucc 9), (.negSucc 123), (.negSucc 35)],
  [(.negSucc 0), (.negSucc 66), (.ofNat 101), (.ofNat 101), (.ofNat 76), (.ofNat 61), (.ofNat 115), (.negSucc 122), (.negSucc 34), (.negSucc 116), (.negSucc 62), (.negSucc 102), (.ofNat 54), (.ofNat 103), (.negSucc 18), (.negSucc 91)]]

/-- The network's answer for the pair `(a, b)`. -/
def answer (a b : Nat) : Nat := LeanCheckedNetwork.answer E1 E2 W2 a b

/-- The statement to prove. The required theorem must have exactly this type. -/
def Spec : Prop := ∀ a, a < 23 → ∀ b, b < 23 → answer a b = (a + b) % 23

end LeanCheckedNetwork.Net
