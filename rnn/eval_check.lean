import RnnAdder
open RnnAdder
def pairs13_7 : List Input := [(true, true), (false, true), (true, true), (true, false)]   -- 13 = 1101b, 7 = 0111b, LSB first
def pairs255_1 : List Input := [(true, true), (true, false), (true, false), (true, false), (true, false), (true, false), (true, false), (true, false)]
#eval (run Trained.net Trained.net.h0 pairs13_7, finalCarry Trained.net Trained.net.h0 pairs13_7)
#eval bitsToNat (run Trained.net Trained.net.h0 pairs13_7) + 2 ^ 4 * (if finalCarry Trained.net Trained.net.h0 pairs13_7 then 1 else 0)
#eval (run Trained.net Trained.net.h0 pairs255_1, finalCarry Trained.net Trained.net.h0 pairs255_1)
#eval bitsToNat (run Trained.net Trained.net.h0 pairs255_1) + 2 ^ 8 * (if finalCarry Trained.net Trained.net.h0 pairs255_1 then 1 else 0)
#print axioms Trained16.adds
#print axioms Trained16.sums_correct
#print axioms Trained16.carry_correct
