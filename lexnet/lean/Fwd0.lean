/- Step 2a: the thirteen automaton fields, W, N and the opener flag of the full forward cell agree
   with the reference left-to-right pass, for every reachable automaton state, W/N value and byte. -/
import lean.NetExtra
import lean.Hash
namespace Lexnet
open Hash Units
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def autoOf (s : Ref.Left) : AState :=
  [enc s.block, enc s.line, enc s.inStr, enc s.inChr, enc s.pp, enc s.escaped, enc s.slash,
   enc s.star, enc s.closed, enc s.strClosed, enc s.chrClosed, enc s.lineStart, enc s.ppBackslash]

def mkL (a : AState) (ww wn : Bool) : Ref.Left :=
  { block := bit a 0, line := bit a 1, inStr := bit a 2, inChr := bit a 3, pp := bit a 4,
    escaped := bit a 5, slash := bit a 6, star := bit a 7, closed := bit a 8,
    strClosed := bit a 9, chrClosed := bit a 10, lineStart := bit a 11, ppBackslash := bit a 12,
    wasWord := ww, wasNumber := wn }

def coreCheck (a : AState) (ww wn : Bool) (c : Nat) : Bool :=
  let x := (embedding (Fin.ofNat 256 c)).flags
  let r := Ref.step (mkL a ww wn) c
  autoStep x a == autoOf r.1 &&
  wnStep x a (enc ww) (enc wn) == (enc r.1.wasWord, enc r.1.wasNumber) &&
  openStep x a == enc r.2.opener

def coreAll : Bool :=
  reach.all fun a => [false, true].all fun ww => [false, true].all fun wn =>
    (List.range 256).all fun c => coreCheck a ww wn c

def coreOne (i : Nat) : Bool := (reach.getD i []).length == 13 && [false, true].all fun ww => [false, true].all fun wn => (List.range 256).all fun c => coreCheck (reach.getD i []) ww wn c
end Lexnet
