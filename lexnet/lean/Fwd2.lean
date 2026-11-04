/- Step 2b: the counter and the two base-64 hash registers, by symbolic linear arithmetic. -/
import lean.NetExtra
namespace Lexnet
set_option maxHeartbeats 0

/-- Bounds under which the hash registers behave as described. -/
structure HIn (wc code d h1 h2 : Int) : Prop where
  wc : wc = 0 ∨ wc = 1
  code : 0 ≤ code ∧ code ≤ 63
  d : 0 ≤ d ∧ d ≤ 14
  h1 : 0 ≤ h1 ∧ h1 < 2 ^ 48
  h2 : 0 ≤ h2 ∧ h2 < 2 ^ 36

theorem hash_idle (wc code d h1 h2 : Int) (h : HIn wc code d h1 h2) :
    (hashStep wc code 0 d h1 h2).1 = 14 ∧ (hashStep wc code 0 d h1 h2).2.1 = code ∧
    (hashStep wc code 0 d h1 h2).2.2 = 0 := by
  obtain ⟨a, b, c, e, f⟩ := h
  unfold hashStep; simp only []; omega

theorem hash_first (wc code d h1 h2 : Int) (h : HIn wc code d h1 h2) (hd : 8 ≤ d) :
    (hashStep wc code 1 d h1 h2).1 = d - 1 ∧
    (wc = 1 → (hashStep wc code 1 d h1 h2).2.1 = 64 * h1 + code) ∧
    (wc = 0 → (hashStep wc code 1 d h1 h2).2.1 = code) ∧
    (hashStep wc code 1 d h1 h2).2.2 = h2 := by
  obtain ⟨a, b, c, e, f⟩ := h
  unfold hashStep; simp only []; omega

theorem hash_second (wc code d h1 h2 : Int) (h : HIn wc code d h1 h2) (hd : 2 ≤ d) (hd2 : d ≤ 7) :
    (hashStep wc code 1 d h1 h2).1 = d - 1 ∧
    (hashStep wc code 1 d h1 h2).2.1 = h1 ∧
    (wc = 1 → (hashStep wc code 1 d h1 h2).2.2 = 64 * h2 + code) ∧
    (wc = 0 → (hashStep wc code 1 d h1 h2).2.2 = code) := by
  obtain ⟨a, b, c, e, f⟩ := h
  unfold hashStep; simp only []; omega

theorem hash_full (wc code d h1 h2 : Int) (h : HIn wc code d h1 h2) (hd : d ≤ 1) :
    (hashStep wc code 1 d h1 h2).1 = 0 ∧ (hashStep wc code 1 d h1 h2).2.1 = h1 ∧
    (hashStep wc code 1 d h1 h2).2.2 = h2 := by
  obtain ⟨a, b, c, e, f⟩ := h
  unfold hashStep; simp only []; omega
end Lexnet
