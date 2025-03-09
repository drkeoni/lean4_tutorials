import Mathlib.Data.Nat.Basic

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m with
  | zero => contradiction
  | succ m0 =>
    cases m0 with
    | zero => contradiction
    | succ m1 =>
      apply Nat.succ_le_succ
      let t := Nat.add_le_add_right (Nat.zero_le m1) 1
      simp at t
      exact t

  #check Nat.zero_le
  #check Nat.add_le_add_left
  variables (m1 : ℕ)
  #check Nat.add_le_add_left (Nat.zero_le m1) 1