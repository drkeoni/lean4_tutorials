import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

def fac : ℕ → ℕ
| 0       => 1
| (n + 1) => (n + 1) * fac n

theorem le_mul_trans {a b c d: ℕ} (h₁ : a ≤ b * c) (h₂ : b ≤ d) : a ≤ d * c := 
  le_trans h₁ (Nat.mul_le_mul_right c h₂)

/-
  2 to the power of (n - 1) is
    less than equal to n!
-/
theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n := by
  cases n with simp [fac]
  | succ n1 =>
    induction n1 with simp [fac]
    | succ n0 ih =>
      have eq1 : 2 ^ (n0 + 1) ≤ 2 * ((n0 + 1) * fac n0) := by
        rw [←(mul_le_mul_left (Nat.zero_lt_succ 1))] at ih
        have : Nat.succ 1 = 2 := by rfl
        rw [this, mul_comm, ←Nat.pow_succ] at ih
        exact ih
      have h₁ : 2 ≤ (Nat.succ n0 + 1) := by linarith
      exact le_mul_trans eq1 h₁



      


















#check mul_le_mul_left
#check zero_lt_two
#check Nat.zero_lt_succ 1
#check Nat.succ
example : Nat.succ 1 = 2
#check Nat.pow_succ
#check Nat.mul_assoc
#check Nat.zero_lt_succ
#check Nat.mul_le_mul
#check Nat.mul_le_mul_right
#check Nat.le_trans



