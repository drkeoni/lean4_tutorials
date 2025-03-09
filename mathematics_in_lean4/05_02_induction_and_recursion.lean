import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

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

variables {α : Type u} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

#check Finset.sum s f
#check Finset.prod s f

open BigOperators
open Finset

example : s.sum f = ∑ x in s, f x := rfl
example : s.prod f = ∏ x in s, f x := rfl

example : (range n).sum f = ∑ x in range n, f x := rfl
example : (range n).prod f = ∏ x in range n, f x := rfl

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 := by
  rw [eq_comm]
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction n with
  | zero => simp
  | succ n0 ih =>
    simp [Finset.sum_range_succ] at *
    have : Nat.succ n0 = n0 + 1 := by rfl
    simp [this] at *
    ring_nf at *
    let t := 6 * (1 + n0 * 2 + n0 ^2)
    have h : t + (n0 + n0 ^ 2 * 3 + n0 ^ 3 * 2) = t + (6 * ((Finset.sum (range n0) fun x => x ^ 2) + n0 ^ 2)) := by
      rw [Nat.add_left_cancel_iff]
      exact ih
    ring_nf at h
    have : 6 + n0 * 12 + n0 ^ 2 * 6 = 6 * (1 + n0 * 2 + n0 ^ 2) := by
      ring_nf
    rw [this] at h
    conv at h =>
      rhs
      rw [add_comm, ←Nat.mul_add]
    exact h

    
    





      





    








example : 0 < 2 := by norm_num
#check Nat.div_eq_of_eq_mul_right
#check eq_comm
#check Finset.sum_range_succ
#check Nat.succ
#check Nat.add_left_cancel_iff
#check Nat.mul_add















#check mul_le_mul_left
#check zero_lt_two
#check Nat.zero_lt_succ 1
#check Nat.succ
example : Nat.succ 1 = 2 := by rfl
#check Nat.mul_assoc
#check Nat.zero_lt_succ
#check Nat.mul_le_mul
#check Nat.mul_le_mul_right
#check Nat.le_trans



