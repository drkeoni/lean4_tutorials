import Mathlib.Data.Real.Basic
import Mathlib.Algebra.GroupPower.Order

variable {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x := by
  cases le_or_gt 0 x with
  | inl h₁ =>
    rw [abs_of_nonneg h₁]
  | inr h₂ =>
    linarith [abs_pos_of_neg h₂]
  
theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x := by
  cases le_or_gt 0 x with
  | inl h₁ => linarith [abs_of_nonneg h₁]
  | inr h₂ => linarith [abs_of_neg h₂]

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=  by
  cases le_or_gt 0 (x + y) with
  -- x + y ≥ 0 
  | inl h₁ =>
    rw [←abs_eq_self] at h₁
    rw [h₁]
    linarith [le_abs_self x, le_abs_self y]
  -- x + y < 0
  | inr h₂ =>
    have : abs (x + y) = -(x + y) := abs_eq_neg_self.mpr (le_iff_eq_or_lt.mpr (Or.inr h₂))
    linarith [neg_le_abs_self x, neg_le_abs_self y]

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · exact Or.inl xlt
  · contradiction
  · exact Or.inr xgt  
  
example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) : z ≥ 0 := by
  rcases h with ⟨a, b, ha | hb⟩ <;> simp_all <;> linarith [sq_nonneg a, sq_nonneg b]
  
example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 := by
  simp [sub_eq_zero] at h
  exact h

variable {R : Type} [CommRing R] [IsDomain R]
variable (x y : R)

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 := by
  simp [sub_eq_zero] at h
  exact h

#check abs_pos_of_neg
#check abs_of_neg
#check le_neg
#check le_neg_of_le_neg
#check lt_imp_lt_of_le_imp_le
#check le_iff_eq_or_lt
#check lt_of_abs_lt
#check lt_of_eq_of_lt
#check abs_eq
#check abs_pos
#check abs_nonneg
#check abs_eq_self
#check abs_eq_neg_self
#check le_add_left
#check lt_mul_of_lt_mul_right
#check lt_of_pow_lt_pow
#check pow_lt_one
#check sq_nonneg
#check eq_zero_or_eq_zero_of_mul_eq_zero
#check sub_eq_zero