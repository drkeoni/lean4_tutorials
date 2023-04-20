import Std.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

def f (x : Nat) := x + 3

example (a b c : ℝ) : (c * b) * a = b * (a * c) := by
  ring
