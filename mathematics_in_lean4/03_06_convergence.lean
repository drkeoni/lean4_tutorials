import Std.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

variable (n : ℕ)

/--
  For all positive epsilon, there exists a N
  such that all values of the sequence past N
  are within epsilon of a
-/
def converges_to (s : ℕ → ℝ) (a : ℝ) := 
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

/-
  This must exist in the standard library but I couldn't
  find it
-/
theorem max_ge (a b : ℕ) : (max a b ≥ a) ∧ (max a b ≥ b) := by
  cases max_cases a b with
  | inl h =>
    simp [h.left, h.right]
  | inr h =>
    simp [h.left, le_iff_lt_or_eq]
    exact Or.inl h.right

set_option trace.linarith false

theorem converges_to_const (a : ℝ) : converges_to (fun x : ℕ => a) a := by
  intros ε εpos
  use 0
  intros n _
  dsimp
  rw [sub_self, abs_zero]
  exact εpos

theorem le_lt_trans {a b c : ℝ} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  cases le_iff_eq_or_lt.mp h₁ with
  | inl h₃ => 
    simp [h₃]
    exact h₂
  | inr h₃ => exact lt_trans h₃ h₂

/-
  the sum of two convergent sequences
  is convergent
-/
theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
  converges_to (fun n => s n + t n) (a + b) := by
  intros ε εpos
  dsimp
  -- this should be provable with linarith but mathlib4
  -- doesn't seem to be there yet
  have ε2pos : 0 < ε / 2 := div_pos εpos zero_lt_two
  cases cs (ε / 2) ε2pos with
  | intro w h =>
    cases ct (ε / 2) ε2pos with
    | intro w₂ h₂ =>
      let w₃ := max w w₂
      have f : ∀ (n : ℕ), n ≥ w₃ → abs (s n + t n - (a + b)) < ε := by
        intros n h₃
        have : w₃ ≥ w := (max_ge w w₂).left
        let t₁ := h n (ge_trans h₃ this)
        have : w₃ ≥ w₂ := (max_ge w w₂).right
        let t₂ := h₂ n (ge_trans h₃ this)
        have v : abs (s n - a) + abs (t n - b) < ε := by
          conv =>
            rhs
            rw [←half_add_self ε]
            rw [←div_add_div_same]
          exact add_lt_add t₁ t₂
        let u := abs_add (s n - a) (t n - b)
        let u₄ := le_lt_trans u v
        have : s n - a + (t n - b) = s n + t n - (a + b) := by ring
        rw [this] at u₄
        exact u₄
      exact ⟨ w₃, f ⟩

/-
  If 
    sequence s converges to a
  then
    c times the sequence s converges to c * a
-/
theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (fun n => c * s n) (c * a) := by
  by_cases h : c = 0
  · convert converges_to_const 0
    ext
    simp [h, zero_mul]
    simp [h]
  · have acpos : 0 < abs c := abs_pos.mpr h
    intros ε εpos
    -- have ∀ (n : ℕ), n ≥ N → abs (s n - a) < ε / abs c
    let ⟨N, h₁⟩ := cs (ε / abs c) (div_pos εpos acpos)
    use N
    intros n ngtn
    conv =>
      lhs
      congr
      · simp
        simp [←mul_sub_left_distrib]
    have t₃ : abs c ≠ 0 := by linarith
    rw [
      abs_mul, 
      mul_comm, 
      ←div_lt_div_right acpos,
      mul_div_assoc,
      div_self t₃,
      mul_one
    ]
    exact h₁ n ngtn

/-
  The terms of a convergent series are absolutely bound
  beyond a certain point
-/
theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b := by
    let ⟨ N, h ⟩ := cs 1 zero_lt_one
    use N, (abs a + 1)
    intros n hn
    let t₁ := h n hn
    let t₂ := (add_lt_add_iff_right (abs a)).mpr t₁
    let u := abs_add (s n - a) a
    let v := le_lt_trans u t₂
    conv at v => 
      lhs
      congr
      simp
    rw [add_comm]
    exact v

/-
  if s converges to a and t converges to 0
  then
    s * t converges to 0
-/
lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (fun n => s n * t n) 0 := by
  intros ε εpos
  dsimp
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B :=
    lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  let ⟨ N₁, h₁ ⟩ := ct _ pos₀
  let N₂ := max N₀ N₁ 
  use N₂
  intros n₁ hn₁
  have ngt₀ : n₁ ≥ N₀ := ge_trans hn₁ (max_ge N₀ N₁).left
  have ngt₁ : n₁ ≥ N₁ := ge_trans hn₁ (max_ge N₀ N₁).right
  let u := h₀ n₁ ngt₀
  let v := h₁ n₁ ngt₁
  let w := mul_lt_mul'' u v (abs_nonneg $ s n₁) (abs_nonneg $ t n₁ - 0)
  conv at w =>
    lhs
    simp [←abs_mul]
  have b_ne_zero : B ≠ 0 := by linarith 
  conv at w =>
    rhs
    rw [mul_comm, mul_comm_div, div_self b_ne_zero, mul_one]
  simp
  exact w

/-
  If 
    s converges to a and t converges to b
  then
    s * t converges to a * b
-/
theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (fun n => s n * t n) (a * b) := by
  have h₁ : converges_to (fun n => s n * (t n - b)) 0 := by
    apply aux cs
    convert converges_to_add ct (converges_to_const (-b))
    ring
  convert (converges_to_add h₁ (converges_to_mul_const b cs))
  ext
  simp
  ring
  ring

/-
  Limits are unique
-/
theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b := by
  by_contra h
  have abpos : abs (a - b) > 0 := abs_pos.mpr (sub_ne_zero.mpr h)
  let u := converges_to_mul_const (-1) sb
  let v := converges_to_add sa u
  simp [converges_to] at v
  let ⟨N, hn⟩ := v (abs (a - b)) abpos
  let w := hn N (le_refl N)
  conv at w =>
    lhs
    rw [←abs_neg]
    congr
    ring_nf
    rw [add_comm, ←sub_eq_add_neg]
  simp [lt_self_iff_false (abs (a - b))] at w
  
#check abs_zero
#check abs_eq_zero
#check abs_eq
#check abs_zsmul
#check abs_mul
#check abs_add
#check abs_sub
#check abs_nonneg
#check abs_add'
#check abs_sub_le
#check abs_nonpos_iff
#check abs_pos
#check abs_pos_of_neg
#check abs_neg

#check ge_trans

#check max_def
#check max_def'
#check max_lt
#check max_def_lt
#check max_eq_iff
#check max_eq_left_iff

#check lt_add_iff_pos_left
#check lt_add_neg_iff_lt
#check lt_add_of_lt_add_left
#check lt_of_add_lt_add_left
#check lt_of_add_lt_of_nonneg_left
#check lt_of_mul_lt_mul_of_nonneg_left
#check lt_of_mul_lt_mul_left'
#check lt_of_mul_lt_mul_of_nonneg_right
#check lt_mul_of_lt_mul_of_nonneg_left
#check lt_mul_of_lt_mul_left
#check lt_of_mul_lt_mul_right
#check lt_neg_of_lt_neg
#check lt_asymm
#check lt_of_eq_of_lt
#check lt_two_mul_self
#check lt_imp_lt_of_le_imp_le
#check lt_trans
#check lt_self_iff_false

#check le_trans
#check le_of_lt
#check le_imp_le_iff_lt_imp_lt
#check le_iff_eq_or_lt
#check le_of_eq (refl n)
#check le_refl

#check div_nonneg
#check div_pos
#check div_pos_iff
#check div_inv_eq_mul
#check div_self
#check div_lt_div_right
#check div_add_div_same

#check mul_assoc
#check mul_lt_mul_left
#check mul_lt_mul_right
#check mul_lt_mul''
#check mul_inv_cancel_left
#check mul_inv_cancel_right
#check mul_inv_cancel_right₀
#check mul_inv_cancel_of_invertible
#check mul_left_inv
#check mul_div_assoc
#check mul_comm_div
#check mul_sub_left_distrib
#check mul_sub_right_distrib

#check add_lt_add
#check add_lt_add_iff_right

#check half_add_self

#check sub_ne_zero

#check iff_false_right

#check Float


  -- cases ct (ε / 2) ε2pos

  -- cases cs (ε / 2) ε2pos with Ns hs
  -- cases ct (ε / 2) ε2pos with Nt ht
  -- use max Ns Nt
  -- sorry