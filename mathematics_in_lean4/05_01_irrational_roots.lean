import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Factorization.Basic

#print Nat.coprime
#print Nat.gcd

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := h

example (m n : Nat) (h : m.coprime n) : m.gcd n = 1 := by
  rw [Nat.coprime] at h
  exact h

example : 5 + 3 = 2 * 4 := by norm_num

/-
  The following two examples aren't working in
  mathlib4 yet
-/
-- example : Nat.coprime 12 7 := by norm_num
-- example : Nat.gcd 12 8 = 4 := by norm_num

#check @Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ (m : ℕ), m < p → m ∣ p → m = 1 :=
  by rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ (m : ℕ), m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

-- using norm_num for this is not in mathlib4
example : Nat.Prime 17 := by
  rw [Nat.prime_def_minFac]
  apply And.intro
  · norm_num
  · rfl
  
-- commonly used
example : Nat.Prime 2 := Nat.prime_two
example : Nat.Prime 3 := Nat.prime_three

#norm_num (6 ^ 2) + (4 * 5)
#norm_num 3 ∣ 6

#check Nat.prime_def_minFac
#eval Nat.minFac 17

#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

example {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) :
  b = c := by
  -- library_search suggests the following:
  exact (mul_right_inj' h').mp h

/-
  If m, n are coprime
  then m^2 ≠ 2 n^2  
-/
example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 := by
  intro sqr_eq
  have m2 : 2 ∣ m := by
    have : 2 ∣ m^2 := by
      simp [dvd_iff_exists_eq_mul_left]
      use n^2
      linarith
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp m2
  have h₂ : 2 * (2 * k^2) = 2 * n^2 := by
    rw [←sqr_eq, meq]
    ring
  have : 2 * k^2 = n^2 := by
    have : 2 ≠ 0 := by norm_num
    exact (mul_right_inj' this).mp h₂
  have n2 : 2 ∣ n := by
    have : 2 ∣ n^2 := by
      simp [dvd_iff_exists_eq_mul_left]
      use k^2
      linarith
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_two this
  have h₅ : 2 ∣ m.gcd n :=
    Nat.dvd_gcd m2 n2
  have : 2 ∣ 1 := by
    rwa [Nat.coprime_iff_gcd_eq_one.mp coprime_mn] at h₅
  norm_num at this

/-
The power of p in m*n is the sum of
  the power of p in m
  plus the power of p in n
-/
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
  (m * n).factorization p = m.factorization p + n.factorization p := by
    rw [Nat.factorization_mul mnez nnez]
    rfl

/-
The power of p in n^k is
  k times the power of p in n
-/
theorem factorization_pow' (n k p : ℕ) :
  (n^k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem nat.prime.factorization' {p : ℕ} (prime_p : p.Prime) :
  p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m^2 ≠ p * n^2 := by
  intro sqr_eq
  have nsqr_nez : n^2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m^2) p = 2 * m.factorization p := by
    rw [factorization_pow']
  have eq2 : (p * n^2).factorization p = 2 * n.factorization p + 1 := by
    rw [
      factorization_mul' (Nat.Prime.ne_zero prime_p) nsqr_nez,
      factorization_pow',
      nat.prime.factorization' prime_p,
      add_comm
    ]
  have : (2 * m.factorization p) % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [←eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this

/-
If m^k = r * n^k for some m, n, k, r
  then k divides the power of p in r for all prime p
-/
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k)
  {p : ℕ} (prime_p : p.Prime) : k ∣ r.factorization p := by
  cases r with
  | zero => simp
  | succ r0 =>
    have npow_nz : n^k ≠ 0 := by
      by_contra npowz
      rw [ne_eq] at nnz
      exact absurd (pow_eq_zero npowz) nnz
    have eq1 : (m^k).factorization p = k * m.factorization p := by
      rw [factorization_pow']
    have eq2 : (r0.succ * n^k).factorization p =
      k * n.factorization p + r0.succ.factorization p := by
      rw [
        factorization_mul' (Nat.succ_ne_zero r0) npow_nz,
        factorization_pow',
        add_comm
      ]
    have eq3 : r0.succ.factorization p = k * (m.factorization p - n.factorization p) := by
      rw [Nat.mul_sub_left_distrib k (m.factorization p) (n.factorization p)]
      rw [←eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
    rw [mul_comm] at eq3
    rw [dvd_iff_exists_eq_mul_left]
    exact ⟨ (Nat.factorization m p - Nat.factorization n p), eq3 ⟩

#check mul_sub
#check Nat.succ_ne_zero
#check ne_eq
#check pow_eq_zero
#check Nat.Prime.ne_zero

#check dvd_iff_exists_eq_mul_left
#check Nat.Prime.dvd_of_dvd_pow
#check Nat.dvd_gcd
#check Nat.coprime_iff_gcd_eq_one

#check Nat.factors
#check Nat.prime_of_mem_factors
#check Nat.prod_factors
#check Nat.factors_unique

#check add_comm

#eval Nat.factors 12

example {m n k : ℕ} : k * (m - n) = k * m - k * n := Nat.mul_sub_left_distrib k m n
