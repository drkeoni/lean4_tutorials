

#check List.nil_append
#check []
#check List.nil

theorem nil_append2 (as : List α) : List.append [] as = as := by
  rfl

theorem append_nil_nil : @List.append α [] [] = [] := by
  rfl

#check List.reverse_append

theorem append_nil (as : List α) : List.append as [] = as := by
  simp [List.reverse_append]

/-
Exercise 1

Try defining other operations on the natural 
numbers, such as multiplication, the predecessor
function (with pred 0 = 0), truncated subtraction
(with n - m = 0 when m is greater than or equal to n), 
and exponentiation. 
Then try proving some of their basic properties,
building on the theorems we have already proved.
-/
namespace Hidden

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero   => m
  | Nat.succ n => Nat.succ (add m n)

theorem add_zero (m : Nat) : add m .zero = m := by
  simp [add]

theorem zero_add (m : Nat) : add .zero m = m := by
  induction m
  · simp [add]
  · simp [add]
    assumption

-- (x + y) + 1 = (x + 1) + y
theorem add_one (m n : Nat) : .succ (add m n) = add (.succ m) n := by
  induction n
  case zero => simp [add]
  case succ n0 ih =>
    simp [add]
    exact ih

-- addition is commutative
theorem add_comm (m n : Nat) : add m n = add n m := by
  induction n
  case zero => simp [add_zero, zero_add]
  case succ n0 ih =>
    simp [add, ←add_one]
    exact ih

-- same thing but simpler
example (m : Nat) : add .zero m = m := by
  induction m <;> simp [add] <;> assumption

-- the definition of multiplication
def mul (m n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ n0 => add m (mul m n0)

-- 3 * 2 = 6
#eval mul (Nat.succ (Nat.succ (Nat.succ Nat.zero))) (Nat.succ (Nat.succ Nat.zero))

-- 0 * m = 0
theorem zero_mul (m : Nat) : mul .zero m = .zero := by
  induction m
  case zero => simp [mul]
  case succ n ih => simp [mul, ih, add]

-- n * (m + 1) = n + (n * m)
theorem n_times_m_plus_one (n m : Nat) : mul n (.succ m) = add n (mul n m) := by
  induction m <;> simp [mul]
    
theorem add_assoc (x y z : Nat) : add (add x y) z = add (add z y) x := by
  induction y
  case zero => simp [add, add_comm]
  case succ y0 ih =>
    simp_all [add_comm]
    simp [add]
    exact ih

theorem add_assoc2 (x y z : Nat) : add x (add y z) = add y (add x z) := by
  induction z
  case zero => simp [add, add_comm]
  case succ z0 ih => simp [add, ih]
  
-- (n + 1) * m = (n * m) + m
theorem n_plus_one_times_m (n m : Nat) : mul (.succ n) m = add (mul n m) m := by
  induction m
  case zero => simp [add, mul]
  case succ m0 ih =>
    simp [n_times_m_plus_one]
    simp_all [add_comm]
    simp [add, add_assoc]

-- multiplication is commutative
theorem mul_comm (m n : Nat) : mul m n = mul n m := by
  induction n
  case zero => simp [mul, zero_mul]
  case succ n0 ih =>
    simp [mul]
    cases m
    · simp [zero_add, mul, zero_mul]
    · simp_all [n_plus_one_times_m, ih, add_comm]

-- m to the power of n
def pow (m n : Nat) : Nat :=
  match n with
  | .zero => .succ .zero
  | .succ n0 => mul m (pow m n0)

-- 2**3
#eval pow (.succ (.succ .zero)) (.succ (.succ (.succ .zero)))

-- m * (n + o) = m * n + m * o
theorem mul_add (m n o: Nat) : mul m (add n o) = add (mul m n) (mul m o) := by
  induction o
  case zero => simp [mul, add]
  case succ o0 ih => simp [add, mul, ih, add_assoc2]

-- m * (n * o) = n * (m * o)
theorem mul_assoc (m n o: Nat) : mul m (mul n o) = mul n (mul m o) := by
  induction o
  case zero => simp [mul]
  case succ o0 ih => simp [mul, mul_add, ih, mul_comm]

-- m**(n + o) = (m**n) * (m**o)
theorem m_to_power_n_o (m n o: Nat) : pow m (add n o) = mul (pow m n) (pow m o) := by
  induction o
  case zero => simp [add, pow, mul]
  case succ o0 ih => simp [pow, mul_assoc, ih]
    
end Hidden

/-
  Exercise 2

  Define some operations on lists, like a length function or the reverse function.
  Prove some properties, such as the following:

  a. length (s ++ t) = length s + length t

  b. length (reverse t) = length t

  c. reverse (reverse t) = t   

-/
namespace Exercise2

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α
deriving Repr

def append (as bs : List α) : List α :=
  match as with
  | .nil       => bs
  | .cons a as => .cons a (append as bs)

infixl:65 " ++ " => Exercise2.append

theorem nil_append (as : List α) : append .nil as = as := rfl

theorem append_nil (as : List α) : append as .nil = as := by
  induction as
  case nil => simp [append]
  case cons a as0 ih => simp [append, ih]

theorem cons_append (a : α) (as bs : List α) : append (.cons a as) bs = .cons a (append as bs) := rfl

def alist := List.cons "a" List.nil

def abcList := (List.cons "c" (List.cons "b" (List.cons "a" List.nil)))

#eval alist ++ alist

def length (as : List α) : Nat :=
  match as with
  | .nil => 0
  | .cons a as0 => 1 + length as0

theorem len_append (as bs : List α) : length (as ++ bs) = length as + length bs := by
  induction as
  case nil => simp [append, length]
  case cons a as0 ih => simp [length, ih, Nat.add_assoc]

def reverse (as : List α) : List α :=
  match as with
  | .nil => .nil
  | .cons a as0 => append (reverse as0) (.cons a .nil)

#eval abcList
#eval reverse abcList

theorem len_reverse (as : List α) : length (reverse as) = length as := by
  induction as
  case nil => simp [reverse]
  case cons a as0 ih => simp [length, reverse, len_append, ih, Nat.add_comm]

theorem append_assoc (as bs cs : List α) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  induction as
  case nil => simp [nil_append]
  case cons a as0 ih => simp [append, ih]

theorem reverse_append (as bs : List α) : reverse (as ++ bs) = reverse bs ++ reverse as := by
  induction as
  case nil => simp [reverse, append, append_nil]
  case cons a as0 ih => simp [reverse, ih, append_assoc]

theorem reverse_reverse (as : List α) : reverse (reverse as) = as := by
  induction as
  case nil => simp [reverse]
  case cons a as0 ih =>
    simp [reverse, reverse_append, nil_append, ih, cons_append]

#check Nat.add_assoc

end Exercise2

/-
Define an inductive data type consisting of
terms built up from the following constructors:

- const n, a constant denoting the natural number n
- var n, a variable, numbered n
- plus s t, denoting the sum of s and t
- times s t, denoting the product of s and t

Recursively define a function that evaluates
any such term with respect to an assignment of
values to the variables.
-/

namespace Exercise3

inductive Term where
  | const : Nat → Term
  | var : Nat → Term
  | plus : Term → Term → Term
  | times : Term → Term → Term

def eval (ctx : Nat → Nat) (t : Term) : Nat :=
  match t with
  | .const n => n
  | .var n => ctx n
  | .plus n m => (eval ctx n) + (eval ctx m)
  | .times n m => (eval ctx n) * (eval ctx m)

def ctx1 : Nat → Nat
  | 0 => 5
  | 1 => 2
  | _ => 0

#eval eval ctx1 (.plus (.var 0) (.const 3))

end Exercise3

