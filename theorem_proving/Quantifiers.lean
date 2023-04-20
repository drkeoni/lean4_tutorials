example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left

variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)

variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r    -- ∀ (x y z : α), r x y → r y z → r x z
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc

variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd

-- Exercise 1

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
  Iff.intro
  (
    fun h : ∀ x, p x ∧ q x =>
      ⟨
      fun y : α =>
        show p y from (h y).left,
      fun y : α =>
        show q y from (h y).right
      ⟩  
  )
  (
    fun h : (∀ x, p x) ∧ (∀ x, q x) =>
      fun y : α =>
        have h1 : p y := h.left y
        have h2 : q y := h.right y
        show p y ∧ q y from ⟨ h1, h2 ⟩ 
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h : (∀ x, p x → q x) =>
    fun h2 : (∀ x, p x) =>
      fun y : α =>
        show q y from h y (h2 y)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
    Or.elim h
    (
      fun h2 : ∀ x, p x =>
        fun y : α =>
          show p y ∨ q y from Or.inl (h2 y)
    )
    (
      fun h2 : ∀ x, q x =>
        fun y : α =>
          show p y ∨ q y from Or.inr (h2 y)
    )

-- from text

def divides (x y : Nat) : Prop :=
  ∃ k, k*x = y

-- prove if x divides y and y divides z then x divides z
-- have k₁ * x = y
-- have k₂ * y = z
-- then claim k₁ * k₂ is the witness of x divides z
-- k₂*(k₁ * x) = z
-- (k₂ * k₁) * x = z
-- (k₁ * k₂) * x = z
-- q.e.d.
def divides_trans (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
  let ⟨k₁, d₁⟩ := h₁
  let ⟨k₂, d₂⟩ := h₂
  ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

-- k is the witness that k * x = k * x
def divides_mul (x : Nat) (k : Nat) : divides x (k*x) :=
  ⟨k, rfl⟩

instance : Trans divides divides divides where
  trans := divides_trans

example (h₁ : divides x y) (h₂ : y = z) : divides x (2*z) :=
  calc
    divides x y     := h₁
    _ = z           := h₂
    divides _ (2*z) := divides_mul ..

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    -- w is the witness
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)

def is_even (a : Nat) := ∃ b, a = 2 * b

variable (a b : Nat)

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
  Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
    Exists.intro (w1 + w2)
      (calc
        a + b = 2 * w1 + 2 * w2  := by rw [hw1, hw2]
          _   = 2 * (w1 + w2)    := by rw [Nat.mul_add])))

theorem even_plus_even2 (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩

-- exercise 2

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) :=
  fun h : α =>
    Iff.intro
    (
      fun h2 : (∀ x : α, r) =>
        h2 h
    )
    (
      fun h2 : r => fun _ : α => h2
    )

open Classical

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (
    fun h : ∀ x, p x ∨ r =>
      byCases
      (
        fun h2 : r =>
          show (∀ x, p x) ∨ r from Or.inr h2
      )
      (
        -- if r is False then it must be the case
        -- that under h we have (∀ x, p x)
        fun h2 : ¬r =>
          have h4 : (∀ x, p x) := (
            fun y : α =>
              Or.elim (h y)
              (
                id
              )
              (
                fun h3 : r => absurd h3 h2
              )
          )
          show (∀ x, p x) ∨ r from Or.inl h4
      )
  )
  (
    fun h : (∀ x, p x) ∨ r =>
      Or.elim h
      (
        fun h2 : (∀ x, p x) =>
          fun y : α =>
            show p y ∨ r from Or.inl (h2 y)
      )
      (
        fun h2 : r =>
          fun y : α =>
            show p y ∨ r from Or.inr h2
      )
  )

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    Iff.intro
    (
      fun h : ∀ x, r → p x =>
        fun h2 : r =>
          fun y : α =>
            (h y) h2
    )
    (
      fun h : r → ∀ x, p x =>
        fun y : α =>
          fun h2 : r =>
            (h h2) y
    )

-- intermediate exercises

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h : (∃ x : α, r) =>
    let ⟨ _, d ⟩ := h
    show r from d

example : (∃ x : α, r) → r :=
  fun ⟨ w, d ⟩ => d

example (a : α) : r → (∃ x : α, r) :=
  fun h : r =>
    ⟨ a, h ⟩ 

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (
    fun h : ∃ x, p x ∧ r =>
      let ⟨ w, d ⟩ := h
      ⟨ ⟨ w, d.left ⟩, d.right ⟩
  )
  (
    fun h : (∃ x, p x) ∧ r =>
      let ⟨ w, d ⟩ := h.left
      ⟨ w, ⟨ d, h.right ⟩ ⟩
  )


example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (
    fun h : (∃ x, p x ∨ q x) =>
      let ⟨ w, d ⟩ := h
      Or.elim d
      (
        fun h2 : p w => Or.inl ⟨ w, h2 ⟩ 
      )
      (
        fun h2 : q w => Or.inr ⟨ w, h2 ⟩ 
      )
  )
  (
    fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
      (
        fun h2 : ∃ x, p x =>
          let ⟨ w, d ⟩ := h2
          ⟨ w, Or.inl d ⟩
      )
      (
        fun h2 : ∃ x, q x =>
          let ⟨ w, d ⟩ := h2
          ⟨ w, Or.inr d ⟩
      )
  )

  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    Iff.intro
    (
      fun h : ∃ x, r → p x =>
        let ⟨ w, d ⟩ := h
        fun h2 : r => ⟨ w, d h2 ⟩
    )
    (
      fun h : r → ∃ x, p x =>
        sorry
    )

-- Exercise 3

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  byContradiction (
    byCases
    (
      fun h1 : shaves barber barber =>
        have f : _ := Iff.mp (h barber)
        absurd h1 (f h1)
    )
    (
      fun h1 : ¬ shaves barber barber =>
        have f : _ := Iff.mpr (h barber)
        absurd (f h1) h1
    )
  )

-- Exercise 4

variable (a b c k n: Nat)

def even (n : Nat) : Prop :=
  ∃ k, 2 * k = n

def prime (n : Nat) : Prop :=
  ¬ ∃ k, divides k n

def infinitely_many_primes : Prop :=
  ∀ k, ∃ p, prime p ∧ p ≥ k  

def Fermat_prime (n : Nat) : Prop :=
  ∃ k, 2^(2^k) + 1 = n  

def infinitely_many_Fermat_primes : Prop :=
  ∀ k, ∃ p, Fermat_prime p ∧ p ≥ k

def goldbach_conjecture : Prop :=
  -- ∀ k, ∃ q, ∃ p, (k > 1) → prime q ∧ prime p ∧ (p + q = 2 * k)
  ∀ k, ∃ q, ∃ p, (k > 1) → prime q ∧ prime p ∧ (p + q = 2 * k)

def Fermat's_last_theorem : Prop :=
  ∀ n, (n > 2) →
    ¬ (∃ a : Nat, ∃ b : Nat, ∃ c : Nat, a^n + b^n = c^n)
