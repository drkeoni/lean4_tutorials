variable (p q r : Prop)

#check False → False

def h1 : p ∧ q → q ∧ p :=
  fun h : p ∧ q =>
    show q ∧ p from And.intro (And.right h) (And.left h)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p 
        from And.intro (And.right h) (And.left h)
    )
    (fun h : q ∧ p =>
      show p ∧ q
        from And.intro (And.right h) (And.left h)
    )

example : p ∨ q ↔ q ∨ p := 
  Iff.intro
    (
      fun h : p ∨ q =>
        show q ∨ p from
          Or.elim h
            (fun hp : p => show q ∨ p from Or.inr hp)
            (fun hq : q => show q ∨ p from Or.inl hq)
    )
    (
      fun h : q ∨ p =>
        show p ∨ q from
          Or.elim h
            (fun hq : q => show p ∨ q from Or.inr hq)
            (fun hp : p => show p ∨ q from Or.inl hp)
    )

example : p ∨ False ↔ p :=
  Iff.intro
    (
      fun h: p ∨ False =>
        show p from
          Or.elim h
            (fun hp : p => hp)
            (fun (hf : False) => False.elim hf)
    )
    (
      fun h: p =>
        show p ∨ False from Or.inl h
    )



open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun (h: p → q ∨ r) =>
    Or.elim (em p)
    -- assume p
    ( 
      fun (hp: p) =>
        -- produce q ∨ r
        Or.elim (h hp)
        -- assume q
        (fun hq : q => Or.inl (fun h2 : p => hq))
        -- assume r
        (fun hr : r => Or.inr (fun h2 : p => hr))
    )
    -- assume ¬p
    (
      fun (hnp: ¬p) =>
        -- we show p → q
        Or.inl (fun (hp: p) => show q from absurd hp hnp)
    )

example : (p → q) → (¬p ∨ q) :=
  λ h1 : p → q =>
    byCases
      (λ hp : p => Or.inr (h1 hp))
      (λ hnp : ¬p => Or.inl hnp)

example : p ∧ ¬q → ¬(p → q) :=
  fun h : p ∧ ¬q =>
    fun h2 : p → q =>
      absurd (h2 h.left) h.right

example : (p → q) → (¬q → ¬p) :=
  fun (h : p → q)(hnq : ¬q) =>
      show ¬p from fun hp : p => absurd (h hp) hnq


