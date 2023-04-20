/-
Exercise 5


-/
namespace Exercise5

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

#eval sampleExpr

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => (eval v e₁) + (eval v e₂)
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0

#eval eval sampleVal sampleExpr

def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr
  | plus e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂))
  | e => e

def sampleExpr2 : Expr :=
  plus (times (plus (const 1) (const 0)) (const 7)) (times (const 2) (const 3))

#eval fuse sampleExpr2

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro h
  induction h with
  | const n => simp [simpConst]
  | var n => simp [simpConst]
  | plus e₁ e₂ ih1 ih2 =>
    cases e₁ with
    | const m =>
      cases e₂ with
      | const o => simp [simpConst, eval]
      | var o => simp [eval]
      | plus o p => simp [eval]
      | times o p => simp [eval]
    | var o => simp [eval]
    | plus o p => simp [eval]
    | times o p => simp [eval]
  | times e₁ e₂ ih1 ih2 =>
    cases e₁ with
    | const m =>
      cases e₂ with
      | const o => simp [simpConst, eval]
      | var o => simp [eval]
      | plus o p => simp [eval]
      | times o p => simp [eval]
    | var o => simp [eval]
    | plus o p => simp [eval]
    | times o p => simp [eval]

-- With a little inspection the above solution can be
-- written more succintly
example (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
  intro h
  induction h with simp [eval]
  | plus e₁ e₂ _ _ =>
    cases e₁ <;> cases e₂ <;> simp [simpConst, eval]
  | times e₁ e₂ _ _ =>
    cases e₁ <;> cases e₂ <;> simp [simpConst, eval]

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e := by
  intro h
  induction h with simp [fuse]
  | plus e₁ e₂ ih₁ ih₂ =>
    cases e₁ <;> cases e₂ <;> simp_all [fuse, simpConst_eq, eval]
  | times e₁ e₂ ih₁ ih₂ =>
    cases e₁ <;> cases e₂ <;> simp_all [fuse, simpConst_eq, eval]

end Exercise5