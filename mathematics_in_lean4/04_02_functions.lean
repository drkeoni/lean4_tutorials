/- 02_Functions -/
import Init.Classical
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Parity

open Set
open Function

section

variable (α β : Type)
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

/-
  exercise

  The image of s (through f) is a subset of v
  iff
  s is a subset of the pre-image of v
-/
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  -- maybe this used to be more difficult in lean 3?
  simp [subset_def]

/-
  For an injective function:

  The pre-image of the image of s is a subset of s
-/
example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  simp [Injective] at h
  simp [subset_def]
  intros x y h₁ h₂
  have : y = x := h h₂
  subst this
  exact h₁

/-
  If u is a subset of v then
  The pre-image of u is a subset of the pre-image of v
-/
example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  simp [subset_def] at *
  intros x h₁
  exact (h (f x) h₁)

/-
  Moving on to inverse functions
-/
variable {α β : Type} [Inhabited α] [Inhabited β]
variable (f : α → β)

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) := Classical.choose_spec h

open Classical

noncomputable def inverse (f : α → β) : β → α :=
  fun (y : β) => 
    if h : ∃ x, f x = y then
      Classical.choose h
    else 
      default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y := by
    rw [inverse]
    rw [dif_pos]
    exact Classical.choose_spec h

example : Injective f ↔ LeftInverse (inverse f) f := by
  rw [LeftInverse, Injective]
  apply Iff.intro
  · intros h₁ x
    by_cases h : ∃ x₂, f x₂ = f x
    · simp [inverse]
      exact h₁ (choose_spec h)
    · have : ∃ x₂, f x₂ = f x := by
        have : f x = f x := by rfl
        exact ⟨ x, this ⟩ 
      contradiction
  · intros h₁ x x₂ h₂
    let t := h₁ x₂
    let t₂ := h₁ x
    rw [h₂] at t₂
    rw [t₂] at t
    exact t

example : Surjective f ↔ RightInverse (inverse f) f := by
  simp [Function.RightInverse, Surjective, LeftInverse]
  apply Iff.intro
  · intros h₁ y
    exact inverse_spec y (h₁ y)
  · intros h₁ y
    let t₁ := h₁ y
    rw [inverse] at t₁
    by_cases h : ∃ x, f x = y
    · exact h
    · simp [h] at t₁
      exact ⟨ default, t₁ ⟩
     
/-
  There is no surjective function from
  a set to its power set
-/
theorem Cantor : ∀ f : α → Set α, ¬ Surjective f := by
  intros f surjf
  let S := { i | i ∉ f i}
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by
      rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rwa [h] at h₁
  contradiction

#check eq_comm

#check dif_pos
#check LeftInverse
#check choose
#check choose_spec
#check axiom_of_choice

end