/-
  04_03 The Schröder-Bernstein Theorem
-/
import Init.Classical
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Tactic.Set

open Set
open Function
open Classical

variable {α β : Type} [Nonempty β]
variable (x : α) (y : β)
variable (f : α → β)
variable (g : β → α)
variable (n : ℕ)

#check (invFun g : α → β)
#check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
#check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
#check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

/-
  sequence of sets formed from g'' (f'' ...)
-/
def sb_aux : ℕ → Set α
  | 0       => univ \ (g '' univ)
  | (n + 1) => g '' (f '' sb_aux n)
/-
  union of these sets
-/
def sb_set := ⋃ n, sb_aux f g n
/-
  the Schroder-Bernstein bijection
-/
noncomputable def sb_fun (x : α) : β := 
  if x ∈ sb_set f g then
    f x
  else
    invFun g x

theorem sb_right_inv {x : α} (hx : x ∉ sb_set f g) : g (invFun g x) = x := by
  have h₁ : x ∈ g '' univ := by
    contrapose! hx
    rw [sb_set, mem_unionᵢ]
    use 0
    rw [sb_aux, mem_diff]
    exact ⟨mem_univ x, hx⟩
  have : ∃ y, g y = x := by
    simp [mem_def] at h₁
    apply mem_range.mp
    exact h₁
  exact invFun_eq this

/-
  Show that the function defined by sb_fun is injective
  if f and g are injective
-/
theorem sb_injective (hf: Injective f) (hg : Injective g) :
  Injective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intros x₁ x₂ hxeq
  show x₁ = x₂
  simp only [h_def, sb_fun, ←A_def] at hxeq
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
  -- mathlib4 doesn't have wlog
  -- so we'll probably have to do 2x the work
  · match xA with
    | Or.inl x₁A =>
      have x₂A : x₂ ∈ A := by
        apply not_imp_self.mp
        intro x₂nA
        rw [if_pos x₁A, if_neg x₂nA] at hxeq
        rw [A_def, sb_set, mem_unionᵢ] at x₁A
        have x₂eq : x₂ = g (f x₁) := by
          have : g (f x₁) = g (invFun g x₂) := by rw [hxeq]
          rw [sb_right_inv f g x₂nA] at this
          exact eq_comm.mp this
        rcases x₁A with ⟨n, hn⟩
        rw [A_def, sb_set, mem_unionᵢ]
        use n + 1
        simp [sb_aux]
        exact ⟨x₁, hn, x₂eq.symm⟩
      rw [if_pos x₁A, if_pos x₂A] at hxeq
      exact hf hxeq
    | Or.inr x₂A =>
      have x₁A : x₁ ∈ A := by
        apply not_imp_self.mp
        intro x₁nA
        rw [if_pos x₂A, if_neg x₁nA] at hxeq
        rw [A_def, sb_set, mem_unionᵢ] at x₂A
        have x₁eq : x₁ = g (f x₂) := by
          have : g (f x₂) = g (invFun g x₁) := by rw [hxeq]
          rw [sb_right_inv f g x₁nA] at this
          exact eq_comm.mp this
        rcases x₂A with ⟨n, hn⟩
        rw [A_def, sb_set, mem_unionᵢ]
        use n + 1
        simp [sb_aux]
        exact ⟨x₂, hn, x₁eq.symm⟩
      rw [if_pos x₂A, if_pos x₁A] at hxeq
      exact hf hxeq
  push_neg at xA
  rw [if_neg xA.left, if_neg xA.right] at hxeq
  have : g (invFun g x₁) = g (invFun g x₂) := by rw [hxeq]
  rw [sb_right_inv f g xA.left, sb_right_inv f g xA.right] at this
  exact this

/-
  Show that the function defined by sb_fun is surjective
  if f and g are injective
-/
theorem sb_surjective (hf: Injective f) (hg : Injective g) :
  Surjective (sb_fun f g) := by
  set A := sb_set f g with A_def
  set h := sb_fun f g with h_def
  intro y
  by_cases gyA : g y ∈ A
  · rw [A_def, sb_set, mem_unionᵢ] at gyA
    rcases gyA with ⟨n, hn⟩
    cases n with
    | zero =>
      simp [sb_aux] at hn
    | succ n₂ =>
      simp [sb_aux] at hn
      rcases hn with ⟨x, xmem, hx⟩
      use x
      have : x ∈ A := by
        rw [A_def, sb_set, mem_unionᵢ]
        exact ⟨n₂, xmem⟩
      simp only [h_def, sb_fun, if_pos this]
      exact hg hx
  have : h (g y) = invFun g (g y) :=
    by simp [sb_fun, if_neg gyA]
  rw [leftInverse_invFun hg] at this
  exact ⟨ g y, this ⟩
  
/-
  The Schröder-Bernstein theorem

  If
    f is an injective function : α → β
    g is an injective function : β → α

  Then
    there exists an h : α → β
    s.t. h is a bijective 
-/
theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf: Injective f) (hg : Injective g) :
  ∃ h : α → β, Bijective h :=
  ⟨sb_fun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩

#check mem_univ
#check nonempty_def
#check mem_def
#check range

#check congr_fun_congr_arg
#check ne_of_apply_ne
#check exists_apply_eq
#check forall_apply_eq_imp_iff