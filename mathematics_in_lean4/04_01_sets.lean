import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.Parity

open Set

variable {α : Type}
variable (s t u : Set α)

/-
  I rewrote this to not use rintros
  (and lean4 syntax)
-/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  dsimp
  intros x h₂
  simp [mem_inter_iff] at h₂
  exact ⟨ (h x h₂.left), h₂.right ⟩

/-- same statement but using implicit simp -/
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intros x xsu
  exact ⟨h xsu.1, xsu.2⟩

/-- exercise -/
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  simp [subset_def]
  intros x h₂
  match h₂ with
  | Or.inl y => exact ⟨ y.left, Or.inl y.right ⟩
  | Or.inr y => exact ⟨ y.left, Or.inr y.right ⟩

/- exercise -/
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  simp [subset_def]
  intros x h₁ h₂
  -- I guess we get to use de Morgan's law
  -- (I was assuming we weren't able to use
  -- classical logic)
  simp [not_or] at h₂
  exact ⟨ ⟨ h₁, h₂.left ⟩, h₂.right ⟩

/- exercise -/
example : s ∩ (s ∪ t) = s := by
  have h₁ : s ∩ (s ∪ t) ⊆ s := by
    intros x h₂
    exact h₂.left
  have h₂ : s ⊆ s ∩ (s ∪ t) := by
    intros x h₂
    simp [subset_def]
    exact  ⟨ h₂, Or.inl h₂ ⟩
  apply Subset.antisymm h₁ h₂

/- exercise -/
example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) := by
  apply Subset.antisymm
  · simp [subset_def]
    intros x h₁
    apply And.intro
    · match h₁ with
      | Or.inl h₂ => exact Or.inl h₂.left
      | Or.inr h₂ => exact Or.inr h₂.left
    · match h₁ with
      | Or.inl h₂ => intros; exact h₂.right
      | Or.inr h₂ => intros h₃; exact absurd h₃ h₂.right
  · simp [subset_def]
    intros x h₁ h₂
    match h₁ with
    | Or.inl h₃ => exact Or.inl ⟨ h₃, h₂ h₃ ⟩
    | Or.inr h₃ =>
      have h₄ : x ∈ t → ¬ x ∈ s := imp_not_comm.mp h₂
      exact Or.inr ⟨ h₃, h₄ h₃ ⟩

#check or_iff_not_imp_left

/- exercise -/

/- in the book they say there's a prime theorem that says
   that a prime is either two or odd
   I can't find it, so maybe I can derive it...
-/
theorem prime_imp_two_or_odd {n : ℕ} : Nat.Prime n → (n = 2) ∨ ¬ Even n := by
  intro p
  rw [Nat.prime_def_lt] at p
  by_cases n ≤ 2
  · match n with
    | 0 => contradiction
    | 1 => contradiction
    | 2 => exact Or.inl (refl 2)
  · have h₁ : 2 < n := not_le.mp h
    have h₂ : ¬ Even n := by
      -- assume Even n
      by_contra h₃
      -- rewrite that 2 | n₂
      simp [even_iff_two_dvd] at h₃
      let ⟨ _, p₂ ⟩ := p
      -- show that 2 = 1
      let h₄ := p₂ 2 h₁ h₃
      contradiction
    exact Or.inr h₂

/-
  Exercise
  - Show that the intersection of all primes and numbers > 2
    is a subset of the set of all odd numbers
-/
example : { n | Nat.Prime n } ∩ { n | n > 2} ⊆ { n | ¬ Even n } := by
  intro n n₂
  simp [inter_def] at n₂
  match prime_imp_two_or_odd n₂.left with
  -- show that assuming n = 2 leads to a contradiction with n₂
  | Or.inl n_eq_2 =>
    -- 2 ≠ n
    have h2 : ¬ n = 2 := by
      let h := (Nat.lt_iff_le_and_ne.mp n₂.right).right
      simp [ne_eq, ne_comm] at h
      exact h
    contradiction
  -- the other side is just that n is odd
  | Or.inr n_is_odd => exact n_is_odd

/-
  exercise
-/

section

variable (s t : Set ℕ)
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬ Even x) (h₁ : ∀ x ∈ t, Nat.Prime x) :
  ∀ x ∈ s, ¬ Even x ∧ Nat.Prime x := by
  intros x h
  simp [subset_def] at ssubt
  exact ⟨ h₀ _ $ ssubt _ h, h₁ _ $ ssubt _ h ⟩ 

end

section

variable {α I : Type}
variable (A B : I → Set α)
variable (s : Set α)

/-
  exercise
-/
example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) := by
  ext x
  apply Iff.intro
  · intros h
    simp [mem_unionᵢ] at *
    match h with
    | Or.inl a => exact (fun _ => Or.inr a)
    | Or.inr a => exact (fun i => Or.inl (a i))
  · intros h
    simp [mem_unionᵢ, mem_interᵢ] at *
    simp [forall_or_right] at h
    rw [or_comm]
    exact h
    
end

section

def primes : Set ℕ := {x | Nat.Prime x}

/-
  exercise

  Show that the union of all numbers that are less
  than primes is the universal set of numbers (ℕ)
-/
example : (⋃ p ∈ primes, {x | x ≤ p}) = univ := by
  ext x
  simp [mem_unionᵢ]
  let ⟨ p, hp ⟩ := Nat.exists_infinite_primes x
  exact ⟨ p, ⟨ hp.right, hp.left ⟩ ⟩

end






#check mem_univ

#check Nat.lt_iff_le_and_ne
#check 2 ≠ 2
#check ne_eq
#check ne_comm

#check Nat.Prime
#check Nat.prime_def_le_sqrt
#check Nat.prime_def_lt
#check Nat.prime_def_lt'
#check Nat.prime_def_le_sqrt
#check Nat.prime_two
#check Nat.exists_infinite_primes





         


        
      




  
    
  





  
    