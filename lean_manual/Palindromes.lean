-- corresponding to https://leanprover.github.io/lean4/doc/examples/palindromes.lean.html

open List

-- definition of palindromic lists
inductive Palindrome : List α → Prop where
| nil      : Palindrome []
| single   : (a : α) → Palindrome [a]
| sandwich : (a : α) → Palindrome as → Palindrome ([a] ++ as ++ [a])

-- if a list is a palindrome then the reversed list is also a palindrome
theorem palindrome_reverse (h : Palindrome as) : Palindrome as.reverse := by
  induction h with
  | nil => exact Palindrome.nil
  | single a => exact Palindrome.single a
  | sandwich a as ih => 
      simp
      exact Palindrome.sandwich a ih

-- if a list is a palindrome then the list equals itself reversed
theorem reverse_eq_of_palindrome (h : Palindrome as) : as.reverse = as := by
  induction h with
  | nil => rfl
  | single a => rfl
  | sandwich _ _ ih => simp [ih]

-- produce the last element for a non-empty list
def List.last : (as : List α) → as ≠ [] → α
  | [a], _ => a
  | _::a₂::as, _ => (a₂::as).last (by simp)

-- for a non-empty list, you can form the list by appending the suffix-trimmed list
-- to a list containing the suffix
@[simp] theorem List.dropLast_append_last (h : as ≠ []) : as.dropLast ++ [as.last h] = as := by
  match as with
  | [] => contradiction
  | [a] => simp [last, dropLast]
  | a::a₂::tail => 
      simp [last, dropLast]
      exact dropLast_append_last (as := a₂::tail) (by simp)
      
--
-- a theorem for an induction principle for lists
--
-- we have two base cases: [] and [a]
-- when using induction we can show that if the hypothesis is true
-- for the prefix/suffix trimmed list then the hypothesis is true for the
-- untrimmed list
theorem List.palindrome_ind (motive : List α -> Prop)
  (h₁ : motive [])
  (h₂ : (a : α) → motive [a])
  (h₃ : (a b : α) → (as : List α) → motive as → motive ([a] ++ as ++ [b]))
  (as : List α)
  : motive as :=
  match as with
  -- produce the first base case
  | [] => h₁
  -- produce the second base case
  | [a] => h₂ a
  -- for the third case 
  | a₁::a₂::as' => 
    -- the induction hypothesis: we assume everything holds
    -- for a list missing a first and last element
    have ih := palindrome_ind motive h₁ h₂ h₃ (a₂::as').dropLast
    have : [a₁] ++ (a₂::as').dropLast ++ [(a₂::as').last (by simp)] = a₁::a₂::as' :=
      -- turns a₁ into [a₁]
      -- uses a₁::a₂::as' = [a₁] ++ (a₂::as') , but I think this is two rules
      -- also uses the dropLast_append_last rewrite
      by simp
      -- identify this with the motive we'd like to return
      -- ih allows us to identify (a₂::as').dropLast as "as" in h₃
      this ▸ h₃ _ _ _ ih
termination_by _ as => as.length

#check List.cons_getElem_succ