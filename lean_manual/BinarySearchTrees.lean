inductive Tree (β: Type v) where
  | leaf
  | node (left : Tree β) (key : Nat) (value : β) (right : Tree β)
deriving Repr

-- whether a tree contains a key k
def Tree.contains (t : Tree β) (k : Nat) : Bool :=
  match t with
  | leaf => false
  | node left key _ right =>
    if k < key then
      left.contains k
    else if key < k then
      right.contains k
    else
      true

-- return value at key k
def Tree.find? (t : Tree β) (k : Nat) : Option β :=
  match t with
  | leaf => none
  | node left key value right =>
    if k < key then
      left.find? k
    else if key < k then
      right.find? k
    else
      some value

-- insert k, v into tree
def Tree.insert (t : Tree β) (k : Nat) (v : β) : Tree β :=
  match t with
  | leaf => node leaf k v leaf
  | node left key value right =>
    if k < key then
      node (left.insert k v) key value right
    else if key < k then
      node left key value (right.insert k v)
    else
      node left k v right

#eval (@Tree.leaf Nat).insert 2 3

def Tree.toList (t : Tree β) : List (Nat × β) :=
  match t with
  | leaf => []
  | node l k v r => l.toList ++ [(k, v)] ++ r.toList

#eval ((@Tree.leaf Nat).insert 2 3).toList

#eval Tree.leaf.insert 2 "two"
  |>.insert 3 "three"
  |>.insert 1 "one"

#eval Tree.leaf.insert 2 "two"
  |>.insert 3 "three"
  |>.insert 1 "one"
  |>.toList

-- tail-recursive version of toList
def Tree.toListTR (t : Tree β) : List (Nat × β) :=
  go t []
  where go (t : Tree β) (acc : List (Nat × β)) : List (Nat × β) :=
    match t with
    | leaf => acc
    | node l k v r => go l ((k, v) :: go r acc)

-- proof that original toList is same as TR version
theorem Tree.toList_eq_toListTR (t : Tree β) : t.toList = t.toListTR := by
  simp [toListTR, go t []]
where
  go (t : Tree β) (acc : List (Nat × β)) : toListTR.go t acc = t.toList ++ acc := by
    induction t generalizing acc <;>
      -- simp [toListTR.go, toList, *, List.append_assoc]
      simp [*, toListTR.go, toList, List.append_assoc]

@[csimp] theorem Tree.toList_eq_toListTR_csimp : @Tree.toList = @Tree.toListTR := by
  funext β t
  apply toList_eq_toListTR

-- auxiliary type for representing the proposition that
-- a predicate holds for all values in a tree
inductive ForallTree (p : Nat → β → Prop) : Tree β → Prop
  | leaf : ForallTree p .leaf
  | node:
     ForallTree p left →
     p key value →
     ForallTree p right →
     ForallTree p (.node left key value right)

#check Tree.leaf.insert 2 "two"

def myTree := Tree.leaf.insert 2 "two"
def prop (_ : Nat) (s : String) : Prop := s = "two"

#eval myTree
#check ForallTree prop myTree

example : ForallTree prop myTree := by
  simp [Tree.insert]
  apply ForallTree.node
  · exact .leaf
  · simp [prop]
  · exact .leaf

example : ForallTree prop myTree := by
  simp [myTree, Tree.insert]
  apply ForallTree.node <;> simp [ForallTree.leaf, prop]

/-
  Defining the invariant for a binary search tree
-/
inductive BST : Tree β → Prop
  | leaf : BST .leaf
  | node :
    ForallTree (fun k v => k < key) left →
    ForallTree (fun k v => key < k) right →
    BST left → BST right →
    BST (.node left key value right)

example : BST myTree := by
  simp [myTree, Tree.insert, BST.node, BST.leaf, ForallTree.leaf]

/-
  Tactic that proves lhs = rhs
  And then substitutes rhs into lhs
-/
local macro "have_eq " lhs:term:max rhs:term:max : tactic =>
  `(tactic|
     (have h : $lhs = $rhs :=
        by simp_arith at *; apply Nat.le_antisymm <;> assumption
      try subst $lhs
     )
  )

/-
  Tactic that takes each case of e (e and ¬ e)
  and applies all hypotheses to simplify
-/
local macro "by_cases' " e:term : tactic =>
  `(tactic | by_cases $e <;> simp [*])

attribute [local simp] Tree.insert

/-
  Prove that if we have we've asserted
  that 
  1) p holds for all of t
  2) p holds for key, value
  then
  3) inserting key, value into t maintains
     the forall proposition
-/
theorem Tree.forall_insert_of_forall
  (h₁ : ForallTree p t) (h₂ : p key value)
  : ForallTree p (t.insert key value) := by
  induction h₁ with
  | leaf => simp [h₂, ForallTree.node, ForallTree.leaf]
  | node hl hp hr ihl ihr =>
    -- renames elided key with k
    -- (what's the syntax here??)
    rename Nat => k
    -- consider key < k and k <= key
    by_cases' key < k
    -- we can produce a ForallTree term
    · exact ForallTree.node ihl hp hr
    -- consider k < key and k == key
    · by_cases' k < key
      -- we can produce a ForallTree term
      · exact ForallTree.node hl hp ihr
      -- if k == key then we need to substitute this in
      -- and produce the ForallTree term
      · have_eq key k
        exact ForallTree.node hl h₂ hr

/-
  Prove that inserting a key, value
  into a BST produces a BST
-/
theorem Tree.bst_insert_of_bst
  {t : Tree β} (h : BST t) (key : Nat) (value : β)
  : BST (t.insert key value) := by
  induction h with
  -- if h is a leaf then we can trivially produce a node
  | leaf => exact BST.node ForallTree.leaf ForallTree.leaf BST.leaf BST.leaf
  | node h₁ h₂ b₁ b₂ ih₁ ih₂ =>
    -- again, not sure how this works
    rename Nat => k
    -- the simp here seems to apply forall_insert_of_forall
    -- that's kind of surprising
    simp
    -- split on key < k and k <= key
    by_cases' key < k
    -- if key < k then produce a BST
    -- this uses the property that insert into a tree
    -- satisfying key < k preserves this property
    · exact BST.node (forall_insert_of_forall h₁ ‹key < k›) h₂ ih₁ b₂
    -- split on k < key and k == key
    · by_cases' k < key
      -- produce a BST (analogous to above)
      · exact BST.node h₁ (forall_insert_of_forall h₂ ‹k < key›) b₁ ih₂
      -- replace key with k
      · have_eq key k
        -- produce the BST since everybody satisties the reqts
        exact BST.node h₁ h₂ b₁ b₂
  
/-
  Moving on to defining the notion of a BinTree

  A BinTree is a Tree that satisfies the BST property
-/
def BinTree (β : Type u) := { t : Tree β // BST t }

def BinTree.mk : BinTree β := ⟨ Tree.leaf, BST.leaf ⟩

def BinTree.contains (b : BinTree β) (k : Nat) : Bool :=
  -- b.val gives us the Tree
  b.val.contains k

def BinTree.find? (b : BinTree β) (k : Nat) : Option β :=
  b.val.find? k

def BinTree.insert (b : BinTree β) (k : Nat) (value : β) : BinTree β :=
  -- b.property gives us the BST
  ⟨ b.val.insert k value, b.val.bst_insert_of_bst b.property k value ⟩ 

/-
  Prove that finding anything in an empty BinTree
  produces none
-/
theorem BinTree.find_mk (k : Nat) : BinTree.mk.find? k = (none : Option β) := by
  simp [BinTree.mk, BinTree.find?, Tree.find?]

-- allow a lot of simplication
attribute [local simp]
  BinTree.mk BinTree.contains BinTree.find?
  BinTree.insert Tree.find? Tree.contains Tree.insert

/-
  Prove that finding k after insert (k, v) produces
  v
-/
theorem BinTree.find_insert (b : BinTree β) (k : Nat) (v : β)
  : (b.insert k v).find? k = some v := by
  -- extract the tree and BST property
  let ⟨t, h⟩ := b
  -- reduce the problem to Tree.find_insert
  simp
  -- the "with simp" here seems to 
  -- automatically handle the leaf case
  -- also rewriting h
  -- also the k == key case is handled
  --   by Tree.find? on a node containing k
  induction t with simp
  | node left key value right ihl ihr =>
    by_cases' k < key
    -- "cases h" seems to add the BST
    -- features from the current t into
    -- our context
    -- (recall t is a node)
    · cases h
      -- we can solve our problem if we had a BST left
      apply ihl
      -- that's in our assumptions at this point
      assumption
    · by_cases' key < k
      -- same as above
      cases h
      apply ihr
      assumption



        




