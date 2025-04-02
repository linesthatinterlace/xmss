import Mathlib

inductive BTree (α : Type u) : ℕ → Type u where
  | leaf : α → BTree α 0
  | node : BTree α n → BTree α n → BTree α (n + 1)
deriving Repr, DecidableEq
