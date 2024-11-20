import Mathlib

inductive BTree (α : Type u) : Type u where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
deriving Repr, DecidableEq

namespace BTree

variable {α : Type u} {a b : α} {t l r : BTree α} {n : ℕ}

def height : BTree α → ℕ
  | leaf _ => 0
  | (node l r) => max l.height r.height + 1

section Height

@[simp] theorem height_leaf : (leaf a).height = 0 := rfl

@[simp] theorem height_node : (node l r).height = max l.height r.height + 1 := rfl

theorem left_height_lt : l.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_left _ _

theorem right_height_lt : r.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_right _ _

theorem height_node_of_heights_eq (hl : l.height = n) (hr : r.height = n) :
    (node l r).height = n + 1 := by
  simp_rw [height_node, add_left_inj, hl, hr, max_self]

end Height

def isPerfectOfHeight : ℕ → BTree α → Bool
  | 0, leaf _ => true
  | (_ + 1), leaf _ => false
  | 0, node _ _ => false
  | (n + 1), node l r => l.isPerfectOfHeight n && r.isPerfectOfHeight n

section IsPerfectOfHeight

@[simp] theorem isPerfectOfHeight_zero_leaf :
    (leaf a).isPerfectOfHeight 0  = true := rfl
@[simp] theorem isPerfectOfHeight_succ_leaf :
    (leaf a).isPerfectOfHeight (n + 1) = false := rfl
@[simp] theorem isPerfectOfHeight_zero_node :
    (node l r).isPerfectOfHeight 0 = false := rfl
@[simp] theorem isPerfectOfHeight_succ_node :
    (node l r).isPerfectOfHeight (n + 1) =
    (l.isPerfectOfHeight n && r.isPerfectOfHeight n) := rfl

theorem isPerfectOfHeight_false_of_ne_height (h : t.height ≠ n) :
    t.isPerfectOfHeight n = false := by
  induction t generalizing n with | leaf _ => _ | node l r IHL IHR => _  <;> cases n
  · exact (Ne.irrefl h).elim
  · rfl
  · rfl
  · simp_rw [height_node, Nat.succ_ne_succ, ne_eq, max_eq_iff, not_or,
      not_and'] at h
    simp_rw [isPerfectOfHeight_succ_node, Bool.and_eq_false_iff]
    exact (Nat.le_total r.height l.height).imp
      (fun hlr => IHL (h.1 hlr)) (fun hlr => IHR (h.2 hlr))

theorem height_eq_of_isPerfectOfHeight (h : t.isPerfectOfHeight n) : t.height = n := by
  by_contra c
  simp_rw [isPerfectOfHeight_false_of_ne_height c] at h
  contradiction

theorem isPerfectOfHeight_node_false_of_height_ne (h : l.height ≠ r.height) :
    (node l r).isPerfectOfHeight n = false := by
  cases n with | zero => _ | succ n => _
  · rfl
  · simp_rw [isPerfectOfHeight_succ_node]
    rcases eq_or_ne l.height n with rfl | hn
    · rw [isPerfectOfHeight_false_of_ne_height h.symm, Bool.and_false]
    · rw [isPerfectOfHeight_false_of_ne_height hn, Bool.false_and]

end IsPerfectOfHeight

def isPerfect (t : BTree α) : Prop := t.isPerfectOfHeight (t.height)

section IsPerfect

instance : DecidablePred (isPerfect (α := α)) :=
  fun t => decidable_of_iff (t.isPerfectOfHeight (t.height) = true) Iff.rfl

theorem isPerfect_def : t.isPerfect ↔ t.isPerfectOfHeight (t.height) := Iff.rfl

theorem isPerfect_leaf : (leaf a).isPerfect := rfl

theorem isPerfect_node_of_height_eq (h : l.height = r.height) :
    (node l r).isPerfect ↔ (l.isPerfect ∧ r.isPerfect) := by
  simp_rw [isPerfect_def, height_node, isPerfectOfHeight_succ_node,
    h, max_self,  Bool.and_eq_true]

theorem isPerfect_node_iff : (node l r).isPerfect ↔
    (l.isPerfect ∧ r.isPerfect ∧ l.height = r.height) := by
  simp_rw [isPerfect_def, height_node, isPerfectOfHeight_succ_node]
  by_cases h : l.height = r.height
  · simp_rw [h, max_self, and_true, Bool.and_eq_true]
  · simp_rw [h, and_false]
    rcases Ne.lt_or_lt h with h | h
    · simp_rw [max_eq_right_of_lt h, isPerfectOfHeight_false_of_ne_height h.ne,
        Bool.false_and, Bool.false_eq_true]
    · simp_rw [max_eq_left_of_lt h, isPerfectOfHeight_false_of_ne_height h.ne,
        Bool.and_false, Bool.false_eq_true]

theorem isPerfect_node_of_isPerfect_of_isPerfect_of_heights_eq
    (hl : l.isPerfect) (hr : r.isPerfect)
    (hl₂ : l.height = n)
    (hr₂ : r.height = n)  :
    (node l r).isPerfect := isPerfect_node_iff.mpr ⟨hl, hr, hl₂ ▸ hr₂ ▸ rfl⟩

end IsPerfect

def PerfectBTree (α : Type u) := Subtype (isPerfect (α := α))

def PerfectBTreeStack (α : Type u) := List (PerfectBTree α)

end BTree
