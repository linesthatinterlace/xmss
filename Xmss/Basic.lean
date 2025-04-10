import Mathlib.Algebra.Order.Ring.Canonical
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

variable {α : Type*}

variable {n m k : ℕ}

namespace Nat

theorem inf_div (a b c : ℕ) : (a ⊓ b) / c = a / c ⊓ b / c := by
  rcases le_or_lt a b with hab | hab
  · simp_rw [min_eq_left hab, min_eq_left (Nat.div_le_div_right hab)]
  · simp_rw [min_eq_right hab.le, min_eq_right (Nat.div_le_div_right hab.le)]

theorem sup_div (a b c : ℕ) : (a ⊔ b) / c = a / c ⊔ b / c := by
  rcases le_or_lt a b with hab | hab
  · simp_rw [max_eq_right hab, max_eq_right (Nat.div_le_div_right hab)]
  · simp_rw [max_eq_left hab.le, max_eq_left (Nat.div_le_div_right hab.le)]

end Nat

namespace List

theorem ext_getElem_iff (s t : List α) : s = t ↔
    s.length = t.length ∧ (∀ i (hi₁ : i < s.length) (hi₁ : i < t.length), s[i] = t[i]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · exact List.ext_getElem h.1 h.2

@[elab_as_elim]
def doubleRec {α : Type*} {motive : List α → Sort*} (l : List α)  (nil : motive [])
    (singleton : ∀ a, motive [a])
    (cons_cons : ∀ a b l, motive l → motive (a :: b :: l)) : motive l :=
  match l with
  | [] => nil
  | [a] => singleton a
  | _ :: _ :: l => cons_cons _ _ _ (doubleRec l nil singleton cons_cons)

section DoubleRec

variable {motive : List α → Sort*} {nil : motive []} {singleton : ∀ a, motive [a]}
  {cons_cons : ∀ a b l, motive l → motive (a :: b :: l)}

@[simp]
theorem doubleRec_nil : doubleRec ([] : List α) nil singleton cons_cons = nil := rfl
@[simp]
theorem doubleRec_singleton {a : α} : doubleRec [a] nil singleton cons_cons = singleton a := rfl
@[simp]
theorem doubleRec_cons₂ {a b : α} {l : List α} :
    doubleRec (a :: b :: l) nil singleton cons_cons =
    cons_cons a b l (doubleRec l nil singleton cons_cons) := rfl

end DoubleRec

section Length

theorem length_take_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.take n).length = n := length_take_of_le (hl ▸ Nat.le_add_right _ _)

theorem length_drop_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.drop n).length = m := length_drop ▸ (hl ▸ add_tsub_cancel_left _ _)

end Length

end List

inductive BT (α : Type*) : ℕ → Type _ where
  | leaf : (a : α) → BT α 0
  | node {n : ℕ} : (l : BT α n) → (r : BT α n) → BT α (n + 1)
deriving Repr, DecidableEq

namespace BT

section Leaf

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by simp only [leaf.injEq]

end Leaf

section Node

theorem node_inj_iff {a b c d : BT α n}: a.node b = c.node d ↔ a = c ∧ b = d := by
  simp only [node.injEq]

end Node

def val (t : BT α 0) : α := match t with | leaf a => a

section Val

@[simp] theorem val_leaf {a : α} : (leaf a).val = a := rfl

end Val

def left (t : BT α (n + 1)) : BT α n := match t with | node l _ => l

section Left

@[simp] theorem left_node {l r : BT α n} : (node l r).left = l := rfl

end Left

def right (t : BT α (n + 1)) : BT α n := match t with | node _ r => r

section Right

@[simp] theorem right_node {l r : BT α n} : (node l r).right = r := rfl

end Right

section LeftRight

@[simp] theorem node_left_right {t : BT α (n + 1)} : t.left.node t.right = t := by cases t ; rfl

end LeftRight

@[simps!]
def BTEquivPair : BT α (n + 1) ≃ BT α n × BT α n where
  toFun := fun p => (p.left, p.right)
  invFun := fun p => node p.1 p.2
  left_inv := fun p => by simp_rw [node_left_right]
  right_inv := fun p => by simp_rw [left_node, right_node]

section Ext

@[ext]
theorem ext_zero {a b : BT α 0} (hab : a.val = b.val) : a = b := by
  cases a ; cases b
  simp_rw [leaf.injEq]
  exact hab

@[ext]
theorem ext_succ {a b : BT α (n + 1)} (hab₁ : a.left = b.left) (hab₂ : a.right = b.right) :
    a = b := by
  cases a ; cases b
  simp_rw [node.injEq]
  exact ⟨hab₁, hab₂⟩

end Ext

protected def cast {n m : ℕ} (h : n = m) (t : BT α n) : BT α m := h ▸ t

section Cast

variable {a : α}

@[simp]
theorem cast_rfl {t : BT α n} : t.cast rfl = t := rfl

theorem cast_eq_cast {h : n = m} {t : BT α n} : t.cast h = h ▸ t := rfl

@[simp]
theorem cast_cast {t : BT α n} {h : n = m} {h' : m = n} : (t.cast h).cast h' = t := by
  cases h ; cases h' ; rfl

@[simps! apply symm_apply]
def castEquiv (h : n = m) : BT α n ≃ BT α m where
  toFun := BT.cast h
  invFun := BT.cast h.symm
  left_inv _ := cast_cast
  right_inv _ := cast_cast

@[simp] theorem coe_castEquiv {h : n = m} : ⇑(castEquiv (α := α) h) = BT.cast h := rfl
@[simp] theorem coe_castEquiv_symm {h : n = m} :
    ⇑(castEquiv (α := α) h).symm = BT.cast h.symm := rfl

end Cast

def toSubTree {n : ℕ} (t : BT α n) (i : ℕ) (hi : i ≤ n) (v : ℕ) (hv : v < 2^(n - i)) :
    BT α i :=
    match hi with
  | .refl  => _


def toSubTree {n : ℕ} (t : BT α n) (i : ℕ) (hi : i ≤ n) (v : ℕ) (hv : v < 2^i) : BT α (n - i) :=
    match i with
  | 0 => t
  | (j + 1) => match n, t with
    | _, leaf _ => (Nat.not_succ_le_zero _ hi).elim
    | m + 1, node l r =>
      (toSubTree (bif v.testBit j then r else l) j
      (Nat.le_of_succ_le_succ hi) (v % 2^j)
      (Nat.mod_lt _ (Nat.two_pow_pos _))).cast (Nat.succ_sub_succ _ _).symm


#eval toSubTree (node (node (leaf 1) (leaf 2)) (node (leaf 3) (leaf 4))) 1 (by decide) 1 (by decide)


instance getElem : GetElem (BT α n) ℕ α (fun _ i => i < 2^n) where
  getElem := n.recOn (fun a _ _ => a.val) (fun n get lr i hi =>
    if hi' : i < 2^n then
    get lr.left i hi' else
    get lr.right (i - 2^n) <|
    Nat.sub_lt_right_of_lt_add (le_of_not_lt hi')
    (hi.trans_eq (Nat.two_pow_succ _)))

def toList {n : ℕ} : BT α n → List α
  | leaf a => [a]
  | node l r => toList l ++ toList r

section ToList

variable {a : α} {s t l r : BT α n}

@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl
@[simp] theorem toList_node : (node l r).toList = l.toList ++ r.toList := rfl
theorem toList_zero {a : BT α 0} : a.toList = [a.val] := by cases a ; rfl
theorem toList_succ {a : BT α (n + 1)} :
    a.toList = a.left.toList ++ a.right.toList := by cases a ; rfl

@[simp]
theorem length_toList : (toList t).length = 2^n := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · rfl
  · simp_rw [toList_node, List.length_append, Nat.two_pow_succ, IHL, IHR]

@[simp] theorem toList_ne_nil : toList t ≠ [] :=
  List.ne_nil_of_length_pos (length_toList ▸ Nat.two_pow_pos _)

theorem eq_iff_toList_eq : s = t ↔ s.toList = t.toList := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [BT.ext_zero_iff, toList_zero, List.cons_eq_cons, and_true]
  · simp_rw [BT.ext_succ_iff, toList_succ, IH]
    refine ⟨fun h => h.1 ▸ h.2 ▸ rfl, fun H => ?_⟩
    exact List.append_inj H (length_toList.trans length_toList.symm)

@[simp]
theorem toList_cast {h : n = m} {t : BT α n} : (t.cast h).toList = t.toList := by
  cases h ; rfl

@[simp]
theorem toList_eq_rec {h : n = m} {t : BT α n} : (h ▸ t).toList = t.toList := by
  cases h ; rfl

theorem eq_level_of_toList_eq_toList {s : BT α n} {t : BT α m}
    (h : s.toList = t.toList) : n = m := by
  have hs := length_toList (t := s)
  have ht := length_toList (t := t)
  rw [h] at hs
  have hst := hs.symm.trans ht
  simp_rw [Nat.pow_right_inj (refl 2)] at hst
  exact hst

theorem cast_eq_iff {s : BT α n} {t : BT α m} (h : n = m) :
    s.cast h = t ↔ s.toList = t.toList:= by
  refine ⟨fun h => h ▸ ?_, fun hst => ?_⟩
  · simp_rw [toList_cast]
  · cases h
    simp_rw [cast_rfl, eq_iff_toList_eq, hst]

end ToList

def flatten {n : ℕ} : BT (BT α m) n → BT α (m + n)
  | leaf a => a
  | node l r => node l.flatten r.flatten

section Flatten

variable {t l r : BT (BT α n) m} {a : BT α n}

@[simp] theorem flatten_leaf : (leaf a).flatten = a := rfl

@[simp] theorem flatten_node : (node l r).flatten = node l.flatten r.flatten := rfl

end Flatten

abbrev BTL (α : Type*) (n : ℕ) := List (BT α n)

namespace BTL

def toList (s : BTL α n) : List α := s.flatMap BT.toList

section ToList

variable {a : BT α n} {s t : BTL α n}

@[simp] theorem toList_nil : toList (α := α) (n := n) [] = [] := rfl
@[simp] theorem toList_cons : toList (a :: s) = a.toList ++ toList s := rfl
theorem toList_singleton : toList [a] = a.toList := List.flatMap_singleton _ _
@[simp] theorem toList_append : toList (s ++ t) = toList s ++ toList t := List.flatMap_append
theorem toList_ne_nil_iff : toList s = [] ↔ s = [] := by
  unfold toList
  simp_rw [List.flatMap_eq_nil_iff, BT.toList_ne_nil,
    imp_false, List.eq_nil_iff_forall_not_mem]

theorem eq_iff_toList_eq : s = t ↔ s.toList = t.toList := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · simp_rw [toList_nil, List.nil_eq, toList_ne_nil_iff]
  · simp_rw [toList_cons]
    cases t with | nil => _ | cons b t => _
    · simp_rw [List.cons_ne_nil, toList_nil, List.append_eq_nil_iff, toList_ne_nil, false_and]
    · simp_rw [List.cons_eq_cons, BT.eq_iff_toList_eq, toList_cons, IH]
      refine ⟨fun h => h.1 ▸ h.2 ▸ rfl, fun H => ?_⟩
      exact List.append_inj H (length_toList.trans length_toList.symm)

theorem toList_map_leaf {s : List α} : BTL.toList (s.map leaf) = s := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [List.map_cons, BTL.toList_cons, toList_leaf, List.singleton_append, IH]

theorem toList_toList {t : BT (BT α n) m} : BTL.toList t.toList = t.flatten.toList := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [flatten_leaf, toList_leaf, BTL.toList_singleton]
  · simp_rw [flatten_node, toList_node, BTL.toList_append, IHL, IHR]

end ToList

@[simps!]
def castEquiv (h : n = m) := Equiv.listEquivOfEquiv (BT.castEquiv (α := α) h)

def modTwo (l : BTL α n) : Option (BT α n) :=
  l.doubleRec none some (fun _ _ _ => id)

section ModTwo

variable {a b l r : BT α n} {s t : BTL α n}

@[simp] theorem modTwo_nil : modTwo ([] : BTL α n) = none := rfl
@[simp] theorem modTwo_singleton : modTwo [a] = a := rfl
@[simp] theorem modTwo_cons₂ : modTwo (l :: r :: s) = modTwo s := rfl

theorem modTwo_append_singleton  :
    modTwo (s ++ [a]) = bif (modTwo s).isSome then none else some a := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b s IH => _
  · rfl
  · rfl
  · simp_rw [List.cons_append, modTwo_cons₂, IH]

theorem modTwo_eq_dite_odd : modTwo s = if hs : Odd s.length then
    some (s.getLast (List.ne_nil_of_length_pos hs.pos)) else none := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b s IH => _
  · rfl
  · rfl
  · simp_rw [modTwo_cons₂, IH, List.length_cons, Nat.odd_add_one, not_not,
      List.getLast_cons_cons]
    split_ifs with hs
    · simp_rw [Option.some_inj]
      exact (List.getLast_cons _).symm
    · rfl

theorem modTwo_eq_dite_even : modTwo s = if h : Even s.length then none else
    some (s.getLast (List.ne_nil_of_length_pos (Nat.not_even_iff_odd.mp h).pos)) := by
  simp_rw [modTwo_eq_dite_odd, ← Nat.not_odd_iff_even, dite_not]

theorem modTwo_eq_some_of_length_odd (hs : Odd s.length) : modTwo s =
    some (s.getLast (List.ne_nil_of_length_pos hs.pos)) := by
  rw [modTwo_eq_dite_odd, dif_pos hs]

theorem modTwo_eq_none_of_length_even (hs : Even s.length) : modTwo s = none := by
  simp_rw [modTwo_eq_dite_even, dif_pos hs]

theorem length_even_of_modTwo_eq_none (hs : modTwo s = none) : Even s.length := by
  simp_rw [modTwo_eq_dite_odd, dite_eq_right_iff, Option.some_ne_none,
    imp_false, Nat.not_odd_iff_even] at hs
  exact hs

theorem length_odd_of_modTwo_eq_some (hs : modTwo s = some a) : Odd s.length := by
  simp_rw [modTwo_eq_dite_odd, Option.dite_none_right_eq_some, Option.some_inj] at hs
  rcases hs with ⟨hs, _⟩
  exact hs

end ModTwo

def divTwo (l : BTL α n) : BTL α (n + 1) :=
  l.doubleRec [] (fun _ => []) (fun l r _ ds => l.node r :: ds)

section DivTwo

variable {a b l r : BT α n} {s : BTL α n} {lr : BT α (n + 1)}

@[simp] theorem divTwo_nil : divTwo ([] : BTL α n) = [] := rfl
@[simp] theorem divTwo_singleton : divTwo [a] = [] := rfl
@[simp] theorem divTwo_cons₂ : divTwo (l :: r :: s) = l.node r :: divTwo s := rfl
theorem divTwo_cons₂_left_right : divTwo (lr.left :: lr.right :: s) = lr :: divTwo s := by
  simp only [divTwo_cons₂, node_left_right]

theorem divTwo_append_singleton :
    divTwo (s ++ [b]) = divTwo s ++ (modTwo s).elim [] ([node · b]) := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [List.nil_append, divTwo_singleton, divTwo_nil, modTwo_nil,
      Option.elim_none, List.append_nil]
  · simp_rw [divTwo_singleton, modTwo_singleton, List.singleton_append, divTwo_cons₂,
      divTwo_nil, Option.elim_some, List.nil_append]
  · simp only [List.cons_append, divTwo_cons₂, IH, modTwo_cons₂]

theorem divTwo_append_singleton_of_modTwo_eq_some (hs : modTwo s = some a) :
    divTwo (s ++ [b]) = divTwo s ++ [node a b] := by
  simp_rw [divTwo_append_singleton, hs, Option.elim_some]

theorem divTwo_append_singleton_of_modTwo_eq_none (hs : modTwo s = none) :
    divTwo (s ++ [b]) = divTwo s := by
  simp_rw [divTwo_append_singleton, hs, Option.elim_none, List.append_nil]

@[simp]
theorem length_divTwo : (divTwo s).length = s.length / 2 := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [divTwo_nil, List.length_nil]
  · simp_rw [divTwo_singleton, List.length_cons, List.length_nil]
  · simp_rw [divTwo_cons₂, List.length_cons, IH, add_assoc,
        one_add_one_eq_two, Nat.add_div_right _ zero_lt_two]

theorem length_divTwo_le_length :
    (divTwo s).length ≤ s.length := by
  rw [length_divTwo]
  exact Nat.div_le_self _ _

theorem length_divTwo_lt_length_of_ne_nil (hs : s ≠ []) :
    (divTwo s).length < s.length := by
  rw [length_divTwo]
  exact Nat.div_lt_self (List.length_pos_of_ne_nil hs) one_lt_two

theorem bit_lt_length_of_lt_divTwo_length {i : ℕ} (b : Bool) (hi : i < (divTwo s).length) :
    i.bit b < s.length := by
  simp_rw [length_divTwo, Nat.lt_div_iff_mul_lt zero_lt_two,
    mul_comm i, Nat.lt_sub_iff_add_lt, ] at hi
  cases b
  · exact (Nat.lt_succ_self _).trans hi
  · exact hi

theorem two_mul_lt_length_of_lt_divTwo_length {i : ℕ} (hi : i < (divTwo s).length) :
    2 * i < s.length := bit_lt_length_of_lt_divTwo_length false hi

theorem two_mul_succ_lt_length_of_lt_divTwo_length {i : ℕ} (hi : i < (divTwo s).length) :
    2 * i + 1 < s.length := bit_lt_length_of_lt_divTwo_length true hi

theorem getElem_divTwo {i : ℕ} (hi : i < (divTwo s).length) :
  (divTwo s)[i] =
    node (s[2*i]'(two_mul_lt_length_of_lt_divTwo_length hi))
      (s[2*i + 1]'(two_mul_succ_lt_length_of_lt_divTwo_length hi)) := by
  induction s using List.doubleRec generalizing i with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · contradiction
  · contradiction
  · simp_rw [divTwo_cons₂, List.getElem_cons_succ]
    cases i
    · simp_rw [mul_zero, List.getElem_cons_zero]
    · simp_rw [mul_add, Nat.mul_succ, List.getElem_cons_succ, IH]

theorem take_divTwo : (divTwo s).take k = divTwo (s.take (2*k)) := by
  simp only [List.ext_getElem_iff, length_divTwo, List.length_take, Nat.inf_div,
    mul_div_cancel_left₀ _ (two_ne_zero), lt_inf_iff,  true_and, List.getElem_take,
    getElem_divTwo, implies_true]

theorem drop_divTwo : (divTwo s).drop k = divTwo (s.drop (2*k)) := by
  simp only [List.ext_getElem_iff, length_divTwo, List.length_drop, Nat.inf_div,
    mul_div_cancel_left₀ _ (two_ne_zero), lt_inf_iff,  true_and, List.getElem_drop,
    getElem_divTwo, implies_true, Nat.sub_mul_div', mul_add, add_assoc]

theorem toList_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    (divTwo s).toList = s.toList := by
  induction s using List.doubleRec with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · contradiction
  · simp_rw [divTwo_cons₂, BTL.toList_cons, toList_node, List.append_assoc,
      List.append_cancel_left_eq, IH hs]

end DivTwo

def divModTwo (l : BTL α n) : Option (BT α n) × BTL α (n + 1) :=
  l.doubleRec (none, []) (some · , []) (fun l r _ (mts, dts) => (mts, l.node r :: dts))

section DivModTwo

variable {a b l r : BT α n} {s : BTL α n}

@[simp] theorem divModTwo_nil : divModTwo ([] : BTL α n) = (none, []) := rfl
@[simp] theorem divModTwo_singleton : divModTwo [a] = (some a, []) := rfl
@[simp] theorem divModTwo_cons₂ : divModTwo (l :: r :: s) =
    ((divModTwo s).1, l.node r :: (divModTwo s).2) := rfl

@[simp] theorem divModTwo_eq_divTwo_modTwo : divModTwo s = (modTwo s, divTwo s) :=
    s.doubleRec rfl (fun _ => rfl) (fun _ _ _ h => by
      simp_rw [divModTwo_cons₂, h, modTwo_cons₂, divTwo_cons₂])

end DivModTwo

def mulTwo (s : BTL α (n + 1)) : BTL α n := s.flatMap fun lr => [lr.left, lr.right]

section MulTwo

variable {s t : BTL α (n + 1)} {a lr : BT α (n + 1)} {b l r : BT α n}

@[simp] theorem mulTwo_nil : mulTwo (α := α) (n := n) [] = [] := rfl
@[simp] theorem mulTwo_cons : mulTwo (a :: s) = a.left :: a.right :: mulTwo s := rfl
theorem mulTwo_singleton : mulTwo [a] = [a.left, a.right] := rfl
theorem mulTwo_append : mulTwo (s ++ t) = mulTwo s ++ mulTwo t := List.flatMap_append
@[simp] theorem mulTwo_append_singleton : mulTwo (s ++ [lr]) = mulTwo s ++ [lr.left, lr.right] :=
  List.flatMap_append

@[simp] theorem mulTwo_cons_node : mulTwo ((node l r) :: s) = l :: r :: mulTwo s := rfl

@[simp]
theorem length_mulTwo : (mulTwo s).length = 2 * s.length := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [mulTwo_cons, List.length_cons, IH, mul_add]

@[simp] theorem toList_mulTwo : s.mulTwo.toList = s.toList := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [mulTwo_cons, toList_cons, toList_succ, List.append_assoc, IH]

@[simp] theorem divTwo_mulTwo : s.mulTwo.divTwo = s := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [mulTwo_cons, divTwo_cons₂, node_left_right, IH]

@[simp] theorem modTwo_mulTwo : s.mulTwo.modTwo = none := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [mulTwo_cons, modTwo_cons₂, IH]

@[simp] theorem modTwo_mulTwo_append_singleton :
    (s.mulTwo ++ [b]).modTwo = b := by
  rw [modTwo_append_singleton, modTwo_mulTwo,
    Option.isSome_none, cond_false, Option.some_inj]

@[simp] theorem divTwo_mulTwo_append_singleton :
    (s.mulTwo ++ [b]).divTwo = s := by
  rw [divTwo_append_singleton, modTwo_mulTwo,
    Option.elim_none, divTwo_mulTwo, List.append_nil]

@[simp] theorem mulTwo_divTwo_of_modTwo_eq_none {s : BTL α n} (hs : modTwo s = none) :
    mulTwo (divTwo s) = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [divTwo_nil, mulTwo_nil]
  · contradiction
  · simp_rw [modTwo_cons₂] at hs
    simp_rw [divTwo_cons₂, mulTwo_cons, left_node, right_node, IH hs]

@[simp] theorem mulTwo_divTwo_append_singleton_of_modTwo_eq_some {s : BTL α n} {c : BT α n}
    (hs : modTwo s = some c) : mulTwo (divTwo s) ++ [c] = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    simp_rw [hs, divTwo_singleton, mulTwo_nil, List.nil_append]
  · simp_rw [modTwo_cons₂] at hs
    simp_rw [divTwo_cons₂, mulTwo_cons, left_node, right_node, List.cons_append, IH hs]

theorem modTwo_eq_none_iff {s : BTL α n} :
    s.modTwo = none ↔ ∃ ss, s = mulTwo ss :=
  ⟨fun hs => ⟨_, (mulTwo_divTwo_of_modTwo_eq_none hs).symm⟩,
  fun ⟨_, h⟩ => h ▸ modTwo_mulTwo⟩

theorem modTwo_eq_some_iff {s : BTL α n} {c : BT α n} :
    s.modTwo = some c ↔ ∃ ss, s = mulTwo ss ++ [c] :=
  ⟨fun hs => ⟨_, (mulTwo_divTwo_append_singleton_of_modTwo_eq_some hs).symm⟩,
  fun ⟨_, h⟩ => h ▸ modTwo_mulTwo_append_singleton⟩

end MulTwo

def bit (ao : Option (BT α n)) (s : BTL α (n + 1)) : BTL α n := s.mulTwo ++ ao.toList

section Bit

variable {ao : Option (BT α n)} {s : BTL α (n + 1)} {a : BT α n} {b : BT α (n + 1)}

@[simp] theorem bit_nil : bit ao ([] : BTL α (n + 1)) = ao.toList := rfl
@[simp] theorem bit_cons : bit ao (b :: s) = b.left :: b.right :: bit ao s := rfl

@[simp] theorem bit_none :
    bit none s = mulTwo s := by
  unfold bit
  simp only [Option.toList_none, List.append_nil]

@[simp] theorem bit_some :
    bit (some a) s = mulTwo s ++ [a] := by
  unfold bit
  simp only [Option.toList_some]

@[simp] theorem toList_bit :
    (bit ao s).toList = s.toList ++ BTL.toList (ao.toList) := by
  cases ao
  · simp only [bit_none, toList_mulTwo, Option.toList_none, toList_nil, List.append_nil]
  · simp only [bit_some, toList_append, toList_mulTwo, toList_cons, toList_nil,
      List.append_nil, Option.toList_some]

end Bit

section BitDivTwoModTwoMulTwo

variable {ao : Option (BT α n)} {a l r : BT α n} {s : BTL α n} {ss : BTL α (n + 1)}

@[simp]
theorem bit_modTwo_divTwo : bit (modTwo s) (divTwo s) = s := by
  cases hs : modTwo s
  · simp_rw [bit_none, mulTwo_divTwo_of_modTwo_eq_none hs]
  · simp_rw [bit_some, mulTwo_divTwo_append_singleton_of_modTwo_eq_some hs]

theorem bit_modTwo_node_cons_divTwo {l r : BT α n} :
    bit (modTwo s) (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [bit_cons, left_node, right_node, bit_modTwo_divTwo]

@[simp]
theorem divTwo_bit : divTwo (bit ao ss) = ss := by
  cases ao
  · simp_rw [bit_none, divTwo_mulTwo]
  · simp_rw [bit_some, divTwo_append_singleton_of_modTwo_eq_none modTwo_mulTwo,
      divTwo_mulTwo]

@[simp]
theorem modTwo_bit : modTwo (bit ao ss) = ao := by
  cases ao
  · simp_rw [bit_none, modTwo_mulTwo]
  · simp_rw [bit_some, modTwo_append_singleton,
      modTwo_mulTwo, Option.isSome_none, Bool.cond_false]

def bitDivModEquiv : Option (BT α n) × BTL α (n + 1) ≃ BTL α n where
  toFun as := bit as.1 as.2
  invFun s := ⟨(modTwo s), (divTwo s)⟩
  left_inv as := by simp_rw [modTwo_bit, divTwo_bit]
  right_inv s := by simp_rw [bit_modTwo_divTwo]

end BitDivTwoModTwoMulTwo

def listToBT : (n : ℕ) → (s : List α) → s.length = 2^n → BT α n
  | 0, s => fun h => leaf <| s[0]
  | (n + 1), s => fun h => node
      (listToBT n (s.take (2^n)) (s.length_take_of_length_eq_add (h ▸ Nat.two_pow_succ _)))
      (listToBT n (s.drop (2^n)) (s.length_drop_of_length_eq_add (h ▸ Nat.two_pow_succ _)))

section ListToBT

variable {a b : α} {s t : List α}

@[simp]
theorem toList_listToBT {hs : s.length = 2^n} : (listToBT n s hs).toList = s := by
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨a, rfl⟩
    simp_rw [listToBT, List.getElem_cons_zero, toList_leaf]
  · rw [Nat.two_pow_succ] at hs
    simp_rw [listToBT, toList_node, IH, List.take_append_drop]

@[simp]
theorem listToBT_singleton : listToBT 0 [a] rfl = leaf a := rfl

theorem listToBT_zero {hs : s.length = 2^0} : listToBT 0 s hs = leaf s[0] := rfl

@[simp]
theorem listToBT_doubleton : listToBT 1 [a, b] rfl = node (leaf a) (leaf b) := rfl

theorem listToBT_one {hs : s.length = 2^1} : listToBT 1 s hs =
  node (leaf <| s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)))
    (leaf <| s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_one, List.length_eq_two] at hs
  rcases hs with ⟨a, b, rfl⟩
  rfl

theorem listToBT_succ (hs : s.length = 2^(n + 1)) :
  listToBT (n + 1) s hs = node
    (listToBT n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (listToBT n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) := rfl

theorem listToBT_append (hs : s.length = 2^n) (ht : t.length = 2^n)
    (hst : (s ++ t).length = 2^(n + 1) := List.length_append.trans
      (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)) :
    listToBT (n + 1) (s ++ t) hst = node (listToBT n s hs) (listToBT n t ht) := by
  simp_rw [BT.eq_iff_toList_eq,  toList_node, toList_listToBT]

end ListToBT

def btlToBT (n : ℕ) (s : BTL α m) (hs : s.length = 2^n) : BT α (m + n) :=
  flatten (listToBT n s hs)

section BTLToBT

variable {n : ℕ} {s t : BTL α m} {hs : s.length = 2^n}

@[simp]
theorem toList_btlToBT :
    (btlToBT n s hs).toList = s.toList :=
  BTL.toList_toList.symm.trans (congrArg₂ _ rfl toList_listToBT)

theorem listToBT_toList_btlToBT :
    listToBT (m + n) (btlToBT n s hs).toList length_toList = btlToBT n s hs := by
  simp_rw [BT.eq_iff_toList_eq, toList_btlToBT, toList_listToBT]

@[simp]
theorem btlToBT_singleton {a : BT α n}: btlToBT 0 [a] rfl = a := rfl

theorem btlToBT_zero {hs : s.length = 2^0} : btlToBT 0 s hs = s[0] := rfl

@[simp]
theorem btlToBT_doubleton {a b : BT α n} :
    btlToBT 1 [a, b] rfl = node a b := rfl

theorem btlToBT_one {hs : s.length = 2^1} : btlToBT 1 s hs =
  node (s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)))
    (s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_one, List.length_eq_two] at hs
  rcases hs with ⟨a, b, rfl⟩
  rfl

theorem btlToBT_succ (hs : s.length = 2^(n + 1)) :
  btlToBT (n + 1) s hs = node
    (btlToBT n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (btlToBT n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) :=
  rfl

theorem btlToBT_append (hs : s.length = 2^n) (ht : t.length = 2^n)
    (hst : (s ++ t).length = 2^(n + 1) := List.length_append.trans
      (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)) :
    btlToBT (n + 1) (s ++ t) hst = (btlToBT n s hs).node (btlToBT n t ht) := by
  simp_rw [BT.eq_iff_toList_eq, toList_node, toList_btlToBT, BTL.toList_append]

theorem btlToBT_divTwo (hs : s.length = 2^(n + 1)) :
  btlToBT (n + 1) s hs = Nat.succ_add_eq_add_succ _ _ ▸
    btlToBT n (divTwo s) (length_divTwo ▸ hs ▸ by
    simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero]) := by
  have H : modTwo s = none :=
    modTwo_eq_none_of_length_even (hs ▸ by simp_rw [pow_succ', even_two_mul])
  simp_rw [BT.eq_iff_toList_eq, toList_eq_rec, toList_btlToBT,
    BTL.toList_divTwo_of_modTwo_eq_none H]

end BTLToBT

@[elab_as_elim, specialize]
def bitRec {motive : (n : ℕ) → BTL α n → Sort*} {n : ℕ} (s : BTL α n)
    (nil : ∀ {n}, motive n []) (singleton : ∀ {n} a, motive n [a])
    (cons₂ : ∀ {n} a l r s, motive (n + 1) (l.node r :: s) → motive n (l :: r :: bit a s)) :
    motive n s := match s with
  | [] => nil
  | [a] => singleton a
  | l :: r :: s =>
    bit_modTwo_divTwo (s := s) ▸
    cons₂ (modTwo s) l r (divTwo s)
    (bitRec (l.node r :: divTwo s) nil singleton cons₂)
  termination_by s.length
  decreasing_by exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

section BitRec

variable {motive : (n : ℕ) → BTL α n → Sort*}
    {nil : ∀ {n}, motive n []} {singleton : ∀ {n} a, motive n [a]}
    {cons₂ : ∀ {n} a l r s, motive (n + 1) (l.node r :: s) → motive n (l :: r :: bit a s)}
    {a l r : BT α n} {s : BTL α n}

@[simp] theorem bitRec_nil : bitRec (n := n) [] nil singleton cons₂ = nil := by
  rw [bitRec]
@[simp] theorem bitRec_singleton : bitRec (n := n) [a] nil singleton cons₂ = singleton a := by
  rw [bitRec]

@[simp] theorem bitRec_cons₂ : bitRec (motive := motive) (n := n) (l :: r :: s) nil singleton cons₂ =
    bit_modTwo_divTwo (s := s) ▸
    cons₂ (modTwo s) l r (divTwo s) (bitRec (motive := motive)
    (l.node r :: divTwo s) nil singleton cons₂) := by simp_rw [bitRec]

end BitRec

end BTL
end BT

abbrev SBT (α : Type*) := (n : ℕ) × BT α n

namespace SBT

open BT BTL

def height (a : SBT α) := a.1

section Height

variable {n : ℕ} {a : BT α n}

@[simp] theorem fst_eq_height {a : SBT α} : a.1 = a.height := rfl

@[simp] theorem height_mk : height ⟨n, a⟩ = n := rfl

end Height

def toBT (a : SBT α) : BT α a.height := a.2

section ToBT

variable {a : BT α n}

@[simp] theorem snd_eq_toBT {a : SBT α} : a.2 = a.toBT := rfl

@[simp] theorem toBT_mk : toBT ⟨n, a⟩ = a := rfl

end ToBT

def ofBT (a : BT α n) : SBT α := ⟨n, a⟩

section OfBT

variable {a b l r : BT α n}

@[simp] theorem mk_eq_ofBT : Sigma.mk n a = ofBT a := rfl
@[simp] theorem height_ofBT : (ofBT a).height = n := rfl
@[simp] theorem toBT_ofBT : (ofBT a).toBT = a := rfl
@[simp] theorem ofBT_toBT {t : SBT α} : ofBT (toBT t) = t := rfl
@[simp] theorem ofBT_inj : ofBT a = ofBT b ↔ a = b := by
  unfold ofBT
  simp_rw [Sigma.ext_iff, heq_eq_eq, true_and]

end OfBT

def ofBTCasesOn {motive : (t : SBT α) → Sort*} (t : SBT α)
    (ofBT : ∀ {n}, (t : BT α n) → motive (ofBT t)) :
    motive t := match t with | Sigma.mk _ t => ofBT t

section OfBTCasesOn

variable {motive : (t : SBT α) → Sort*} {t : SBT α}
    {ofBT : ∀ {n}, (t : BT α n) → motive (ofBT t)}

theorem ofBTCasesOn_ofBT : ofBTCasesOn t ofBT = ofBT (toBT t) := rfl

end OfBTCasesOn


def toList (a : SBT α) := a.toBT.toList

section ToList

variable {a b s t : SBT α}

@[simp] theorem toList_toBT : a.toBT.toList = a.toList := rfl
@[simp] theorem toList_ofBT {a : BT α m} : (ofBT a).toList = a.toList := rfl

@[simp] theorem toList_ne_nil : toList a ≠ [] :=
  List.ne_nil_of_length_pos (length_toList ▸ Nat.two_pow_pos _)

theorem eq_of_eq_toList (hab : a.toList = b.toList) : a = b := by
  cases a using ofBTCasesOn with | ofBT a => _
  cases b using ofBTCasesOn with | ofBT b => _
  simp_rw [toList_ofBT] at hab
  have heq := eq_level_of_toList_eq_toList hab
  cases (eq_level_of_toList_eq_toList hab)
  simp_rw [ofBT_inj, BT.eq_iff_toList_eq, hab]

theorem eq_iff_toList_eq {a b : SBT α} :
     a = b ↔ a.toList = b.toList := ⟨fun h => h ▸ rfl, eq_of_eq_toList⟩

end ToList

protected def copy {m : ℕ} (a : SBT α) (h : a.height = m) : SBT α := ofBT (a.toBT.cast h)

section Copy

variable {a : SBT α} {h : a.height = m}

@[simp] theorem toBT_copy : (a.copy h).toBT = a.toBT.cast h := rfl
@[simp] theorem ofBT_cast {h : n = m} {a : BT α n} :
    ofBT (a.cast h) = ofBT a := by
  simp_rw [SBT.eq_iff_toList_eq, toList_ofBT, toList_cast]

@[simp] theorem height_copy : (a.copy h).height = m := rfl
@[simp] theorem toList_copy (h : a.height = m) : (a.copy h).toList = a.toList := by
  unfold toList
  simp_rw [toBT_copy, toList_cast]

@[simp] theorem copy_eq : a.copy h = a := by
  simp_rw [SBT.eq_iff_toList_eq, toList_copy]

end Copy

def leaf (a : α) : SBT α := ofBT (BT.leaf a)

section Leaf

variable {a b : α}

@[simp] theorem ofBT_leaf {a : α} : ofBT (BT.leaf a) = leaf a := rfl
@[simp] theorem mk_leaf : ⟨0, BT.leaf a⟩ = leaf a := rfl

@[simp] theorem height_leaf : (leaf a).height = 0 := rfl
@[simp] theorem toBT_leaf : (leaf a).toBT = BT.leaf a := rfl
@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by
  simp_rw [eq_iff_toList_eq, toList_leaf, List.singleton_inj]

theorem ofBT_comp_leaf : ofBT ∘ BT.leaf = leaf (α := α) := rfl

end Leaf

def node (a : BT α n) (b : BT α n) : SBT α := ofBT (a.node b)

section Node

variable  {a b c d l r : BT α n}

@[simp] theorem ofBT_node : ofBT (BT.node l r) = node l r := rfl

@[simp] theorem height_node : (node a b).height = n + 1 := rfl
@[simp] theorem toBT_node : (node a b).toBT = a.node b := rfl
@[simp] theorem toList_node : (node a b).toList = a.toList ++ b.toList := rfl

theorem node_inj_iff : node a b = node c d ↔ a = c ∧ b = d := by
  unfold node
  simp_rw [ofBT_inj, BT.node_inj_iff]

theorem ofBT_comp_node : ofBT ∘ (BT.node (n := n) (α := α)).uncurry =
    Function.uncurry (fun l r => node l r) := funext <| fun _ => by
  simp_rw [eq_iff_toList_eq]
  unfold Function.uncurry
  simp only [Function.comp_apply, ofBT_node, toList_node, toList_ofBT,
    BT.toList_node, toList_node, toList_ofBT]

theorem node_left_right {a : BT α (n + 1)} : node a.left a.right = ofBT a := by
  unfold node
  simp_rw [BT.node_left_right]

end Node

def ofBTRecOn {motive : (t : SBT α) → Sort*} (t : SBT α)
    (leaf : ∀ a, motive (leaf a))
    (node : ∀ {n} (l r : BT α n), motive (ofBT l) → motive (ofBT r) →
      motive (node l r)) :
    motive t := match t with
    | ⟨0, (BT.leaf a)⟩ => leaf a
    | ⟨(_ + 1), (BT.node l r)⟩ =>
      node l r (ofBTRecOn (ofBT l) leaf node) (ofBTRecOn (ofBT r) leaf node)
    termination_by t.height

section OfBTRecOn

variable {motive : (t : SBT α) → Sort*} {t : SBT α}
    {leaf : ∀ a, motive (leaf a)}
    {node : ∀ {n} (l r : BT α n), motive (ofBT l) → motive (ofBT r) →
      motive (node l r)} {a : α} {l r : BT α n}

@[simp]
theorem ofBTRecOn_leaf : ofBTRecOn (SBT.leaf a) leaf node = leaf a := by
  unfold ofBTRecOn SBT.leaf
  simp_rw [← mk_eq_ofBT]

@[simp]
theorem ofBTRecOn_node : ofBTRecOn (SBT.node l r) leaf node =
    node l r (ofBTRecOn (ofBT l) leaf node) (ofBTRecOn (ofBT r) leaf node) := by
  conv_lhs => unfold ofBTRecOn
  unfold SBT.node
  simp_rw [← mk_eq_ofBT]

end OfBTRecOn

def ofBTLeafNodeCasesOn {motive : (t : SBT α) → Sort*} (t : SBT α)
    (leaf : ∀ a, motive (leaf a))
    (node : ∀ {n}, (l r : BT α n) → motive (node l r)) :
    motive t := t.ofBTRecOn leaf (fun _ _ _ _ => node _ _)

section OfBTLeafNodeCasesOn

variable {motive : (t : SBT α) → Sort*} {t : SBT α}
    {leaf : ∀ a, motive (leaf a)}
    {node : ∀ {n} (l r : BT α n), motive (node l r)} {a : α} {l r : BT α n}

@[simp]
theorem ofBTLeafNodeCasesOn_leaf : ofBTLeafNodeCasesOn (SBT.leaf a) leaf node = leaf a := by
  unfold ofBTLeafNodeCasesOn
  simp only [ofBTRecOn_leaf]

@[simp]
theorem ofBTLeafNodeCasesOn_node : ofBTLeafNodeCasesOn (SBT.node l r) leaf node = node l r := by
  unfold ofBTLeafNodeCasesOn
  simp only [ofBTRecOn_node]

end OfBTLeafNodeCasesOn

section LeafNode

theorem exists_leaf_or_node (t : SBT α) :
    (∃ (a : α), t = leaf a) ∨
    (∃ (n : ℕ) (l r : BT α n), t = node l r) := by
  cases t using ofBTLeafNodeCasesOn with | leaf a => _ | node l r => _
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, _, _, rfl⟩

end LeafNode

abbrev SBTL (α : Type*) := List (SBT α)

namespace SBTL

def toList (s : SBTL α) : List α := s.reverse.flatMap SBT.toList

section ToList

variable {a : SBT α} {s t : SBTL α}

@[simp] theorem toList_nil : toList (α := α) [] = [] := rfl
@[simp] theorem toList_cons : toList (a :: s) = s.toList ++ a.toList := by
  unfold toList
  simp_rw [List.reverse_cons, List.flatMap_append, List.flatMap_singleton]

theorem toList_singleton : toList [a] = a.toList := by
  unfold toList
  simp_rw [List.reverse_singleton, List.flatMap_singleton]
@[simp] theorem toList_append : toList (s ++ t) = toList t ++ toList s := by
  unfold toList
  simp_rw [List.reverse_append, List.flatMap_append]

theorem toList_ne_nil_iff : toList s= [] ↔ s = [] := by
  unfold toList
  simp_rw [List.flatMap_eq_nil_iff, SBT.toList_ne_nil,
    imp_false, List.eq_nil_iff_forall_not_mem, List.mem_reverse]

theorem toList_map_leaf {s : List α} : BTL.toList (s.map BT.leaf) = s := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [List.map_cons, BTL.toList_cons, BT.toList_leaf, List.singleton_append, IH]

end ToList

def btlToStack {n : ℕ} (s : BTL α n) : SBTL α :=
  s.bitRec [] ([ofBT ·]) (fun a _ _ _ => a.elim (·) (ofBT · :: ·))

section BTLToStack

variable {ao : Option (BT α n)} {a b l r : BT α n} {s : BTL α n}

@[simp]
theorem btlToStack_nil : btlToStack ([] : BTL α n) = [] := by
  rw [btlToStack, BTL.bitRec]

@[simp]
theorem btlToStack_singleton : btlToStack [a] = [ofBT a] := by
  rw [btlToStack, BTL.bitRec]

theorem btlToStack_cons₂ :
    btlToStack (l :: r :: s) =
    ((modTwo s).elim (·) (ofBT · :: ·) (btlToStack (l.node r :: divTwo s))) := by
  rw [btlToStack, bitRec_cons₂, eq_rec_constant]
  cases modTwo s <;> rfl


@[simp]
theorem btlToStack_cons₂_mulTwo {s : BTL α (n + 1)}:
    btlToStack (l :: r :: s.mulTwo) = btlToStack (l.node r :: s) := by
  simp_rw [btlToStack_cons₂, modTwo_mulTwo, Option.elim_none, divTwo_mulTwo]

@[simp]
theorem btlToStack_cons₂_mulTwo_append_singleton {s : BTL α (n + 1)}:
    btlToStack (l :: r :: (s.mulTwo ++ [a])) = ofBT a :: btlToStack (l.node r :: s) := by
  simp_rw [btlToStack_cons₂, modTwo_mulTwo_append_singleton, Option.elim_some,
    divTwo_mulTwo_append_singleton]

theorem btlToStack_cons₂_of_modTwo_none (hs : modTwo s = none) :
    btlToStack (l :: r :: s) = btlToStack (l.node r :: divTwo s) := by
  simp_rw [btlToStack_cons₂, hs, Option.elim_none]

@[simp]
theorem btlToStack_double : btlToStack [a, b] = [node a b] := by
  rw [btlToStack_cons₂_of_modTwo_none rfl, divTwo_nil, btlToStack_singleton, ofBT_node]

theorem btlToStack_cons₂_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack (l :: r :: s) = ofBT a :: btlToStack (l.node r :: divTwo s) := by
  simp_rw [btlToStack_cons₂, hs, Option.elim_some]

@[simp]
theorem btlToStack_mulTwo {s : BTL α (n + 1)} :
    btlToStack s.mulTwo = btlToStack s := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [mulTwo_nil, btlToStack_nil]
  · simp_rw [mulTwo_cons, btlToStack_cons₂_mulTwo, BT.node_left_right]

@[simp]
theorem btlToStack_mulTwo_append_singleton {s : BTL α (n + 1)} :
    btlToStack (mulTwo s ++ [a]) = ofBT a :: btlToStack s := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [mulTwo_nil, List.nil_append, btlToStack_singleton, btlToStack_nil]
  · simp_rw [mulTwo_cons, List.cons_append,
      btlToStack_cons₂_mulTwo_append_singleton, BT.node_left_right]

@[simp]
theorem btlToStack_mulTwo_append_double {s : BTL α (n + 1)} :
    btlToStack (s.mulTwo ++ [a, b]) = btlToStack (s ++ [a.node b]) := by
  have H : s.mulTwo ++ [a, b] = (s ++ [a.node b]).mulTwo := by
    simp_rw [mulTwo_append_singleton, left_node, right_node]
  rw [H, btlToStack_mulTwo]

@[simp]
theorem btlToStack_eq_nil_iff : btlToStack s = [] ↔ s = [] := by
  induction s using bitRec with | nil => _ | singleton a => _ | cons₂ a l r s IH => _
  · simp_rw [btlToStack_nil]
  · simp_rw [btlToStack_singleton, List.cons_ne_nil]
  · cases a
    · simp_rw [bit_none, btlToStack_cons₂_mulTwo, IH, List.cons_ne_nil]
    · simp_rw [bit_some, btlToStack_cons₂_mulTwo_append_singleton, List.cons_ne_nil]

@[simp]
theorem btlToStack_ne_nil_iff : btlToStack s ≠ [] ↔ s ≠ [] := btlToStack_eq_nil_iff.not

@[simp]
theorem btlToStack_cons_ne_nil : btlToStack (b :: s) ≠ [] := by
  simp_rw [btlToStack_ne_nil_iff]
  exact List.cons_ne_nil _ _

theorem le_height_head_btlToStack_cons {n : ℕ} {b : BT α n} {s : BTL α n} : n ≤
    ((btlToStack (b :: s)).head btlToStack_cons_ne_nil).height := match s with
  | [] => by simp_rw [btlToStack_singleton, List.head_cons, height_ofBT, le_refl]
  | (a :: s) => match hs : modTwo s with
    | none => by
      simp_rw [btlToStack_cons₂_of_modTwo_none hs]
      exact (Nat.le_succ _).trans le_height_head_btlToStack_cons
    | some a => by
      simp_rw [btlToStack_cons₂_of_modTwo_some hs, List.head_cons, height_ofBT, le_refl]
  termination_by s.length

theorem height_head_btlToStack_succ_ne {n : ℕ} {b : BT α (n + 1)} {s : BTL α (n + 1)} :
    ((btlToStack (b :: s)).head btlToStack_cons_ne_nil).height ≠ n :=
  (Nat.lt_of_succ_le (le_height_head_btlToStack_cons)).ne'

@[simp]
theorem btlToStack_bit {s : BTL α (n + 1)} :
    btlToStack (bit ao s) = ao.toList.map ofBT ++ btlToStack s := by
  cases ao
  · simp_rw [bit_none, btlToStack_mulTwo, Option.toList_none, List.map_nil, List.nil_append]
  · simp only [bit_some, btlToStack_mulTwo_append_singleton, Option.toList_some, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append]

theorem btlToStack_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack s = ofBT a :: btlToStack (divTwo s) := by
  simp_rw [modTwo_eq_some_iff] at hs
  rcases hs with ⟨_, rfl⟩
  simp_rw [btlToStack_mulTwo_append_singleton, divTwo_mulTwo_append_singleton]

theorem btlToStack_of_modTwo_none (hs : modTwo s = none) :
    btlToStack s = btlToStack (divTwo s) := by
  simp_rw [modTwo_eq_none_iff] at hs
  rcases hs with ⟨_, rfl⟩
  simp_rw [btlToStack_mulTwo, divTwo_mulTwo]

theorem btlToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    btlToStack (s ++ [a]) = ofBT a :: btlToStack s  := by
  simp_rw [modTwo_eq_none_iff] at hs
  rcases hs with ⟨_, rfl⟩
  simp_rw [btlToStack_mulTwo, btlToStack_mulTwo_append_singleton]

theorem btlToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack (s ++ [b]) = btlToStack (divTwo s ++ [a.node b]) := by
  simp_rw [modTwo_eq_some_iff] at hs
  rcases hs with ⟨_, rfl⟩
  simp_rw [divTwo_mulTwo_append_singleton, List.append_assoc,
    List.singleton_append, btlToStack_mulTwo_append_double]

theorem btlToStack_eq  :
    btlToStack s = (modTwo s).toList.map ofBT ++ btlToStack (divTwo s) := by
  rw [← bit_modTwo_divTwo (s := s), btlToStack_bit, bit_modTwo_divTwo]

theorem btlToStack_two_pow {s : BTL α m} (hs : s.length = 2^n) :
    btlToStack s = [ofBT <| btlToBT n s hs] := by
  induction n generalizing m with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨_, rfl⟩
    simp_rw [btlToStack_singleton, btlToBT_singleton]
  · have hs' : modTwo s = none :=
      modTwo_eq_none_of_length_even (hs ▸ by simp_rw [pow_succ', even_two_mul])
    have IH' := IH (s := divTwo s) (length_divTwo ▸ hs ▸ by
        simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero])
    simp_rw [btlToStack_of_modTwo_none hs', IH',
      btlToBT_divTwo, List.cons_eq_cons, eq_iff_toList_eq,
      toList_ofBT, toList_eq_rec, true_and]

theorem btlToStack_append {s t : BTL α m} (hs : s.length = 2^n)
    (ht : t.length = 2^n) :
    btlToStack (s ++ t) =
    [ofBT <| (btlToBT n s hs).node (btlToBT n t ht)] := by
  have hst : (s ++ t).length = 2^(n + 1) :=
    List.length_append.trans (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)
  simp_rw [btlToStack_two_pow hst, btlToBT_append hs ht]

theorem toList_btlToStack {s : BTL α m} :
    (btlToStack s).toList = s.toList := by
  induction s using bitRec with | nil => _ | singleton a => _ | cons₂ a l r s IH => _
  · simp_rw [btlToStack_nil, SBTL.toList_nil, BTL.toList_nil]
  · simp only [btlToStack_singleton, toList_cons, toList_nil, toList_ofBT, List.nil_append,
      BTL.toList_cons, BTL.toList_nil, List.append_nil]
  · simp only [BTL.toList_cons, BT.toList_node, List.append_assoc] at IH ⊢
    rcases a with _ | a
    · simp_rw [bit_none, btlToStack_cons₂_mulTwo, IH, BTL.toList_mulTwo]
    · simp_rw [bit_some, btlToStack_cons₂_mulTwo_append_singleton,
        toList_cons, IH, toList_ofBT, List.append_assoc,
        BTL.toList_append, toList_mulTwo, BTL.toList_cons,
        BTL.toList_nil, List.append_nil]

end BTLToStack

def listToStack (s : List α) : SBTL α := btlToStack (s.map BT.leaf)

section ListToStack

variable {a b l r : α} {s : List α}

@[simp]
theorem listToStack_nil : listToStack ([] : List α) = [] := by
  rw [listToStack, List.map_nil, btlToStack_nil]

@[simp]
theorem listToStack_singleton : listToStack [a] = [leaf a] := by
  rw [listToStack, List.map_singleton, btlToStack_singleton, ofBT_leaf]

theorem listToStack_cons₂ :
    listToStack (l :: r :: s) = (modTwo (s.map BT.leaf)).elim (·) (fun a s => ofBT a :: s)
    (btlToStack ((((BT.leaf l).node (BT.leaf r))) :: divTwo (s.map BT.leaf))) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons₂]

@[simp]
theorem listToStack_cons₂_of_modTwo_none (hs : modTwo (s.map BT.leaf) = none) :
    listToStack (l :: r :: s) =
    btlToStack ((BT.leaf l).node (BT.leaf r) :: divTwo (s.map BT.leaf)) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons₂_of_modTwo_none hs]

@[simp]
theorem listToStack_cons₂_of_modTwo_some
    (hs : modTwo (s.map BT.leaf) = some (BT.leaf a)) :
    listToStack (l :: r :: s) =
    leaf a :: btlToStack ((BT.leaf l).node (BT.leaf r) :: divTwo (s.map BT.leaf)) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons₂_of_modTwo_some hs, ofBT_leaf]

theorem listToStack_of_modTwo_some (hs : modTwo (s.map BT.leaf) = some (BT.leaf a)) :
    listToStack s = leaf a :: btlToStack (divTwo (s.map BT.leaf)) := by
  rw [listToStack, btlToStack_of_modTwo_some hs, ofBT_leaf]

theorem listToStack_of_modTwo_none (hs : modTwo (s.map BT.leaf) = none) :
    listToStack s = btlToStack (divTwo (s.map BT.leaf)) := by
  rw [listToStack, btlToStack_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_none (hs : modTwo (s.map BT.leaf) = none) :
    listToStack (s ++ [a]) = leaf a :: btlToStack (s.map BT.leaf) := by
  simp_rw [listToStack, List.map_append, List.map_singleton,
    btlToStack_append_singleton_of_modTwo_none hs, ofBT_leaf]

theorem listToStack_append_singleton_of_modTwo_some
    (hs : modTwo (s.map BT.leaf) = some (BT.leaf a)) : listToStack (s ++ [b]) =
    btlToStack (divTwo (s.map BT.leaf) ++ [(BT.leaf a).node (BT.leaf b)]) := by
  simp_rw [listToStack, List.map_append, List.map_singleton,
    btlToStack_append_singleton_of_modTwo_some hs]

theorem listToStack_two_pow {s : List α} (hs : s.length = 2^n) :
    listToStack s = [ofBT <| listToBT n s hs] := by
  simp_rw [listToStack, btlToStack_two_pow ((List.length_map _).trans hs),
    List.singleton_inj, eq_iff_toList_eq, toList_ofBT, toList_btlToBT,
    toList_listToBT, BTL.toList_map_leaf]

theorem listToStack_append (s t : List α) (hs : s.length = 2^n) (ht : t.length = 2^n) :
    listToStack (s ++ t) = [ofBT <| (listToBT n s hs).node (listToBT n t ht)] := by
  have hst : (s ++ t).length = 2^(n + 1) :=
    List.length_append.trans (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)
  simp_rw [listToStack_two_pow hst, listToBT_append hs ht]

theorem toList_listToStack : (listToStack s).toList = s := by
  unfold listToStack
  simp_rw [toList_btlToStack, BTL.toList_map_leaf]

end ListToStack

abbrev sortedFrom (s : SBTL α) (m : ℕ) : Prop :=
  s.Sorted (height · < height ·) ∧ ∀ x ∈ s, m ≤ x.height

section SortedFrom

variable {a c : SBT α} {s : SBTL α}

theorem sortedFrom_nil : sortedFrom (α := α) [] m := ⟨List.sorted_nil, List.forall_mem_nil _⟩

theorem sortedFrom_singleton_of_le_height (ha : m ≤ a.height) : sortedFrom [a] m :=
  ⟨List.sorted_singleton _, List.forall_mem_singleton.mpr ha⟩

end SortedFrom

def push {m : ℕ} (s : SBTL α) (b : BT α m) : SBTL α := match s with
  | [] => ([ofBT b])
  | (a :: s) =>
    if hab : a.height = m then push s ((a.toBT.cast hab).node b)
    else ofBT b :: a :: s

section Push

variable {a c : SBT α} {s : SBTL α} {b c : BT α m}

@[simp] theorem push_nil : push [] b = [ofBT b] := rfl
theorem push_cons : push (a :: s) b =
    if hab : a.height = m then push s ((a.toBT.cast hab).node b) else ofBT b :: a :: s := rfl
@[simp] theorem push_singleton : push [a] b =
    if hab : a.height = m then [node (a.toBT.cast hab) b] else [ofBT b, a] := rfl
@[simp] theorem push_singleton_of_ne (hab : a.height ≠ m) :
    push [a] b = [ofBT b, a] := dif_neg hab
@[simp] theorem push_singleton_of_eq (hab : a.height = m) :
    push [a] b = [node (a.toBT.cast hab) b] := dif_pos hab
@[simp] theorem push_singleton_ofBT :
    push [ofBT c] b = [ofBT <| c.node b] := dif_pos rfl

@[simp] theorem push_cons_of_ne (hab : a.height ≠ m) :
    push (a :: s) b = ofBT b :: a :: s := dif_neg hab
@[simp] theorem push_cons_of_eq (hab : a.height = m) :
    push (a :: s) b = push s ((a.toBT.cast hab).node b) := dif_pos hab
@[simp] theorem push_cons_ofBT :
    push (ofBT c :: s) b = push s (c.node b) := dif_pos rfl

@[simp] theorem push_ne_nil : push s b ≠ [] := by
  induction s generalizing m with | nil => _ | cons a s IH => _
  · exact List.cons_ne_nil _ _
  · rw [push_cons]
    split_ifs
    · exact IH
    · exact List.cons_ne_nil _ _

theorem le_height_head_push : m ≤ ((push s b).head push_ne_nil).height := by
  induction s generalizing m with | nil => _ | cons a s IH => _
  · exact le_rfl
  · simp_rw [push_cons]
    split_ifs
    · exact (Nat.le_succ _).trans IH
    · exact le_rfl

theorem lt_push_height_head_of_lt :
    ∀ {n}, n < m → n < ((push s b).head push_ne_nil).height :=
  fun h => h.trans_le le_height_head_push

theorem height_head_push_succ_ne {b : BT α (m + 1)} :
    ((push s b).head push_ne_nil).height ≠ m :=
  (lt_push_height_head_of_lt (Nat.lt_succ_self _)).ne'

theorem push_of_head_ne (hs : ∀ {hs : s ≠ []}, (s.head hs).height ≠ m) :
    push s b = ofBT b :: s := by
  cases s
  · exact push_nil
  · specialize hs (hs := List.cons_ne_nil _ _)
    simp_rw [List.head_cons] at hs
    simp_rw [push_cons_of_ne hs]

theorem push_push_of_height_lt {b : BT α m} {c : BT α n} (h : n < m) :
    (push s b).push c = ofBT c :: push s b :=
  push_of_head_ne (lt_push_height_head_of_lt h).ne'

@[simp]
theorem toList_push : (push s b).toList = s.toList ++ b.toList := by
  induction s generalizing m with
  | nil => _ | cons a s IH => _
  · simp_rw [push_nil, toList_singleton, toList_nil, List.nil_append, toList_ofBT]
  · simp_rw [push_cons,  apply_dite, IH, BT.toList_node, toList_cast, toList_toBT,
      toList_cons, toList_ofBT, List.append_assoc, dite_eq_ite, ite_self]

theorem push_left_push_right {b : BT α (m + 1)} (hs : ∀ {hs : s ≠ []}, (s.head hs).height ≠ m) :
    (s.push b.left).push b.right = s.push b := by
  simp_rw [push_of_head_ne hs, push_cons_ofBT, BT.node_left_right]

theorem push_push_left_push_right {a : BT α (m + 1)} {b : BT α (m + 1)} :
    ((s.push a).push b.left).push b.right = (s.push a).push b :=
  push_left_push_right height_head_push_succ_ne

end Push

def pushStack (s : BTL α m) (t : SBTL α) := s.foldl push t

section PushStack

variable {a b : BT α m} {s s' : BTL α m} {t : SBTL α} {as : SBT α}

@[simp] theorem pushStack_nil : t.pushStack (m := m) [] = t := rfl
@[simp] theorem pushStack_cons : t.pushStack (a :: s) = (push t a).pushStack s := rfl
@[simp] theorem pushStack_singleton : t.pushStack [a] = push t a := rfl
@[simp] theorem pushStack_append :
    t.pushStack (s ++ s') = (t.pushStack s).pushStack s' := List.foldl_append
theorem pushStack_append_singleton :
    t.pushStack (s ++ [a]) = push (t.pushStack s) a := by
  simp_rw [pushStack_append, pushStack_singleton]

theorem pushStack_eq_nil_iff : t.pushStack s = [] ↔ t = [] ∧ s = [] := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · simp_rw [pushStack_nil, and_true]
  · simp_rw [pushStack_cons, IH, push_ne_nil, List.cons_ne_nil, false_and, and_false]

theorem pushStack_ne_nil_iff : t.pushStack s ≠ [] ↔ t ≠ [] ∨ s ≠ [] := by
  simp_rw [ne_eq, pushStack_eq_nil_iff, not_and_or]

theorem pushStack_ne_nil_of_stack_ne_nil (ht : t ≠ []) :
    t.pushStack s ≠ [] := pushStack_ne_nil_iff.mpr (Or.inl ht)

theorem pushStack_ne_nil_of_pushList_ne_nil (hs : s ≠ []) :
    t.pushStack s ≠ [] := pushStack_ne_nil_iff.mpr (Or.inr hs)

theorem le_height_head_pushStack (h : t ≠ []) (ht : m ≤ (t.head h).height)
  (hts := pushStack_ne_nil_of_stack_ne_nil h) :
    m ≤ ((t.pushStack s).head hts).height := by
  cases t
  · contradiction
  · cases s using List.reverseRecOn
    · exact ht
    · simp_rw [pushStack_append_singleton]
      exact le_height_head_push

theorem height_head_pushStack_succ_ne {s : BTL α (m + 1)} (h : t ≠ [])
    (ht : m < (t.head h).height)
  (hts := pushStack_ne_nil_of_stack_ne_nil h) :
    ((t.pushStack s).head hts).height ≠ m :=
  (Nat.lt_of_succ_le (le_height_head_pushStack (s := s) h ht)).ne'

@[simp] theorem toList_pushStack :
    (t.pushStack s).toList = t.toList ++ s.toList := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · simp_rw [pushStack_nil, BTL.toList_nil, List.append_nil]
  · simp_rw [pushStack_cons, IH, toList_push, List.append_assoc, BTL.toList_cons]

theorem pushStack_mulTwo {s : BTL α (m + 1)} (ht : ∀ {ht : t ≠ []}, (t.head ht).height ≠ m) :
    t.pushStack (mulTwo s) = t.pushStack s := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [mulTwo_cons, pushStack_cons, push_left_push_right ht, IH height_head_push_succ_ne]

theorem pushStack_mulTwo_append_singleton {s : BTL α (m + 1)}
    (ht : ∀ {ht : t ≠ []}, (t.head ht).height ≠ m) :
    t.pushStack (mulTwo s ++ [a]) = (t.pushStack s).push a := by
  simp_rw [pushStack_append_singleton, pushStack_mulTwo ht]

theorem pushStack_mulTwo_singleton {a : SBT α} (ha : a.height ≠ m) {s : BTL α (m + 1)} :
    pushStack (mulTwo s) [a] = pushStack s [a] := by
  rw [pushStack_mulTwo]
  exact ha

theorem pushStack_mulTwo_singleton_succ {a : BT α (m + 1)}
    {s : BTL α (m + 1)} : pushStack (mulTwo s) [ofBT a] = pushStack s [ofBT a] :=
  pushStack_mulTwo_singleton (height_ofBT.trans_ne (Nat.succ_ne_self _))

theorem pushStack_mulTwo_singleton_node {a b : BT α m}
    {s : BTL α (m + 1)} : pushStack (mulTwo s) [node a b] = pushStack s [node a b] :=
  pushStack_mulTwo_singleton (height_ofBT.trans_ne (Nat.succ_ne_self _))

end PushStack

def btlPushToStack (s : BTL α m) : SBTL α := pushStack s []

section BTLPushToStack

variable {a b : BT α m} {s s' : BTL α m}

@[simp] theorem btlPushToStack_nil : btlPushToStack ([] : BTL α m) = [] := rfl
@[simp] theorem btlPushToStack_cons : btlPushToStack (a :: s) = pushStack s [ofBT a] := rfl

@[simp] theorem btlPushToStack_cons₂ : btlPushToStack (a :: b :: s) =
    pushStack s [node a b] := by
  simp_rw [btlPushToStack_cons, pushStack_cons, push_singleton_ofBT, ofBT_node]

@[simp] theorem btlPushToStack_singleton : btlPushToStack [a] = [ofBT a] := by
  rw [btlPushToStack_cons, pushStack_nil]

@[simp] theorem btlPushToStack_double : btlPushToStack [a, b] = [node a b] := by
  rw [btlPushToStack_cons₂, pushStack_nil]

@[simp] theorem btlPushToStack_cons_leaf {a : α} {s : BTL α 0}:
     btlPushToStack (BT.leaf a :: s) = pushStack s [leaf a] := rfl

@[simp] theorem btlPushToStack_cons_node {s : BTL α (m + 1)}:
     btlPushToStack (a.node b :: s) = pushStack s [node a b] := rfl

@[simp] theorem btlPushToStack_mulTwo {s : BTL α (m + 1)}:
    btlPushToStack (mulTwo s) = btlPushToStack s := pushStack_mulTwo (fun {ht} => (ht rfl).elim)

@[simp]
theorem btlPushToStack_append_singleton : btlPushToStack (s ++ [a]) = push (btlPushToStack s) a :=
  pushStack_append_singleton

theorem succ_le_height_head_btlPushToStack {s : BTL α (m + 1)} {hs : btlPushToStack s.mulTwo ≠ []} :
    m + 1 ≤ (List.head (btlPushToStack s.mulTwo) hs).height := by
  cases s with | nil => _ | cons a s => _
  · simp_rw [mulTwo_nil, btlPushToStack_nil, ne_eq, not_true] at hs
  · simp_rw [mulTwo_cons, btlPushToStack_cons₂, pushStack_mulTwo_singleton_node]
    exact le_height_head_pushStack (List.cons_ne_nil _ _) (le_refl (m + 1))

theorem height_head_btlPushToStack_ne {s : BTL α (m + 1)} {hs : btlPushToStack s.mulTwo ≠ []} :
    (List.head (btlPushToStack s.mulTwo) hs).height ≠ m :=
  ((Nat.lt_succ_self _).trans_le succ_le_height_head_btlPushToStack).ne'

theorem btlPushToStack_mulTwo_append_singleton {s : BTL α (m + 1)} :
    btlPushToStack (mulTwo s ++ [a]) = ofBT a :: btlPushToStack s := by
  simp_rw [btlPushToStack_append_singleton,
    push_of_head_ne height_head_btlPushToStack_ne, btlPushToStack_mulTwo]

@[simp] theorem btlPushToStack_append : btlPushToStack (s ++ s') = (btlPushToStack s).pushStack s' :=by
  unfold btlPushToStack
  simp_rw [pushStack_append]

theorem btlPushToStack_apply_eq_btlToStack_apply {m : ℕ} {s : BTL α m} :
    btlPushToStack s = btlToStack s := by
  rcases eq_or_ne s [] with rfl | hs'
  · simp_rw [btlPushToStack_nil, btlToStack_nil]
  · rcases hs : modTwo s
    · rw [← mulTwo_divTwo_of_modTwo_eq_none hs]
      simp_rw [btlPushToStack_mulTwo, btlToStack_mulTwo]
      exact btlPushToStack_apply_eq_btlToStack_apply
    · rw [← mulTwo_divTwo_append_singleton_of_modTwo_eq_some hs]
      simp_rw [btlPushToStack_mulTwo_append_singleton, btlToStack_mulTwo_append_singleton]
      simp_rw [List.cons_inj_right]
      exact btlPushToStack_apply_eq_btlToStack_apply
termination_by s.length
decreasing_by all_goals exact length_divTwo_lt_length_of_ne_nil hs'

theorem btlPushToStack_eq_btlToStack :
    btlPushToStack (α := α) (m := m) = btlToStack :=
  funext <| fun _ => btlPushToStack_apply_eq_btlToStack_apply

end BTLPushToStack

def listPushToStack (s : List α) : SBTL α := btlPushToStack (s.map BT.leaf)

section ListPushToStack

theorem listToStack_eq_listPushToStack : listPushToStack (α := α) = listToStack :=
    funext <| fun s => by
  unfold listToStack listPushToStack
  simp_rw [btlPushToStack_eq_btlToStack]

theorem listPushToStack_two_pow {s : List α} (hs : s.length = 2^n) :
    listPushToStack s = [ofBT <| listToBT n s hs] := by
  simp_rw [listToStack_eq_listPushToStack, listToStack_two_pow hs]

end ListPushToStack

def listPushToBT (n : ℕ) (s : List α) (hs : s.length = 2^n) : BT α n :=
  ((listPushToStack s).head (listPushToStack_two_pow hs ▸ List.cons_ne_nil _ _)).toBT.cast
  (by simp_rw [listPushToStack_two_pow hs, List.head_singleton, height_ofBT])

section ListPushToBT

theorem listPushToBT_eq_listToBT : listPushToBT (α := α) = listToBT :=
    funext <| fun n => funext <| fun s => funext <| fun hs => by
  unfold listPushToBT
  simp_rw [cast_eq_iff, toList_toBT, listPushToStack_two_pow hs, List.head_cons, toList_ofBT]

theorem listPushToBT_zero {s : List α} {hs : s.length = 2^0} : listPushToBT 0 s hs =
    BT.leaf s[0] := by
  simp_rw [listPushToBT_eq_listToBT, listToBT_zero]

theorem listPushToBT_succ {s : List α} {hs : s.length = 2^(n + 1)} :
    listPushToBT (n + 1) s hs = BT.node
    (listPushToBT n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (listPushToBT n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) := by
  simp_rw [listPushToBT_eq_listToBT, listToBT_succ]

end ListPushToBT

end SBTL

end SBT
