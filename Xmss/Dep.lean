import Mathlib

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

universe u

variable {α : Type u}

theorem ext_getElem_iff (s t : List α) : s = t ↔
    s.length = t.length ∧ (∀ i (hi₁ : i < s.length) (hi₁ : i < t.length), s[i] = t[i]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · exact List.ext_getElem h.1 h.2

@[elab_as_elim]
def doubleRec {α : Type*} {motive : List α → Sort u} (l : List α)  (nil : motive [])
    (singleton : ∀ a, motive [a])
    (cons_cons : ∀ a b l, motive l → motive (a :: b :: l)) : motive l :=
  match l with
  | [] => nil
  | [a] => singleton a
  | _ :: _ :: l => cons_cons _ _ _ (doubleRec l nil singleton cons_cons)

section DoubleRec

variable {motive : List α → Sort u} {nil : motive []} {singleton : ∀ a, motive [a]}
  {cons_cons : ∀ a b l, motive l → motive (a :: b :: l)}

@[simp]
theorem doubleRec_nil : doubleRec ([] : List α) nil singleton cons_cons = nil := rfl
@[simp]
theorem doubleRec_singleton {a : α} : doubleRec [a] nil singleton cons_cons = singleton a := rfl
@[simp]
theorem doubleRec_cons_cons {a b : α} {l : List α} :
    doubleRec (a :: b :: l) nil singleton cons_cons =
    cons_cons a b l (doubleRec l nil singleton cons_cons) := rfl

end DoubleRec

theorem length_take_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.take n).length = n := length_take_of_le (hl ▸ Nat.le_add_right _ _)

theorem length_drop_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.drop n).length = m := length_drop ▸ (hl ▸ add_tsub_cancel_left _ _)

end List

inductive BTree (α : Type u) : ℕ → Type u where
  | leaf : (a : α) → BTree α 0
  | node : (l : BTree α n) → (r : BTree α n) → BTree α (n + 1)
deriving Repr, DecidableEq

namespace BTree


variable {n m : ℕ}

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by simp only [leaf.injEq]

theorem node_inj_iff {a b c d : BTree α n}: a.node b  = c.node d ↔ a = c ∧ b = d := by
  simp only [node.injEq]

def val (t : BTree α 0) : α := match t with | leaf a => a

@[simp] theorem val_leaf {a : α} : (leaf a).val = a := rfl

def left (t : BTree α (n + 1)) : BTree α n := match t with | node l _ => l

def right (t : BTree α (n + 1)) : BTree α n := match t with | node _ r => r

@[simp] theorem left_node {l r : BTree α n} : (node l r).left = l := rfl
@[simp] theorem right_node {l r : BTree α n} : (node l r).right = r := rfl
@[simp] theorem node_left_right {t : BTree α (n + 1)} : t.left.node t.right = t := by cases t ; rfl

def BTreeEquivPair : BTree α (n + 1) ≃ BTree α n × BTree α n where
  toFun := fun p => (p.left, p.right)
  invFun := fun p => node p.1 p.2
  left_inv := fun p => by simp_rw [node_left_right]
  right_inv := fun p => by simp_rw [left_node, right_node]

@[ext]
theorem ext_zero {a b : BTree α 0} (hab : a.val = b.val) : a = b := by
  cases a ; cases b
  simp_rw [leaf.injEq]
  exact hab

@[ext]
theorem ext_succ {a b : BTree α (n + 1)} (hab₁ : a.left = b.left) (hab₂ : a.right = b.right) :
    a = b := by
  cases a ; cases b
  simp_rw [node.injEq]
  exact ⟨hab₁, hab₂⟩

protected def cast {n m : ℕ} (h : n = m) : BTree α n → BTree α m
  | leaf a => match m with | 0 => leaf a
  | node l r => match m with
  | _ + 1 => node (l.cast (Nat.add_right_cancel h)) (r.cast (Nat.add_right_cancel h))

section Cast

@[simp]
theorem cast_rfl {t : BTree α n} : t.cast rfl = t := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · rfl
  · simp_rw [BTree.ext_succ_iff]
    exact ⟨IHL, IHR⟩

theorem cast_eq_cast {h : n = m} {t : BTree α n} : t.cast h = h ▸ t := by
  cases h ; rw [cast_rfl]

@[simp]
theorem cast_cast {t : BTree α n} {h : n = m} {h' : m = n} : (t.cast h).cast h' = t := by
  cases h ; cases h' ; simp_rw [cast_rfl]

def castEquiv (h : n = m) : BTree α n ≃ BTree α m where
  toFun := BTree.cast h
  invFun := BTree.cast h.symm
  left_inv _ := cast_cast
  right_inv _ := cast_cast

end Cast

def toList {n : ℕ} : BTree α n → List α
  | leaf a => [a]
  | node l r => toList l ++ toList r

section ToList

variable {s t : BTree α n}

@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl
@[simp] theorem toList_node : (node l r).toList = l.toList ++ r.toList := rfl
theorem toList_zero {a : BTree α 0} : a.toList = [a.val] := by cases a ; rfl
theorem toList_succ {a : BTree α (n + 1)} :
    a.toList = a.left.toList ++ a.right.toList := by cases a ; rfl

theorem length_toList : (toList t).length = 2^n := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · rfl
  · simp_rw [toList_node, List.length_append, Nat.two_pow_succ, IHL, IHR]

@[simp] theorem toList_ne_nil : toList t ≠ [] :=
  List.ne_nil_of_length_pos (length_toList ▸ Nat.two_pow_pos _)

theorem toList_ext_iff : s = t ↔ s.toList = t.toList := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [BTree.ext_zero_iff, toList_zero, List.cons_eq_cons, and_true]
  · simp_rw [BTree.ext_succ_iff, toList_succ, IH]
    refine ⟨fun h => h.1 ▸ h.2 ▸ rfl, ?_⟩
    simp_rw [List.ext_getElem_iff, List.length_append, List.getElem_append,
      length_toList, true_and]
    refine fun H => ⟨fun i hi _ => ?_, fun i hi _  => ?_⟩
    · specialize H i
      simp_rw [Nat.lt_add_left _ hi, hi, dite_true, forall_true_left] at H
      exact H
    · specialize H (i + 2^n)
      simp_rw [Nat.add_lt_add_right hi, (Nat.le_add_left _ _).not_lt,
        dite_false, forall_true_left, add_tsub_cancel_right] at H
      exact H

@[simp]
theorem toList_cast {h : n = m} {t : BTree α n} : (t.cast h).toList = t.toList := by
  cases h ; rw [cast_rfl]

@[simp]
theorem toList_eq_rec {h : n = m} {t : BTree α n} : (h ▸ t).toList = t.toList := by
  cases h ; rfl

theorem eq_level_of_toList_eq_toList {s : BTree α n} {t : BTree α m}
    (h : s.toList = t.toList) : n = m := by
  have hs := length_toList (t := s)
  have ht := length_toList (t := t)
  rw [h] at hs
  have hst := hs.symm.trans ht
  simp_rw [Nat.pow_right_inj (refl 2)] at hst
  exact hst

theorem toList_eq_toList_iff {s : BTree α n} {t : BTree α m} :
    s.toList = t.toList ↔ ∃ (h : n = m), s.cast h = t := by
  refine ⟨fun h => ⟨eq_level_of_toList_eq_toList h, ?_⟩, fun ⟨h, hst⟩ => hst ▸ ?_⟩
  · simp_rw [toList_ext_iff, toList_cast, h]
  · simp_rw [toList_cast]

theorem flatMap_map_leaf {s : List α} : (s.map leaf).flatMap toList = s := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [List.map_cons, List.flatMap_cons, toList_leaf, List.singleton_append, IH]

end ToList

def flatten {n : ℕ} : BTree (BTree α m) n → BTree α (m + n)
  | leaf a => a
  | node l r => node l.flatten r.flatten

section Flatten

variable {t l r : BTree (BTree α n) m} {a : BTree α n}

@[simp] theorem flatten_leaf : (leaf a).flatten = a := rfl

@[simp] theorem flatten_node : (node l r).flatten = node l.flatten r.flatten := rfl

theorem toList_flatten : t.flatten.toList = t.toList.flatMap toList := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [flatten_leaf, toList_leaf, List.flatMap_singleton]
  · simp_rw [flatten_node, toList_node, List.flatMap_append, IHL, IHR]

end Flatten


def modTwo (l : List (BTree α n)) : Option (BTree α n) :=
  l.doubleRec none some (fun _ _ _ => id)

section ModTwo

@[simp] theorem modTwo_nil : modTwo ([] : List (BTree α n)) = none := rfl
@[simp] theorem modTwo_singleton : modTwo [a] = a := rfl
@[simp] theorem modTwo_cons_cons : modTwo (l :: r :: s) = modTwo s := rfl

theorem modTwo_eq_dite_odd : modTwo s = if hs : Odd s.length then
    some (s.getLast (List.ne_nil_of_length_pos hs.pos)) else none := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b s IH => _
  · rfl
  · rfl
  · simp_rw [modTwo_cons_cons, IH, List.length_cons, Nat.odd_add_one, not_not,
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

theorem ne_nil_of_modTwo_eq_some (hs : modTwo s = some a) : s ≠ [] :=
    List.ne_nil_of_length_pos (length_odd_of_modTwo_eq_some hs).pos

theorem getLast_eq_of_modTwo_eq_some (hs : modTwo s = some a) :
    s.getLast (ne_nil_of_modTwo_eq_some hs) = a := by
  simp_rw [modTwo_eq_dite_odd, Option.dite_none_right_eq_some, Option.some_inj] at hs
  rcases hs with ⟨_, hs⟩
  exact hs

theorem exists_append_singleton_eq_of_modTwo_eq_some (hs : modTwo s = some a) :
    ∃ s', s = s' ++ [a] := by
  have hs' := getLast_eq_of_modTwo_eq_some hs
  simp_rw [List.getLast_eq_iff_getLast?_eq_some (ne_nil_of_modTwo_eq_some hs),
    List.getLast?_eq_some_iff] at hs'
  exact hs'

theorem modTwo_append_singleton_eq_ite_even :
    modTwo (s ++ [a]) = if Even (List.length s) then some a else none := by
  rw [modTwo_eq_dite_odd]
  simp_rw [List.length_append, List.length_singleton, Nat.odd_add_one, Nat.not_odd_iff_even,
    List.getLast_append_singleton, dite_eq_ite]

theorem modTwo_append_singleton_eq_ite_odd :
    modTwo (s ++ [a]) = if Odd (List.length s) then none else some a := by
  simp_rw [modTwo_append_singleton_eq_ite_even, ← Nat.not_odd_iff_even, ite_not]

theorem modTwo_append_singleton_of_length_odd (hs : Odd s.length) :
    modTwo (s ++ [a]) = none := by
  simp_rw [modTwo_append_singleton_eq_ite_odd, if_pos hs]

theorem modTwo_append_singleton_of_length_even (hs : Even s.length) :
    modTwo (s ++ [a]) = some a := by
  simp_rw [modTwo_append_singleton_eq_ite_even, if_pos hs]

theorem modTwo_append_singleton_of_modTwo_eq_some (hs : modTwo s = some b) :
    modTwo (s ++ [a]) = none :=
  modTwo_append_singleton_of_length_odd (length_odd_of_modTwo_eq_some hs)

theorem modTwo_append_singleton_of_modTwo_eq_none (hs : modTwo s = none) :
    modTwo (s ++ [a]) = some a :=
  modTwo_append_singleton_of_length_even (length_even_of_modTwo_eq_none hs)

theorem modTwo_eq_none_iff : modTwo s = none ↔ Even s.length :=
    ⟨length_even_of_modTwo_eq_none, modTwo_eq_none_of_length_even⟩

theorem modTwo_eq_some_iff : modTwo s = some a ↔
    (∃ h : Odd s.length, s.getLast (List.ne_nil_of_length_pos h.pos) = a) :=
  ⟨fun hs => ⟨length_odd_of_modTwo_eq_some hs, getLast_eq_of_modTwo_eq_some hs⟩,
  fun ⟨hs, hs'⟩ => hs' ▸ (modTwo_eq_some_of_length_odd hs)⟩

theorem modTwo_eq_some_iff_length_odd_and_exists_append_singleton :
    modTwo s = some a ↔ Odd s.length ∧ ∃ s', s = s' ++ [a] :=
  ⟨fun hs => ⟨length_odd_of_modTwo_eq_some hs, exists_append_singleton_eq_of_modTwo_eq_some hs⟩,
  fun ⟨hs, ⟨s', hs'⟩⟩ => hs' ▸ (modTwo_eq_some_of_length_odd hs).trans
    (by simp_rw [hs', List.getLast_append_singleton])⟩

theorem modTwo_eq_some_iff_exists_modTwo_eq_none_and_append_singleton :
    modTwo s = some a ↔ ∃ s', modTwo s' = none ∧ s = s' ++ [a] := by
  simp_rw [modTwo_eq_some_iff_length_odd_and_exists_append_singleton, modTwo_eq_none_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨hs, ⟨s', hs'⟩⟩
    use s'
    subst hs'
    simp_rw [List.length_append, List.length_singleton, Nat.odd_add_one,
      Nat.not_odd_iff_even] at hs
    exact ⟨hs, rfl⟩
  · intro ⟨s', hs, hs'⟩
    subst hs'
    simp_rw [List.length_append, List.length_singleton, Nat.odd_add_one,
      Nat.not_odd_iff_even]
    exact ⟨hs, ⟨s', rfl⟩⟩

end ModTwo

def divTwo (l : List (BTree α n)) : List (BTree α (n + 1)) :=
  l.doubleRec [] (fun _ => []) (fun l r _ ds => l.node r :: ds)

section DivTwo

variable {s :  List (BTree α n)}

@[simp] theorem divTwo_nil : divTwo ([] : List (BTree α n)) = [] := rfl
@[simp] theorem divTwo_singleton : divTwo [a] = [] := rfl
@[simp] theorem divTwo_cons_cons : divTwo (l :: r :: s) = l.node r :: divTwo s := rfl

@[simp]
theorem length_divTwo : (divTwo s).length = s.length / 2 := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [divTwo_nil, List.length_nil]
  · simp_rw [divTwo_singleton, List.length_cons, List.length_nil]
  · simp_rw [divTwo_cons_cons, List.length_cons, IH, add_assoc,
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
  · simp_rw [divTwo_cons_cons, List.getElem_cons_succ]
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

theorem flatMap_toList_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    (divTwo s).flatMap toList = s.flatMap toList := by
  induction s using List.doubleRec with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · contradiction
  · simp_rw [divTwo_cons_cons, List.flatMap_cons, toList_node, List.append_assoc,
      List.append_cancel_left_eq, IH hs]


end DivTwo

def divModTwo (l : List (BTree α n)) : Option (BTree α n) × List (BTree α (n + 1)) :=
  l.doubleRec (none, []) (some · , []) (fun l r _ (mts, dts) => (mts, l.node r :: dts))

@[simp] theorem divModTwo_nil : divModTwo ([] : List (BTree α n)) = (none, []) := rfl
@[simp] theorem divModTwo_singleton : divModTwo [a] = (some a, []) := rfl
@[simp] theorem divModTwo_cons_cons : divModTwo (l :: r :: s) =
    ((divModTwo s).1, l.node r :: (divModTwo s).2) := rfl

section DivModTwo

variable {s :  List (BTree α n)}

@[simp] theorem divModTwo_eq_divTwo_modTwo : divModTwo s = (modTwo s, divTwo s) :=
    s.doubleRec rfl (fun _ => rfl) (fun _ _ _ h => by
      simp_rw [divModTwo_cons_cons, h, modTwo_cons_cons, divTwo_cons_cons])

theorem divTwo_append_singleton :
    divTwo (s ++ [b]) = divTwo s ++ (modTwo s).toList.map (node · b) := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [List.nil_append, divTwo_singleton, divTwo_nil, modTwo_nil, Option.toList_none,
      List.map_nil, List.append_nil]
  · simp_rw [divTwo_singleton, modTwo_singleton, List.singleton_append, divTwo_cons_cons,
      divTwo_nil, Option.toList_some, List.map_singleton, List.nil_append]
  · simp only [List.cons_append, divTwo_cons_cons, IH, modTwo_cons_cons]

theorem divTwo_append_singleton_of_modTwo_eq_some (hs : modTwo s = some a) :
    divTwo (s ++ [b]) = divTwo s ++ [node a b] := by
  simp_rw [divTwo_append_singleton, hs, Option.toList_some, List.map_singleton]

theorem divTwo_append_singleton_of_modTwo_eq_none (hs : modTwo s = none) :
    divTwo (s ++ [b]) = divTwo s := by
  simp_rw [divTwo_append_singleton, hs, Option.toList_none, List.map_nil, List.append_nil]

theorem divTwo_append_singleton_of_length_even (hs : Even s.length) :
    divTwo (s ++ [b]) = divTwo s := by
  simp_rw [divTwo_append_singleton_of_modTwo_eq_none (modTwo_eq_none_of_length_even hs)]

theorem divTwo_append_singleton_of_length_odd (hs : Odd s.length) :
    divTwo (s ++ [b]) = divTwo s ++ [node (s.getLast (List.ne_nil_of_length_pos hs.pos)) b] := by
  simp_rw [divTwo_append_singleton_of_modTwo_eq_some (modTwo_eq_some_of_length_odd hs)]


end DivModTwo

def mulTwo (s : List (BTree α (n + 1))) : List (BTree α n) :=
  s.flatMap (fun p => [p.left, p.right])

section MulTwo

@[simp] theorem mulTwo_nil : mulTwo ([] : List (BTree α (n + 1))) = [] := rfl
@[simp] theorem mulTwo_cons : mulTwo (lr :: ss) = lr.left :: lr.right :: mulTwo ss := rfl

end MulTwo

def bit :  Option (BTree α n) → List (BTree α (n + 1)) → List (BTree α n)
  | ao, [] => ao.toList
  | ao, (lr :: ss) => lr.left :: lr.right :: bit ao ss

section Bit

variable {ao : Option (BTree α n)}

@[simp] theorem bit_nil : bit ao ([] : List (BTree α (n + 1))) = ao.toList := rfl
@[simp] theorem bit_none_nil : bit none ([] : List (BTree α (n + 1))) = [] := rfl
@[simp] theorem bit_some_nil : bit (some a) ([] : List (BTree α (n + 1))) = [a] := rfl
@[simp] theorem bit_cons : bit ao (lr :: ss) = lr.left :: lr.right :: bit ao ss := rfl

end Bit

section BitDivTwoModTwoMulTwo

variable {ao : Option (BTree α n)} {ss : List (BTree α (n + 1))}

@[simp]
theorem bit_modTwo_divTwo : bit (modTwo s) (divTwo s) = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [modTwo_nil, divTwo_nil, bit_none_nil]
  · simp_rw [modTwo_singleton, divTwo_singleton, bit_some_nil]
  · simp_rw [modTwo_cons_cons, divTwo_cons_cons, bit_cons, left_node, right_node, IH]

@[simp]
theorem bit_none_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    bit none (divTwo s) = s := by simp_rw [hs.symm, bit_modTwo_divTwo]

@[simp]
theorem bit_some_divTwo_of_modTwo_eq_some (hs : modTwo s = some a) :
    bit (some a) (divTwo s) = s := by simp_rw [hs.symm, bit_modTwo_divTwo]

theorem bit_modTwo_node_cons_divTwo {l r : BTree α n} :
    bit (modTwo s) (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [bit_cons, left_node, right_node, bit_modTwo_divTwo]

theorem bit_none_node_cons_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    bit none (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [hs.symm, bit_modTwo_node_cons_divTwo]

theorem bit_some_node_cons_divTwo_of_modTwo_eq_some (hs : modTwo s = some a) :
    bit (some a) (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [hs.symm, bit_modTwo_node_cons_divTwo]

@[simp]
theorem divTwo_bit : divTwo (bit ao ss) = ss := by
  induction ss with | nil => _ | cons a ss IH => _
  · cases ao
    · simp_rw [bit_none_nil, divTwo_nil]
    · simp_rw [bit_some_nil, divTwo_singleton]
  · simp_rw [bit_cons, divTwo_cons_cons, node_left_right, IH]

@[simp]
theorem modTwo_bit : modTwo (bit ao ss) = ao := by
  induction ss with | nil => _ | cons a ss IH => _
  · cases ao
    · simp_rw [bit_none_nil, modTwo_nil]
    · simp_rw [bit_some_nil, modTwo_singleton]
  · simp_rw [bit_cons, modTwo_cons_cons, IH]

def bitDivModEquiv : Option (BTree α n) × List (BTree α (n + 1)) ≃ List (BTree α n) where
  toFun as := bit as.1 as.2
  invFun s := ⟨(modTwo s), (divTwo s)⟩
  left_inv as := by simp_rw [modTwo_bit, divTwo_bit]
  right_inv s := by simp_rw [bit_modTwo_divTwo]

end BitDivTwoModTwoMulTwo

def listToTree : (n : ℕ) → (s : List α) → s.length = 2^n → BTree α n
  | 0, s => fun h => leaf <| s.getLast (List.ne_nil_of_length_pos (h ▸ Nat.two_pow_pos _))
  | (n + 1), s => fun h => node
      (listToTree n (s.take (2^n)) (s.length_take_of_length_eq_add (h ▸ Nat.two_pow_succ _)))
      (listToTree n (s.drop (2^n)) (s.length_drop_of_length_eq_add (h ▸ Nat.two_pow_succ _)))

section ListToTree

variable {s t : List α}

@[simp]
theorem toList_listToTree {hs : s.length = 2^n} : (listToTree n s hs).toList = s := by
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨a, rfl⟩
    simp_rw [listToTree, List.getLast_singleton, toList_zero, List.singleton_inj, val_leaf]
  · rw [Nat.two_pow_succ] at hs
    simp_rw [listToTree, toList_node, IH, List.take_append_drop]

@[simp]
theorem listToTree_singleton : listToTree 0 [a] rfl = leaf a := rfl

theorem listToTree_zero {hs : s.length = 2^0} : listToTree 0 s hs =
  leaf (s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := rfl

theorem listToTree_zero_eq_head {hs : s.length = 2^0} : listToTree 0 s hs =
    leaf (s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_zero, List.length_eq_one_iff] at hs
  rcases hs with ⟨a, rfl⟩
  rfl

@[simp]
theorem listToTree_doubleton : listToTree 1 [a, b] rfl = node (leaf a) (leaf b) := rfl

theorem listToTree_one {hs : s.length = 2^1} : listToTree 1 s hs =
  node (leaf <| s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)))
    (leaf <| s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_one, List.length_eq_two] at hs
  rcases hs with ⟨a, b, rfl⟩
  rfl

theorem listToTree_succ (hs : s.length = 2^(n + 1)) :
  listToTree (n + 1) s hs = node
    (listToTree n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (listToTree n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) := rfl

theorem listToTree_append (hs : s.length = 2^n) (ht : t.length = 2^n)
    (hst : (s ++ t).length = 2^(n + 1) := List.length_append.trans
      (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)) :
    listToTree (n + 1) (s ++ t) hst = node (listToTree n s hs) (listToTree n t ht) := by
  simp_rw [toList_ext_iff,  toList_node, toList_listToTree]

end ListToTree

def treeListToTree (n : ℕ) (s : List (BTree α m)) (hs : s.length = 2^n) : BTree α (m + n) :=
  flatten (listToTree n s hs)

section TreeListToTree

variable {s : List (BTree α m)}

@[simp]
theorem toList_treeListToTree :
    (treeListToTree n s hs).toList = s.flatMap toList :=
  toList_flatten.trans (congrArg₂ _ rfl toList_listToTree)

@[simp]
theorem treeListToTree_singleton { a : BTree α n}: treeListToTree 0 [a] rfl = a := rfl

theorem treeListToTree_zero {hs : s.length = 2^0} : treeListToTree 0 s hs =
  s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := rfl

theorem treeListToTree_zero_eq_head {hs : s.length = 2^0} : treeListToTree 0 s hs =
    s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := by
  simp_rw [pow_zero, List.length_eq_one_iff] at hs
  rcases hs with ⟨a, rfl⟩
  rfl

@[simp]
theorem treeListToTree_doubleton {a b : BTree α n} :
    treeListToTree 1 [a, b] rfl = node a b := rfl

theorem treeListToTree_one {hs : s.length = 2^1} : treeListToTree 1 s hs =
  node (s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)))
    (s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_one, List.length_eq_two] at hs
  rcases hs with ⟨a, b, rfl⟩
  rfl

theorem treeListToTree_succ (hs : s.length = 2^(n + 1)) :
  treeListToTree (n + 1) s hs = node
    (treeListToTree n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (treeListToTree n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) :=
  rfl

theorem treeListToTree_append (hs : s.length = 2^n) (ht : t.length = 2^n)
    (hst : (s ++ t).length = 2^(n + 1) := List.length_append.trans
      (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)) :
    treeListToTree (n + 1) (s ++ t) hst = (treeListToTree n s hs).node (treeListToTree n t ht) := by
  simp_rw [toList_ext_iff, toList_node, toList_treeListToTree, List.flatMap_append]

theorem treeListToTree_divTwo (hs : s.length = 2^(n + 1)) :
  treeListToTree (n + 1) s hs = Nat.succ_add_eq_add_succ _ _ ▸
    treeListToTree n (divTwo s) (length_divTwo ▸ hs ▸ by
    simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero]) := by
  have H : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, Nat.pow_succ', even_two_mul]
  simp_rw [toList_ext_iff, toList_eq_rec, toList_treeListToTree,
    flatMap_toList_divTwo_of_modTwo_eq_none H]

end TreeListToTree

@[elab_as_elim, specialize]
def bitRec {motive : (n : ℕ) → List (BTree α n) → Sort u} {n : ℕ} (s : List (BTree α n))
    (nil : ∀ {n}, motive n []) (singleton : ∀ {n} a, motive n [a])
    (bith : ∀ {n} a l r s, motive (n + 1) (l.node r :: s) → motive n (l :: r :: bit a s)) :
    motive n s := match s with
  | [] => nil
  | [a] => singleton a
  | l :: r :: s =>
    bit_modTwo_divTwo (s := s) ▸
    bith (modTwo s) l r (divTwo s)
    (bitRec (l.node r :: divTwo s) nil singleton bith)
  termination_by s.length
  decreasing_by exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

section BitRec

variable {motive : (n : ℕ) → List (BTree α n) → Sort u}
    {nil : ∀ {n}, motive n []} {singleton : ∀ {n} a, motive n [a]}
    {bith : ∀ {n} a l r s, motive (n + 1) (l.node r :: s) → motive n (l :: r :: bit a s)}
    {l r : BTree α n}

@[simp] theorem bitRec_nil : bitRec (n := n) [] nil singleton bith = nil := by
  rw [bitRec]
@[simp] theorem bitRec_singleton : bitRec (n := n) [a] nil singleton bith = singleton a := by
  rw [bitRec]

@[simp] theorem bitRec_bith : bitRec (motive := motive) (n := n) (l :: r :: s) nil singleton bith =
    bit_modTwo_divTwo (s := s) ▸
    bith (modTwo s) l r (divTwo s) (bitRec (motive := motive)
    (l.node r :: divTwo s) nil singleton bith) := by simp_rw [bitRec]

end BitRec

end BTree

abbrev SBTree (α : Type u) := (n : ℕ) × BTree α n

namespace SBTree

open BTree

def height (a : SBTree α) := a.1

section Height

variable {n : ℕ} {a : BTree α n}

@[simp] theorem fst_eq_height {a : SBTree α} : a.1 = a.height := rfl

@[simp] theorem height_mk : height ⟨n, a⟩ = n := rfl

end Height

variable {n : ℕ} {a : BTree α n}

def toBTree (a : SBTree α) := a.2

section ToBTree

@[simp] theorem snd_eq_toBTree {a : SBTree α} : a.2 = a.toBTree := rfl

@[simp] theorem toBTree_mk : toBTree ⟨n, a⟩ = a := rfl

end ToBTree

def toList (a : SBTree α) := a.toBTree.toList

section ToList

@[simp] theorem toList_mk : toList ⟨n, a⟩ = a.toList := rfl

end ToList

theorem eq_of_eq_of_toList_eq : ∀ {a b : SBTree α},
    a.height = b.height → a.toList = b.toList → a = b
  | ⟨n, a⟩, ⟨m, b⟩, hab, heq => by
    simp_rw [height_mk] at hab
    simp_rw [toList_mk, toList_eq_toList_iff, hab, exists_true_left] at heq
    subst hab heq
    simp_rw [cast_rfl]

theorem eq_iff_eq_and_isList_eq {a b : SBTree α} :
     a = b ↔ a.height = b.height ∧ a.toList = b.toList :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => eq_of_eq_of_toList_eq h.1 h.2⟩

def leaf (a : α) : SBTree α := ⟨0, BTree.leaf a⟩

section Leaf

variable {a b : α}

@[simp] theorem mk_leaf : ⟨0, BTree.leaf a⟩ = leaf a := rfl

@[simp] theorem leaf_height : (leaf a).height = 0 := rfl
@[simp] theorem leaf_toBTree : (leaf a).toBTree = BTree.leaf a := rfl
@[simp] theorem leaf_toList : (leaf a).toList = [a] := rfl

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by
  simp_rw [eq_iff_eq_and_isList_eq, leaf_height, leaf_toList, List.singleton_inj, true_and]

end Leaf

def node (a b : SBTree α) (hab : a.height = b.height) : SBTree α :=
  ⟨b.height + 1, (a.toBTree.cast hab).node b.toBTree⟩

section Node
variable {a b c d: SBTree α} (hab : a.height = b.height) (hcd : c.height = d.height)

@[simp] theorem node_mk {a : BTree α n} {b : BTree α m} (hab : n = m) :
  node ⟨n, a⟩ ⟨m, b⟩ hab = ⟨m + 1, (a.cast hab).node b⟩ := rfl

@[simp] theorem node_height : (a.node b hab).height = b.height + 1 := rfl
theorem node_height' : (a.node b hab).height = a.height + 1 := hab ▸ rfl
@[simp] theorem node_toBTree : (a.node b hab).toBTree = (a.toBTree.cast hab).node b.toBTree := rfl
@[simp] theorem node_toList : (a.node b hab).toList = a.toList ++ b.toList :=
  congrArg₂ _ toList_cast rfl

theorem node_inj_iff : a.node b hab = c.node d hcd ↔ a = c ∧ b = d := by
  cases a ; cases b ; cases c ; cases d
  simp only [height_mk] at hab hcd ; subst hab hcd
  simp_rw [eq_iff_eq_and_isList_eq, node_height, Nat.add_left_inj, node_toList, height_mk,
    ← and_and_left, and_congr_right_iff, toList_mk]
  intro hbd ; subst hbd
  simp_rw [← toList_node, ← toList_ext_iff, BTree.node_inj_iff]

end Node

section LeafNode

theorem forall_exists_leaf_or_node (t : SBTree α) :
    (∃ (a : α), t = leaf a) ∨
    (∃ (l r : SBTree α) (hlr : l.height = r.height), t = node l r hlr) := by
  cases t with | mk n t => _
  cases n with | zero => _ | succ n => _
  · cases t with | leaf a => _
    exact Or.inl ⟨a, rfl⟩
  · cases t with | node l r => _
    refine Or.inr ⟨⟨n, l⟩, ⟨n, r⟩, ?_⟩
    simp_rw [node_mk, cast_rfl, height_mk, exists_const]

end LeafNode

def treeListToStack {n : ℕ} (s : List (BTree α n)) : List (SBTree α) :=
  bitRec s [] (fun a => [⟨_, a⟩]) (fun a _ _ _ r => a.elim r (⟨_, ·⟩ :: r))

section TreeListToStack

variable {a l r : BTree α n} {s : List (BTree α n)}

@[simp]
theorem treeListToStack_nil : treeListToStack ([] : List (BTree α n)) = [] := by
  rw [treeListToStack, bitRec]

@[simp]
theorem treeListToStack_singleton  : treeListToStack [a] = [⟨n, a⟩] := by
  rw [treeListToStack, bitRec]

theorem treeListToStack_cons_cons :
    treeListToStack (l :: r :: s) =
    ((modTwo s).elim (·) (⟨n, ·⟩ :: ·)) (treeListToStack (l.node r :: divTwo s)) := by
  rw [treeListToStack, bitRec_bith, eq_rec_constant]
  cases modTwo s <;> rfl

@[simp]
theorem treeListToStack_cons_cons_of_modTwo_none (hs : modTwo s = none) :
    treeListToStack (l :: r :: s) = treeListToStack (l.node r :: divTwo s) := by
  simp_rw [treeListToStack_cons_cons, hs, Option.elim_none]

@[simp]
theorem treeListToStack_cons_cons_of_modTwo_some (hs : modTwo s = some a) :
    treeListToStack (l :: r :: s) = ⟨n, a⟩ :: treeListToStack (l.node r :: divTwo s) := by
  simp_rw [treeListToStack_cons_cons, hs, Option.elim_some]

theorem treeListToStack_of_modTwo_some (hs : modTwo s = some a) :
    treeListToStack s = ⟨n, a⟩ :: treeListToStack (divTwo s) := by
  cases s using bitRec
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    subst hs
    simp_rw [treeListToStack_singleton, divTwo_singleton, treeListToStack_nil]
  · simp_rw [modTwo_cons_cons] at hs
    rw [divTwo_cons_cons, treeListToStack_cons_cons_of_modTwo_some hs]

theorem treeListToStack_of_modTwo_none (hs : modTwo s = none) :
    treeListToStack s = treeListToStack (divTwo s) := by
  cases s using bitRec
  · simp_rw [divTwo_nil, treeListToStack_nil]
  · contradiction
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [divTwo_cons_cons, treeListToStack_cons_cons_of_modTwo_none hs]

theorem treeListToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    treeListToStack (s ++ [a]) = ⟨n, a⟩ :: treeListToStack s := by
  rw [treeListToStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, treeListToStack_of_modTwo_none hs]

theorem treeListToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    treeListToStack (s ++ [b]) = treeListToStack (divTwo s ++ [a.node b]) := by
  rw [treeListToStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

theorem treeListToStack_two_pow {s : List (BTree α m)} (hs : s.length = 2^n) :
    treeListToStack s = [⟨m + n, treeListToTree n s hs⟩] := by
  induction n generalizing m with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨_, rfl⟩
    simp_rw [treeListToStack_singleton, treeListToTree_singleton, Nat.add_zero]
  · have hs' : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, pow_succ', even_two_mul]
    have IH' := IH (s := divTwo s) (length_divTwo ▸ hs ▸ by
        simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero])
    simp_rw [treeListToStack_of_modTwo_none hs', IH', List.singleton_inj,
      treeListToTree_divTwo, eq_iff_eq_and_isList_eq, height_mk, Nat.succ_add_eq_add_succ,
      toList_mk, toList_eq_rec, true_and]

theorem treeListToStack_append {s t : List (BTree α m)} (hs : s.length = 2^n)
    (ht : t.length = 2^n) :
    treeListToStack (s ++ t) =
    [⟨m + n + 1, (treeListToTree n s hs).node (treeListToTree n t ht)⟩] := by
  have hst : (s ++ t).length = 2^(n + 1) :=
    List.length_append.trans (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)
  simp_rw [treeListToStack_two_pow hst, treeListToTree_append hs ht, List.singleton_inj,
    eq_iff_eq_and_isList_eq, height_mk, toList_mk, add_assoc, true_and]

end TreeListToStack

def listToStack (s : List α) : List (SBTree α) := treeListToStack (s.map BTree.leaf)

section TreeListToStack

variable {a b l r : α} {s : List α}

@[simp]
theorem listToStack_nil : listToStack ([] : List α) = [] := by
  rw [listToStack, List.map_nil, treeListToStack_nil]

@[simp]
theorem listToStack_singleton : listToStack [a] = [leaf a] := by
  rw [listToStack, List.map_singleton, treeListToStack_singleton, mk_leaf]

theorem listToStack_cons_cons :
    listToStack (l :: r :: s) = (modTwo (s.map BTree.leaf)).elim (·) (⟨0, ·⟩ :: ·)
    (treeListToStack ((((BTree.leaf l).node (BTree.leaf r))) :: divTwo (s.map BTree.leaf))) := by
  simp_rw [listToStack, List.map_cons, treeListToStack_cons_cons]

@[simp]
theorem listToStack_cons_cons_of_modTwo_none (hs : modTwo (s.map BTree.leaf) = none) :
    listToStack (l :: r :: s) =
    treeListToStack ((BTree.leaf l).node (BTree.leaf r) :: divTwo (s.map BTree.leaf)) := by
  simp_rw [listToStack, List.map_cons, treeListToStack_cons_cons_of_modTwo_none hs]

@[simp]
theorem listToStack_cons_cons_of_modTwo_some
    (hs : modTwo (s.map BTree.leaf) = some (BTree.leaf a)) :
    listToStack (l :: r :: s) = leaf a ::
    treeListToStack ((BTree.leaf l).node (BTree.leaf r) :: divTwo (s.map BTree.leaf)) := by
  simp_rw [listToStack, List.map_cons, treeListToStack_cons_cons_of_modTwo_some hs, mk_leaf]

theorem listToStack_of_modTwo_some (hs : modTwo (s.map BTree.leaf) = some (BTree.leaf a)) :
    listToStack s = leaf a :: treeListToStack (divTwo (s.map BTree.leaf)) := by
  rw [listToStack, treeListToStack_of_modTwo_some hs, mk_leaf]

theorem listToStack_of_modTwo_none (hs : modTwo (s.map BTree.leaf) = none) :
    listToStack s = treeListToStack (divTwo (s.map BTree.leaf)) := by
  rw [listToStack, treeListToStack_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_none (hs : modTwo (s.map BTree.leaf) = none) :
    listToStack (s ++ [a]) = leaf a :: treeListToStack (s.map BTree.leaf) := by
  simp_rw [listToStack, List.map_append, List.map_singleton,
    treeListToStack_append_singleton_of_modTwo_none hs, mk_leaf]

theorem listToStack_append_singleton_of_modTwo_some
    (hs : modTwo (s.map BTree.leaf) = some (BTree.leaf a)) : listToStack (s ++ [b]) =
    treeListToStack (divTwo (s.map BTree.leaf) ++ [(BTree.leaf a).node (BTree.leaf b)]) := by
  simp_rw [listToStack, List.map_append, List.map_singleton,
    treeListToStack_append_singleton_of_modTwo_some hs]

theorem listToStack_two_pow {s : List α} (hs : s.length = 2^n) :
    listToStack s = [⟨n, listToTree n s hs⟩] := by
  simp_rw [listToStack, treeListToStack_two_pow ((List.length_map _).trans hs),
    List.singleton_inj, eq_iff_eq_and_isList_eq, height_mk, zero_add, true_and, toList_mk,
    toList_treeListToTree, toList_listToTree, flatMap_map_leaf]

theorem listToStack_append (s t : List α) (hs : s.length = 2^n) (ht : t.length = 2^n) :
    listToStack (s ++ t) = [⟨n + 1, (listToTree n s hs).node (listToTree n t ht)⟩] := by
  have hst : (s ++ t).length = 2^(n + 1) :=
    List.length_append.trans (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)
  simp_rw [listToStack_two_pow hst, listToTree_append hs ht]

end TreeListToStack

def push (st : List (SBTree α)) (b : SBTree α) : List (SBTree α) := match st with
  | [] => [b]
  | a :: st => if hab : a.height = b.height then push st (a.node b hab) else b :: a :: st

def sbTreeListToStack (ls : List (SBTree α)) : List (SBTree α) :=
  ls.foldl push []

#eval sbTreeListToStack [leaf 1, leaf 2, leaf 3, leaf 4]
#eval treeListToStack [BTree.leaf 1, BTree.leaf 2, BTree.leaf 3, BTree.leaf 4]

end SBTree
