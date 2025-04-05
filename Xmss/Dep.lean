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

inductive BT (α : Type u) : ℕ → Type u where
  | leaf : (a : α) → BT α 0
  | node : (l : BT α n) → (r : BT α n) → BT α (n + 1)
deriving Repr, DecidableEq

namespace BT


variable {n m : ℕ}

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by simp only [leaf.injEq]

theorem node_inj_iff {a b c d : BT α n}: a.node b  = c.node d ↔ a = c ∧ b = d := by
  simp only [node.injEq]

def val (t : BT α 0) : α := match t with | leaf a => a

@[simp] theorem val_leaf {a : α} : (leaf a).val = a := rfl

def left (t : BT α (n + 1)) : BT α n := match t with | node l _ => l

def right (t : BT α (n + 1)) : BT α n := match t with | node _ r => r

@[simp] theorem left_node {l r : BT α n} : (node l r).left = l := rfl
@[simp] theorem right_node {l r : BT α n} : (node l r).right = r := rfl
@[simp] theorem node_left_right {t : BT α (n + 1)} : t.left.node t.right = t := by cases t ; rfl

def BTEquivPair : BT α (n + 1) ≃ BT α n × BT α n where
  toFun := fun p => (p.left, p.right)
  invFun := fun p => node p.1 p.2
  left_inv := fun p => by simp_rw [node_left_right]
  right_inv := fun p => by simp_rw [left_node, right_node]

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

protected def cast {n m : ℕ} (h : n = m) : BT α n → BT α m
  | leaf a => match m with | 0 => leaf a
  | node l r => match m with
  | _ + 1 => node (l.cast (Nat.add_right_cancel h)) (r.cast (Nat.add_right_cancel h))

section Cast

variable {a : α}

@[simp]
theorem cast_rfl {t : BT α n} : t.cast rfl = t := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · rfl
  · simp_rw [BT.ext_succ_iff]
    exact ⟨IHL, IHR⟩

theorem cast_eq_cast {h : n = m} {t : BT α n} : t.cast h = h ▸ t := by
  cases h ; rw [cast_rfl]

@[simp]
theorem cast_cast {t : BT α n} {h : n = m} {h' : m = n} : (t.cast h).cast h' = t := by
  cases h ; cases h' ; simp_rw [cast_rfl]

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

def toList {n : ℕ} : BT α n → List α
  | leaf a => [a]
  | node l r => toList l ++ toList r

section ToList

variable {s t : BT α n}

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
  cases h ; rw [cast_rfl]

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

theorem toList_eq_toList_iff {s : BT α n} {t : BT α m} :
    s.toList = t.toList ↔ ∃ (h : n = m), s.cast h = t := by
  refine ⟨fun h => ⟨eq_level_of_toList_eq_toList h, ?_⟩, fun ⟨h, hst⟩ => hst ▸ ?_⟩
  · simp_rw [eq_iff_toList_eq, toList_cast, h]
  · simp_rw [toList_cast]

end ToList

def flatten {n : ℕ} : BT (BT α m) n → BT α (m + n)
  | leaf a => a
  | node l r => node l.flatten r.flatten

section Flatten

variable {t l r : BT (BT α n) m} {a : BT α n}

@[simp] theorem flatten_leaf : (leaf a).flatten = a := rfl

@[simp] theorem flatten_node : (node l r).flatten = node l.flatten r.flatten := rfl

end Flatten

abbrev BTL (α : Type u) (n : ℕ) := List (BT α n)

namespace BTL

variable {a : BT α n} {s t : BTL α n}

def toList (s : BTL α n) : List α := s.flatMap BT.toList

section ToList

@[simp] theorem toList_nil : toList (α := α) (n := n) [] = [] := rfl
@[simp] theorem toList_cons : toList (a :: s) = a.toList ++ toList s := rfl
@[simp] theorem toList_singleton : toList [a] = a.toList := List.flatMap_singleton _ _
@[simp] theorem toList_append : toList (s ++ t) = toList s ++ toList t := List.flatMap_append
theorem toList_ne_nil_iff : toList l = [] ↔ l = [] := by
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

@[simp] theorem modTwo_nil : modTwo ([] : BTL α n) = none := rfl
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

def divTwo (l : BTL α n) : BTL α (n + 1) :=
  l.doubleRec [] (fun _ => []) (fun l r _ ds => l.node r :: ds)

section DivTwo

variable {s :  BTL α n}

@[simp] theorem divTwo_nil : divTwo ([] : BTL α n) = [] := rfl
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

theorem toList_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    (divTwo s).toList = s.toList := by
  induction s using List.doubleRec with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · contradiction
  · simp_rw [divTwo_cons_cons, BTL.toList_cons, toList_node, List.append_assoc,
      List.append_cancel_left_eq, IH hs]

end DivTwo

def divModTwo (l : BTL α n) : Option (BT α n) × BTL α (n + 1) :=
  l.doubleRec (none, []) (some · , []) (fun l r _ (mts, dts) => (mts, l.node r :: dts))

@[simp] theorem divModTwo_nil : divModTwo ([] : BTL α n) = (none, []) := rfl
@[simp] theorem divModTwo_singleton : divModTwo [a] = (some a, []) := rfl
@[simp] theorem divModTwo_cons_cons : divModTwo (l :: r :: s) =
    ((divModTwo s).1, l.node r :: (divModTwo s).2) := rfl

section DivModTwo

variable {s :  BTL α n}

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

def bit :  Option (BT α n) → BTL α (n + 1) → BTL α n
  | ao, [] => ao.toList
  | ao, (lr :: ss) => lr.left :: lr.right :: bit ao ss

section Bit

variable {ao : Option (BT α n)} {s : BTL α (n + 1)} {b : BT α (n + 1)}

@[simp] theorem bit_nil : bit ao ([] : BTL α (n + 1)) = ao.toList := rfl
@[simp] theorem bit_none_nil : bit none ([] : BTL α (n + 1)) = [] := rfl
@[simp] theorem bit_some_nil : bit (some a) ([] : BTL α (n + 1)) = [a] := rfl
@[simp] theorem bit_none_singleton : bit none [b] = [b.left, b.right] := rfl
@[simp] theorem bit_some_singleton : bit (some a) [b] = [b.left, b.right, a] := rfl
@[simp] theorem bit_cons : bit ao (lr :: ss) = lr.left :: lr.right :: bit ao ss := rfl

theorem bit_none_eq_flatMap :
    bit none s = s.flatMap fun lr => [lr.left, lr.right] := by
  induction s using List.doubleRec with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · simp_rw [bit_none_singleton, List.flatMap_singleton]
  · simp_rw [bit_cons, IH, List.flatMap_cons, List.cons_append, List.nil_append]

theorem bit_some_eq_bit_none_append : bit (some a) s = bit none s ++ [a] := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [bit_cons, List.cons_append, IH]

theorem toList_bit :
    (bit ao s).toList = s.toList ++ BTL.toList (ao.toList) := by
  induction s using List.doubleRec with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · simp_rw [bit_cons, bit_nil, BTL.toList_cons, BTL.toList_nil, List.append_nil,
      toList_succ, List.append_assoc]
  · simp_rw [bit_cons, BTL.toList_cons, IH, toList_succ, List.append_assoc]

@[simp] theorem toList_bit_none :
    (bit none s).toList = s.toList := by
  rw [toList_bit, Option.toList_none, toList_nil, List.append_nil]

@[simp] theorem toList_bit_some :
    (bit (some a) s).toList = s.toList ++ a.toList := by
  rw [toList_bit, Option.toList_some, toList_singleton]


end Bit

section BitDivTwoModTwoMulTwo

variable {ao : Option (BT α n)} {ss : BTL α (n + 1)}

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

theorem bit_modTwo_node_cons_divTwo {l r : BT α n} :
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

def bitDivModEquiv : Option (BT α n) × BTL α (n + 1) ≃ BTL α n where
  toFun as := bit as.1 as.2
  invFun s := ⟨(modTwo s), (divTwo s)⟩
  left_inv as := by simp_rw [modTwo_bit, divTwo_bit]
  right_inv s := by simp_rw [bit_modTwo_divTwo]

end BitDivTwoModTwoMulTwo

def listToBT : (n : ℕ) → (s : List α) → s.length = 2^n → BT α n
  | 0, s => fun h => leaf <| s.getLast (List.ne_nil_of_length_pos (h ▸ Nat.two_pow_pos _))
  | (n + 1), s => fun h => node
      (listToBT n (s.take (2^n)) (s.length_take_of_length_eq_add (h ▸ Nat.two_pow_succ _)))
      (listToBT n (s.drop (2^n)) (s.length_drop_of_length_eq_add (h ▸ Nat.two_pow_succ _)))

section ListToBT

variable {s t : List α}

@[simp]
theorem toList_listToBT {hs : s.length = 2^n} : (listToBT n s hs).toList = s := by
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨a, rfl⟩
    simp_rw [listToBT, List.getLast_singleton, toList_zero, List.singleton_inj, val_leaf]
  · rw [Nat.two_pow_succ] at hs
    simp_rw [listToBT, toList_node, IH, List.take_append_drop]

@[simp]
theorem listToBT_singleton : listToBT 0 [a] rfl = leaf a := rfl

theorem listToBT_zero {hs : s.length = 2^0} : listToBT 0 s hs =
  leaf (s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := rfl

theorem listToBT_zero_eq_head {hs : s.length = 2^0} : listToBT 0 s hs =
    leaf (s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [pow_zero, List.length_eq_one_iff] at hs
  rcases hs with ⟨a, rfl⟩
  rfl

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

variable {n : ℕ} {s t : BTL α m}

@[simp]
theorem toList_btlToBT :
    (btlToBT n s hs).toList = s.toList :=
  BTL.toList_toList.symm.trans (congrArg₂ _ rfl toList_listToBT)

theorem listToBT_toList_btlToBT {hs : s.length = 2^n} :
    listToBT (m + n) (btlToBT n s hs).toList length_toList = btlToBT n s hs := by
  simp_rw [BT.eq_iff_toList_eq, toList_btlToBT, toList_listToBT]

@[simp]
theorem btlToBT_singleton {a : BT α n}: btlToBT 0 [a] rfl = a := rfl

theorem btlToBT_zero {hs : s.length = 2^0} : btlToBT 0 s hs =
  s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := rfl

theorem btlToBT_zero_eq_head {hs : s.length = 2^0} : btlToBT 0 s hs =
    s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := by
  simp_rw [pow_zero, List.length_eq_one_iff] at hs
  rcases hs with ⟨a, rfl⟩
  rfl

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
  have H : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, Nat.pow_succ', even_two_mul]
  simp_rw [BT.eq_iff_toList_eq, toList_eq_rec, toList_btlToBT,
    BTL.toList_divTwo_of_modTwo_eq_none H]

end BTLToBT

@[elab_as_elim, specialize]
def bitRec {motive : (n : ℕ) → BTL α n → Sort u} {n : ℕ} (s : BTL α n)
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

variable {motive : (n : ℕ) → BTL α n → Sort u}
    {nil : ∀ {n}, motive n []} {singleton : ∀ {n} a, motive n [a]}
    {bith : ∀ {n} a l r s, motive (n + 1) (l.node r :: s) → motive n (l :: r :: bit a s)}
    {l r : BT α n}

@[simp] theorem bitRec_nil : bitRec (n := n) [] nil singleton bith = nil := by
  rw [bitRec]
@[simp] theorem bitRec_singleton : bitRec (n := n) [a] nil singleton bith = singleton a := by
  rw [bitRec]

@[simp] theorem bitRec_bith : bitRec (motive := motive) (n := n) (l :: r :: s) nil singleton bith =
    bit_modTwo_divTwo (s := s) ▸
    bith (modTwo s) l r (divTwo s) (bitRec (motive := motive)
    (l.node r :: divTwo s) nil singleton bith) := by simp_rw [bitRec]

end BitRec

end BTL
end BT

abbrev SBT (α : Type u) := (n : ℕ) × BT α n

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

@[simp] theorem snd_eq_toBT {a : SBT α} : a.2 = a.toBT := rfl

@[simp] theorem toBT_mk : toBT ⟨n, a⟩ = a := rfl

end ToBT

def ofBT (a : BT α n) : SBT α := ⟨n, a⟩

section OfBT

variable {a l r : BT α n}

@[simp] theorem height_ofBT : (ofBT a).height = n := rfl
@[simp] theorem toBT_ofBT : (ofBT a).toBT = a := rfl

end OfBT

protected def copy {m : ℕ} (a : SBT α) (h : a.height = m) : SBT α := ofBT (a.toBT.cast h)

section Copy

variable {a : SBT α} {h : a.height = m}

@[simp] theorem toBT_copy : (a.copy h).toBT = a.toBT.cast h := rfl
@[simp] theorem ofBT_cast {h : n = m} {a : BT α n} :
    ofBT (a.cast h) = (ofBT a).copy h := rfl

end Copy

def toList (a : SBT α) := a.toBT.toList

section ToList

variable {a s t : SBT α}

@[simp] theorem toList_toBT : a.toBT.toList = a.toList := rfl
@[simp] theorem toList_ofBT {a : BT α m} : (ofBT a).toList = a.toList := rfl
@[simp] theorem toList_copy (h : a.height = m) : (a.copy h).toList = a.toList := by
  unfold toList
  simp_rw [toBT_copy, toList_cast]

@[simp] theorem toList_mk {a : BT α n}: toList ⟨n, a⟩ = a.toList := rfl

@[simp] theorem toList_ne_nil : toList a ≠ [] :=
  List.ne_nil_of_length_pos (length_toList ▸ Nat.two_pow_pos _)

theorem eq_of_eq_toList : ∀ {a b : SBT α}, a.toList = b.toList → a = b
  | ⟨n, a⟩, ⟨m, b⟩, hab => by
    simp_rw [toList_mk] at hab
    have heq : n = m := eq_level_of_toList_eq_toList hab
    simp_rw [toList_eq_toList_iff, heq, exists_true_left] at hab
    subst hab heq
    simp_rw [cast_rfl]

theorem eq_iff_toList_eq {a b : SBT α} :
     a = b ↔ a.toList = b.toList := ⟨fun h => h ▸ rfl, eq_of_eq_toList⟩

end ToList

def leaf (a : α) : SBT α := ⟨0, BT.leaf a⟩

section Leaf

variable {a b : α}

@[simp] theorem mk_leaf : ⟨0, BT.leaf a⟩ = leaf a := rfl

@[simp] theorem height_leaf : (leaf a).height = 0 := rfl
@[simp] theorem toBT_leaf : (leaf a).toBT = BT.leaf a := rfl
@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl

theorem leaf_inj_iff {a b : α} : leaf a = leaf b ↔ a = b := by
  simp_rw [eq_iff_toList_eq, toList_leaf, List.singleton_inj]

@[simp] theorem ofBT_leaf {a : α} : ofBT (BT.leaf a) = leaf a := rfl
theorem ofBT_comp_leaf : ofBT ∘ BT.leaf = leaf (α := α) := rfl

end Leaf

def node (a b : SBT α) (hab : a.height = b.height) : SBT α :=
  ⟨b.height + 1, (a.toBT.cast hab).node b.toBT⟩

section Node
variable {a b c d: SBT α} (hab : a.height = b.height) (hcd : c.height = d.height)

@[simp] theorem node_mk {a : BT α n} {b : BT α m} (hab : n = m) :
  node ⟨n, a⟩ ⟨m, b⟩ hab = ⟨m + 1, (a.cast hab).node b⟩ := rfl

@[simp] theorem height_node : (a.node b hab).height = b.height + 1 := rfl
theorem height_node' : (a.node b hab).height = a.height + 1 := hab ▸ rfl
@[simp] theorem toBT_node : (a.node b hab).toBT = (a.toBT.cast hab).node b.toBT := rfl
@[simp] theorem toList_node : (a.node b hab).toList = a.toList ++ b.toList :=
  congrArg₂ _ toList_cast rfl

theorem node_inj_iff : a.node b hab = c.node d hcd ↔ a = c ∧ b = d := by
  cases a ; cases b ; cases c ; cases d
  simp only [height_mk] at hab hcd ; subst hab hcd
  simp_rw [eq_iff_toList_eq, toList_node, toList_mk,
    ← BT.toList_node, toList_eq_toList_iff, Nat.add_left_inj]
  refine ⟨fun ⟨heq, hst⟩ => ?_, fun ⟨⟨heq, hs⟩, ⟨_, ht⟩⟩ => ?_⟩ <;> subst heq
  · simp_rw [cast_rfl, node_inj_iff] at hst
    simp_rw [cast_rfl, exists_const, hst, true_and]
  · simp only [cast_rfl] at hs ht
    simp only [cast_rfl, hs, ht, exists_const]

@[simp] theorem ofBT_node : ofBT (BT.node l r) =
    node (ofBT l) (ofBT r) rfl := by
  simp_rw [eq_iff_toList_eq, toList_node, toList_ofBT, BT.toList_node]

theorem ofBT_comp_node : ofBT ∘ (BT.node (n := n) (α := α)).uncurry =
    Function.uncurry (fun l r => node (ofBT l) (ofBT r) rfl) := funext <| fun _ => by
  simp_rw [eq_iff_toList_eq]
  unfold Function.uncurry
  simp only [Function.comp_apply, ofBT_node, toList_node, toList_ofBT,
    BT.toList_node, toList_node, toList_ofBT]

end Node

section LeafNode

theorem forall_exists_leaf_or_node (t : SBT α) :
    (∃ (a : α), t = leaf a) ∨
    (∃ (l r : SBT α) (hlr : l.height = r.height), t = node l r hlr) := by
  cases t with | mk n t => _
  cases n with | zero => _ | succ n => _
  · cases t with | leaf a => _
    exact Or.inl ⟨a, rfl⟩
  · cases t with | node l r => _
    refine Or.inr ⟨⟨n, l⟩, ⟨n, r⟩, ?_⟩
    simp_rw [node_mk, cast_rfl, height_mk, exists_const]

end LeafNode

abbrev SBTL (α : Type u) := List (SBT α)

namespace SBTL

def toList (s : SBTL α) : List α := s.reverse.flatMap SBT.toList

section ToList

variable {a : SBT α} {s : SBTL α}

@[simp] theorem toList_nil : toList (α := α) [] = [] := rfl
@[simp] theorem toList_cons : toList (a :: s) = s.toList ++ a.toList := by
  unfold toList
  simp_rw [List.reverse_cons, List.flatMap_append, List.flatMap_singleton]

@[simp] theorem toList_singleton : toList [a] = a.toList := by
  unfold toList
  simp_rw [List.reverse_singleton, List.flatMap_singleton]
@[simp] theorem toList_append : toList (s ++ t) = toList t ++ toList s := by
  unfold toList
  simp_rw [List.reverse_append, List.flatMap_append]

theorem toList_ne_nil_iff : toList l = [] ↔ l = [] := by
  unfold toList
  simp_rw [List.flatMap_eq_nil_iff, SBT.toList_ne_nil,
    imp_false, List.eq_nil_iff_forall_not_mem, List.mem_reverse]

theorem toList_map_leaf {s : List α} : BTL.toList (s.map BT.leaf) = s := by
  induction s with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [List.map_cons, BTL.toList_cons, BT.toList_leaf, List.singleton_append, IH]

end ToList

def btlToStack {n : ℕ} (s : BTL α n) : SBTL α :=
  s.bitRec [] (fun a => [ofBT a]) (fun a _ _ _ r => a.elim r (ofBT · :: r))

section BTLToStack

variable {a l r : BT α n} {s : BTL α n}

@[simp]
theorem btlToStack_nil : btlToStack ([] : BTL α n) = [] := by
  rw [btlToStack, BTL.bitRec]

@[simp]
theorem btlToStack_singleton : btlToStack [a] = [ofBT a] := by
  rw [btlToStack, BTL.bitRec]

theorem btlToStack_cons_cons :
    btlToStack (l :: r :: s) =
    ((modTwo s).elim (·) (fun a r => (ofBT a :: r)) (btlToStack (l.node r :: divTwo s))) := by
  rw [btlToStack, bitRec_bith, eq_rec_constant]
  cases modTwo s <;> rfl

@[simp]
theorem btlToStack_cons_cons_of_modTwo_none (hs : modTwo s = none) :
    btlToStack (l :: r :: s) = btlToStack (l.node r :: divTwo s) := by
  simp_rw [btlToStack_cons_cons, hs, Option.elim_none]

@[simp]
theorem btlToStack_cons_cons_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack (l :: r :: s) = ofBT a :: btlToStack (l.node r :: divTwo s) := by
  simp_rw [btlToStack_cons_cons, hs, Option.elim_some]

theorem btlToStack_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack s = ofBT a :: btlToStack (divTwo s) := by
  cases s using bitRec
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    subst hs
    simp_rw [btlToStack_singleton, divTwo_singleton, btlToStack_nil]
  · simp_rw [modTwo_cons_cons] at hs
    rw [divTwo_cons_cons, btlToStack_cons_cons_of_modTwo_some hs]

theorem btlToStack_of_modTwo_none (hs : modTwo s = none) :
    btlToStack s = btlToStack (divTwo s) := by
  cases s using bitRec
  · simp_rw [divTwo_nil, btlToStack_nil]
  · contradiction
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [divTwo_cons_cons, btlToStack_cons_cons_of_modTwo_none hs]

theorem btlToStack_eq  :
    btlToStack s = (modTwo s).toList.map ofBT ++ btlToStack (divTwo s) := by
  cases hs : modTwo s
  · simp_rw [btlToStack_of_modTwo_none hs, Option.toList_none, List.map_nil, List.nil_append]
  · simp_rw [btlToStack_of_modTwo_some hs, Option.toList_some,
      List.map_singleton, List.singleton_append]

theorem btlToStack_bit {s : BTL α (n + 1)} :
    btlToStack (bit ao s) = ao.toList.map ofBT ++ btlToStack s := by
  rw [btlToStack_eq, modTwo_bit, divTwo_bit]

theorem btlToStack_bit_none {s : BTL α (n + 1)} :
    btlToStack (bit none s) = btlToStack s := by
  rw [btlToStack_of_modTwo_none modTwo_bit, divTwo_bit]

theorem btlToStack_bit_some {s : BTL α (n + 1)} :
    btlToStack (bit (some a) s) = ofBT a :: btlToStack s := by
  rw [btlToStack_of_modTwo_some modTwo_bit, divTwo_bit]

theorem btlToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    btlToStack (s ++ [a]) = ofBT a :: btlToStack s  := by
  rw [btlToStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, btlToStack_of_modTwo_none hs]

theorem btlToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    btlToStack (s ++ [b]) = btlToStack (divTwo s ++ [a.node b]) := by
  rw [btlToStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

theorem btlToStack_two_pow {s : BTL α m} (hs : s.length = 2^n) :
    btlToStack s = [ofBT <| btlToBT n s hs] := by
  induction n generalizing m with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨_, rfl⟩
    simp_rw [btlToStack_singleton, btlToBT_singleton]
  · have hs' : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, pow_succ', even_two_mul]
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
  induction s using bitRec with | nil => _ | singleton a => _ | bith a l r s IH => _
  · simp_rw [btlToStack_nil, SBTL.toList_nil, BTL.toList_nil]
  · simp only [btlToStack_singleton, toList_cons, toList_nil, toList_ofBT, List.nil_append,
      BTL.toList_cons, BTL.toList_nil, List.append_nil]
  · simp only [BTL.toList_cons, BT.toList_node, List.append_assoc] at IH ⊢
    rcases a with _ | a
    · simp_rw [btlToStack_cons_cons_of_modTwo_none modTwo_bit,
        divTwo_bit, IH, BTL.toList_bit, Option.toList_none, BTL.toList_nil,
        List.append_nil]
    · simp_rw [btlToStack_cons_cons_of_modTwo_some modTwo_bit,
        divTwo_bit, toList_cons, IH, toList_ofBT, List.append_assoc, BTL.toList_bit,
        Option.toList_some, BTL.toList_cons, BTL.toList_nil, List.append_nil]

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

theorem listToStack_cons_cons :
    listToStack (l :: r :: s) = (modTwo (s.map BT.leaf)).elim (·) (fun a s => ofBT a :: s)
    (btlToStack ((((BT.leaf l).node (BT.leaf r))) :: divTwo (s.map BT.leaf))) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons_cons]

@[simp]
theorem listToStack_cons_cons_of_modTwo_none (hs : modTwo (s.map BT.leaf) = none) :
    listToStack (l :: r :: s) =
    btlToStack ((BT.leaf l).node (BT.leaf r) :: divTwo (s.map BT.leaf)) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons_cons_of_modTwo_none hs]

@[simp]
theorem listToStack_cons_cons_of_modTwo_some
    (hs : modTwo (s.map BT.leaf) = some (BT.leaf a)) :
    listToStack (l :: r :: s) =
    leaf a :: btlToStack ((BT.leaf l).node (BT.leaf r) :: divTwo (s.map BT.leaf)) := by
  simp_rw [listToStack, List.map_cons, btlToStack_cons_cons_of_modTwo_some hs, ofBT_leaf]

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

def push {m : ℕ} (s : SBTL α) (b : BT α m) : SBTL α := match s with
  | [] => ([ofBT b])
  | (a :: s) =>
    if hab : a.height = m then push s ((a.toBT.cast hab).node b)
    else ofBT b :: a :: s

section Push

variable {a c : SBT α} {s : SBTL α} {b : BT α m}

@[simp] theorem push_nil : push [] b = [ofBT b] := rfl
theorem push_cons : push (a :: s) b =
    if hab : a.height = m then push s ((a.toBT.cast hab).node b) else ofBT b :: a :: s := rfl
@[simp] theorem push_singleton : push [a] b =
    if hab : a.height = m then [node a (ofBT b) hab] else [ofBT b, a] := rfl

@[simp] theorem push_cons_of_ne (hab : a.height ≠ m) :
    push (a :: s) b = ofBT b :: a :: s := dif_neg hab
@[simp] theorem push_cons_of_eq (hab : a.height = m) :
    push (a :: s) b = push s ((a.toBT.cast hab).node b) := dif_pos hab

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

theorem lt_push_head_height_of_lt :
    ∀ {n}, n < m → n < ((push s b).head push_ne_nil).height :=
  fun h => h.trans_le le_height_head_push

theorem ne_push_succ_head_height {b : BT α (m + 1)} :
    ((push s b).head push_ne_nil).height ≠ m :=
  (lt_push_head_height_of_lt (Nat.lt_succ_self _)).ne'

theorem push_of_head_ne (hs : ∀ (hs : s ≠ []), (s.head hs).height ≠ m) :
    push s b = ofBT b :: s := by
  cases s
  · exact push_nil
  · specialize hs (List.cons_ne_nil _ _)
    simp_rw [List.head_cons] at hs
    simp_rw [push_cons_of_ne hs]

theorem push_push_of_height_lt {b : BT α m} {c : BT α n} (h : n < m) :
    (push s b).push c = ofBT c :: push s b :=
  push_of_head_ne (fun _ => (lt_push_head_height_of_lt h).ne')

@[simp]
theorem toList_push : (push s b).toList = s.toList ++ b.toList := by
  induction s generalizing m with
  | nil => _ | cons a s IH => _
  · simp_rw [push_nil, toList_singleton, toList_nil, List.nil_append, toList_ofBT]
  · simp_rw [push_cons,  apply_dite, IH, BT.toList_node, toList_cast, toList_toBT,
      toList_cons, toList_ofBT, List.append_assoc, dite_eq_ite, ite_self]

theorem push_left_push_right {b : BT α (m + 1)} (hs : ∀ (hs : s ≠ []), (s.head hs).height ≠ m) :
    (s.push b.left).push b.right = s.push b := by
  simp_rw [push_of_head_ne hs, push_cons_of_eq rfl, toBT_ofBT, cast_rfl, node_left_right]

theorem push_push_left_push_right {a : BT α (m + 1)} {b : BT α (m + 1)} :
    ((s.push a).push b.left).push b.right = (s.push a).push b :=
  push_left_push_right (fun _ => ne_push_succ_head_height)

end Push

def pushStack (s : BTL α m) (t : SBTL α) := s.foldl push t

section PushStack

variable {a b : BT α m} {s s' : BTL α m} {t : SBTL α} {as : SBT α}

@[simp] theorem pushStack_nil : t.pushStack (m := m) [] = t := rfl
@[simp] theorem pushStack_cons : t.pushStack (a :: s) = (push t a).pushStack s := rfl
@[simp] theorem pushStack_singleton : t.pushStack [a] = push t a := rfl
@[simp] theorem pushStack_append :
    t.pushStack (s ++ s') = (t.pushStack s).pushStack s' := List.foldl_append
@[simp] theorem pushStack_append_singleton :
    t.pushStack (s ++ [a]) = push (t.pushStack s) a := by
  simp_rw [pushStack_append, pushStack_singleton]

@[simp] theorem toList_pushStack :
    (t.pushStack s).toList = t.toList ++ s.toList := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · simp_rw [pushStack_nil, BTL.toList_nil, List.append_nil]
  · simp_rw [pushStack_cons, IH, toList_push, List.append_assoc, BTL.toList_cons]

theorem pushStack_bit_none {s : BTL α (m + 1)} (ht : ∀ (ht : t ≠ []), (t.head ht).height ≠ m) :
    t.pushStack (bit none s) = t.pushStack s := by
  induction s using List.doubleRec generalizing t with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · rfl
  · simp_rw [bit_none_singleton, pushStack_cons, pushStack_nil, push_left_push_right ht]
  · simp_rw [bit_cons, pushStack_cons, push_left_push_right ht, push_push_left_push_right]
    refine IH (fun _ => ne_push_succ_head_height)

theorem pushStack_bit_none_singleton {a : SBT α} (ha : a.height ≠ m) {s : BTL α (m + 1)} :
    pushStack (bit none s) [a] = pushStack s [a] := by
  rw [pushStack_bit_none]
  exact fun _ => ha

theorem pushStack_bit_none_singleton_of_height_succ {a : SBT α} (ha : a.height = m + 1)
    {s : BTL α (m + 1)} : pushStack (bit none s) [a] = pushStack s [a] :=
  pushStack_bit_none_singleton (ha.trans_ne (Nat.succ_ne_self _))

end PushStack

def btlPushToStack (s : BTL α m) : SBTL α := pushStack s []

section BTLPushToStack

variable {a : BT α m} {s s' : BTL α m}

@[simp] theorem btlPushToStack_nil : btlPushToStack ([] : BTL α m) = [] := rfl
@[simp] theorem btlPushToStack_cons : btlPushToStack (a :: s) = pushStack s [ofBT a]:= by
  unfold btlPushToStack
  simp_rw [pushStack_cons, push_nil]

@[simp] theorem btlPushToStack_singleton : btlPushToStack [a] = [ofBT a] := by simp_rw [btlPushToStack_cons, pushStack_nil]

@[simp] theorem btlPushToStack_append_singleton : btlPushToStack (s ++ [a]) = push (btlPushToStack s) a :=
  pushStack_append_singleton

@[simp] theorem btlPushToStack_append : btlPushToStack (s ++ s') = (btlPushToStack s).pushStack s' :=by
  unfold btlPushToStack
  simp_rw [pushStack_append]

@[simp] theorem btlPushToStack_eq_btlToStack :
    btlPushToStack (α := α) (m := m) = btlToStack := funext <| fun s => by
  induction s using bitRec with | nil => _ | singleton a => _ | bith a l r s IH => _
  · simp only [btlPushToStack_nil, btlToStack_nil]
  · simp only [btlPushToStack_cons, pushStack_nil, btlToStack_singleton]
  · simp only [btlPushToStack_cons, ofBT_node] at IH
    simp_rw [btlPushToStack_cons, pushStack_cons, push_cons, height_ofBT, dite_true, toBT_ofBT,
      cast_rfl, push_nil, ofBT_node]
    have H := pushStack_bit_none_singleton_of_height_succ (s := s)
      (a := (ofBT l).node (ofBT r) rfl) rfl
    rcases a with _ | a
    · rw [btlToStack_cons_cons_of_modTwo_none modTwo_bit, divTwo_bit]
      simp_rw [← IH, H]
    · rw [btlToStack_cons_cons_of_modTwo_some modTwo_bit, divTwo_bit,
        bit_some_eq_bit_none_append, pushStack_append, pushStack_cons, pushStack_nil]
      simp_rw [← IH, H]
      refine push_of_head_ne (fun _ => ?_)
      cases s using List.reverseRecOn
      · simp_rw [pushStack_nil]
        exact Nat.succ_ne_self _
      · simp_rw [pushStack_append_singleton]
        exact ne_push_succ_head_height

end BTLPushToStack

def listPushToStack (ls : List α) : SBTL α := btlPushToStack (ls.map BT.leaf)

section ListPushToStack

theorem listToStack_eq_listPushToStack : listToStack = listPushToStack (α := α) :=
    funext <| fun s => by
  unfold listToStack listPushToStack
  simp_rw [btlPushToStack_eq_btlToStack]

#eval (fun a => listPushToStack a == listToStack a) [1, 2, 3]
#eval (fun a => listPushToStack a == listToStack a) [1, 2, 3, 4, 5, 6]
#eval (fun a => listPushToStack a == listToStack a) (List.range 10000)

end ListPushToStack

end SBTL

end SBT
