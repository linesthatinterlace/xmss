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

theorem ext_getElem_iff (s t : List α) : s = t ↔
    s.length = t.length ∧ (∀ i (hi₁ : i < s.length) (hi₁ : i < t.length), s[i] = t[i]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · exact List.ext_getElem h.1 h.2

@[elab_as_elim]
def doubleRec {motive : List α → Sort u} (l : List α)  (nil : motive [])
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

end List

inductive BTree (α : Type u) : ℕ → Type u where
  | leaf : (a : α) → BTree α 0
  | node : (l : BTree α n) → (r : BTree α n) → BTree α (n + 1)
deriving Repr, DecidableEq

namespace BTree

def val (t : BTree α 0) : α := match t with | leaf a => a

def left (t : BTree α (n + 1)) : BTree α n := match t with | node l _ => l

def right (t : BTree α (n + 1)) : BTree α n := match t with | node _ r => r

@[simp] theorem left_node {l r : BTree α n } : (node l r).left = l := rfl
@[simp] theorem right_node {l r : BTree α n } : (node l r).right = r := rfl
@[simp] theorem node_left_right {t : BTree α (n + 1)} : t.left.node t.right = t := by cases t ; rfl

def BTreeEquivPair : BTree α (n + 1) ≃ BTree α n × BTree α n where
  toFun := fun p => (p.left, p.right)
  invFun := fun p => node p.1 p.2
  left_inv := fun p => by simp_rw [node_left_right]
  right_inv := fun p => by simp_rw [left_node, right_node]

variable {n : ℕ}

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

abbrev SigmaBTree (α : Type u) := (n : ℕ) × BTree α n

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

def listToStack (n : ℕ) (s : List (BTree α n)) : List (SigmaBTree α) :=
  bitRec s [] (fun a => [⟨_, a⟩]) (fun a _ _ _ r => a.elim r (⟨_, ·⟩ :: r))

#eval listToStack 0 [leaf 0, leaf 1, leaf 2, leaf 3, leaf 4, leaf 5]

section LiftToStack

variable {a l r : BTree α n} {s : List (BTree α n)}

@[simp]
theorem listToStack_nil : listToStack n ([] : List (BTree α n)) = [] := by
  rw [listToStack, bitRec]

@[simp]
theorem listToStack_singleton  : listToStack n [a] = [⟨n, a⟩] := by
  rw [listToStack, bitRec]

theorem listToStack_cons_cons :
    listToStack n (l :: r :: s) =
    ((modTwo s).elim (·) (⟨n, ·⟩ :: ·)) (listToStack (n + 1) (l.node r :: divTwo s)) := by
  rw [listToStack, bitRec_bith, eq_rec_constant]
  cases modTwo s <;> rfl

@[simp]
theorem listToStack_cons_cons_of_modTwo_none (hs : modTwo s = none) :
    listToStack n (l :: r :: s) = listToStack (n + 1) (l.node r :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_none]

@[simp]
theorem listToStack_cons_cons_of_modTwo_some (hs : modTwo s = some a) :
    listToStack n (l :: r :: s) = ⟨n, a⟩ :: listToStack (n + 1) (l.node r :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_some]

theorem listToStack_of_modTwo_some (hs : modTwo s = some a) :
    listToStack n s = ⟨n, a⟩ :: listToStack (n + 1) (divTwo s) := by
  cases s using bitRec
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    subst hs
    simp_rw [listToStack_singleton, divTwo_singleton, listToStack_nil]
  · simp_rw [modTwo_cons_cons] at hs
    rw [divTwo_cons_cons, listToStack_cons_cons_of_modTwo_some hs]

theorem listToStack_of_modTwo_none (hs : modTwo s = none) :
    listToStack n s = listToStack (n + 1) (divTwo s) := by
  cases s using bitRec
  · simp_rw [divTwo_nil, listToStack_nil]
  · contradiction
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [divTwo_cons_cons, listToStack_cons_cons_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    listToStack n (s ++ [a]) = ⟨n, a⟩ :: listToStack n s := by
  rw [listToStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, listToStack_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    listToStack n (s ++ [b]) = listToStack (n + 1) (divTwo s ++ [node a b]) := by
  rw [listToStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

end LiftToStack

end BTree
