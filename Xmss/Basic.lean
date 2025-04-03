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

variable {a : α} {ao : Option α} {s : List α} {ss : List (α × α)}

theorem ext_getElem_iff (s t : List α) : s = t ↔
    s.length = t.length ∧ (∀ i (hi₁ : i < s.length) (hi₁ : i < t.length), s[i] = t[i]) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    exact ⟨rfl, fun _ _ _ => rfl⟩
  · exact List.ext_getElem h.1 h.2

@[elab_as_elim]
def doubleRec {motive : List α → Sort*} (l : List α)  (nil : motive [])
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
theorem doubleRec_cons_cons {a b : α} {l : List α} :
    doubleRec (a :: b :: l) nil singleton cons_cons =
    cons_cons a b l (doubleRec l nil singleton cons_cons) := rfl

end DoubleRec

def modTwo (l : List α) : Option α :=
  l.doubleRec none some (fun _ _ _ => id)

section ModTwo

@[simp] theorem modTwo_nil : modTwo ([] : List α) = none := rfl
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

def divTwo (l : List α) : List (α × α) :=
  l.doubleRec [] (fun _ => []) (fun l r _ ds => (l, r) :: ds)

section DivTwo

@[simp] theorem divTwo_nil : divTwo ([] : List α) = [] := rfl
@[simp] theorem divTwo_singleton : divTwo [a] = [] := rfl
@[simp] theorem divTwo_cons_cons : divTwo (l :: r :: s) = (l, r) :: divTwo s := rfl

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

theorem bit_lt_length_of_lt_divTwo_length {i : ℕ} (b : Bool) (hi : i < s.divTwo.length) :
    i.bit b < s.length := by
  simp_rw [length_divTwo, Nat.lt_div_iff_mul_lt zero_lt_two,
    mul_comm i, Nat.lt_sub_iff_add_lt, ] at hi
  cases b
  · exact (Nat.lt_succ_self _).trans hi
  · exact hi

theorem two_mul_lt_length_of_lt_divTwo_length {i : ℕ} (hi : i < s.divTwo.length) :
    2 * i < s.length := bit_lt_length_of_lt_divTwo_length false hi

theorem two_mul_succ_lt_length_of_lt_divTwo_length {i : ℕ} (hi : i < s.divTwo.length) :
    2 * i + 1 < s.length := bit_lt_length_of_lt_divTwo_length true hi

theorem getElem_divTwo {i : ℕ} (hi : i < List.length s.divTwo) :
  (s.divTwo)[i] =
    (s[2*i]'(two_mul_lt_length_of_lt_divTwo_length hi),
      s[2*i + 1]'(two_mul_succ_lt_length_of_lt_divTwo_length hi)) := by
  induction s using List.doubleRec generalizing i with
  | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · contradiction
  · contradiction
  · simp_rw [divTwo_cons_cons, List.getElem_cons_succ]
    cases i
    · simp_rw [mul_zero, List.getElem_cons_zero]
    · simp_rw [mul_add, Nat.mul_succ, List.getElem_cons_succ, IH]

theorem take_divTwo : s.divTwo.take k = divTwo (s.take (2*k)) := by
  simp only [List.ext_getElem_iff, length_divTwo, List.length_take, Nat.inf_div,
    mul_div_cancel_left₀ _ (two_ne_zero), lt_inf_iff,  true_and, List.getElem_take,
    getElem_divTwo, implies_true]

theorem drop_divTwo : s.divTwo.drop k = divTwo (s.drop (2*k)) := by
  simp only [List.ext_getElem_iff, length_divTwo, List.length_drop, Nat.inf_div,
    mul_div_cancel_left₀ _ (two_ne_zero), lt_inf_iff,  true_and, List.getElem_drop,
    getElem_divTwo, implies_true, Nat.sub_mul_div', mul_add, add_assoc]

end DivTwo

def divModTwo (l : List α) : Option α × List (α × α) :=
  l.doubleRec (none, []) (some · , []) (fun l r _ (mts, dts) => (mts, (l, r) :: dts))

@[simp] theorem divModTwo_nil : divModTwo ([] : List α) = (none, []) := rfl
@[simp] theorem divModTwo_singleton : divModTwo [a] = (some a, []) := rfl
@[simp] theorem divModTwo_cons_cons : divModTwo (l :: r :: s) =
    ((divModTwo s).1, (l, r) :: (divModTwo s).2) := rfl

section DivModTwo

@[simp] theorem divModTwo_eq_divTwo_modTwo {s : List α} : divModTwo s = (modTwo s, divTwo s) :=
    s.doubleRec rfl (fun _ => rfl) (fun _ _ _ h => by
      simp_rw [divModTwo_cons_cons, h, modTwo_cons_cons, divTwo_cons_cons])

theorem divTwo_append_singleton :
    divTwo (s ++ [b]) = divTwo s ++ s.modTwo.toList.map (·, b) := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [List.nil_append, divTwo_singleton, divTwo_nil, modTwo_nil, Option.toList_none,
      List.map_nil, List.append_nil]
  · simp_rw [divTwo_singleton, modTwo_singleton, List.singleton_append, divTwo_cons_cons,
      divTwo_nil, Option.toList_some, List.map_singleton, List.nil_append]
  · simp only [List.cons_append, divTwo_cons_cons, IH, modTwo_cons_cons]

end DivModTwo

def mulTwo (s : List (α × α)) : List α := s.flatMap (fun ⟨x, y⟩ => [x, y])

section MulTwo

@[simp] theorem mulTwo_nil : mulTwo ([] : List (α × α)) = [] := rfl
@[simp] theorem mulTwo_cons : mulTwo (lr :: ss) = lr.1 :: lr.2 :: mulTwo ss := rfl

end MulTwo

def bit :  Option α → List (α × α) → List α
  | ao, [] => ao.toList
  | ao, (lr :: ss) => lr.1 :: lr.2 :: bit ao ss

section Bit

@[simp] theorem bit_nil : bit ao ([] : List (α × α)) = ao.toList := rfl
@[simp] theorem bit_none_nil : bit none ([] : List (α × α)) = [] := rfl
@[simp] theorem bit_some_nil : bit (some a) ([] : List (α × α)) = [a] := rfl
@[simp] theorem bit_cons : bit ao (lr :: ss) = lr.1 :: lr.2 :: bit ao ss := rfl

end Bit

section BitDivTwoModTwoMulTwo

@[simp]
theorem bit_modTwo_divTwo : bit s.modTwo s.divTwo = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [modTwo_nil, divTwo_nil, bit_none_nil]
  · simp_rw [modTwo_singleton, divTwo_singleton, bit_some_nil]
  · simp_rw [modTwo_cons_cons, divTwo_cons_cons, bit_cons, IH]

theorem divTwo_bit : (bit ao ss).divTwo = ss := by
  induction ss with | nil => _ | cons a ss IH => _
  · cases ao
    · simp_rw [bit_none_nil, divTwo_nil]
    · simp_rw [bit_some_nil, divTwo_singleton]
  · simp_rw [bit_cons, divTwo_cons_cons, IH]

theorem modTwo_bit : (bit ao ss).modTwo = ao := by
  induction ss with | nil => _ | cons a ss IH => _
  · cases ao
    · simp_rw [bit_none_nil, modTwo_nil]
    · simp_rw [bit_some_nil, modTwo_singleton]
  · simp_rw [bit_cons, modTwo_cons_cons, IH]

end BitDivTwoModTwoMulTwo

abbrev PairRec (α : Type u) : ℕ → Type u
  | 0 => α
  | (n + 1) => PairRec α n × PairRec α n

instance instPairRecRepr [h : Repr α] : (n : ℕ) → Repr (PairRec α n)
  | 0 => h
  | (n + 1) => haveI := (instPairRecRepr n) ; inferInstance

abbrev SigmaPairRec (α : Type u) := (n : ℕ) × PairRec α n

def listToStack (n : ℕ) : List (PairRec α n) → List ((n : ℕ) × PairRec α n)
  | [] => []
  | [a] => [⟨n, a⟩]
  | l :: r :: s => ((modTwo s).elim (·) (⟨n, ·⟩ :: ·)) (listToStack (n + 1) ((l, r) :: divTwo s))
  termination_by s => s.length
  decreasing_by all_goals exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

section LiftToStack

variable {a l r : PairRec α n} {s : List (PairRec α n)}


@[simp]
theorem listToStack_nil : listToStack n ([] : List (PairRec α n)) = [] := by rw [listToStack]

@[simp]
theorem listToStack_nil_zero : listToStack 0 ([] : List α) = [] := by rw [listToStack]

@[simp]
theorem listToStack_nil_succ : listToStack (n + 1)
    ([] : List (PairRec α n × PairRec α n)) = [] := by rw [listToStack]


@[simp]
theorem listToStack_singleton  : listToStack n [a] = [⟨n, a⟩] := by
  rw [listToStack]


theorem listToStack_cons_cons :
    listToStack n (l :: r :: s) =
    ((modTwo s).elim (·) (⟨n, ·⟩ :: ·)) (listToStack (n + 1) ((l, r) :: divTwo s)) := by
  rw [listToStack]


@[simp]
theorem listToStack_cons_cons_of_modTwo_none (hs : modTwo s = none) :
    listToStack n (l :: r :: s) = listToStack (n + 1) ((l, r) :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_none]

@[simp]
theorem listToStack_cons_cons_of_modTwo_some (hs : modTwo s = some a) :
    listToStack n (l :: r :: s) = ⟨n, a⟩ :: listToStack (n + 1) ((l, r) :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_some]

theorem listToStack_of_modTwo_some (hs : modTwo s = some a) :
    listToStack n s = ⟨n, a⟩ :: (divTwo s).listToStack (n + 1) := by
  fun_induction listToStack
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    subst hs
    simp_rw [listToStack_singleton, divTwo_singleton, listToStack_nil_succ]

  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [listToStack_cons_cons_of_modTwo_some hs, divTwo_cons_cons]

theorem listToStack_of_modTwo_none (hs : modTwo s = none) :
    listToStack s = (divTwo s).listToStack := by
  fun_induction listToStack
  · simp_rw [divTwo_nil]
  · contradiction
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [listToStack_cons_cons_of_modTwo_none hs, divTwo_cons_cons]

theorem listToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    listToStack (s ++ [a]) = a :: listToStack s := by
  rw [listToStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, listToStack_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    listToStack (s ++ [b]) = listToStack (s.divTwo ++ [node a b]) := by
  rw [listToStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

end LiftToStack

#eval (listToStack (α := ℕ) 0 [0, 1, 2, 3, 4, 5, 6])

theorem length_take_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.take n).length = n := length_take_of_le (hl ▸ Nat.le_add_right _ _)

theorem length_drop_of_length_eq_add (l : List α) (hl : l.length = n + m) :
  (l.drop n).length = m := length_drop _ _ ▸ (hl ▸ add_tsub_cancel_left _ _)

end List

inductive BTree (α : Type u) : Type u where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
deriving Repr, DecidableEq, Inhabited

namespace BTree

variable {α : Type u} {β : Type v} {a b : α} {t l r : BTree α} {n : ℕ}

instance [IsEmpty α] : IsEmpty (BTree α) := ⟨fun t => t.recOn isEmptyElim (fun _ _ C => C.elim)⟩

instance [Nonempty α] : Infinite (BTree α) :=
  Infinite.of_injective (fun (i : ℕ) =>
    i.recOn (leaf (Classical.arbitrary _)) (fun _ t => node t t))
    (fun i => i.recOn (fun j => j.recOn (fun _ => rfl)
    (fun _ _ C => BTree.noConfusion C))
    (fun _ IH j => j.recOn (fun C => BTree.noConfusion C)
    fun _ _ H => congrArg _ (IH (node.injEq _ _ _ _ ▸ H).1)))

theorem leaf_inj_iff : leaf a = leaf a' ↔ a = a' := by simp_rw [leaf.injEq]

theorem node_inj_iff : node l r = node l' r' ↔ (l = l' ∧ r = r') := by
  simp_rw [node.injEq]

@[simp] theorem node_ne_leaf : node l r ≠ leaf a := BTree.noConfusion

@[simp] theorem leaf_ne_node : leaf a ≠ node l r := BTree.noConfusion


def height : BTree α → ℕ
  | leaf _ => 0
  | (node l r) => max l.height r.height + 1

section Height

@[simp] theorem height_leaf : (leaf a).height = 0 := rfl

@[simp] theorem height_node : (node l r).height = max l.height r.height + 1 := rfl

theorem height_eq_zero_iff : t.height = 0 ↔ ∃ a, t = leaf a := by
  cases t
  · simp_rw [height_leaf, leaf_inj_iff, exists_eq']
  · simp_rw [height_node, Nat.succ_ne_zero, node_ne_leaf, exists_false]

instance : NeZero (node l r).height := ⟨Nat.noConfusion⟩

theorem height_eq_succ_iff :
    (node l r).height = n + 1 ↔
    ((l.height = n ∧ r.height ≤ l.height) ∨ (r.height = n ∧ l.height ≤ r.height)) := by
  simp_rw [height_node, add_left_inj, max_eq_iff]

theorem height_left_eq_of_node_eq_succ_of_height_eq_height (hn : (node l r).height = n + 1)
    (hlr : l.height = r.height) : l.height = n := by
  simp_rw [height_eq_succ_iff, hlr.symm, le_refl, and_true, or_self] at hn
  exact hn

theorem height_right_eq_of_node_eq_succ_of_height_eq_height (hn : (node l r).height = n + 1)
    (hlr : l.height = r.height) : r.height = n := by
  simp_rw [height_eq_succ_iff, hlr, le_refl, and_true, or_self] at hn
  exact hn

theorem height_node_of_height_le (hlr : r.height ≤ l.height) :
    (node l r).height = l.height + 1 := height_node ▸ (Nat.max_eq_left hlr).symm ▸ rfl

theorem height_node_of_height_ge (hlr : l.height ≤ r.height) :
    (node l r).height = r.height + 1 := height_node ▸ (Nat.max_eq_right hlr).symm ▸ rfl

theorem height_node_of_heights_eq (hl : l.height = n) (hr : r.height = n) :
    (node l r).height = n + 1 := by
  simp_rw [height_eq_succ_iff, hl, hr, le_refl, true_and, true_or]

theorem left_height_lt : l.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_left _ _

theorem right_height_lt : r.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_right _ _

end Height

inductive IsPerfectOfHeight : ℕ → BTree α → Prop where
  | zero_leaf {a} : IsPerfectOfHeight 0 (leaf a)
  | succ_node {n l r} : l.IsPerfectOfHeight n →
    r.IsPerfectOfHeight n → IsPerfectOfHeight (n + 1) (node l r)

section IsPerfectOfHeight

open IsPerfectOfHeight

@[simp] theorem not_succ_leaf : ¬ (leaf a).IsPerfectOfHeight (n + 1) := fun h => nomatch h
@[simp] theorem not_zero_node : ¬ (node l r).IsPerfectOfHeight 0 := fun h => nomatch h

theorem IsPerfectOfHeight.left_of_succ_node (h : (node l r).IsPerfectOfHeight (n + 1)) :
    l.IsPerfectOfHeight n := match h with | succ_node hl _ => hl

theorem IsPerfectOfHeight.right_of_succ_node (h : (node l r).IsPerfectOfHeight (n + 1)) :
    r.IsPerfectOfHeight n := match h with | succ_node _ hr => hr

theorem succ_node_iff : (node l r).IsPerfectOfHeight (n + 1) ↔
    l.IsPerfectOfHeight n ∧ r.IsPerfectOfHeight n :=
  ⟨fun h => ⟨left_of_succ_node h, right_of_succ_node h⟩, fun h => succ_node h.1 h.2⟩

instance instDecidableIsPerfectOfHeight : (n : ℕ) → (t : BTree α) →
  Decidable (IsPerfectOfHeight n t)
  | 0, leaf _ => isTrue zero_leaf
  | (_ + 1), leaf _ => isFalse not_succ_leaf
  | 0, node _ _ => isFalse not_zero_node
  | (n + 1), node l r =>
    match instDecidableIsPerfectOfHeight n l with
    | isFalse hl => isFalse (left_of_succ_node.mt hl)
    | isTrue hl => match instDecidableIsPerfectOfHeight n r with
      | isFalse hr => isFalse (right_of_succ_node.mt hr)
      | isTrue hr => isTrue (succ_node hl hr)

theorem IsPerfectOfHeight.height_eq (h : t.IsPerfectOfHeight n) : t.height = n := by
  induction t generalizing n with | leaf _ => _ | node l r IHL IHR => _  <;> cases n
  · rfl
  · contradiction
  · contradiction
  · simp_rw [succ_node_iff] at h
    simp_rw [height_node, Nat.succ_inj, max_eq_iff]
    exact (Nat.le_total r.height l.height).imp
      (fun hlr => ⟨IHL h.1, hlr⟩ ) (fun hlr => ⟨IHR h.2, hlr⟩)

theorem false_of_ne_height : t.height ≠ n → ¬ t.IsPerfectOfHeight n := height_eq.mt

theorem IsPerfectOfHeight.height_eq_height_of_node (h : (node l r).IsPerfectOfHeight n) :
    l.height = r.height := by
  cases n with | zero => _ | succ n => _
  · contradiction
  · simp_rw [succ_node_iff] at h
    simp_rw [height_eq h.1, height_eq h.2]

theorem not_node_of_height_ne : l.height ≠ r.height → ¬ (node l r).IsPerfectOfHeight n :=
  height_eq_height_of_node.mt

end IsPerfectOfHeight

def IsPerfect (t : BTree α) : Prop := t.IsPerfectOfHeight t.height

section IsPerfect

open IsPerfectOfHeight

theorem IsPerfect_def : t.IsPerfect ↔ t.IsPerfectOfHeight t.height := Iff.rfl

instance : DecidablePred (IsPerfect (α := α)) :=
  fun _ => decidable_of_decidable_of_iff IsPerfect_def.symm

theorem IsPerfectOfHeight_iff_isPerfect_and_height_eq :
    t.IsPerfectOfHeight n ↔ t.IsPerfect ∧ t.height = n := by
  rw [t.IsPerfect_def]
  exact ⟨fun h => ⟨h.height_eq ▸ h, h.height_eq ▸ rfl⟩, fun h => h.2 ▸ h.1⟩

@[simp] theorem IsPerfect_leaf : (leaf a).IsPerfect := IsPerfectOfHeight.zero_leaf

theorem IsPerfect_node_of_height_eq_height (h : l.height = r.height) :
    (node l r).IsPerfect ↔ l.IsPerfect ∧ r.IsPerfect := by
  simp_rw [IsPerfect_def, height_node, succ_node_iff, h, max_self]

@[simp] theorem IsPerfect_node_iff : (node l r).IsPerfect ↔
    l.IsPerfect ∧ r.IsPerfect ∧ l.height = r.height := by
  simp_rw [IsPerfect_def, height_node, succ_node_iff]
  by_cases h : l.height = r.height
  · simp_rw [h, max_self, and_true]
  · simp_rw [h, and_false]
    rcases Ne.lt_or_lt h with h | h
    · simp_rw [max_eq_right_of_lt h, false_of_ne_height h.ne, false_and]
    · simp_rw [max_eq_left_of_lt h, false_of_ne_height h.ne, and_false]

theorem IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq
    (hl : l.IsPerfect) (hr : r.IsPerfect) (hl₂ : l.height = n) (hr₂ : r.height = n) :
    (node l r).IsPerfect := IsPerfect_node_iff.mpr ⟨hl, hr, hl₂ ▸ hr₂ ▸ rfl⟩

theorem IsPerfect.node_of_IsPerfect_right_of_height_eq_height
    (hl : l.IsPerfect) (hr : r.IsPerfect) (hlr : l.height = r.height) :
    (node l r).IsPerfect := IsPerfect_node_iff.mpr ⟨hl, hr, hlr⟩

theorem IsPerfect.node_of_IsPerfect_left_of_heights_eq
    (hr : r.IsPerfect) (hl : l.IsPerfect)
    (hlr : l.height = r.height) :
    (node l r).IsPerfect := IsPerfect_node_iff.mpr ⟨hl, hr, hlr⟩

theorem IsPerfect.left (hlr : (node l r).IsPerfect) : l.IsPerfect :=
  (IsPerfect_node_iff.mp hlr).1
theorem IsPerfect.right (hlr : (node l r).IsPerfect) : r.IsPerfect :=
  (IsPerfect_node_iff.mp hlr).2.1
theorem IsPerfect.height_eq_height (hlr : (node l r).IsPerfect) : l.height = r.height :=
  (IsPerfect_node_iff.mp hlr).2.2
theorem IsPerfect.double_node (h : l.IsPerfect) : (node l l).IsPerfect :=
  IsPerfect_node_iff.mpr ⟨h, h, rfl⟩

theorem IsPerfect.height_eq_left_succ (hlr : (node l r).IsPerfect) :
    (node l r).height = l.height + 1 := height_node ▸ hlr.height_eq_height ▸ Nat.max_self _ ▸ rfl
theorem IsPerfect.height_eq_right_succ (hlr : (node l r).IsPerfect) :
    (node l r).height = r.height + 1 := height_node ▸ hlr.height_eq_height ▸ Nat.max_self _ ▸ rfl

end IsPerfect


def count : BTree α → ℕ
  | leaf _ => 1
  | node l r => l.count + r.count

section Count

@[simp] theorem count_leaf : (leaf a).count = 1 := rfl

@[simp] theorem count_node : (node l r).count = l.count + r.count := rfl

theorem height_lt_count : t.height < t.count := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · exact zero_lt_one
  · rcases Nat.exists_eq_add_of_lt IHL with ⟨nl, hl⟩
    rcases Nat.exists_eq_add_of_lt IHR with ⟨nr, hr⟩
    simp_rw [height_node, count_node, hl,  hr, ← add_assoc, Nat.succ_lt_succ_iff,
      max_lt_iff]
    exact ⟨by linarith, by linarith⟩

theorem succ_height_le_count : t.height + 1 ≤ t.count := height_lt_count

instance : NeZero t.count := ⟨Nat.ne_zero_of_lt height_lt_count⟩

theorem count_le_two_pow_height : t.count ≤ 2^t.height := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [count_leaf, height_leaf, pow_zero, le_refl]
  · simp_rw [count_node, height_node, pow_succ', two_mul]
    exact Nat.add_le_add
      (IHL.trans (Nat.pow_le_pow_of_le one_lt_two (le_max_left _ _)))
      (IHR.trans (Nat.pow_le_pow_of_le one_lt_two (le_max_right _ _)))

theorem IsPerfect.count_eq_two_pow_height (ht : t.IsPerfect) : t.count = 2^t.height := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [count_leaf, height_leaf, pow_zero]
  · simp_rw [IsPerfect_node_iff] at ht
    simp_rw [count_node, height_node, pow_succ', two_mul, ht.2.2, IHL ht.1, IHR ht.2.1, ht.2.2,
      max_self]

end Count


def skeleton : BTree α → BTree Unit
  | leaf _ => leaf ()
  | node l r => node l.skeleton r.skeleton

section Skeleton

@[simp] theorem skeleton_leaf : (leaf a).skeleton = leaf () := rfl

@[simp] theorem skeleton_node : (node l r).skeleton = node l.skeleton r.skeleton := rfl

end Skeleton

def replicate {α : Type u} (a : α) : BTree Unit → BTree α
  | leaf () => leaf a
  | node l r => node (l.replicate a) (r.replicate a)

section Replicate

variable {l r : BTree Unit}

@[simp] theorem replicate_leaf : (leaf ()).replicate a = leaf a := rfl

@[simp] theorem replicate_node :
    (node l r).replicate a = node (l.replicate a) (r.replicate a) := rfl

end Replicate

def flatMap : BTree α → (α → BTree β) → BTree β
  | leaf a, f => f a
  | node l r, f => node (l.flatMap f) (r.flatMap f)

section FlatMap

variable {f : α → BTree β}

@[simp] theorem flatMap_leaf : (leaf a).flatMap f = f a := rfl

@[simp] theorem flatMap_node : (node l r).flatMap f = node (l.flatMap f) (r.flatMap f) := rfl

theorem flatMap_flatMap {g : β → BTree γ} :
    (t.flatMap f).flatMap g = t.flatMap (fun x => (f x).flatMap g) := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem flatMap_leaf_right : t.flatMap leaf = t := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

end FlatMap

def map (f : α → β) : BTree α →  BTree β
  | leaf a => leaf (f a)
  | node l r => node (l.map f) (r.map f)

section Map

variable {f : α → β} {g : β → γ}

@[simp] theorem map_leaf : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_node : (node l r).map f = node (l.map f) (r.map f) := rfl

@[simp] theorem id_map : map id t = t := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem comp_map : map (g ∘ f) t = map g (map f t) := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem flatMap_leaf_comp : t.flatMap (leaf ∘ f) = t.map f := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

end Map

def flatten : BTree (BTree α) → BTree α
  | leaf a => a
  | node l r => node (l.flatten) (r.flatten)

section Flatten

variable {t l r : BTree (BTree α )} {a : BTree α}

@[simp] theorem flatten_leaf : (leaf a).flatten = a := rfl

@[simp] theorem flatten_node : (node l r).flatten = node l.flatten r.flatten := rfl

@[simp] theorem flatMap_id : t.flatMap id = t.flatten := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

end Flatten

def mapConst (a : α) : BTree β → BTree α
  | leaf _ => leaf a
  | node l r => node (l.mapConst a) (r.mapConst a)

section MapConst

variable {b : β} {t : BTree β}

@[simp] theorem mapConst_leaf : (leaf b).mapConst a = leaf a := rfl

@[simp] theorem mapConst_node {l r : BTree β} :
    (node l r).mapConst a = node (l.mapConst a) (r.mapConst a) := rfl

@[simp] theorem map_const : t.map (Function.const β a) = t.mapConst a := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem map_comp_const : map ∘ Function.const β = mapConst (α := α) :=
  funext (fun _ => funext fun _ => map_const)

@[simp] theorem replicate_skeleton : replicate a t.skeleton = t.mapConst a := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

theorem flatMap_const_leaf : t.flatMap (Function.const _ (leaf a)) = t.mapConst a := by
  induction t
  · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

end MapConst

def seq : BTree (α → β) → BTree α →  BTree β
  | leaf f, leaf a => leaf (f a)
  | leaf f, node l r => node (l.map f) (r.map f)
  | node l r, t => node (l.seq t) (r.seq t)

section Seq

variable {sf : BTree (α → β)} {f : α → β}

@[simp] theorem seq_leaf_leaf : (leaf f).seq (leaf a) = leaf (f a) := rfl

@[simp] theorem seq_leaf_node : (leaf f).seq (node l r) = node (l.map f) (r.map f) := rfl

@[simp] theorem seq_node {l r : BTree (α → β)} :
    (node l r).seq t = node (l.seq t) (r.seq t) := rfl

@[simp] theorem leaf_seq : (leaf f).seq t = t.map f := by cases t <;> rfl

@[simp] theorem flatMap_map : sf.flatMap (t.map ·) = sf.seq t := by
  induction sf
  · cases t
    · rfl
    · rfl
  · exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

theorem flatMap_flatMap_leaf_comp : sf.flatMap (fun f => t.flatMap (leaf ∘ f)) = sf.seq t :=
  (congrArg _ (funext fun _ => flatMap_leaf_comp)).trans flatMap_map

end Seq

def seqLeft : BTree α → BTree β → BTree α
  | leaf a, leaf _ => leaf a
  | node l r, leaf _ => node l r
  | leaf a, node l r => node (l.mapConst a) (r.mapConst a)
  | node l r, node l' r' => node (l.seqLeft (l'.node r')) (r.seqLeft (l'.node r'))

section SeqLeft

variable {b : β} {s : BTree β}

@[simp] theorem seqLeft_leaf_right : t.seqLeft (leaf b) = t := by
  cases t <;> rfl

@[simp] theorem seqLeft_leaf_left : (leaf a).seqLeft s = s.mapConst a := by
  cases s <;> rfl

@[simp] theorem seqLeft_leaf_node {l r : BTree β} : (leaf a).seqLeft (node l r) =
    node (l.mapConst a) (r.mapConst a) := rfl

@[simp] theorem seqLeft_node_left :
    (node l r).seqLeft s = node (l.seqLeft s) (r.seqLeft s) := by
  cases s
  · simp_rw [seqLeft_leaf_right]
  · rfl

@[simp] theorem flatMap_mapConst : t.flatMap (s.mapConst ·) = t.seqLeft s := by
  induction t
  · simp only [flatMap_leaf, seqLeft_leaf_left]
  · simp only [flatMap_node, seqLeft_node_left]
    exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem map_const_seq : (map (Function.const β) t).seq s = t.seqLeft s := by
  induction t
  · simp only [map_leaf, leaf_seq, map_const, seqLeft_leaf_left]
  · simp only [flatMap_node, seqLeft_node_left]
    exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

theorem flatMap_flatMap_const_leaf :
    t.flatMap (fun a => s.flatMap (Function.const _ (leaf a))) = t.seqLeft s :=
  (congrArg _ (funext (fun _ => flatMap_const_leaf))).trans flatMap_mapConst

end SeqLeft

def seqRight : BTree α → BTree β → BTree β
  | leaf _, leaf b => leaf b
  | leaf _, node l r => node l r
  | node l r, leaf b => node (l.mapConst b) (r.mapConst b)
  | node l r, node l' r' => node (l.seqRight (node l' r')) (r.seqRight (node l' r'))

section SeqRight

variable {b : β} {s : BTree β}

@[simp] theorem seqRight_leaf_left : (leaf a).seqRight s = s := by cases s <;> rfl

@[simp] theorem seqRight_leaf_right : t.seqRight (leaf b) = t.mapConst b := by cases t <;> rfl

@[simp] theorem seqRight_node_leaf : (node l r).seqRight (leaf b) =
    node (l.mapConst b) (r.mapConst b) := rfl

@[simp] theorem seqRight_node_left : (node l r).seqRight s =
    node (l.seqRight s) (r.seqRight s) := by
  cases s
  · simp_rw [seqRight_leaf_right, mapConst_node]
  · rfl

@[simp] theorem flatMap_const : t.flatMap (Function.const _ s) = t.seqRight s := by
  induction t
  · simp only [flatMap_leaf, Function.const_apply, seqRight_leaf_left]
  · simp only [flatMap_node, seqRight_node_left]
    exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

@[simp] theorem mapConst_id_seq : (mapConst id t).seq s = t.seqRight s := by
  induction t
  · simp only [mapConst_leaf, leaf_seq, id_map, seqRight_leaf_left]
  · simp only [mapConst_node, seq_node, seqRight_node_left]
    exact node_inj_iff.mpr ⟨by assumption, by assumption⟩

theorem map_const_id_seq : (map (Function.const _ id) t).seq s = t.seqRight s := by
  simp_rw [map_const, mapConst_id_seq]

end SeqRight

instance : Monad BTree where
  pure := leaf
  bind := flatMap
  map := map
  mapConst := mapConst
  seq t s := t.seq (s ())
  seqLeft t s := t.seqLeft (s ())
  seqRight t s := t.seqRight (s ())

section Monad

variable {α  β : Type u} {a : α} {t : BTree α} {s : BTree β} {sf : BTree (α → β)}
  {tt : BTree (BTree α)}

@[simp] theorem pure_eq_leaf : pure a = leaf a := rfl

@[simp] theorem bind_eq_flatMap : t >>= f = t.flatMap f := rfl

@[simp] theorem map_eq_map {f : α → β} : f <$> t = t.map f := rfl

@[simp] theorem seqLeft_eq_seqLeft : t <* s = t.seqLeft s := rfl

@[simp] theorem seqRight_eq_seqRight : t *> s = t.seqRight s := rfl

@[simp] theorem seq_eq_seq : sf <*> t = sf.seq t := rfl

@[simp] theorem mapConst_eq_replicate_skeleton {a : β} :
    Functor.mapConst a t = t.mapConst a := rfl

@[simp] theorem join_eq_flatten : Monad.join tt = tt.flatten := flatMap_id

instance : LawfulMonad BTree where
  map_const := map_comp_const.symm
  id_map _ := id_map
  seqLeft_eq _ _ := map_const_seq.symm
  seqRight_eq _ _ := map_const_id_seq.symm
  pure_seq _ _ := leaf_seq
  bind_pure_comp _ _ := flatMap_leaf_comp
  bind_map _ _ := flatMap_map
  pure_bind _ _ := flatMap_leaf
  bind_assoc _ _ _ := flatMap_flatMap

end Monad

end BTree

abbrev BTStack (α : Type u) := List (BTree α)
namespace BTStack

variable {s t : BTStack α} {a b l r : BTree α} {v : α}

open BTree

def count (s : BTStack α) : ℕ := s.foldr (BTree.count · + ·) 0

section count

@[simp] theorem count_nil : count ([] : BTStack α) = 0 := rfl
@[simp] theorem count_cons : count (a :: s) = a.count + count s := rfl

theorem count_singleton : count [a] = a.count := rfl

theorem count_append_singleton : count (s ++ [a]) = s.count + a.count := by
  induction s with | nil => _ | cons b t IH => _
  · simp_rw [List.nil_append, count_nil, count_singleton, zero_add]
  · simp_rw [List.cons_append, count_cons, IH, add_assoc]

theorem count_append : count (s ++ t) = s.count + t.count := by
  induction t generalizing s with | nil => _ | cons a t IH => _
  · simp_rw [List.append_nil, count_nil, add_zero]
  · rw [List.append_cons, IH, count_append_singleton, count_cons, add_assoc]

end count


def IsSMH (s : BTStack α) := s.Sorted (fun a b => a.height < b.height)

section IsSMH

instance : DecidableRel (fun (a : BTree α) (b : BTree α) => a.height < b.height) :=
    fun a b => a.height.decLt b.height

instance : Decidable (IsSMH s) := List.decidableSorted _

@[simp] theorem IsSMH_nil : IsSMH (α := α) [] := List.sorted_nil

@[simp] theorem IsSMH_cons_iff : IsSMH (a :: s) ↔ (∀ b ∈ s, a.height < b.height) ∧ IsSMH s :=
  List.pairwise_cons

@[simp] theorem IsSMH_singleton : IsSMH [a] := List.sorted_singleton _

@[simp] theorem IsSMH_append_iff : IsSMH (s ++ t) ↔
  IsSMH s ∧ IsSMH t ∧ ∀ a ∈ s, ∀ b ∈ t, a.height < b.height := List.pairwise_append

@[simp] theorem IsSMH_append_singleton_iff : IsSMH (s ++ [a]) ↔ IsSMH s ∧
    (∀ b ∈ s, b.height < a.height) := by
  simp_rw [IsSMH_append_iff, IsSMH_singleton, List.mem_singleton, forall_eq, true_and]


@[simp] theorem IsSMH.cons_of (h : ∀ b ∈ s, a.height < b.height) (hsh : IsSMH s):
    IsSMH (a :: s) := IsSMH_cons_iff.mpr ⟨h, hsh⟩

@[simp] theorem IsSMH.append_singleton_of (hsh : IsSMH s) (h : ∀ b ∈ s, b.height < a.height) :
    IsSMH (s ++ [a]) := IsSMH_append_singleton_iff.mpr ⟨hsh, h⟩

theorem IsSMH.of_cons : IsSMH (a :: s) → IsSMH s := And.right ∘ IsSMH_cons_iff.mp

theorem IsSMH.of_append_singleton : IsSMH (s ++ [a]) → IsSMH s := And.left ∘ IsSMH_append_singleton_iff.mp

theorem IsSMH.cons_height_lt_height_of_mem : IsSMH (a :: s) →
    ∀ b ∈ s, a.height < b.height := And.left ∘ IsSMH_cons_iff.mp

theorem IsSMH.cons_height_le_height_of_mem (hsh : IsSMH (a :: s)) :
    ∀ b ∈ s, a.height ≤ b.height := fun _ hb => (hsh.cons_height_lt_height_of_mem _ hb).le

theorem IsSMH.height_lt_append_singleton_height_of_mem : IsSMH (s ++ [a]) →
    ∀ b ∈ s, b.height < a.height := And.right ∘ IsSMH_append_singleton_iff.mp

theorem IsSMH.height_le_append_singleton_height_of_mem (hsh : IsSMH (s ++ [a])) :
    ∀ b ∈ s, b.height ≤ a.height := fun _ hb => (hsh.height_lt_append_singleton_height_of_mem _ hb).le

theorem IsSMH.cons_of_cons {b : BTree α} (hab : a.height < b.height) (hsh : IsSMH (b :: s)) :
    IsSMH (a :: s) := IsSMH.cons_of
  (fun _ hb => hab.trans <| hsh.cons_height_lt_height_of_mem _ hb) hsh.of_cons

theorem IsSMH.cons_cons {b : BTree α} (hab : a.height < b.height) (hsh : IsSMH (b :: s)) :
    IsSMH (a :: (b :: s)) := hsh.cons_of
    (fun _ hb => (List.mem_cons.mp hb).elim (fun h => h ▸ hab)
    (fun hb => hab.trans <| hsh.cons_height_lt_height_of_mem _ hb))

theorem IsSMH.append_singleton_of_append_singleton {b : BTree α} (hba : b.height < a.height) (hsh : IsSMH  (s ++ [b])) :
    IsSMH (s ++ [a]) := IsSMH.append_singleton_of
  hsh.of_append_singleton (fun _ hb => hba.trans' <| hsh.height_lt_append_singleton_height_of_mem _ hb)

theorem IsSMH.append_singleton_append_singleton {b : BTree α} (hba : b.height < a.height) (hsh : IsSMH (s ++ [b])) :
    IsSMH ((s ++ [b]) ++ [a]) := hsh.append_singleton_of
    (fun _ hb => (List.mem_append.mp hb).elim
    (fun hb => hba.trans' <| hsh.height_lt_append_singleton_height_of_mem _ hb)
    (fun h => List.eq_of_mem_singleton h ▸ hba))

theorem IsSMH.cons_height_lt_append_singleton_height {b : BTree α}
      (hsh : IsSMH (a :: (s ++ [b]))) : a.height < b.height :=
      hsh.cons_height_lt_height_of_mem _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem IsSMH.cons_height_lt_append_singleton_height' {b : BTree α}
      (hsh : IsSMH ((a :: s) ++ [b])) : a.height < b.height :=
      hsh.height_lt_append_singleton_height_of_mem _ (List.mem_cons_self _ _)

end IsSMH

def IsPerfectOfHeight (n : ℕ) (s : BTStack α) := s.Forall (BTree.IsPerfectOfHeight n)

section IsPerfectOfHeight

@[simp] theorem IsPerfectOfHeight_iff : IsPerfectOfHeight n s ↔
    ∀ b ∈ s, b.IsPerfectOfHeight n := List.forall_iff_forall_mem

@[simp] theorem IsPerfectOfHeight_nil : IsPerfectOfHeight n ([] : BTStack α) := trivial

@[simp] theorem IsPerfectOfHeight_cons_iff :
    IsPerfectOfHeight n (a :: s) ↔ a.IsPerfectOfHeight n ∧ IsPerfectOfHeight n s := List.forall_cons _ _ _

@[simp] theorem IsPerfectOfHeight.of_cons_head :
  IsPerfectOfHeight n (a :: s) → a.IsPerfectOfHeight n := fun h => (IsPerfectOfHeight_cons_iff.mp h).1
@[simp] theorem IsPerfectOfHeight.of_cons_tail :
    IsPerfectOfHeight n (a :: s) → IsPerfectOfHeight n s := fun h => (IsPerfectOfHeight_cons_iff.mp h).2

theorem IsPerfectOfHeight.cons_of (ha : a.IsPerfectOfHeight n) :
    IsPerfectOfHeight n s → IsPerfectOfHeight n (a :: s) :=
  fun h => IsPerfectOfHeight_cons_iff.mpr ⟨ha, h⟩

@[simp] theorem IsPerfectOfHeight_append :
    IsPerfectOfHeight n (s ++ t) ↔ IsPerfectOfHeight n s ∧ IsPerfectOfHeight n t := by
  simp_rw [IsPerfectOfHeight_iff, List.mem_append, or_imp, forall_and]

@[simp] theorem IsPerfectOfHeight_singleton_iff :
    IsPerfectOfHeight n [a] ↔ a.IsPerfectOfHeight n := by
  simp_rw [IsPerfectOfHeight_iff, List.mem_singleton, forall_eq]

@[simp] theorem IsPerfectOfHeight_append_singleton_iff :
    IsPerfectOfHeight n (s ++ [a]) ↔ IsPerfectOfHeight n s ∧ a.IsPerfectOfHeight n := by
  simp_rw [IsPerfectOfHeight_append, IsPerfectOfHeight_singleton_iff]

end IsPerfectOfHeight

def IsPerfect (s : BTStack α) := s.Forall (BTree.IsPerfect)

section IsPerfect

@[simp] theorem IsPerfect_iff : IsPerfect s ↔ ∀ b ∈ s, b.IsPerfect := List.forall_iff_forall_mem

@[simp] theorem IsPerfect_nil : IsPerfect ([] : BTStack α) := trivial

@[simp] theorem IsPerfect_cons_iff : IsPerfect (a :: s) ↔ a.IsPerfect ∧ IsPerfect s :=
  List.forall_cons _ _ _

@[simp] theorem IsPerfect.of_cons_head : IsPerfect (a :: s) → a.IsPerfect :=
  fun h => (IsPerfect_cons_iff.mp h).1
@[simp] theorem IsPerfect.of_cons_tail : IsPerfect (a :: s) → IsPerfect s :=
  fun h => (IsPerfect_cons_iff.mp h).2

theorem IsPerfect.cons_of (ha : a.IsPerfect) : IsPerfect s → IsPerfect (a :: s) :=
  fun h => IsPerfect_cons_iff.mpr ⟨ha, h⟩

@[simp] theorem IsPerfect_append :
    IsPerfect (s ++ t) ↔ IsPerfect s ∧ IsPerfect t := by
  simp_rw [IsPerfect_iff, List.mem_append, or_imp, forall_and]

@[simp] theorem IsPerfect_singleton_iff : IsPerfect [a] ↔ a.IsPerfect := by
  simp_rw [IsPerfect_iff, List.mem_singleton, forall_eq]

@[simp] theorem IsPerfect_append_singleton_iff :
    IsPerfect (s ++ [a]) ↔ IsPerfect s ∧ a.IsPerfect := by
  simp_rw [IsPerfect_append, IsPerfect_singleton_iff]

end IsPerfect

def modTwo : BTStack α → Option (BTree α)
  | [] => none
  | [a] => some a
  | _ :: _ :: s => modTwo s

section ModTwo

@[simp] theorem modTwo_nil : modTwo ([] : BTStack α) = none := rfl
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

def divTwo : BTStack α → BTStack α
  | [] => []
  | [_] => []
  | l :: r :: s => node l r :: divTwo s

@[simp] theorem divTwo_nil : divTwo ([] : BTStack α) = [] := rfl
@[simp] theorem divTwo_singleton : divTwo [a] = [] := rfl
@[simp] theorem divTwo_cons_cons : divTwo (l :: r :: s) = node l r :: divTwo s := rfl


def divModTwo : BTStack α → Option (BTree α) × BTStack α
  | [] => (none, [])
  | [a] => (some a, [])
  | l :: r :: s =>
    let (mts, dts) := divModTwo s
    (mts, node l r :: dts)

section DivModTwo

@[simp] theorem divModTwo_eq_divTwo_modTwo {s : BTStack α} :
    divModTwo s = (modTwo s, divTwo s) := match s with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: s => by
    unfold divModTwo
    simp_rw [divModTwo_eq_divTwo_modTwo (s := s), divTwo_cons_cons, modTwo_cons_cons]

theorem divTwo_append_singleton :
    divTwo (s ++ [b]) = divTwo s ++ s.modTwo.toList.map (node · b) := by
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

theorem count_eq_count_divTwo_add_elim_count_modTwo :
    s.count = (divTwo s).count + (modTwo s).elim 0 BTree.count := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [divTwo_nil, count_nil, modTwo_nil, Option.elim_none]
  · simp_rw [divTwo_singleton, count_singleton, count_nil, modTwo_singleton, Option.elim_some,
      zero_add]
  · simp_rw [divTwo_cons_cons, modTwo_cons_cons, count_cons, IH, count_node, add_assoc]

theorem count_divTwo_of_modTwo_eq_none (hs : modTwo s = none) :
    s.count = count (divTwo s) := by
  simp_rw [count_eq_count_divTwo_add_elim_count_modTwo (s := s), hs, Option.elim_none, add_zero]

theorem count_divTwo_of_modTwo_eq_some (hs : modTwo s = some a) :
    s.count = count (divTwo s) + a.count := by
  simp_rw [count_eq_count_divTwo_add_elim_count_modTwo (s := s), hs, Option.elim_some]

theorem count_divTwo_le_count : count (divTwo s) ≤ count s := by
  rcases hs : modTwo s with (_ | a)
  · simp_rw [count_divTwo_of_modTwo_eq_none hs, le_rfl]
  · simp_rw [count_divTwo_of_modTwo_eq_some hs]
    exact Nat.le_add_right _ _

end DivModTwo

def listToStack : BTStack α → BTStack α
  | [] => []
  | [a] => [a]
  | l :: r :: s => (modTwo s).elim (·) (· :: ·) (listToStack (l.node r :: divTwo s))
  termination_by s => s.length
  decreasing_by all_goals exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

section ListToStack

@[simp]
theorem listToStack_nil : listToStack ([] : List (BTree α)) = [] := by rw [listToStack]

@[simp]
theorem listToStack_singleton : listToStack [a] = [a] := by rw [listToStack]

theorem listToStack_cons_cons :
    listToStack (l :: r :: s) =
    (modTwo s).elim (·) (· :: ·) (listToStack (l.node r :: divTwo s)) := by rw [listToStack]


@[simp]
theorem listToStack_cons_cons_of_modTwo_none (hs : modTwo s = none) :
    listToStack (l :: r :: s) = listToStack (l.node r :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_none]

@[simp]
theorem listToStack_cons_cons_of_modTwo_some (hs : modTwo s = some a) :
    listToStack (l :: r :: s) = a :: listToStack (l.node r :: divTwo s) := by
  simp_rw [listToStack_cons_cons, hs, Option.elim_some]

theorem listToStack_of_modTwo_some (hs : modTwo s = some a) :
    listToStack s = a :: (divTwo s).listToStack := by
  fun_induction listToStack
  · contradiction
  · simp_rw [modTwo_singleton, Option.some_inj] at hs
    simp_rw [hs, listToStack_singleton, divTwo_singleton, listToStack_nil]
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [listToStack_cons_cons_of_modTwo_some hs, divTwo_cons_cons]

theorem listToStack_of_modTwo_none (hs : modTwo s = none) :
    listToStack s = (divTwo s).listToStack := by
  fun_induction listToStack
  · simp_rw [divTwo_nil]
  · contradiction
  · simp_rw [modTwo_cons_cons] at hs
    simp_rw [listToStack_cons_cons_of_modTwo_none hs, divTwo_cons_cons]

theorem listToStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    listToStack (s ++ [a]) = a :: listToStack s := by
  rw [listToStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, listToStack_of_modTwo_none hs]

theorem listToStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    listToStack (s ++ [b]) = listToStack (s.divTwo ++ [node a b]) := by
  rw [listToStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

theorem count_listToStack : s.listToStack.count = s.count := by
  fun_induction listToStack with | case1 => _ | case2 a => _ | case3 l r s IH => _
  · simp_rw [listToStack_nil]
  · simp_rw [listToStack_singleton]
  · simp_rw [count_cons, count_node] at IH
    simp_rw [listToStack_cons_cons]
    cases hs : modTwo s with | none => _ | some a => _
    · simp_rw [Option.elim_none, count_cons, IH,
        count_divTwo_of_modTwo_eq_none hs, add_assoc]
    · simp_rw [Option.elim_some, count_cons, IH,
        count_divTwo_of_modTwo_eq_some hs, add_comm a.count, add_assoc]

end ListToStack

def listToTree : (n : ℕ) → (s : BTStack α) → s.length = 2^n → BTree α
  | 0, s => fun h => s.getLast (List.ne_nil_of_length_pos (h ▸ Nat.two_pow_pos _))
  | (n + 1), s => fun h => node
      (listToTree n (s.take (2^n)) (s.length_take_of_length_eq_add (h ▸ Nat.two_pow_succ _)))
      (listToTree n (s.drop (2^n)) (s.length_drop_of_length_eq_add (h ▸ Nat.two_pow_succ _)))

section ListToTree

theorem listToTree_zero {hs : s.length = 2^0} : listToTree 0 s hs =
  s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := rfl

theorem listToTree_zero_eq_head? {hs : s.length = 2^0} : listToTree 0 s hs =
    s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)) := by
  simp_rw [pow_zero, List.length_eq_one_iff] at hs
  rcases hs with ⟨a, rfl⟩
  rfl

theorem listToTree_singleton : listToTree 0 [a] rfl = a := rfl

theorem listToTree_succ (s : BTStack α) (hs : s.length = 2^(n + 1)) :
  listToTree (n + 1) s hs = node
    (listToTree n (s.take (2^n)) (s.length_take_of_length_eq_add (hs ▸ Nat.two_pow_succ _)))
    (listToTree n (s.drop (2^n)) (s.length_drop_of_length_eq_add (hs ▸ Nat.two_pow_succ _))) := rfl

theorem listToTree_one {hs : s.length = 2^1} : listToTree 1 s hs =
  node (s.head (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _)))
    (s.getLast (List.ne_nil_of_length_pos (hs ▸ Nat.two_pow_pos _))) := by
  simp_rw [listToTree_succ, listToTree_zero, pow_zero, List.getLast_eq_getElem,
    List.head_eq_getElem, BTree.node_inj_iff, List.length_take,
    List.length_drop, List.getElem_take, hs, List.getElem_drop, pow_one,
    min_eq_left (one_lt_two).le, Nat.add_one_sub_one, Nat.sub_self, true_and]

theorem listToTree_doubleton : listToTree 1 [a, b] rfl = node a b := rfl

theorem listToTree_append (s t : BTStack α) (hs : s.length = 2^n) (ht : t.length = 2^n)
    (hst : (s ++ t).length = 2^(n + 1) := (List.length_append _ _).trans
      (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)) :
    listToTree (n + 1) (s ++ t) hst = node (listToTree n s hs) (listToTree n t ht) := by
  simp_rw [listToTree_succ, BTree.node_inj_iff, List.take_append_of_le_length hs.ge,
    List.take_of_length_le hs.le, List.drop_append_of_le_length hs.ge,
    List.drop_of_length_le hs.le, List.nil_append, true_and]

theorem listToTee_divTwo (s : BTStack α) (hs : s.length = 2^(n + 1)) :
  listToTree (n + 1) s hs = listToTree n s.divTwo (length_divTwo ▸ hs ▸ by
    simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero]) := by
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [zero_add, pow_one, List.length_eq_two] at hs
    rcases hs with ⟨a, b, rfl⟩
    simp_rw [zero_add, divTwo_cons_cons, divTwo_nil,
      listToTree_doubleton, listToTree_singleton]
  · simp_rw [listToTree_succ s, listToTree_succ (s.divTwo),
      BTree.node_inj_iff, IH, take_divTwo, drop_divTwo, pow_succ', true_and]

end ListToTree

section ListToTreeStack

theorem listToStack_two_pow (s : BTStack α) (hs : s.length = 2^n) :
    listToStack s = [listToTree n s hs] := by
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hs
    rcases hs with ⟨_, rfl⟩
    simp_rw [listToStack_singleton, listToTree_singleton]
  · have hs' : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, pow_succ', even_two_mul]
    have IH' := IH (s.divTwo) (length_divTwo ▸ hs ▸ by
        simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero])
    simp_rw [listToStack_of_modTwo_none hs', IH', List.cons_eq_cons, and_true,
      listToTee_divTwo]

theorem listToStack_append (s t : BTStack α) (hs : s.length = 2^n) (ht : t.length = 2^n) :
    listToStack (s ++ t) = [(listToTree n s hs).node (listToTree n t ht)] := by
  have hst : (s ++ t).length = 2^(n + 1) :=
    (List.length_append s t).trans (hs.symm ▸ ht.symm ▸ (Nat.two_pow_succ _).symm)
  rw [listToStack_two_pow (s ++ t) hst, listToTree_append _ _ hs ht]

end ListToTreeStack

def push (b : BTree α) : BTStack α → BTStack α
  | [] => [b]
  | a :: s => if a.height = b.height then
    push (node a b) s else b :: a :: s

section Push

@[simp] theorem push_nil : push a ([] : BTStack α) = [a] := rfl

@[simp] theorem push_cons_of_height_eq (h : a.height = b.height) :
    push b (a :: s) = push (node a b) s := by
  simp_rw [push, if_pos h]

@[simp] theorem push_cons_of_height_ne (h : a.height ≠ b.height) :
    push b (a :: s) = b :: a :: s := by
  rw [push]
  simp_rw [if_neg h]


@[simp] theorem mem_push_nil : c ∈ push b [] ↔ c = b := by
  simp_rw [push_nil, List.mem_singleton]

@[simp] theorem mem_push_cons_of_height_lt (h : b.height < a.height) :
    c ∈ push b (a :: s) ↔ c = b ∨ c = a ∨ c ∈ s  := by
  simp_rw [push_cons_of_height_lt h, List.mem_cons]

@[simp] theorem mem_push_cons_of_height_ge (h : a.height ≤ b.height) :
    c ∈ push b (a :: s) ↔ c ∈ s.push (node a b) := by
  simp_rw [push_cons_of_height_ge h]

@[simp] theorem mem_push_cons_of_height_eq (h : a.height = b.height) :
    c ∈ push b (a :: s) ↔ c ∈ s.push (node a b) := by
  simp_rw [push_cons_of_height_eq h]

@[simp] theorem push_ne_nil : s.push b ≠ [] := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, ne_eq, List.cons_ne_nil, not_false_eq_true]
  · by_cases hab : a.height ≤ b.height
    · rw [push_cons_of_height_ge hab]
      exact IH
    · rw [push_cons_of_height_lt (lt_of_not_le hab)]
      exact List.cons_ne_nil _ _

/-
theorem push_eq_cons_iff :
    push b s = b :: t ↔ s = t ∧ (s ≠ [] → b.height < s.firstHeight) := by
  cases s with | nil => _ | cons a _ => _
  · simp_rw [push_nil, List.cons_eq_cons, true_and, ne_eq, not_true_eq_false,
      false_implies, and_true]
  · simp_rw [ne_eq, List.cons_ne_nil, not_false_eq_true, firstHeight_cons, forall_const]
    · rcases lt_or_le b.height a.height with hab | hab
      · simp_rw [push_cons_of_height_lt hab, List.cons_eq_cons, hab, true_and, and_true]
      · simp_rw [push_cons_of_height_ge hab, hab.not_lt, and_false, iff_false]
        intro H
        have C := (firstHeight_cons ▸ congrArg (firstHeight) H) ▸ height_le_firstHeight_push
        simp_rw [height_node, height_addToHeight, Nat.succ_le_iff, (le_max_right _ _).not_lt] at C

theorem push_of_height_lt (hbs : s ≠ [] → b.height < s.firstHeight) : s.push b = b :: s := by
  rw [push_eq_cons_iff]
  exact ⟨rfl, hbs⟩
-/

theorem length_push_nil : (push a []).length = 1 := by
  simp_rw [push_nil, List.length_singleton]

theorem length_push_cons_of_height_lt (h : b.height < a.height) :
    (push b (a :: s)).length = (a :: s).length + 1 := by
  simp_rw [push_cons_of_height_lt h, List.length_cons]

theorem length_push_le : (s.push b).length ≤ s.length + 1 := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, List.length_singleton, List.length_nil, Nat.zero_add, le_rfl]
  · rcases lt_or_le b.height a.height with hab | hab
    · rw [push_cons_of_height_lt hab, List.length_cons]
    · rw [push_cons_of_height_ge hab]
      exact IH.trans (Nat.succ_le_succ (Nat.lt_succ_self _).le)

theorem push_eq_cons_iff_length_eq_succ :
    s.push b = b :: s ↔ (s.push b).length = s.length + 1 := by
  refine ⟨fun h => h ▸ rfl, ?_⟩
  cases s with | nil => _ | cons a s => _
  · simp_rw [push_nil, implies_true]
  · rcases lt_or_le b.height a.height with hab | hab
    · simp_rw [push_cons_of_height_lt hab, implies_true]
    · simp_rw [push_cons_of_height_ge hab]
      simp_rw [List.length_cons]
      exact fun H => ((Nat.le_of_succ_le_succ (H.symm.trans_le length_push_le)).not_lt
        (Nat.lt_succ_self _)).elim

theorem IsSMH.push_of (hsh : IsSMH s) : IsSMH (push b s) := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, IsSMH_singleton]
  · by_cases hab : a.height ≤ b.height
    · simp_rw [push_cons_of_height_ge hab]
      exact IH hsh.of_cons
    · simp_rw [push_cons_of_height_lt (lt_of_not_le hab)]
      exact hsh.cons_cons (lt_of_not_le hab)

theorem IsSMH.count_push (hsh : IsSMH s) (hb : ∀ a ∈ s, b.height ≤ a.height) :
    (push b s).count = b.count + s.count := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · rfl
  · simp_rw [List.mem_cons, forall_eq_or_imp] at hb
    rcases hb.1.eq_or_lt with hab | hab
    · simp_rw [push_cons_of_height_ge hab.ge]
      by_cases hs : s = []
      · simp_rw [hs, push_nil, count_cons, count_node, count_nil, add_zero, add_comm]
      · rw [IH hsh.of_cons (fun _ hx => height_node_of_heights_eq hab.symm rfl ▸
          (Nat.succ_le_of_lt (hb.1.trans_lt (hsh.cons_height_lt_height_of_mem _ hx))))]
        simp_rw [count_node, count_cons, add_comm b.count, add_assoc, Nat.add_right_inj, add_comm]
    · simp_rw [push_cons_of_height_lt hab, count_cons]

/-
theorem IsPerfect.push_of_IsPerfect (hb : b.IsPerfect) (has : IsPerfect s) :
    IsPerfect (s.push b) := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, IsPerfect_singleton_iff, hb]
  · by_cases hab : a.height ≤ b.height
    · simp_rw [push_cons_of_height_ge hab]
      refine IH ?_ has.of_cons_tail
      sorry
    · simp_rw [IsPerfect_cons_iff] at has
      simp_rw [push_cons_of_height_lt (lt_of_not_le hab), IsPerfect_cons_iff]
      exact ⟨hb, has⟩
-/
theorem IsSMH.height_ge_of_mem_push (hc : c ∈ s.push b) (hsh : IsSMH s) :
    b.height ≤ c.height := by
  induction s generalizing b c with | nil => _ | cons a s IH => _
  · simp_rw [mem_push_nil.mp hc, le_rfl]
  · by_cases hab : a.height ≤ b.height
    · rw [mem_push_cons_of_height_ge hab] at hc
      specialize IH hc
      simp_rw [height_node, Nat.succ_le_iff, max_lt_iff] at IH
      exact (IH hsh.of_cons).2.le
    · rcases (mem_push_cons_of_height_lt (lt_of_not_le hab)).mp hc with (rfl | rfl | hc)
      · exact le_rfl
      · exact (lt_of_not_le hab).le
      · exact ((lt_of_not_le hab).trans (hsh.cons_height_lt_height_of_mem _ hc)).le

end Push

def pushStack (s : BTStack α) (t : BTStack α) : BTStack α := s.foldr push t

section PushStack

variable {u v : BTStack α}

@[simp] theorem pushStack_nil : pushStack [] s  = s := List.foldr_nil

@[simp] theorem pushStack_cons : pushStack (a :: s) t = push a (pushStack s t) := List.foldr_cons _

@[simp] theorem pushStack_append_singleton :
    pushStack (s ++ [a]) t = pushStack s (push a t) := List.foldr_append _ _ _ _

@[simp] theorem pushStack_singleton : pushStack [a] s = push a s := by
  simp only [pushStack_nil, pushStack_cons]

@[simp] theorem pushStack_append : pushStack (u ++ v) s = pushStack u (pushStack v s):=
    List.foldr_append _ _ _ _

@[simp] theorem IsSMH.pushStack (hsh : IsSMH s) (hth : IsSMH t) : IsSMH (pushStack s t) := by
  induction s using List.reverseRecOn generalizing t with
    | nil => _ | append_singleton s a IH => _
  · rw [pushStack_nil]
    exact hth
  · rw [pushStack_append_singleton]
    exact IH hsh.of_append_singleton hth.push_of

/-
@[simp] theorem IsPerfect.pushStack (hs : IsPerfect s) (ht : IsPerfect t) :
    IsPerfect (pushStack s t) := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · exact ht
  · simp_rw [pushStack_cons]
    exact (IH hs.of_cons_tail ht).push_of_IsPerfect hs.of_cons_head
-/

/-
theorem pushStack_eq_append_of_lt (hst : s ≠ [] → t ≠ [] → s.lastHeight < t.firstHeight)
  (hsh : s.IsSMH) : pushStack s t = s ++ t := by
  induction s using List.reverseRecOn generalizing t with | nil => _ | append_singleton s a IH => _
  · simp_rw [pushStack_nil, List.nil_append]
  · simp_rw [ne_eq, List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), not_false_eq_true,
      lastHeight_append_singleton, forall_const] at hst
    simp_rw [pushStack_append_singleton]
    rw [push_of_height_lt hst]
    refine (IH ?_ hsh.of_append_singleton).trans (List.append_cons _ _ _)
    simp_rw [ne_eq, List.cons_ne_nil, not_false_eq_true, firstHeight_cons, forall_const]
    exact hsh.lastHeight_lt_height_append_singleton-/

end PushStack

def ofStack (s : BTStack α) := pushStack s []

section OfStack

@[simp] theorem ofStack_nil : ofStack ([] : BTStack α) = [] := rfl

@[simp] theorem ofStack_append_singleton :
    ofStack (s ++ [a]) = pushStack s [a] := pushStack_append_singleton

@[simp] theorem ofStack_cons : ofStack (a :: s) = push a s.ofStack := pushStack_cons

@[simp] theorem ofStack_singleton : ofStack [a] = singleton a := rfl

@[simp] theorem ofStack_append : ofStack (s ++ t) = pushStack s t.ofStack := pushStack_append

theorem IsSMH.ofStack (hsh : IsSMH s) : s.ofStack.IsSMH := IsSMH.pushStack hsh IsSMH_nil

/-
theorem IsPerfect.ofStack (hs : IsPerfect s) : s.ofStack.IsPerfect :=
  IsPerfect.pushStack hs IsPerfect_nil-/

theorem ofStack_length_le : s.ofStack.length ≤ s.length := by
  induction s
  · simp_rw [ofStack_nil, le_refl]
  · simp_rw [ofStack_cons, List.length_cons]
    exact length_push_le.trans (Nat.succ_le_succ (by assumption))

theorem ofStack_eq_of_ofStack_length_eq (hs : s.ofStack.length = s.length) : s.ofStack = s := by
  generalize hsOf : s.ofStack.length = n
  have hs' := hs ▸ hsOf
  clear hs ; revert hsOf ; revert hs'
  induction n generalizing s with | zero => _ | succ n IH => _
  · simp_rw [List.length_eq_zero_iff]
    rintro rfl _
    rfl
  · cases s with | nil => _ | cons a s => _
    · simp_rw [List.length_nil, (Nat.succ_ne_zero _).symm, false_implies]
    · simp_rw [List.length_cons, add_left_inj, ofStack_cons]
      intros hs hsOf
      have H := le_antisymm (hs ▸ ofStack_length_le)
        (Nat.le_of_add_le_add_right (hsOf ▸ length_push_le))
      rw [← H] at hsOf
      rw [← push_eq_cons_iff_length_eq_succ] at hsOf
      rw [IH hs H] at hsOf ⊢
      exact hsOf

end OfStack

def pushLeaf (x : α) (s : BTStack α) : BTStack α := push (leaf x) s

section PushLeaf

variable {x y : α}

@[simp] theorem push_leaf : push (leaf x) s = s.pushLeaf x := rfl

@[simp] theorem pushLeaf_nil : pushLeaf x [] = [leaf x] := push_nil

@[simp] theorem pushLeaf_cons_leaf  :
    pushLeaf y ((leaf x) :: s) = push (node (leaf x) (leaf y)) s := push_cons_of_height_eq rfl

@[simp] theorem pushLeaf_cons_node  :
    pushLeaf y ((node l r) :: s) = (leaf y) :: ((node l r) :: s) :=
  push_cons_of_height_lt (Nat.succ_pos _)

theorem IsSMH.pushLeaf (hsh : IsSMH s) : IsSMH (pushLeaf x s) := hsh.push_of

/-
theorem IsPerfect.pushLeaf (hs : IsPerfect s) : IsPerfect (s.pushLeaf x) :=
  hs.push_of_IsPerfect IsPerfect_leaf
-/

end PushLeaf

def pushLeafs (xs : List α) (s : BTStack α) : BTStack α := xs.foldl (flip pushLeaf) s

section PushLeafs

variable {x : α} {xs ys : List α}

@[simp] theorem pushLeafs_nil : pushLeafs [] s = s := List.foldl_nil

@[simp] theorem pushLeafs_cons : s.pushLeafs (x :: xs) = (s.pushLeaf x).pushLeafs xs :=
    List.foldl_cons _ _

@[simp] theorem pushLeafs_append_singleton :
    pushLeafs (xs ++ [x]) s = (s.pushLeafs xs).pushLeaf x := List.foldl_append _ _ _ _

theorem pushLeafs_singleton : s.pushLeafs [x] = s.pushLeaf x := by
  simp only [pushLeafs_cons, pushLeafs_nil]

@[simp] theorem pushLeafs_append : s.pushLeafs (xs ++ ys) = (s.pushLeafs xs).pushLeafs ys :=
    List.foldl_append _ _ _ _

@[simp] theorem IsSMH.pushLeafs (hsh : IsSMH s) :
    IsSMH (s.pushLeafs xs) := by
  induction xs generalizing s with | nil => _ | cons x xs IH => _
  · exact hsh
  · simp_rw [pushLeafs_cons]
    exact IH hsh.pushLeaf

/-
@[simp] theorem IsPerfect.pushLeafs (hsh : IsPerfect s) :
    IsPerfect (s.pushLeafs xs) := by
  induction xs generalizing s with | nil => _ | cons x xs IH => _
  · exact hsh
  · simp_rw [pushLeafs_cons]
    exact IH hsh.pushLeaf
-/

theorem pushLeafs_eq_pushStack :
    s.pushLeafs xs = pushStack (xs.reverse.map leaf) s := by
  induction xs generalizing s with | nil => _ | cons _ _ IH => _
  · rfl
  · simp_rw [pushLeafs_cons, List.reverse_cons, List.map_append, List.map_singleton,
      pushStack_append, pushStack_singleton, push_leaf, IH]

end PushLeafs

def ofLeafs (xs : List α) : BTStack α := pushLeafs xs []

section OfLeafs

variable {xs : List α} {s : BTStack α}

@[simp]
theorem ofLeafs_nil : ofLeafs [] = ([] : BTStack α) := pushLeafs_nil

@[simp]
theorem ofLeafs_cons : ofLeafs (x :: xs) = pushLeafs xs [leaf x] := pushLeafs_cons

@[simp]
theorem ofLeafs_append_singleton : ofLeafs (xs ++ [x]) = pushLeaf x (ofLeafs xs) :=
  pushLeafs_append_singleton

theorem ofLeafs_append : ofLeafs (xs ++ ys) = pushLeafs ys (ofLeafs xs) := pushLeafs_append

theorem ofLeafs_eq_ofStack : ofLeafs xs = ofStack (xs.reverse.map leaf) := pushLeafs_eq_pushStack

@[simp] theorem ofLeafs_IsSMH : IsSMH (ofLeafs xs) := IsSMH_nil.pushLeafs

/-
@[simp] theorem ofLeafs_IsPerfect : IsPerfect (ofLeafs xs) := IsPerfect_nil.pushLeafs
-/
end OfLeafs
