import Xmss.Lib

namespace List

@[elab_as_elim]
def doubleRec {motive : List α → Sort*} (l : List α)  (nil : motive [])
    (singleton : ∀ a, motive [a])
    (cons_cons : ∀ a b l, motive l → motive (a :: b :: l)) : motive l :=
  match l with
  | [] => nil
  | [a] => singleton a
  | _ :: _ :: l => cons_cons _ _ _ (doubleRec l nil singleton cons_cons)

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

def addToHeight (t : BTree α) : ℕ → BTree α
  | 0 => t
  | (n + 1) =>
    let t' := addToHeight t n
    node t' t'

section AddToHeight

@[simp] theorem addToHeight_zero : t.addToHeight 0 = t := rfl
@[simp] theorem addToHeight_succ : t.addToHeight (n + 1) =
    node (addToHeight t n) (addToHeight t n) := rfl

@[simp] theorem height_addToHeight : (t.addToHeight n).height = t.height + n := by
  induction n
  · rfl
  · rw [addToHeight_succ, height_node_of_height_le le_rfl, ← add_assoc, add_left_inj]
    assumption

end AddToHeight

def IsPerfectOfHeight : ℕ → BTree α → Bool
  | 0, leaf _ => true
  | (_ + 1), leaf _ => false
  | 0, node _ _ => false
  | (n + 1), node l r => l.IsPerfectOfHeight n && r.IsPerfectOfHeight n

section IsPerfectOfHeight

@[simp] theorem IsPerfectOfHeight_zero_leaf :
    (leaf a).IsPerfectOfHeight 0  = true := rfl
@[simp] theorem IsPerfectOfHeight_succ_leaf :
    (leaf a).IsPerfectOfHeight (n + 1) = false := rfl
@[simp] theorem IsPerfectOfHeight_zero_node :
    (node l r).IsPerfectOfHeight 0 = false := rfl
@[simp] theorem IsPerfectOfHeight_succ_node :
    (node l r).IsPerfectOfHeight (n + 1) =
    (l.IsPerfectOfHeight n && r.IsPerfectOfHeight n) := rfl

theorem IsPerfectOfHeight_false_of_ne_height (h : t.height ≠ n) :
    t.IsPerfectOfHeight n = false := by
  induction t generalizing n with | leaf _ => _ | node l r IHL IHR => _  <;> cases n
  · exact (Ne.irrefl h).elim
  · rfl
  · rfl
  · simp_rw [height_node, Nat.succ_ne_succ, ne_eq, max_eq_iff, not_or,
      not_and'] at h
    simp_rw [IsPerfectOfHeight_succ_node, Bool.and_eq_false_iff]
    exact (Nat.le_total r.height l.height).imp
      (fun hlr => IHL (h.1 hlr)) (fun hlr => IHR (h.2 hlr))

theorem height_eq_of_IsPerfectOfHeight (h : t.IsPerfectOfHeight n) : t.height = n := by
  by_contra c
  simp_rw [IsPerfectOfHeight_false_of_ne_height c] at h
  contradiction

theorem IsPerfectOfHeight_node_false_of_height_ne (h : l.height ≠ r.height) :
    (node l r).IsPerfectOfHeight n = false := by
  cases n with | zero => _ | succ n => _
  · rfl
  · simp_rw [IsPerfectOfHeight_succ_node]
    rcases eq_or_ne l.height n with rfl | hn
    · rw [IsPerfectOfHeight_false_of_ne_height h.symm, Bool.and_false]
    · rw [IsPerfectOfHeight_false_of_ne_height hn, Bool.false_and]

end IsPerfectOfHeight

def IsPerfect (t : BTree α) : Prop := t.IsPerfectOfHeight (t.height)

section IsPerfect

instance : DecidablePred (IsPerfect (α := α)) :=
  fun t => decidable_of_iff (t.IsPerfectOfHeight (t.height) = true) Iff.rfl

theorem IsPerfect_def : t.IsPerfect ↔ t.IsPerfectOfHeight (t.height) := Iff.rfl

theorem IsPerfectOfHeight_iff_isPerfect_and_height_eq :
    t.IsPerfectOfHeight n ↔ t.IsPerfect ∧ t.height = n := by
  rw [t.IsPerfect_def]
  exact ⟨fun h => ⟨height_eq_of_IsPerfectOfHeight h ▸ h, height_eq_of_IsPerfectOfHeight h⟩,
    fun h => h.2 ▸ h.1⟩

@[simp] theorem IsPerfect_leaf : (leaf a).IsPerfect := rfl

theorem IsPerfect_node_of_height_eq_height (h : l.height = r.height) :
    (node l r).IsPerfect ↔ (l.IsPerfect ∧ r.IsPerfect) := by
  simp_rw [IsPerfect_def, height_node, IsPerfectOfHeight_succ_node,
    h, max_self,  Bool.and_eq_true]

@[simp] theorem IsPerfect_node_iff : (node l r).IsPerfect ↔
    (l.IsPerfect ∧ r.IsPerfect ∧ l.height = r.height) := by
  simp_rw [IsPerfect_def, height_node, IsPerfectOfHeight_succ_node]
  by_cases h : l.height = r.height
  · simp_rw [h, max_self, and_true, Bool.and_eq_true]
  · simp_rw [h, and_false]
    rcases Ne.lt_or_lt h with h | h
    · simp_rw [max_eq_right_of_lt h, IsPerfectOfHeight_false_of_ne_height h.ne,
        Bool.false_and, Bool.false_eq_true]
    · simp_rw [max_eq_left_of_lt h, IsPerfectOfHeight_false_of_ne_height h.ne,
        Bool.and_false, Bool.false_eq_true]

theorem IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq
    (hl : l.IsPerfect) (hr : r.IsPerfect)
    (hl₂ : l.height = n)
    (hr₂ : r.height = n)  :
    (node l r).IsPerfect := IsPerfect_node_iff.mpr ⟨hl, hr, hl₂ ▸ hr₂ ▸ rfl⟩

theorem IsPerfect.node_of_IsPerfect_right_of_height_eq_height
    (hl : l.IsPerfect) (hr : r.IsPerfect)
    (hlr : l.height = r.height) :
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

@[simp] theorem IsPerfect.addToHeight (ht : t.IsPerfect) : (t.addToHeight n).IsPerfect := by
  induction n
  · exact ht
  · simp_rw [addToHeight_succ, IsPerfect_node_iff, and_true, and_self]
    assumption

theorem height_node_addToHeight_addToHeight : (node (l.addToHeight (r.height - l.height))
    (r.addToHeight (l.height - r.height))).height = (node l r).height := by
  simp_rw [height_node, height_addToHeight, add_left_inj, add_tsub_eq_max, max_comm, max_self]

theorem IsPerfect.node_addToHeight (hl : l.IsPerfect) (hr : r.IsPerfect) :
    (node (l.addToHeight (r.height - l.height))
    (r.addToHeight (l.height - r.height))).IsPerfect := by
  simp_rw [IsPerfect_node_iff, hl.addToHeight, hr.addToHeight, true_and, height_addToHeight,
    add_tsub_eq_max, max_comm]

end IsPerfect


def count : BTree α → ℕ
  | leaf _ => 1
  | node l r => l.count + r.count

section Count

@[simp] theorem count_leaf : (leaf a).count = 1 := rfl

@[simp] theorem count_node : (node l r).count = l.count + r.count := rfl

theorem count_addToHeight : (t.addToHeight n).count = 2^n * t.count := by
  induction n
  · simp_rw [addToHeight_zero, pow_zero, one_mul]
  · simp_rw [addToHeight_succ, count_node, pow_succ', mul_assoc, two_mul]
    exact congrArg₂ _ (by assumption) (by assumption)

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

def ofList (l : List α) (hl : l ≠ []) : BTree α :=
    if h : 1 < l.length then
    node
    (ofList (l.take ((l.length + 1)/2)) <| List.ne_nil_of_length_pos
    (List.length_take_pos.mpr ⟨zero_lt_one.trans_le h.le,
        Nat.div_pos (Nat.succ_le_succ h.le) zero_lt_two⟩))
    (ofList (l.drop ((l.length + 1)/2)) <| List.ne_nil_of_length_pos
    (List.length_drop_pos.mpr (Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left h l.length)))))
      else leaf (l.head hl)
  termination_by l.length

section OfList

variable {l : List α}

theorem ofList_of_length_eq_one (hl : l.length = 1)
    (h' := (List.ne_nil_of_length_pos (hl ▸ zero_lt_one))) :
    ofList l h' = leaf (l.head h') := by
  unfold ofList
  simp_rw [hl, lt_irrefl, dite_false]

@[simp] theorem ofList_singleton : ofList [a] (List.cons_ne_nil _ _) = leaf a :=
  ofList_of_length_eq_one (List.length_singleton _)

theorem ofList_of_one_lt_length (hl : 1 < l.length)
    (hl' := (List.ne_nil_of_length_pos (zero_lt_one.trans hl))) :
  ofList l hl' = node
    (ofList (l.take ((l.length + 1)/2)) <| List.ne_nil_of_length_pos
    (List.length_take_pos.mpr ⟨zero_lt_one.trans_le hl.le,
        Nat.div_pos (Nat.succ_le_succ hl.le) zero_lt_two⟩))
    (ofList (l.drop ((l.length + 1)/2)) <| List.ne_nil_of_length_pos
    (List.length_drop_pos.mpr (Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left hl l.length))))) := by
  rw [ofList]
  simp_rw [hl, dite_true]

theorem ofList_eq_leaf_iff {hl : l ≠ []} : ofList l hl = leaf a ↔ l = [a] := by
  by_cases hl' : 1 < l.length
  · simp_rw [ofList_of_one_lt_length hl', node_ne_leaf, false_iff]
    intro C
    rw [C] at hl'
    contradiction
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero_iff, hl, false_or,
      List.length_eq_one_iff] at hl'
    rcases hl' with ⟨_, rfl⟩
    simp_rw [ofList_singleton, leaf_inj_iff, List.cons.injEq, and_true]

@[simp] theorem height_ofList {hl : l ≠ []} : (ofList l hl).height = (l.length - 1).size := by
  generalize hl' : l.length = n
  induction n using Nat.strongRecOn generalizing l with | ind n IH => _
  have IH : ∀ {l : List α} {hl : l ≠ []}, l.length < n →
    (ofList l hl).height = (l.length - 1).size := fun h => IH _ h rfl
  subst hl'
  by_cases hn : 1 < l.length
  · have hn₁ : (l.length + 1) / 2 < l.length := Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left hn l.length))
    have hl_drop := List.ne_nil_of_length_pos (List.length_drop_pos.mpr hn₁)
    have take_lt := List.length_take_lt_length.mpr hn₁
    have hn₂ : 0 < (l.length + 1) / 2 := Nat.div_pos (Nat.succ_le_succ hn.le) zero_lt_two
    have hl_take := List.ne_nil_of_length_pos (List.length_take_pos.mpr ⟨hn₂.trans hn₁, hn₂⟩)
    have drop_lt := List.length_drop_lt_length.mpr ⟨hn₂.trans hn₁, hn₂⟩
    have drop_le_take := Nat.size_le_size (Nat.sub_le_sub_right
      (List.length_drop_le_length_take (l := l).mpr le_rfl) 1)
    rw [ofList_of_one_lt_length hn, height_node, IH (hl := hl_drop) drop_lt,
      IH (hl := hl_take) take_lt, max_eq_left drop_le_take, List.length_take_succ_length_div_two]
    rcases Nat.exists_eq_add_of_le' hn with ⟨n, hn⟩
    simp_rw [hn, add_right_comm, Nat.succ_eq_add_one, ← Nat.add_assoc n 1 1, one_add_one_eq_two,
      Nat.add_div_right _ zero_lt_two, Nat.add_sub_cancel, Nat.size_div_two_succ]
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero_iff, hl, false_or,
      List.length_eq_one_iff] at hn
    rcases hn with ⟨_, rfl⟩
    simp_rw [List.length_singleton, Nat.sub_self, Nat.size_zero, ofList_singleton, height_leaf]

theorem height_ofList_of_length_eq_one (hl : l.length = 1)
  (h' := (List.ne_nil_of_length_pos (hl ▸ zero_lt_one))) :
    (ofList l h').height = 0 := by
  rw [height_ofList, hl, Nat.sub_self, Nat.size_zero]

@[simp] theorem count_ofList {hl : l ≠ []} : (ofList l hl).count = l.length := by
  generalize hl' : l.length = n
  induction n using Nat.strongRecOn generalizing l with | ind n IH => _
  have IH : ∀ {l : List α} {hl : l ≠ []}, l.length < n →
    (ofList l hl).count = l.length := fun h => IH _ h rfl
  subst hl'
  by_cases hn : 1 < l.length
  · have hn₁ : (l.length + 1) / 2 < l.length := Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left hn l.length))
    have hl_drop := List.ne_nil_of_length_pos (List.length_drop_pos.mpr hn₁)
    have take_lt := List.length_take_lt_length.mpr hn₁
    have hn₂ : 0 < (l.length + 1) / 2 := Nat.div_pos (Nat.succ_le_succ hn.le) zero_lt_two
    have hl_take := List.ne_nil_of_length_pos (List.length_take_pos.mpr ⟨hn₂.trans hn₁, hn₂⟩)
    have drop_lt := List.length_drop_lt_length.mpr ⟨hn₂.trans hn₁, hn₂⟩
    rw [ofList_of_one_lt_length hn, count_node, IH (hl := hl_drop) drop_lt,
      IH (hl := hl_take) take_lt, ← List.length_append, List.take_append_drop]
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero_iff, hl, false_or,
      List.length_eq_one_iff] at hn
    rcases hn with ⟨_, rfl⟩
    simp_rw [ofList_singleton, count_leaf, List.length_singleton]

theorem ofList_append {s t : List α} (hs : s ≠ []) (ht : t ≠ [])
    (hst : 1 < (s ++ t).length := List.length_append _ _ ▸
    Nat.add_le_add (List.length_pos_of_ne_nil hs) (List.length_pos_of_ne_nil ht)):
    ofList (s ++ t) (List.append_ne_nil_of_left_ne_nil hs _) =
    node (ofList ((s ++ t).take (((s ++ t).length + 1) / 2)) (List.ne_nil_of_length_pos
    (List.length_take_pos.mpr ⟨zero_lt_one.trans_le hst.le,
    Nat.div_pos (Nat.succ_le_succ hst.le) zero_lt_two⟩)))
    (ofList ((s ++ t).drop (((s ++ t).length + 1) / 2)) (List.ne_nil_of_length_pos
    (List.length_drop_pos.mpr (Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left hst _)))))) := ofList_of_one_lt_length hst

theorem ofList_append_of_length_eq {s t : List α} (hst : s.length = t.length) (hs : s ≠ [])
    (ht : t ≠ [] := List.ne_nil_of_length_pos (hst ▸ List.length_pos_of_ne_nil hs)) :
    ofList (s ++ t) (List.append_ne_nil_of_left_ne_nil hs _) =
    node (ofList s hs) (ofList t ht) := by
  simp_rw [ofList_append hs ht, List.length_append, hst.symm, ← two_mul,
    Nat.mul_add_div zero_lt_two, Nat.div_eq_of_lt one_lt_two, add_zero, List.take_left',
    List.drop_left']

theorem IsPerfect_ofList_of_length_eq_two_pow (hk : l.length = 2^k) :
    (ofList l (List.ne_nil_of_length_pos (hk ▸ Nat.two_pow_pos _))).IsPerfect := by
  induction k generalizing l with | zero => _ | succ k IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff] at hk
    rcases hk with ⟨_, rfl⟩
    simp_rw [ofList_singleton, IsPerfect_leaf]
  · have hl' : 1 < l.length := hk ▸ ((Nat.one_lt_pow_iff (Nat.succ_ne_zero _)).mpr one_lt_two)
    rw [ofList_of_one_lt_length hl']
    have take_len : (l.take ((l.length + 1) / 2)).length = 2^k := by
      simp_rw [List.length_take, hk, pow_succ', Nat.mul_add_div zero_lt_two,
        Nat.div_eq_of_lt one_lt_two, add_zero, min_eq_left_iff,
        Nat.le_mul_of_pos_left _ zero_lt_two]
    have drop_len : (l.drop ((l.length + 1) / 2)).length = 2^k := by
      simp_rw [List.length_drop, hk, pow_succ', Nat.mul_add_div zero_lt_two,
        Nat.div_eq_of_lt one_lt_two, add_zero, Nat.two_mul, Nat.add_sub_cancel]
    refine IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq (n := k)
      (IH take_len) (IH drop_len) ?_ ?_
    · rw [height_ofList, take_len, Nat.size_pred_pow]
    · rw [height_ofList, drop_len, Nat.size_pred_pow]

theorem IsPerfect_ofList_iff_exists_two_pow_length {hl : l ≠ []}:
    (ofList l hl).IsPerfect ↔ ∃ k, l.length = 2^k :=
  ⟨fun h => ⟨_, count_ofList ▸ h.count_eq_two_pow_height⟩,
    fun ⟨_, h⟩ => IsPerfect_ofList_of_length_eq_two_pow h⟩

theorem IsPerfect_ofList_of_exists_two_pow_length (h : ∃ k, l.length = 2^k) :
    (ofList l (List.ne_nil_of_length_pos (h.choose_spec ▸ Nat.two_pow_pos _))).IsPerfect :=
  IsPerfect_ofList_of_length_eq_two_pow h.choose_spec

theorem height_of_list_of_length_eq_two_pow (hk : l.length = 2^k) :
    (ofList l (List.ne_nil_of_length_pos (hk ▸ Nat.two_pow_pos _))).height = k := by
  simp_rw [height_ofList, hk, Nat.size_pred_pow]

end OfList

def toList : BTree α → List α
  | leaf a => [a]
  | node l r => toList l ++ toList r

section ToList

@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl
@[simp] theorem toList_node : (node l r).toList = l.toList ++ r.toList := rfl

theorem toList_addToHeight : (t.addToHeight n).toList = (fun l => l ++ l)^[n] t.toList := by
  induction n
  · simp_rw [addToHeight_zero, Function.iterate_zero, id_eq]
  · simp_rw [addToHeight_succ, toList_node, Function.iterate_succ', Function.comp_apply]
    exact congrArg₂ _ (by assumption) (by assumption)

@[simp] theorem length_toList : t.toList.length = t.count := by
  induction t
  · rfl
  · exact (List.length_append _ _).trans (congrArg₂ _ (by assumption) (by assumption))

@[simp] theorem toList_ne_nil : t.toList ≠ [] :=
  fun h => (NeZero.ne t.count) (h ▸ length_toList).symm

@[simp] theorem ofList_toList {l : List α} {hl : l ≠ []} : (ofList l hl).toList = l := by
  generalize hl' : l.length = n
  induction n using Nat.strongRecOn generalizing l with | ind n IH => _
  have IH : ∀ {l : List α} {hl : l ≠ []}, l.length < n →
    (ofList l hl).toList = l := fun h => IH _ h rfl
  subst hl'
  by_cases hn : 1 < l.length
  · have hn₁ : (l.length + 1) / 2 < l.length := Nat.div_lt_of_lt_mul
        (Nat.two_mul _ ▸ (Nat.add_lt_add_left hn l.length))
    have hl_drop := List.ne_nil_of_length_pos (List.length_drop_pos.mpr hn₁)
    have take_lt := List.length_take_lt_length.mpr hn₁
    have hn₂ : 0 < (l.length + 1) / 2 := Nat.div_pos (Nat.succ_le_succ hn.le) zero_lt_two
    have hl_take := List.ne_nil_of_length_pos (List.length_take_pos.mpr ⟨hn₂.trans hn₁, hn₂⟩)
    have drop_lt := List.length_drop_lt_length.mpr ⟨hn₂.trans hn₁, hn₂⟩
    rw [ofList_of_one_lt_length hn, toList_node, IH (hl := hl_drop) drop_lt,
      IH (hl := hl_take) take_lt, List.take_append_drop]
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero_iff, hl, false_or,
      List.length_eq_one_iff] at hn
    rcases hn with ⟨_, rfl⟩
    simp_rw [ofList_singleton, toList_leaf]

theorem ofList_inj_iff {l r : List α} {hl : l ≠ []} {hr : r ≠ []} :
    ofList l hl = ofList r hr ↔ l = r := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have H := congrArg toList h
  rwa [ofList_toList, ofList_toList] at H

theorem IsPerfect.toList_ofList (ht : t.IsPerfect) : ofList t.toList toList_ne_nil = t := by
  induction t with | leaf _ => _ | node l r IHL IHR => _
  · simp_rw [toList_leaf, ofList_singleton]
  · have hlr : l.toList.length = r.toList.length := by
      simp_rw [length_toList, ht.left.count_eq_two_pow_height, ht.right.count_eq_two_pow_height,
        ht.height_eq_height]
    simp_rw [toList_node, ofList_append_of_length_eq hlr toList_ne_nil, IHL ht.left, IHR ht.right]

theorem IsPerfect.length_toList (ht : t.IsPerfect) : t.toList.length = 2^t.height := by
  simp_rw [BTree.length_toList, ht.count_eq_two_pow_height]

end ToList

@[simps!]
def equivNeNilListPerfectBTreeOfHeight (k : ℕ) : {l : List α // l.length = 2^k} ≃
    {t : BTree α // t.IsPerfect ∧ t.height = k} where
  toFun l := ⟨_, IsPerfect_ofList_of_length_eq_two_pow l.2,
    height_of_list_of_length_eq_two_pow l.2⟩
  invFun t := ⟨t.1.toList, by rw [t.2.1.length_toList, t.2.2]⟩
  left_inv l := Subtype.ext ofList_toList
  right_inv t := Subtype.ext t.2.1.toList_ofList

@[simps!]
def equivNeNilListPerfectBTree : {l : List α // ∃ k, l.length = 2^k} ≃
    {t : BTree α // t.IsPerfect} where
  toFun l := ⟨_, IsPerfect_ofList_of_exists_two_pow_length l.2⟩
  invFun t := ⟨t.1.toList, ⟨t.1.height, by simp_rw [length_toList, t.2.count_eq_two_pow_height]⟩⟩
  left_inv l := Subtype.ext ofList_toList
  right_inv t := Subtype.ext t.2.toList_ofList

def skeleton : BTree α → BTree Unit
  | leaf _ => leaf ()
  | node l r => node l.skeleton r.skeleton

section Skeleton

@[simp] theorem skeleton_leaf : (leaf a).skeleton = leaf () := rfl

@[simp] theorem skeleton_node : (node l r).skeleton = node l.skeleton r.skeleton := rfl

theorem skeleton_toList : t.skeleton.toList = List.replicate (t.count) () := by
  induction t with | leaf x => _ | node l r IHL IHR => _
  · rfl
  · simp_rw [skeleton_node, count_node, toList_node, IHL, IHR, List.replicate_append_replicate]

theorem skeleton_count : t.skeleton.count = t.count := by
  simp_rw [← length_toList (t := t.skeleton), skeleton_toList, List.length_replicate]

theorem eq_iff_skeleton_eq_toList_eq : s = t ↔ s.skeleton = t.skeleton ∧ s.toList = t.toList := by
  induction t generalizing s with | leaf x => _ | node l r IHL IHR => _
  · simp_rw [skeleton_leaf, toList_leaf]
    cases s
    · simp_rw [skeleton_leaf, leaf_inj_iff, toList_leaf, List.cons_eq_cons, and_true, true_and]
    · simp_rw [skeleton_node, node_ne_leaf, false_and]
  · simp_rw [skeleton_node, toList_node]
    cases s
    · simp_rw [skeleton_leaf, leaf_ne_node, false_and]
    · simp_rw [skeleton_node, node_inj_iff, toList_node]
      refine ⟨fun ⟨hl, hr⟩ => hl ▸ hr ▸ ⟨⟨rfl, rfl⟩, rfl⟩, fun ⟨⟨hl, hr⟩, hlr⟩ => ?_⟩
      simp_rw [IHL, IHR, hl, hr, true_and]
      exact List.append_inj' hlr
        (length_toList ▸ skeleton_count ▸ hr ▸ skeleton_count.symm ▸ length_toList.symm)

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

def count : BTStack α → ℕ
  | [] => 0
  | (a :: s) => a.count + count s

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

def toList : BTStack α → List α
  | [] => []
  | a :: s => a.toList ++ toList s

@[simp] theorem toList_nil : toList ([] : BTStack α) = [] := rfl
@[simp] theorem toList_cons : toList (a :: s) = a.toList ++ s.toList := rfl

@[simp]
theorem length_toList : s.toList.length = s.count := by
  induction s
  · rfl
  · simp_rw [toList_cons, List.length_append, BTree.length_toList, count_cons, add_right_inj]
    assumption

def split : BTree α → BTStack α
  | leaf a => [leaf a]
  | node l r => [l, r]

@[simp] theorem split_leaf {a : α} : split (leaf a) = [leaf a] := rfl
@[simp] theorem split_node : split (node l r) = [l, r] := rfl

@[simp]
theorem split_ne_nil : split a ≠ [] := by cases a <;> exact List.cons_ne_nil _ _

def mulTwo : BTStack α → BTStack α := List.flatMap split

@[simp] theorem mulTwo_nil : mulTwo ([] : BTStack α) = [] := rfl
theorem mulTwo_cons : mulTwo (a :: s) = split a ++ mulTwo s := rfl
@[simp] theorem mulTwo_leaf_cons : mulTwo (leaf v :: s) = leaf v :: mulTwo s := rfl
@[simp] theorem mulTwo_node_cons : mulTwo (node l r :: s) = l :: r :: mulTwo s := rfl

@[simp]
theorem mulTwo_cons_ne_nil : mulTwo (a :: s) ≠ [] := by
  simp_rw [mulTwo_cons]
  exact List.append_ne_nil_of_left_ne_nil split_ne_nil _

@[simp]
theorem mulTwo_eq_nil_iff : mulTwo s = [] ↔ s = [] := by
  cases s
  · exact Iff.rfl
  · simp_rw [mulTwo_cons, List.append_eq_nil_iff, split_ne_nil, List.cons_ne_nil, false_and]


@[simp]
theorem mulTwo_singleton : mulTwo [a] = split a := by
  simp_rw [mulTwo_cons, mulTwo_nil, List.append_nil]

@[simp]
theorem mulTwo_append : mulTwo (s ++ t) = mulTwo s ++ mulTwo t :=  List.flatMap_append _ _ _

theorem mulTwo_append_singleton : mulTwo (s ++ [a]) = mulTwo s ++ split a := by
  rw [mulTwo_append, mulTwo_singleton]

theorem length_le_length_mulTwo : s.length ≤ (mulTwo s).length := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [mulTwo_nil, le_rfl]
  · cases a
    · simp_rw [mulTwo_leaf_cons, List.length_cons, add_le_add_iff_right]
      exact Nat.le_succ_of_le IH
    · simp_rw [mulTwo_node_cons, List.length_cons, add_le_add_iff_right]
      exact IH.trans (Nat.lt_succ_self _).le

theorem length_mulTwo : (mulTwo s).length = 2 * s.length := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [mulTwo_nil, List.length_nil]
  · simp_rw [mulTwo_cons, List.length_append, length_split, List.length_cons, IH,
      Nat.mul_succ, add_comm]

theorem count_mulTwo (hs : ∀ a ∈ s, 0 < a.height) : count (mulTwo s) = count s := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [mulTwo_nil]
  · cases a
    · simp_rw [List.mem_cons, forall_eq_or_imp, height_leaf, lt_self_iff_false, false_and] at hs
    · simp_rw [List.mem_cons, forall_eq_or_imp, height_node, Nat.zero_lt_succ, true_and] at hs
      simp_rw [mulTwo_node_cons, count_cons, count_node, IH hs, add_assoc]

def addOne? : Option (BTree α) → BTStack α → BTStack α
  | none, s => s
  | some a, s => s ++ [a]

@[simp]
theorem addOne?_none : s.addOne? none = s := rfl

@[simp]
theorem addOne?_some : s.addOne? (some a) = s ++ [a] := rfl

def bit' (a : Option (BTree α)) (s : BTStack α) : BTStack α := s.mulTwo.addOne? a

def bit : Option (BTree α) → BTStack α → BTStack α
  | none, [] => []
  | some a, [] => [a]
  | a, b :: s => split b ++ bit a s

@[simp]
theorem bit_none_nil : bit none ([] : BTStack α) = [] := rfl

@[simp]
theorem bit_some_nil : bit (some a) ([] : BTStack α) = [a] := rfl

@[simp]
theorem bit_cons {a : Option (BTree α)} :
    bit a (b :: s) = split b ++ bit a s := by cases a <;> rfl

@[simp]
theorem bit_none : bit none s = s.mulTwo := by
  induction s
  · rfl
  · simp_rw [bit_cons, mulTwo_cons, List.append_cancel_left_eq]
    assumption

@[simp]
theorem bit_some : bit (some a) s = s.mulTwo ++ [a] := by
  induction s
  · rfl
  · simp_rw [bit_cons, mulTwo_cons, List.append_assoc, List.append_cancel_left_eq]
    assumption

@[simp]
theorem bit_leaf_cons {a : Option (BTree α)} :
    bit a (leaf c :: s) = leaf c :: bit a s := by cases a <;> rfl

@[simp]
theorem bit_node_cons {a : Option (BTree α)} : bit a (node l r :: s) = l :: r :: bit a s := by
  cases a <;> rfl

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

def modTwo (s : BTStack α) : Option (BTree α) := if h : Odd s.length then
    some (s.getLast (List.ne_nil_of_length_pos h.pos)) else none

@[simp] theorem modTwo_nil : modTwo ([] : BTStack α) = none := rfl
@[simp] theorem modTwo_singleton : modTwo [a] = a := rfl
@[simp] theorem modTwo_cons_cons : modTwo (l :: r :: s) = modTwo s := by
  unfold modTwo
  simp_rw [List.length_cons, Nat.odd_add_one, not_not, List.getLast_cons_cons, dite_eq_ite]
  refine dite_congr rfl (fun h => ?_) (fun _ => rfl)
  simp_rw [Option.some_inj, List.getLast_cons (List.ne_nil_of_length_pos h.pos)]

@[simp]
theorem bit_modTwo_divTwo : bit (s.modTwo) (s.divTwo) = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [modTwo_nil, divTwo_nil, bit_none_nil]
  · simp_rw [modTwo_singleton, divTwo_singleton, bit_some_nil]
  · simp_rw [modTwo_cons_cons, divTwo_cons_cons, bit_node_cons, IH]

theorem bit_modTwo_node_cons_divTwo : bit (s.modTwo) (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [bit_node_cons, bit_modTwo_divTwo]

theorem length_divTwo : (divTwo s).length = s.length / 2 := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [divTwo_nil, List.length_nil]
  · simp_rw [divTwo_singleton, List.length_cons, List.length_nil]
  · simp_rw [divTwo_cons_cons, List.length_cons, IH, add_assoc,
        one_add_one_eq_two, Nat.add_div_right _ zero_lt_two]

theorem length_divTwo_lt_length_of_ne_nil (hs : s ≠ []) :
    (divTwo s).length < s.length := by
  rw [length_divTwo]
  exact Nat.div_lt_self (List.length_pos_of_ne_nil hs) one_lt_two

theorem length_divTwo_le_length :
    (divTwo s).length ≤ s.length := by
  rw [length_divTwo]
  exact Nat.div_le_self _ _
#check Nat.div2Induction

@[elab_as_elim, specialize]
def divTwoInduction'' {motive : BTStack α → Sort u} (nil : motive [])
    (bit_n : ∀ s, motive (divTwo s) → motive s)
    (bit_s : BTree α → (s : BTStack α) → motive (divTwo s) → motive s) (s : BTStack α) : motive s :=
  s.recOn nil (fun a s rec => match hs : modTwo s with
    | none => _
    | some a => _)

@[elab_as_elim, specialize]
def divTwoInduction {motive : BTStack α → Sort u} (nil : motive [])
    (bit_n : ∀ s, s ≠ [] → (∀ a, s ≠ [a]) → motive (divTwo s) → motive s)
    (bit_s : (a : BTree α) → (s : BTStack α) → s ≠ [] → modTwo s = some a → motive (divTwo s) → motive s) : ∀ s, motive s
  | [] => nil
  | [a] => bit_s a _ (List.cons_ne_nil _ _) _ nil
  | l :: r :: s => match h : modTwo s with
    | none => bit_n (l :: r :: s) (List.cons_ne_nil _ _)
        (by simp_rw [List.cons_eq_cons.not, not_and, List.cons_ne_nil,
          not_false_eq_true, implies_true])
        (divTwoInduction nil bit_n bit_s (node l r :: divTwo s))
    | some a => bit_s a (l :: r :: s) (List.cons_ne_nil _ _) _ (divTwoInduction nil bit_n bit_s (node l r :: divTwo s))
  termination_by s => s.length
  decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.succ_le_succ length_divTwo_le_length)

@[elab_as_elim, specialize]
def divTwoInduction {motive : BTStack α → Sort u} (nil : motive [])
    (bit_n : ∀ s, divTwo s ≠ [] → motive (divTwo s) → motive s)
    (bit_s : BTree α → (s : BTStack α) → motive (divTwo s) → motive s) : ∀ s, motive s
  | [] => nil
  | [a] => bit_s a [a] nil
  | l :: r :: s => match modTwo s with
    | none => bit_n (l :: r :: s) (List.cons_ne_nil _ _)
        (divTwoInduction nil bit_n bit_s (node l r :: divTwo s))
    | some a => bit_s a (l :: r :: s) (divTwoInduction nil bit_n bit_s (node l r :: divTwo s))
  termination_by s => s.length
  decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.succ_le_succ length_divTwo_le_length)

@[elab_as_elim, specialize]
def divTwoInduction' {motive : BTStack α → Sort u} (nil : motive [])
    (bit_n : ∀ s, s ≠ [] → modTwo s = none → motive (divTwo s) → motive s)
    (bit_s : ∀ a s, modTwo s = some a → motive (divTwo s) → motive s) : ∀ s, motive s
  | [] => nil
  | [a] => bit_s a [a] modTwo_singleton nil
  | l :: r :: s => match h : modTwo s with
    | none => bit_n _ (List.cons_ne_nil _ _) (modTwo_cons_cons.trans h) (divTwoInduction' nil bit_n bit_s _)
    | some a => bit_s _ _ (modTwo_cons_cons.trans h) (divTwoInduction' nil bit_n bit_s _)
  termination_by s => s.length
  decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.succ_le_succ length_divTwo_le_length)

@[elab_as_elim, specialize]
def divTwoInduction''' {motive : BTStack α → Sort u} (nil : motive []) (singleton : ∀ a, motive [a])
    (bit_n : ∀ l r s, modTwo s = none → motive (node l r :: divTwo s) → motive (l :: r :: s))
    (bit_s : ∀ a l r s, modTwo s = some a → motive (node l r :: divTwo s) →
      motive (l :: r :: s)) : ∀ s, motive s
  | [] => nil
  | [a] => singleton a
  | l :: r :: s => match h : modTwo s with
    | none => bit_n _ _ _ h _
    | some a => bit_s _ _ _ _ _ _
  termination_by s => s.length
  decreasing_by all_goals exact Nat.lt_succ_of_le (Nat.succ_le_succ length_divTwo_le_length)

@[elab_as_elim, specialize]
def binaryRec {motive : BTStack α → Sort u} (nil : motive [])
    (bit_n : ∀ a s, motive s → motive (bit a s)) : ∀ s, motive s
  | [] => nil
  | [a] => bit (some a) [] nil
  | l :: r :: s => bit_modTwo_node_cons_divTwo ▸
      bit (modTwo s) (node l r :: divTwo s) (binaryRec nil bit _)
  termination_by s => s.length
  decreasing_by exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

@[elab_as_elim, specialize]
def binaryRec {motive : BTStack α → Sort u} (nil : motive [])
    (bit : ∀ a s, motive s → motive (bit a s)) : ∀ s, motive s
  | [] => nil
  | [a] => bit (some a) [] nil
  | l :: r :: s => bit_modTwo_node_cons_divTwo ▸
      bit (modTwo s) (node l r :: divTwo s) (binaryRec nil bit _)
  termination_by s => s.length
  decreasing_by exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

@[simp]
theorem binaryRec_nil {motive : BTStack α → Sort u} {nil : motive []}
    {bit : ∀ a s, motive s → motive (bit a s)} : binaryRec nil bit [] = nil := by rw [binaryRec]

@[simp]
theorem binaryRec_singleton {motive : BTStack α → Sort u} {nil : motive []}
    {bit : ∀ a s, motive s → motive (bit a s)} :
    binaryRec (motive := motive) nil bit [a] = bit (some a) [] nil := by rw [binaryRec]

theorem binaryRec_cons_cons {motive : BTStack α → Sort u} {nil : motive []}
    {bit : ∀ a s, motive s → motive (bit a s)} :
    binaryRec (motive := motive) nil bit (l :: r :: s) =
    bit_modTwo_node_cons_divTwo ▸
    bit (modTwo s) (node l r :: divTwo s) (binaryRec (motive := motive) nil bit _) := by
  rw [binaryRec]



@[elab_as_elim, specialize]
def bitRec {motive : BTStack α → Sort u} (nil : motive []) (singleton : ∀ a, motive [a])
    (bith_n : ∀ s, s ≠ [] → motive s → motive (mulTwo s))
    (bith_s : ∀ a s, s ≠ [] → motive s → motive (mulTwo s ++ [a]))
    : ∀ s, motive s
  | [] => nil
  | [a] => singleton a
  | l :: r :: s => match h : (modTwo s) with
    | none =>  bith_n _ _ _
    | some a => _
  termination_by s => s.length
  decreasing_by exact Nat.succ_lt_succ (Nat.lt_succ_of_le length_divTwo_le_length)

def squashStack (s : BTStack α) : BTStack α :=
  s.bitRec [] ([·]) (fun a l r s rec => rec)

#eval squashStack [leaf 1, leaf 2, leaf 3, leaf 4, leaf 5, leaf 6]

@[simp]
theorem bitRec_nil {motive : BTStack α → Sort u} {nil : motive []} {singleton : ∀ a, motive [a]}
    {bith : ∀ a s, s ≠ [] → motive s → motive (bit a s)} :
    bitRec nil singleton bith [] = nil := by rw [bitRec]

@[simp]
theorem bitRec_singleton {motive : BTStack α → Sort u} {nil : motive []} {singleton : ∀ a, motive [a]}
    {bith : ∀ a s, s ≠ [] → motive s → motive (bit a s)} :
    bitRec nil singleton bith [a] = singleton a := by rw [bitRec]

@[simp]
theorem bitRec_cons_cons {motive : BTStack α → Sort u} {nil : motive []} {singleton : ∀ a, motive [a]}
    {bith : ∀ a s, s ≠ [] → motive s → motive (bit a s)} :
    bitRec nil singleton bith (l :: r :: s) = bit_modTwo_node_cons_divTwo ▸
    bith (modTwo s) (node l r :: divTwo s) (List.cons_ne_nil _ _)
    (bitRec (motive := motive) nil singleton bith _) := by rw [bitRec]


/-
@[elab_as_elim, specialize]
def binaryRec' {motive : BTStack α → Sort u} (nil : motive [])
    (bith : ∀ a s, (s = [] → a.isSome) → motive s → motive (bit a s)) (s : BTStack α) : motive s :=
  s.binaryRec nil (fun a => a.recOn
    (fun s => s.recOn (fun _ => nil) (fun _ _ _ => bith _ _ (fun h => nomatch h)))
    (fun _ s => s.recOn (bith _ _ (fun _ => rfl)) fun _ _ _ => bith _ _ (fun h => nomatch h)))

@[elab_as_elim, specialize]
def binaryRecFromOne {motive : BTStack α → Sort u} (nil : motive []) (singleton : ∀ a, motive [a])
    (bith : ∀ a s, s ≠ [] → motive s → motive (bit a s)) (s : BTStack α) : motive s :=
  s.binaryRec nil (fun a s => s.recOn (a.recOn (fun _ => nil) (fun a _ => singleton a))
  fun _ _ _ => bith _ _ (List.cons_ne_nil _ _))-/


/-
  if 0 < s.length then match modTwo s with
    | none => squashStack (divTwo s)
    | some a => a :: squashStack (divTwo s)
  else []
  termination_by s.length
  decreasing_by exact length_divTwo_lt_length_of_ne_nil (List.ne_nil_of_length_pos (by assumption))-/

@[simp] theorem divModTwo_eq_divTwo_modTwo {s : BTStack α} :
    divModTwo s = (modTwo s, divTwo s) := match s with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: s => by
    unfold divModTwo
    simp_rw [divModTwo_eq_divTwo_modTwo (s := s), divTwo_cons_cons, modTwo_cons_cons]

theorem modTwo_eq_dite_odd : modTwo s = if hs : Odd s.length then
    some (s.getLast (List.ne_nil_of_length_pos hs.pos)) else none := rfl

theorem modTwo_eq_dite_even : modTwo s = if h : Even s.length then none else
    some (s.getLast (List.ne_nil_of_length_pos (Nat.not_even_iff_odd.mp h).pos)) := by
  simp_rw [modTwo_eq_dite_odd, ← Nat.not_odd_iff_even, dite_not]

theorem modTwo_eq_some_of_length_odd (hs : Odd s.length) : modTwo s =
    some (s.getLast (List.ne_nil_of_length_pos hs.pos)) := dif_pos hs

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
  unfold modTwo
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

theorem divTwo_append_singleton :
    divTwo (s ++ [b]) = divTwo s ++ (s.modTwo.elim [] ([node · b])) := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [List.nil_append, divTwo_singleton, divTwo_nil, modTwo_nil,
      Option.elim_none, List.append_nil]
  · simp_rw [divTwo_singleton, modTwo_singleton, List.singleton_append, divTwo_cons_cons,
      divTwo_nil, Option.elim_some, List.nil_append]
  · simp only [List.cons_append, divTwo_cons_cons, IH, modTwo_cons_cons]


theorem divTwo_append_singleton_of_modTwo_eq_some (hs : modTwo s = some a) :
    divTwo (s ++ [b]) = divTwo s ++ [node a b] := by
  simp_rw [divTwo_append_singleton, hs, Option.elim_some]

theorem divTwo_append_singleton_of_modTwo_eq_none (hs : modTwo s = none) :
    divTwo (s ++ [b]) = divTwo s := by
  simp_rw [divTwo_append_singleton, hs, Option.elim_none, List.append_nil]

theorem divTwo_append_singleton_of_length_even (hs : Even s.length) :
    divTwo (s ++ [b]) = divTwo s := by
  simp_rw [divTwo_append_singleton_of_modTwo_eq_none (modTwo_eq_none_of_length_even hs)]

theorem divTwo_append_singleton_of_length_odd (hs : Odd s.length) :
    divTwo (s ++ [b]) = divTwo s ++ [node (s.getLast (List.ne_nil_of_length_pos hs.pos)) b] := by
  simp_rw [divTwo_append_singleton_of_modTwo_eq_some (modTwo_eq_some_of_length_odd hs)]

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


def squashStack' (s : BTStack α) : BTStack α :=
  s.divTwoInduction' [] (fun _ _ s => s) (fun a _ _ s => a :: s)

def squashStack (s : BTStack α) : BTStack α :=
  s.divTwoInduction [] (fun _ s => s) (fun a _ s => a :: s)

def squashStack'' (s : BTStack α) : BTStack α :=
  s.binaryRec [] (fun a _ rec => a.elim rec (· :: rec))

#eval squashStack [leaf 1, leaf 2, leaf 3, leaf 4, leaf 5, leaf 6, leaf 7, leaf 8]
#eval squashStack' [leaf 1, leaf 2, leaf 3, leaf 4, leaf 5, leaf 6, leaf 7, leaf 8]

#eval squashStack'' [leaf 1, leaf 2, leaf 3, leaf 4, leaf 5, leaf 6, leaf 7, leaf 8]


def squashStack'4 (s : BTStack α) : BTStack α :=
  if 0 < s.length then match modTwo s with
    | none => squashStack'4 (divTwo s)
    | some a => a :: squashStack'4 (divTwo s)
  else []
  termination_by s.length
  decreasing_by exact length_divTwo_lt_length_of_ne_nil (List.ne_nil_of_length_pos (by assumption))

@[simp]
theorem squashStack_nil : squashStack ([] : BTStack α) = [] := by
  unfold squashStack
  rw [divTwoInduction]

theorem squashStack_of_modTwo_some (hs : modTwo s = some a) :
    squashStack' s = a :: (divTwo s).squashStack' := by
  rw [squashStack', divTwoInduction'.eq_def]
  cases s
  · contradiction
  · simp
    rw [List.length_cons, if_pos (Nat.zero_lt_succ _), hs]

theorem squashStack_of_modTwo_none (hs : modTwo s = none) :
    squashStack s = (divTwo s).squashStack := by
  cases s
  · simp_rw [divTwo_nil]
  · rw [squashStack.eq_def, List.length_cons, if_pos (Nat.zero_lt_succ _), hs]

@[simp]
theorem squashStack_singleton : squashStack [a] = [a] := by
  rw [squashStack_of_modTwo_some modTwo_singleton, divTwo_singleton, squashStack_nil]

theorem squashStack_append_singleton_of_modTwo_none (hs : modTwo s = none) :
    squashStack (s ++ [a]) = a :: squashStack s := by
  rw [squashStack_of_modTwo_some
    (modTwo_append_singleton_of_length_even (modTwo_eq_none_iff.mp hs)),
    divTwo_append_singleton_of_modTwo_eq_none hs, squashStack_of_modTwo_none hs]

theorem squashStack_append_singleton_of_modTwo_some (hs : modTwo s = some a) :
    squashStack (s ++ [b]) = squashStack (s.divTwo ++ [node a b]) := by
  rw [squashStack_of_modTwo_none (modTwo_append_singleton_of_length_odd
    (modTwo_eq_some_iff.mp hs).1), divTwo_append_singleton_of_modTwo_eq_some hs]

theorem squashStack_two_pow :
    ∀ s, s.length = 2^n → ∃ d : BTree α, squashStack s = [d] := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, List.length_eq_one_iff, forall_exists_index]
    intro _ _ hx
    simp_rw [hx, squashStack_singleton, List.cons_eq_cons, and_true, exists_eq']
  · intro s hs
    have hs' : modTwo s = none := by simp_rw [modTwo_eq_none_iff, hs, pow_succ', Nat.mul_mod_right]
    simp_rw [squashStack_of_modTwo_none hs']
    exact IH _ (length_divTwo ▸ hs ▸ by simp_rw [pow_succ', mul_div_cancel_left₀ _ two_ne_zero])

def firstHeight : BTStack α → ℕ
  | [] => 0
  | (a :: _) => a.height

section FirstHeight

@[simp] theorem firstHeight_nil : firstHeight ([] : BTStack α) = 0 := rfl

@[simp] theorem firstHeight_singleton : firstHeight [a] = a.height := rfl

@[simp] theorem firstHeight_cons : firstHeight (a :: s) = a.height := rfl

@[simp] theorem firstHeight_append_singleton (hs : s ≠ []) :
    firstHeight (s ++ [a]) = firstHeight s := by
  cases s
  · contradiction
  · rfl

@[simp] theorem firstHeight_append (hs : s ≠ []) :
    firstHeight (s ++ t) = firstHeight s := by
  cases s
  · contradiction
  · rfl

theorem firstHeight_eq_head_height (hs) : firstHeight s = (s.head hs).height := by
  cases s
  · contradiction
  · rfl

end FirstHeight

def lastHeight : BTStack α → ℕ
  | [] => 0
  | [a] => a.height
  | _ :: b :: s => lastHeight (b :: s)

section LastHeight

@[simp] theorem lastHeight_nil : lastHeight ([] : BTStack α) = 0 := rfl

@[simp] theorem lastHeight_singleton : lastHeight [a] = a.height := rfl

@[simp] theorem lastHeight_cons (hs : s ≠ []) : lastHeight (a :: s) = lastHeight s := by
  cases s
  · contradiction
  · rfl

@[simp] theorem lastHeight_append_singleton : lastHeight (s ++ [a]) = a.height := by
  induction s with | nil => _ | cons _ s => _
  · rfl
  · cases s
    · rfl
    · assumption

@[simp] theorem lastHeight_reverse_eq_firstHeight {s : BTStack α} :
    lastHeight s.reverse = firstHeight s := by
  cases s
  · rfl
  · simp_rw [List.reverse_cons, lastHeight_append_singleton, firstHeight_cons]

@[simp] theorem firstHeight_reverse_eq_lastHeight {s : BTStack α} :
    firstHeight s.reverse = lastHeight s := by
  rw [← s.reverse_reverse, lastHeight_reverse_eq_firstHeight, s.reverse_reverse]

theorem lastHeight_eq_getLast_height (hs) : lastHeight s = (s.getLast hs).height := by
  cases s using List.reverseRecOn
  · exact hs.irrefl.elim
  · simp_rw [lastHeight_append_singleton, List.getLast_append_singleton]

end LastHeight

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

theorem IsSMH.height_cons_lt_firstHeight (hsh : IsSMH (a :: s)) (hs : s ≠ []) :
    a.height < s.firstHeight :=
  (hsh.cons_height_lt_height_of_mem _ (List.head_mem _)).trans_eq
    (firstHeight_eq_head_height hs).symm

theorem IsSMH.firstHeight_le_mem (hsh : IsSMH s) : ∀ a ∈ s, s.firstHeight ≤ a.height := by
  cases s with | nil => _ | cons a s => _
  · exact fun _ ha => (List.not_mem_nil _ ha).elim
  · simp_rw [firstHeight_cons, List.mem_cons]
    exact fun _ ha => ha.elim
      (fun H => H ▸ le_rfl)
      (fun hb => hsh.cons_height_le_height_of_mem _ hb)

theorem IsSMH.firstHeight_cons_lt (hsh : IsSMH (a :: s)) :
    ∀ b ∈ s, firstHeight (a :: s) < b.height := by
  simp_rw [firstHeight_cons]
  exact hsh.cons_height_lt_height_of_mem

theorem IsSMH.lastHeight_lt_height_append_singleton (hsh : IsSMH (s ++ [a])) (hs : s ≠ []) :
    s.lastHeight < a.height :=
  (hsh.height_lt_append_singleton_height_of_mem _ (List.getLast_mem _)).trans_eq'
  (lastHeight_eq_getLast_height hs)

theorem IsSMH.mem_le_lastHeight (hsh : IsSMH s) : ∀ a ∈ s, a.height ≤ s.lastHeight := by
  cases s using List.reverseRecOn with | nil => _ | append_singleton s a => _
  · exact fun _ ha => (List.not_mem_nil _ ha).elim
  · simp_rw [lastHeight_append_singleton, List.mem_append, List.mem_singleton]
    exact fun _ ha => ha.elim
      (fun hb => hsh.height_le_append_singleton_height_of_mem _ hb)
      (fun H => H ▸ le_rfl)

theorem IsSMH.lt_lastHeight_append_singleton (hsh : IsSMH (s ++ [a])) :
    ∀ b ∈ s, b.height < (s ++ [a]).lastHeight  := by
  simp_rw [lastHeight_append_singleton]
  exact hsh.height_lt_append_singleton_height_of_mem

theorem IsSMH.firstHeight_lt_lastHeight_iff_one_lt_length (hsh : IsSMH s) (hs : s ≠ []) :
    s.firstHeight < s.lastHeight ↔ 1 < s.length := by
  cases s with | nil => _ | cons _ s => _
  · exact hs.irrefl.elim
  · simp_rw [List.length_cons, lt_add_iff_pos_left]
    cases s using List.reverseRecOn
    · simp_rw [firstHeight_cons, lastHeight_singleton, List.length_nil, lt_irrefl]
    · simp_rw [firstHeight_cons, ← List.cons_append, lastHeight_append_singleton,
        List.length_append, List.length_singleton, NeZero.pos,
        hsh.cons_height_lt_append_singleton_height]

theorem IsSMH.firstHeight_le_lastHeight (hsh : IsSMH s) (hs : s ≠ []) :
    s.firstHeight ≤ s.lastHeight := by
  have hs' := Nat.one_le_of_lt (List.length_pos_of_ne_nil hs)
  rcases hs'.eq_or_gt with (hs' | hs')
  · rw [List.length_eq_one_iff] at hs'
    rcases hs' with ⟨_, rfl⟩
    simp_rw [firstHeight_singleton, lastHeight_singleton, le_rfl]
  · rw [← hsh.firstHeight_lt_lastHeight_iff_one_lt_length hs] at hs'
    exact hs'.le

theorem length_le_lastHeight_sub_firstHeight (hsh : IsSMH s) :
    s.length ≤ (s.lastHeight - s.firstHeight) + 1 := by
  induction s with | nil => _ | cons a s IH => _
  · simp_rw [List.length_nil, lastHeight_nil, firstHeight_nil, tsub_zero, zero_add, zero_le_one]
  · specialize IH hsh.of_cons
    cases s using List.reverseRecOn
    · simp_rw [List.length_cons, List.length_nil, zero_add, lastHeight_singleton,
        firstHeight_cons, tsub_self, le_refl]
    · simp_rw [List.length_append, List.length_cons, List.length_nil, zero_add,
        lastHeight_append_singleton, add_le_add_iff_right,
        firstHeight_eq_head_height
        (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))] at IH
      simp_rw [List.length_cons, List.length_append, List.length_singleton, firstHeight_cons,
        ← List.cons_append,
        lastHeight_append_singleton, Nat.succ_le_succ_iff, Nat.succ_le_iff]
      exact IH.trans_lt (Nat.sub_lt_sub_left hsh.cons_height_lt_append_singleton_height
        (hsh.cons_height_lt_height_of_mem _ (List.head_mem _)))

end IsSMH

def IsPerfect (s : BTStack α) := ∀ b ∈ s, b.IsPerfect

section IsPerfect

@[simp] theorem IsPerfect_def : IsPerfect s ↔ ∀ b ∈ s, b.IsPerfect := Iff.rfl

@[simp] theorem IsPerfect_nil : IsPerfect ([] : BTStack α) :=
  fun _ h => (List.not_mem_nil _ h).elim

@[simp] theorem IsPerfect_cons_iff : IsPerfect (a :: s) ↔ a.IsPerfect ∧ IsPerfect s := by
  simp_rw [IsPerfect_def, List.mem_cons, forall_eq_or_imp]

@[simp] theorem IsPerfect.of_cons_head : IsPerfect (a :: s) → a.IsPerfect :=
  fun h => (IsPerfect_cons_iff.mp h).1
@[simp] theorem IsPerfect.of_cons_tail : IsPerfect (a :: s) → IsPerfect s :=
  fun h => (IsPerfect_cons_iff.mp h).2

theorem IsPerfect.cons_of (ha : a.IsPerfect) : IsPerfect s → IsPerfect (a :: s) :=
  fun h => IsPerfect_cons_iff.mpr ⟨ha, h⟩

@[simp] theorem IsPerfect_append :
    IsPerfect (s ++ t) ↔ IsPerfect s ∧ IsPerfect t := by
  simp_rw [IsPerfect_def, List.mem_append, or_imp, forall_and]

@[simp] theorem IsPerfect_singleton_iff : IsPerfect [a] ↔ a.IsPerfect := by
  simp_rw [IsPerfect_def, List.mem_singleton, forall_eq]

@[simp] theorem IsPerfect_append_singleton_iff :
    IsPerfect (s ++ [a]) ↔ IsPerfect s ∧ a.IsPerfect := by
  simp_rw [IsPerfect_append, IsPerfect_singleton_iff]

end IsPerfect

def push (b : BTree α) : BTStack α → BTStack α
  | [] => [b]
  | a :: s => if a.height ≤ b.height then
    push (node (a.addToHeight (b.height - a.height)) b) s else b :: a :: s

section Push

@[simp] theorem push_nil : push a ([] : BTStack α) = [a] := rfl

@[simp] theorem push_cons_of_height_lt (h : b.height < a.height) :
    push b (a :: s) =  b :: a :: s := by
  unfold push
  simp_rw [if_neg h.not_le]

@[simp] theorem push_cons_of_height_ge (h : a.height ≤ b.height) :
    push b (a :: s) = push (node (a.addToHeight (b.height - a.height)) b) s := by
  rw [push]
  simp_rw [if_pos h]

@[simp] theorem push_cons_of_height_eq (h : a.height = b.height) :
    push b (a :: s) = s.push (node a b) := by
  simp_rw [push_cons_of_height_ge h.le, h, Nat.sub_self, addToHeight_zero]

@[simp] theorem mem_push_nil : c ∈ push b [] ↔ c = b := by
  simp_rw [push_nil, List.mem_singleton]

@[simp] theorem mem_push_cons_of_height_lt (h : b.height < a.height) :
    c ∈ push b (a :: s) ↔ c = b ∨ c = a ∨ c ∈ s  := by
  simp_rw [push_cons_of_height_lt h, List.mem_cons]

@[simp] theorem mem_push_cons_of_height_ge (h : a.height ≤ b.height) :
    c ∈ push b (a :: s) ↔ c ∈ s.push (node (a.addToHeight (b.height - a.height)) b) := by
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

theorem push_of_lt_firstHeight (hbs : b.height < s.firstHeight) : s.push b = b :: s := by
  cases s
  · simp_rw [push_nil]
  · exact push_cons_of_height_lt hbs

theorem height_le_firstHeight_push : b.height ≤ (s.push b).firstHeight := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · rw [push_nil, firstHeight_singleton]
  · by_cases hab : a.height ≤ b.height
    · rw [push_cons_of_height_ge hab]
      exact (IH.trans_lt' right_height_lt).le
    · rw [push_cons_of_height_lt (lt_of_not_le hab), firstHeight_cons]

theorem firstHeight_push_of_height_ne_firstHeight (hb : b.height < s.firstHeight) :
    (s.push b).firstHeight = b.height := by
  rw [push_of_lt_firstHeight hb, firstHeight_cons]

theorem firstHeight_push_nil : (push b []).firstHeight = b.height := by
  rw [push_nil, firstHeight_singleton]

theorem firstHeight_push_of_firstHeight_le_of_ne_nil (hbs : s.firstHeight ≤ b.height)
    (hs : s ≠ []) : b.height < (s.push b).firstHeight := by
  cases s
  · exact hs.irrefl.elim
  · rw [firstHeight_cons] at hbs
    rw [push_cons_of_height_ge hbs]
    exact height_le_firstHeight_push.trans_lt' right_height_lt

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
    · simp_rw [push_cons_of_height_ge hab.ge, hab, Nat.sub_self, addToHeight_zero]
      by_cases hs : s = []
      · simp_rw [hs, push_nil, count_cons, count_node, count_nil, add_zero, add_comm]
      · rw [IH hsh.of_cons (fun _ hx => height_node_of_heights_eq hab.symm rfl ▸
          (Nat.succ_le_of_lt (hb.1.trans_lt (hsh.cons_height_lt_height_of_mem _ hx))))]
        simp_rw [count_node, count_cons, add_comm b.count, add_assoc, Nat.add_right_inj, add_comm]
    · simp_rw [push_cons_of_height_lt hab, count_cons]

theorem IsPerfect.push_of_IsPerfect (hb : b.IsPerfect) (has : IsPerfect s) :
    IsPerfect (s.push b) := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, IsPerfect_singleton_iff, hb]
  · by_cases hab : a.height ≤ b.height
    · simp_rw [push_cons_of_height_ge hab]
      refine IH (hb.node_of_IsPerfect_left_of_heights_eq has.of_cons_head.addToHeight ?_)
        has.of_cons_tail
      simp_rw [height_addToHeight, Nat.add_sub_cancel' hab]
    · simp_rw [IsPerfect_cons_iff] at has
      simp_rw [push_cons_of_height_lt (lt_of_not_le hab), IsPerfect_cons_iff]
      exact ⟨hb, has⟩

theorem IsSMH.height_ge_of_mem_push (hc : c ∈ s.push b) (hsh : IsSMH s) :
    b.height ≤ c.height := by
  induction s generalizing b c with | nil => _ | cons a s IH => _
  · simp_rw [mem_push_nil.mp hc, le_rfl]
  · by_cases hab : a.height ≤ b.height
    · rw [mem_push_cons_of_height_ge hab] at hc
      specialize IH hc
      simp_rw [height_node, height_addToHeight, Nat.add_sub_cancel' hab,
        max_self, Nat.succ_le_iff] at IH
      exact (IH hsh.of_cons).le
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

@[simp] theorem IsPerfect.pushStack (hs : IsPerfect s) (ht : IsPerfect t) :
    IsPerfect (pushStack s t) := by
  induction s generalizing t with | nil => _ | cons a s IH => _
  · exact ht
  · simp_rw [pushStack_cons]
    exact (IH hs.of_cons_tail ht).push_of_IsPerfect hs.of_cons_head

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
    exact hsh.lastHeight_lt_height_append_singleton

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

theorem IsPerfect.ofStack (hs : IsPerfect s) : s.ofStack.IsPerfect :=
  IsPerfect.pushStack hs IsPerfect_nil

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

theorem pushLeaf_of_one_le_firstHeight (hbs : 1 ≤ s.firstHeight) :
    s.pushLeaf x = (leaf x) :: s := push_of_lt_firstHeight (Nat.lt_of_succ_le hbs)

theorem pushLeaf_pushLeaf_of_one_le_firstHeight (hbs : 1 ≤ s.firstHeight) :
    (s.pushLeaf x).pushLeaf y = s.push (node (leaf x) (leaf y)) := by
  rw [pushLeaf_of_one_le_firstHeight hbs, pushLeaf_cons_leaf]

@[simp] theorem firstHeight_pushLeaf_of_one_le_firstHeight (hs : 1 ≤ s.firstHeight) :
    (s.pushLeaf x).firstHeight = 0 := by
  rw [pushLeaf_of_one_le_firstHeight hs, firstHeight_cons, height_leaf]

@[simp] theorem firstHeight_pushLeaf_nil : (pushLeaf x []).firstHeight = 0 :=
    firstHeight_singleton

@[simp] theorem one_le_firstHeight_pushLeaf_of_firstHeight_zero_of_ne_nil
    (hbs : s.firstHeight = 0) (hs : s ≠ []) : 1 ≤ (s.pushLeaf x).firstHeight := by
  cases s with | nil => _ | cons a s => _
  · exact hs.irrefl.elim
  · simp_rw [firstHeight_cons, height_eq_zero_iff] at hbs
    rcases hbs with ⟨_, rfl⟩
    rw [pushLeaf_cons_leaf]
    exact height_le_firstHeight_push.trans_eq' rfl

theorem IsSMH.pushLeaf (hsh : IsSMH s) : IsSMH (pushLeaf x s) := hsh.push_of

theorem IsPerfect.pushLeaf (hs : IsPerfect s) : IsPerfect (s.pushLeaf x) :=
  hs.push_of_IsPerfect IsPerfect_leaf

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

@[simp] theorem IsPerfect.pushLeafs (hsh : IsPerfect s) :
    IsPerfect (s.pushLeafs xs) := by
  induction xs generalizing s with | nil => _ | cons x xs IH => _
  · exact hsh
  · simp_rw [pushLeafs_cons]
    exact IH hsh.pushLeaf

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

theorem blahj (hs : s ≠ [] → xs.length.log2 ≤ s.firstHeight) : pushLeafs xs s = pushStack (ofLeafs xs) s := sorry

@[simp] theorem ofLeafs_IsSMH : IsSMH (ofLeafs xs) := IsSMH_nil.pushLeafs

@[simp] theorem ofLeafs_IsPerfect : IsPerfect (ofLeafs xs) := IsPerfect_nil.pushLeafs
#eval ofLeafs [leaf 1, leaf 2, leaf 3, leaf 4, leaf 5, leaf 6, leaf 7]
end OfLeafs
