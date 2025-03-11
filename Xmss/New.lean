import Mathlib

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

instance : NeZero t.count := ⟨Nat.not_eq_zero_of_lt height_lt_count⟩

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
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero, hl, false_or,
      List.length_eq_one] at hl'
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
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero, hl, false_or,
      List.length_eq_one] at hn
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
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero, hl, false_or,
      List.length_eq_one] at hn
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
  · simp_rw [pow_zero, List.length_eq_one] at hk
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
  · simp_rw [not_lt, Nat.le_one_iff_eq_zero_or_eq_one, List.length_eq_zero, hl, false_or,
      List.length_eq_one] at hn
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
