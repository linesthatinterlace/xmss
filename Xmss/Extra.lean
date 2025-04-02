import Xmss.Basic

namespace Nat

theorem size_two_mul [NeZero n] : (2*n).size = n.size + 1 := by
  refine size_bit (b := false) ?_
  simp_rw [bit_false, mul_ne_zero_iff]
  exact ⟨NeZero.ne 2, NeZero.ne n⟩

theorem size_two_mul_add_one : (2*n + 1).size = n.size + 1:= by
  refine size_bit (b := true) ?_
  simp_rw [bit_true, ne_eq, succ_ne_zero, not_false_eq_true]

theorem size_div_two_succ [NeZero n] : (n / 2).size + 1 = n.size := by
  rcases even_or_odd n with h | h
  · have : NeZero (n / 2) := ⟨Nat.div_ne_zero_iff.mpr <|
      ⟨zero_lt_two.ne', (NeZero.one_le).lt_of_ne (fun C => (not_even_one (C ▸ h)).elim)⟩⟩
    rw [← size_two_mul, two_mul_div_two_of_even h]
  · rw [← size_two_mul_add_one, two_mul_div_two_add_one_of_odd h]

theorem size_pred_pow {n : ℕ} : (2^n - 1).size = n := by
  cases n
  · simp_rw [pow_zero, Nat.sub_self, size_zero]
  · exact le_antisymm (size_le.mpr <| Nat.pred_lt_self (Nat.two_pow_pos _))
      (lt_size.mpr <| (Nat.le_pred_iff_lt (Nat.two_pow_pos _)).mpr
      (Nat.pow_lt_pow_succ one_lt_two))


end Nat

namespace List

theorem length_take_succ_length_div_two {l : List α} :
    (l.take ((l.length + 1) / 2)).length = (l.length + 1) / 2 := by
  simp_rw [List.length_take, min_eq_left_iff, Nat.div_le_iff_le_mul_add_pred zero_lt_two,
    two_mul, ← one_add_one_eq_two, Nat.add_sub_cancel, Nat.add_le_add_iff_right,
    Nat.le_add_right]

@[simp]
theorem length_take_pos {l : List α} {k : Nat} :
    0 < (l.take k).length ↔ 0 < l.length ∧ 0 < k := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

@[simp]
theorem length_drop_pos {l : List α} {k : Nat} : 0 < (l.drop k).length ↔ k < l.length := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

theorem length_take_lt_length {l : List α} :
    (List.take k l).length < l.length ↔ k < l.length := by
  simp_rw [length_take, min_lt_iff, lt_self_iff_false, or_false]

theorem length_drop_lt_length {l : List α} :
    (List.drop k l).length < l.length ↔ 0 < l.length ∧ 0 < k := by
  simp_rw [length_drop, tsub_lt_self_iff]

theorem length_drop_le_length_take {l : List α} :
    (l.drop k).length ≤ (l.take k).length ↔ (l.length + 1) / 2 ≤ k := by
  simp_rw [length_drop, length_take, le_min_iff, tsub_le_iff_right, le_add_iff_nonneg_right,
    zero_le, and_true, ← two_mul, Nat.div_le_iff_le_mul_add_pred zero_lt_two,
    ← one_add_one_eq_two, Nat.add_sub_cancel, Nat.add_le_add_iff_right]


end List

namespace BTree


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

variable {t : BTree α}

@[simp] theorem toList_leaf : (leaf a).toList = [a] := rfl
@[simp] theorem toList_node : (node l r).toList = l.toList ++ r.toList := rfl

/-
theorem toList_addToHeight : (t.addToHeight n).toList = (fun l => l ++ l)^[n] t.toList := by
  induction n
  · simp_rw [addToHeight_zero, Function.iterate_zero, id_eq]
  · simp_rw [addToHeight_succ, toList_node, Function.iterate_succ', Function.comp_apply]
    exact congrArg₂ _ (by assumption) (by assumption)
-/

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

section Skeleton

variable {t : BTree α}

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

end BTree

namespace BTStack

def toList : BTStack α → List α
  | [] => []
  | a :: s => a.toList ++ toList s

variable {s : BTStack α}

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

def bit (a : Option (BTree α)) (s : BTStack α) : BTStack α := s.mulTwo.addOne? a

@[simp]
theorem bit_none_nil : bit none ([] : BTStack α) = [] := rfl

@[simp]
theorem bit_some_nil : bit (some a) ([] : BTStack α) = [a] := rfl

@[simp]
theorem bit_cons {a : Option (BTree α)} :
    bit a (b :: s) = split b ++ bit a s := by cases a <;> cases b <;> rfl

@[simp]
theorem bit_none : bit none s = s.mulTwo := rfl

@[simp]
theorem bit_some : bit (some a) s = s.mulTwo ++ [a] := rfl

@[simp]
theorem bit_leaf_cons {a : Option (BTree α)} :
    bit a (leaf c :: s) = leaf c :: bit a s := by cases a <;> rfl

@[simp]
theorem bit_node_cons {a : Option (BTree α)} : bit a (node l r :: s) = l :: r :: bit a s := by
  cases a <;> rfl

@[simp]
theorem bit_modTwo_divTwo : bit s.modTwo s.divTwo = s := by
  induction s using List.doubleRec with | nil => _ | singleton a => _ | cons_cons a b l IH => _
  · simp_rw [modTwo_nil, divTwo_nil, bit_none_nil]
  · simp_rw [modTwo_singleton, divTwo_singleton, bit_some_nil]
  · simp_rw [modTwo_cons_cons, divTwo_cons_cons, bit_node_cons, IH]

theorem mulTwo_divTwo_of_modTwo_eq_none (hs : s.modTwo = none) : s.divTwo.mulTwo = s :=
    Eq.trans (hs ▸ rfl) bit_modTwo_divTwo

theorem mulTwo_divTwo_of_modTwo_eq_some (hs : s.modTwo = some a) : s.divTwo.mulTwo ++ [a] = s :=
    Eq.trans (hs ▸ rfl) bit_modTwo_divTwo

theorem bit_modTwo_node_cons_divTwo : bit (s.modTwo) (l.node r :: divTwo s) = l :: r :: s := by
  simp_rw [bit_node_cons, bit_modTwo_divTwo]

end BTStack
