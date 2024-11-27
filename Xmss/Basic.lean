import Xmss.Lib

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

end IsPerfect


def count : BTree α → ℕ
  | leaf _ => 1
  | node l r => l.count + r.count

section Count

@[simp] theorem count_lead : (leaf a).count = 1 := rfl

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

instance : NeZero (t.count) := ⟨Nat.not_eq_zero_of_lt height_lt_count⟩

theorem count_le_two_pow_height : t.count ≤ 2^t.height := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [count_lead, height_leaf, pow_zero, le_refl]
  · simp_rw [count_node, height_node, pow_succ', two_mul]
    exact Nat.add_le_add
      (IHL.trans (Nat.pow_le_pow_of_le one_lt_two (le_max_left _ _)))
      (IHR.trans (Nat.pow_le_pow_of_le one_lt_two (le_max_right _ _)))

theorem IsPerfect.count_eq_two_pow_height (ht : t.IsPerfect) : t.count = 2^t.height := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [count_lead, height_leaf, pow_zero]
  · simp_rw [IsPerfect_node_iff] at ht
    simp_rw [count_node, height_node, pow_succ', two_mul, ht.2.2, IHL ht.1, IHR ht.2.1, ht.2.2,
      max_self]

end Count

def ofList (l : List α) (hl : l ≠ []) : BTree α :=
    if h : l.length ≤ 1 then leaf (l.head hl) else
    node
    (ofList (l.take ((l.length + 1)/2))
      (List.take_ne_nil_iff.mpr ⟨(Nat.div_ne_zero_iff two_ne_zero).mpr
      (Nat.succ_le_succ (Nat.succ_le_of_lt (List.length_pos_of_ne_nil hl))), hl⟩))
    (ofList (l.drop ((l.length + 1)/2))
      (List.drop_ne_nil_iff.mpr ((Nat.div_lt_iff_lt_mul zero_lt_two).mpr
      (Nat.mul_two _ ▸ (add_lt_add_left (lt_of_not_le h) _)))))
  termination_by l.length

section OfList

variable {l : List α}

theorem ofList_of_length_eq_one (hl : l.length = 1)
    (h' := (List.ne_nil_of_length_pos (hl ▸ zero_lt_one))) :
    ofList l h' = leaf (l.head h') := by
  unfold ofList
  simp_rw [hl, le_rfl, dite_true]

theorem ofList_singleton : ofList [a] (List.cons_ne_nil _ _) = leaf a :=
  ofList_of_length_eq_one (List.length_singleton _)

theorem ofList_of_one_lt_length (hl : 1 < l.length)
    (hl' := (List.ne_nil_of_length_pos (zero_lt_one.trans hl))) :
  ofList l hl' = node
    (ofList (l.take ((l.length + 1)/2))
      (List.take_ne_nil_iff.mpr ⟨(Nat.div_ne_zero_iff two_ne_zero).mpr
      (Nat.succ_le_succ (Nat.succ_le_of_lt (List.length_pos_of_ne_nil hl'))), hl'⟩))
    (ofList (l.drop ((l.length + 1)/2))
      (List.drop_ne_nil_iff.mpr ((Nat.div_lt_iff_lt_mul zero_lt_two).mpr
      (Nat.mul_two _ ▸ (add_lt_add_left hl _))))) := by
  rw [ofList]
  simp_rw [hl.not_le, dite_false]

theorem height_ofList_of_length_eq_one (hl : l.length = 1)
  (h' := (List.ne_nil_of_length_pos (hl ▸ zero_lt_one))) :
    (ofList l h').height = 0 := by rw [ofList_of_length_eq_one hl, height_leaf]

theorem height_ofList_of_one_lt_length (hl : 1 < l.length)
    (hl' := (List.ne_nil_of_length_pos (zero_lt_one.trans hl)))  :
    (ofList l h').height = (l.length - 1).size := by
  generalize hl' : l.length = n

  rw [ofList_of_one_lt_length  hl, height_node]

theorem height_ofList_cons : (ofList (a :: l) (List.cons_ne_nil _ _)).height = l.length.size := by
  generalize hl' : l.length = n
  induction n using Nat.strongRecOn generalizing a l with | ind n IH => _
  simp_rw [ne_eq, cons_ne_nil, not_false_eq_true, forall_true_left] at IH
  by_cases hn : 1 < n
  · have H := List.length_drop_le_length_take_iff_ge_succ_length_div_two (l := l).mpr le_rfl
    simp_rw [ofList_of_one_lt_length (hl' ▸ hn), height_node]
    rw [IH _ _ List.length_take_succ_length_div_two, IH _ _ List.length_drop_succ_length_div_two,
    max_eq_left ]
    sorry

    have HT : (List.take ((l.length + 1) / 2) l).length = (l.length + 1) / 2 :=
      List.length_take_succ_length_div_two
    have HD : (List.drop ((l.length + 1) / 2) l).length = l.length / 2 :=
      List.length_drop_succ_length_div_two

    rw [IH _ _ HT, IH _ _ HD]

/-
len height (len + 1).log1
1 0  0
2 1
3 2
4 2
5 3
6 3
7 3
8 3
9 4

-/

theorem height_ofList {hl : l ≠ []} : (ofList l hl).height = (l.length - 1).size := by
  generalize hl' : l.length = n
  induction n using Nat.strongRecOn generalizing l with | ind n IH => _
  by_cases hn : 1 < n
  · have H := List.length_drop_le_length_take_iff_ge_succ_length_div_two (l := l).mpr le_rfl
    simp_rw [ofList_of_one_lt_length (hl' ▸ hn), height_node]
    rw [IH _ _ List.length_take_succ_length_div_two, IH _ _ List.length_drop_succ_length_div_two,
    max_eq_left ]
    sorry

    have HT : (List.take ((l.length + 1) / 2) l).length = (l.length + 1) / 2 :=
      List.length_take_succ_length_div_two
    have HD : (List.drop ((l.length + 1) / 2) l).length = l.length / 2 :=
      List.length_drop_succ_length_div_two

    rw [IH _ _ HT, IH _ _ HD]


    /-cases n with | zero => _ | succ n => _
  · simp_rw [List.length_eq_zero, hl, IsEmpty.forall_iff]
  · cases n with | zero => _ | succ n => _
    · rw [List.length_eq_one]
      rintro ⟨_, rfl⟩
      rw [ofList_singleton, height_leaf, Nat.size_zero]
    · simp_rw [add_tsub_cancel_right]
      intro h
      have H : 1 < l.length := h ▸ (Nat.succ_lt_succ (Nat.succ_pos _))
      rw [ofList_of_one_lt_length H]
      have HT : (List.take ((l.length + 1) / 2) l).length = (n + 1 + 1 + 1) / 2 := by
        simp_rw [List.length_take, h]

      rw [IH]

  revert hl'
  intro hn
  rcases Nat.exists_eq_add_of_lt (hn ▸ List.length_pos_of_ne_nil hl) with ⟨n, rfl⟩
  revert hn
  simp_rw [zero_add, add_tsub_cancel_right]
  rw [← Nat.bit_testBit_zero_shiftRight_one n]
  cases n with | zero => _ | succ n => _
  · rw [List.length_eq_one]
    rintro ⟨_, rfl⟩
    rw [ofList_singleton, height_leaf, Nat.size_zero]
  · simp_rw [add_assoc, one_add_one_eq_two]
    induction n using Nat.strongRecOn generalizing l with | ind n IH => _
    intro h
    have H : 1 < l.length := h ▸ (Nat.succ_lt_succ (Nat.succ_pos _))
    simp_rw [ofList_of_one_lt_length H, height_node, h, add_assoc]
    rw [IH]
  induction n using Nat.binaryRecFromOne generalizing l with | z₀ => _ | z₁ => _ | f b n hn IH => _
  · rw [List.length_eq_one]
    rintro ⟨_, rfl⟩
    rw [ofList_singleton, height_leaf, Nat.size_zero]
  · sorry
  · rw [Nat.size_bit (Nat.bit_ne_zero _ hn)]
    intro h
    have H : 1 < l.length := h ▸ (Nat.succ_lt_succ (Nat.pos_of_ne_zero (Nat.bit_ne_zero _ hn)))
    simp_rw [ofList_of_one_lt_length H, height_node, h, add_assoc, one_add_one_eq_two,
      Nat.add_div_right _ zero_lt_two, Nat.bit_div_two]

    · simp_rw [List.length_drop, h, add_assoc, one_add_one_eq_two, Nat.add_div_right _ zero_lt_two,
        Nat.bit_div_two, Nat.add_sub_add_right]
      exact h ▸ Nat.bit_div_two b _ ▸ _

  rcases lt_or_le 1 n with (h | h)
  · intro hln
    rw [← hln] at h
    induction n using Nat.div2Induction generalizing l with | ind n IH => _
    rw [ofList_of_one_lt_length, height_node]
    revert n
  · rw [Nat.le_one_iff_eq_zero_or_eq_one] at h
    rcases h with (rfl | rfl)
    · simp_rw [List.length_eq_zero, hl, IsEmpty.forall_iff]
    · rw [List.length_eq_one]
      rintro ⟨_, rfl⟩
      rw [ofList_singleton, height_leaf, Nat.log2_one]
  induction n using Nat.div2Induction generalizing l with | ind n IH => _
  cases n with | zero => _ | succ n => _
  · simp_rw [List.length_eq_zero, hl, IsEmpty.forall_iff]
  ·
  · simp_rw [List.length_eq_zero, hl, IsEmpty.forall_iff]
  · cases n with | zero => _ | succ n => _
    · rw [zero_add]
      exact fun h => ofList_of_length_eq_one h ▸ (Nat.log2_one).symm
    · -/

end OfList

def toList : BTree α → List α
  | leaf a => [a]
  | node l r => toList l ++ toList r

/-

def ofList (l : List α) (hl : l ≠ []) : BTree α :=
    if h : l.length ≤ 1 then leaf (l.head hl) else
    node
    (ofList (l.take ((l.length + 1)/2)) (List.length_pos.mp
    (by simp_rw [List.length_take, lt_min_iff, Nat.div_pos_iff two_ne_zero,
      Nat.succ_le_succ_iff, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero,
      and_self, ne_eq, List.length_eq_zero, hl, not_false_eq_true])))
    (ofList (l.drop ((l.length + 1)/2)) (List.length_pos.mp
    (by simp_rw [List.length_drop, tsub_pos_iff_lt, Nat.div_lt_iff_lt_mul zero_lt_two,
      Nat.mul_two, add_lt_add_iff_left, lt_of_not_le h])))
  termination_by l.length
-/
def blahj (l : List α) : List (List α) :=
  if l.length = 0 then [] else
  blahj (l.drop (2^(l.length.log2))) ++ [(l.take (2^(l.length.log2)))]
  termination_by l.length

#eval Nat.bitIndices 3
#eval blahj ["a", "b", "c"]



#eval ofList' [3, 4, 5, 6, 7] (by decide)

def ofList : {n : ℕ} → (l : List α) → l.length = 2^n → BTree α
  | 0 => fun l hl => leaf (l.head (List.length_pos.mp (hl ▸ Nat.two_pow_pos _)))
  | (n + 1) => fun l hl => node
    (ofList (n := n) (l.take (2^n))
    (by simp_rw [List.length_take, hl, Nat.two_pow_succ, min_eq_left_iff, Nat.le_add_right]))
    (ofList (n := n) (l.drop (2^n))
    (by simp_rw [List.length_drop, hl, Nat.two_pow_succ, Nat.add_sub_cancel]))

def ofList' (l : List α) (h : ∃ n, l.length = 2^n) : BTree α :=
    ofList (n := l.length.log2) l (h.choose_spec ▸ Nat.log2_two_pow ▸ rfl)

def ofTupleAux : {n : ℕ} → (Fin (2^n) → α) → {t : BTree α // t.height = n}
  | 0, bs => ⟨leaf (bs 0), rfl⟩
  | (_ + 1), bs =>
    let (l, r) := Fin.twoPowSuccTupleDivide bs
    ⟨_, height_node_of_heights_eq (ofTupleAux l).prop (ofTupleAux r).prop⟩

def ofTuple (bs : Fin (2^n) → α) : BTree α := (ofTupleAux bs).1

section OfTuple

variable {bs : Fin (2^n) → α}

open Fin

@[simp] theorem height_ofTuple : (ofTuple bs).height = n := (ofTupleAux bs).2


@[simp] theorem ofTuple_zero (bs : Fin (2^0) → α) :
    ofTuple bs = leaf (bs 0) := rfl

@[simp] theorem ofTuple_succ (bs : Fin (2^(n + 1)) → α) :
  ofTuple bs = (node (ofTuple (Fin.twoPowSuccTupleDivide bs).1)
  (ofTuple (Fin.twoPowSuccTupleDivide bs).2)) := rfl

theorem IsPerfect_ofTuple : (ofTuple bs).IsPerfect := by
  induction n with | zero => _ | succ n IH => _
  · simp_rw [ofTuple_zero, IsPerfect_leaf]
  · simp_rw [ofTuple_succ]
    exact IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq IH IH
      height_ofTuple height_ofTuple

@[simp] theorem count_ofTuple : (ofTuple bs).count = 2^n := by
  rw [isPerfect_ofTuple.count_eq_two_pow_height, height_ofTuple]

end OfTuple

def toTuple : (t : BTree α) → {n : ℕ} → t.height = n → t.IsPerfect → (Fin (2^n) → α)
  | leaf a => fun _ _ _ => a
  | node l r => fun htn hlr ⟨i, hi⟩ =>
    (Fin.twoPowSuccTupleDivide (Nat.two_pow_succ _) (Nat.two_pow_succ _)).symm
    ⟨toTuple l hlr.height_eq_height hlr.left, toTuple r rfl hlr.right⟩
    ⟨i, hi.trans_eq (hlr.height_eq_right_succ ▸ htn ▸ rfl)⟩

section ToTuple

@[simp] theorem toTuple_leaf : toTuple (leaf a) (height_leaf) IsPerfect_leaf = fun _ => a := rfl

@[simp] theorem toTuple_node (hlp : l.IsPerfect) (hrp : r.IsPerfect)
    (hl : l.height = n) (hr : r.height = n) :
    toTuple (node l r) (height_node_of_heights_eq hl hr)
    (IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq hlp hrp hl hr) =
    (Fin.twoPowSuccTupleDivide (Nat.two_pow_succ _) (Nat.two_pow_succ _)).symm
    (l.toTuple hl hlp, r.toTuple hr hrp) := by
  ext i
  simp only [toTuple, Fin.twoPowSuccTupleDivide_symm_apply]
  by_cases hi : (i : ℕ) < 2^n
  · rw [Fin.appendTwoPowTuples_apply_of_lt hi, Fin.appendTwoPowTuples_apply_of_lt (hr ▸ hi)]

  cases i
  simp
  rw [Fin.appendTwoPowTuples_apply_of_lt, Fin.appendTwoPowTuples_apply_of_lt]

end ToTuple

theorem toTuple_ofTuple_eq_comp_cast {bs: Fin (2^n) → α} (h : m = n)
    (hh := (height_ofTuple (n := n)).trans h.symm) (hmn := congrArg (fun x => 2^x) h) :
    toTuple (ofTuple bs) hh = bs ∘ Fin.cast hmn := by
  cases h
  induction n with | zero => _ | succ _ IH => _
  · simp_rw [ofTuple_zero, toTuple_leaf]
    exact funext fun _ => congrArg _ (Fin.fin_one_eq_zero _).symm
  · simp_rw [ofTuple_succ, toTuple_node height_ofTuple height_ofTuple,
      IH, Equiv.symm_apply_eq]
    simp_rw [Fin.twoPowSuccTupleDivide_apply, Prod.ext_iff, funext_iff,  Function.comp_apply,
      Fin.fstTwoPowSuccTuple_apply, Fin.sndTwoPowSuccTuple_apply, Function.comp_apply,
      Fin.cast_eq_self, implies_true, and_self]

@[simp] theorem toTuple_ofTuple {bs: Fin (2^n) → α} : toTuple (ofTuple bs) height_ofTuple = bs :=
  toTuple_ofTuple_eq_comp_cast rfl

@[simp] theorem toTuple_ofTuple_height_ofTuple_eq_comp_cast {bs: Fin (2^n) → α}
    (hmn := congrArg (fun x => 2^x) height_ofTuple) :
    toTuple (ofTuple bs) rfl = bs ∘ Fin.cast hmn := toTuple_ofTuple_eq_comp_cast height_ofTuple

@[simp] theorem ofTuple_toTuple (ht : t.height = n) : ofTuple (toTuple t ht) = t := by
  induction n generalizing t with | zero => _ | succ n IH => _
  · rcases exists_of_height_eq_zero ht with ⟨a, rfl⟩
    simp_rw [toTuple_leaf, ofTuple_zero]
  · rcases exists_of_height_eq_succ ht with ⟨l, r, hl, hr, rfl⟩
    simp_rw [ofTuple_succ, toTuple_node hl hr, Equiv.apply_symm_apply, node_inj_iff]
    exact ⟨IH hl, IH hr⟩

@[simps!]
def equivTupleOfHeightEq : {t : PBTree α // t.height = n} ≃ (Fin (2^n) → α) where
  toFun t := toTuple t.1 t.2
  invFun bs := ⟨ofTuple bs, height_ofTuple⟩
  left_inv _ := Subtype.ext <| ofTuple_toTuple _
  right_inv _ := toTuple_ofTuple

def equivSigmaTuple : PBTree α ≃ (Σ n, (Fin (2^n) → α)) where
  toFun t := ⟨t.height, toTuple t rfl⟩
  invFun bs := ofTuple bs.2
  left_inv t := ofTuple_toTuple _
  right_inv := fun bs => by
    simp_rw [Fin.sigma_eq_iff_eq_comp_cast']


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

def BTreeStack (α : Type u) := List (BTree α) --{l :  // l.Sorted (· < ·)}

namespace BTreeStack

open BTree

variable {l r a : BTree α} {s t : BTreeStack α}

instance [Repr α] : Repr (BTreeStack α) := instReprList
instance [DecidableEq α] : DecidableEq (BTreeStack α) := instDecidableEqList

def ofList (l : List (BTree α)) : BTreeStack α := l

section OfList

variable {s t : List (BTree α)}

theorem ofList_injective : Function.Injective (ofList (α := α)) := fun _ _ => id

@[simp] theorem ofList_inj_iff : ofList s = ofList t ↔ s = t := Iff.rfl

instance : Inhabited (BTreeStack α) := ⟨ofList []⟩

end OfList

def toList (l : BTreeStack α) : List (BTree α) := l

section ToList


@[simp] theorem toList_ofList : toList (ofList ts) = ts := rfl

@[simp] theorem ofList_toList : ofList (toList ts) = ts := rfl

theorem toList_injective : Function.Injective (toList (α := α)) := fun _ _ => id

@[simp] theorem toList_inj_iff : s.toList = t.toList ↔ s = t := Iff.rfl

end ToList

instance : Membership (BTree α) (BTreeStack α) where
  mem l a := a ∈ l.toList

section Mem

@[simp] theorem mem_toList_iff : a ∈ s.toList ↔ a ∈ s := Iff.rfl

@[simp] theorem mem_ofList_iff {s : List (BTree α)} : a ∈ ofList s ↔ a ∈ s := Iff.rfl

end Mem

def nil : BTreeStack α := ofList []

section Nil

@[simp] theorem toList_nil : (nil : BTreeStack α).toList = [] := rfl

@[simp] theorem ofList_nil : ofList ([] : List (BTree α)) = nil := rfl

@[simp] theorem toList_eq_nil_iff : s.toList = [] ↔ s = nil := Iff.rfl

@[simp] theorem ofList_eq_nil_iff {s : List (BTree α)} : ofList s = nil ↔ s = [] := Iff.rfl

theorem toList_ne_nil_iff : s.toList ≠ [] ↔ s ≠ nil := toList_eq_nil_iff.not

theorem ofList_ne_nil_iff {s : List (BTree α)} : ofList s ≠ nil ↔ s ≠ [] := Iff.rfl

@[simp] theorem not_mem_nil {t : BTree α} : ¬ t ∈ nil := List.not_mem_nil _

theorem ne_nil_of_mem : a ∈ t → t ≠ nil := List.ne_nil_of_mem

end Nil

def cons (a : BTree α) (s : BTreeStack α) : BTreeStack α := ofList (a :: s.toList)

section Cons


@[simp] theorem cons_inj_iff : cons a s = cons a' s' ↔ ((a = a') ∧ s = s') := List.cons_eq_cons

@[simp] theorem toList_cons : (cons a s).toList = a :: s.toList := rfl

@[simp] theorem ofList_cons {s : List (BTree α)} : ofList (a :: s) = cons a (ofList s) := rfl

@[simp] theorem mem_cons : b ∈ cons a s ↔ b = a ∨ b ∈ s := List.mem_cons

theorem mem_cons_self : a ∈ cons a s := List.mem_cons_self _ _

theorem mem_cons_of_mem (h : b ∈ s) : b ∈ cons a s := List.mem_cons_of_mem _ h

end Cons

section NilCons

@[simp] theorem mem_cons_nil : a ∈ cons b nil ↔ a = b := List.mem_singleton

@[simp] theorem nil_ne_cons : nil ≠ cons a s := List.noConfusion

@[simp] theorem cons_ne_nil : cons a s ≠ nil := List.noConfusion

@[elab_as_elim, induction_eliminator] def nilConsInduction {motive : BTreeStack α → Sort _}
    (nil : motive nil) (cons : (a : BTree α) → (s : BTreeStack α) → motive s → motive (cons a s))
    (t : BTreeStack α) : motive t := t.recOn nil cons

@[simp] theorem nilConsInduction_nil {motive : BTreeStack α → Sort _}
    {nil : motive nil} {cons : (a : BTree α) → (s : BTreeStack α) → motive s → motive (cons a s)} :
    nilConsInduction nil cons BTreeStack.nil = nil := by
  unfold nilConsInduction
  rfl

@[simp] theorem nilConsInduction_cons {motive : BTreeStack α → Sort _}
    {nil : motive nil} {cons : (a : BTree α) → (s : BTreeStack α) → motive s → motive (cons a s)} :
    nilConsInduction nil cons (BTreeStack.cons a s) =
    cons a s (nilConsInduction nil cons s) := by
  conv =>
    lhs
    unfold BTree.node nilConsInduction
  rfl

@[elab_as_elim, cases_eliminator] def nilConsCases {motive : BTreeStack α → Sort _}
    (nil : motive nil) (cons : (a : BTree α) → (s : BTreeStack α) → motive (cons a s))
    (t : BTreeStack α) : motive t := nilConsInduction nil (fun a s _ => cons a s) t

@[simp] theorem nilConsCases_nil {motive : BTreeStack α → Sort _}
    {nil : motive nil} {cons : (a : BTree α) → (s : BTreeStack α) → motive (cons a s)} :
      nilConsCases nil cons BTreeStack.nil = nil := nilConsInduction_nil

@[simp] theorem nilConsCases_cons {motive : BTreeStack α → Sort _}
    {nil : motive nil} {cons : (a : BTree α) → (s : BTreeStack α) → motive (cons a s)} :
      nilConsCases nil cons (BTreeStack.cons a s) = cons a s := nilConsInduction_cons

theorem nil_or_exists_cons (t : BTreeStack α) :
    t = nil ∨ (∃ a s, t = cons a s) := by
  cases t using nilConsCases
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, rfl⟩

theorem exists_of_ne_nil (ht : t ≠ nil) : ∃ a s, t = cons a s := by
  cases t using nilConsCases
  · exact (ht rfl).elim
  · exact ⟨_, _, rfl⟩

end NilCons


def singleton (a : BTree α) : BTreeStack α := cons a nil

section Singleton

theorem singleton_def : singleton a = cons a nil := rfl

@[simp] theorem ofList_singleton : ofList [a] = singleton a := rfl

@[simp] theorem toList_singleton : (singleton a).toList = [a] := rfl

@[simp] theorem cons_eq_singleton_iff : cons a s = singleton b ↔ a = b ∧ s = nil := by
  rw [singleton_def, cons_inj_iff]

@[simp] theorem singleton_ne_nil : singleton a ≠ nil := cons_ne_nil

@[simp] theorem nil_ne_singleton : nil ≠ singleton a := singleton_ne_nil.symm

theorem eq_of_mem_singleton : b ∈ singleton a → b = a := List.eq_of_mem_singleton

@[simp] theorem mem_singleton : b ∈ singleton a ↔ b = a := List.mem_singleton

theorem mem_singleton_self (a : BTree α) : a ∈ singleton a := List.mem_singleton_self a

end Singleton


def getFirst (s : BTreeStack α) : s ≠ nil → BTree α :=
    s.nilConsCases (fun h => h.irrefl.elim) (fun a _ _ => a)

section GetFirst

@[simp] theorem getFirst_cons :
    (cons a s).getFirst cons_ne_nil = a := congrFun nilConsCases_cons cons_ne_nil

@[simp] theorem getFirst_singleton :
    (singleton a).getFirst singleton_ne_nil = a := congrFun nilConsCases_cons cons_ne_nil

theorem getFirst_eq_iff : s.getFirst hs = a ↔ ∃ s', s = cons a s' := by
  cases s using nilConsCases
  · exact hs.irrefl.elim
  · simp_rw [getFirst_cons, cons_inj_iff, exists_and_left, exists_eq', and_true]

@[simp] theorem getFirst_ofList {s : List (BTree α)} {hs : ofList s ≠ nil}
    (hs' := (ofList_ne_nil_iff).mp hs) : (ofList s).getFirst hs = s.head hs' := by
  cases s with | nil => _ | cons a s => _
  · exact hs'.irrefl.elim
  · simp_rw [getFirst_eq_iff, List.head_cons, ofList_cons, cons_inj_iff, true_and, exists_eq']

@[simp] theorem head_toList (h : s ≠ nil) (h' := toList_ne_nil_iff.mpr h) :
    s.toList.head h' = s.getFirst h := by
  cases s using nilConsCases
  · exact h.irrefl.elim
  · simp_rw [toList_cons, List.head_cons, getFirst_cons]

theorem getFirst_mem : s.getFirst hs ∈ s := by
  cases s using nilConsCases
  · exact hs.irrefl.elim
  · simp_rw [getFirst_cons]
    exact mem_cons_self

end GetFirst

def getLast (s : BTreeStack α) : s ≠ nil → BTree α :=
  s.nilConsCases (fun h => h.irrefl.elim)
  (fun a s => nilConsInduction
    (fun a _ => a)
    (fun b _ getLast _ _ => getLast b (cons_ne_nil)) s a)


section GetLast

@[simp] theorem getLast_cons_nil (h := cons_ne_nil) : (cons a nil).getLast h = a := by
  unfold getLast
  rw [nilConsCases_cons, nilConsInduction_nil]

@[simp] theorem getLast_singleton (h := singleton_ne_nil) : (singleton a).getLast h = a := by
  simp_rw [singleton_def, getLast_cons_nil]

theorem getLast_cons_cons :
    (cons a (cons b s)).getLast cons_ne_nil = (cons b s).getLast cons_ne_nil := by
  unfold getLast
  simp_rw [nilConsCases_cons, nilConsInduction_cons]

@[simp] theorem getLast_cons_of_ne_nil (hs : s ≠ nil) (h := cons_ne_nil) :
    (cons a s).getLast h = s.getLast hs := by
  cases s using nilConsCases
  · exact hs.irrefl.elim
  · exact getLast_cons_cons

@[simp] theorem getLast_toList (h : s ≠ nil) (h' := toList_ne_nil_iff.mpr h) :
    s.toList.getLast h' = s.getLast h := by
  induction s with | nil => _ | cons a s IH => _
  · exact h.irrefl.elim
  · simp_rw [toList_cons]
    by_cases hs : s = nil
    · subst hs
      simp_rw [toList_nil, List.getLast_singleton, getLast_cons_nil]
    · simp_rw [getLast_cons_of_ne_nil hs, List.getLast_cons (toList_ne_nil_iff.mpr hs)]
      exact IH _

@[simp] theorem getLast_ofList {s : List (BTree α)} {h' : ofList s ≠ nil}
    (h := (ofList_ne_nil_iff).mp h') : (ofList s).getLast h' = s.getLast h := by
  induction s with | nil => _ | cons a s IH => _
  · exact h'.irrefl.elim
  · by_cases hs : s = []
    · subst s
      simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true,
        ofList_cons, ofList_nil, getLast_cons_nil, List.getLast_singleton]
    · simp_rw [List.getLast_cons hs, ofList_cons,
        getLast_cons_of_ne_nil ((ofList_ne_nil_iff).mpr hs)]
      exact IH _

theorem getLast_mem {hs} : s.getLast hs ∈ s := by
  induction s using nilConsInduction with | nil => _ | cons a s IH => _
  · exact hs.irrefl.elim
  · by_cases hs : s = nil
    · subst hs
      simp_rw [getLast_cons_nil, mem_cons_self]
    · simp_rw [getLast_cons_of_ne_nil hs, mem_cons]
      exact Or.inr IH

theorem getLast_cons_mem (h := cons_ne_nil) (hs : s ≠ nil) : (cons a s).getLast h ∈ s := by
  rw [getLast_cons_of_ne_nil hs]
  exact getLast_mem

end GetLast


def length (s : BTreeStack α) : ℕ :=  s.nilConsInduction 0 (fun _ _ => (· + 1))

section Length

@[simp] theorem length_nil : length (nil : BTreeStack α) = 0 := nilConsInduction_nil

@[simp] theorem length_cons : (cons a s).length = s.length + 1 := nilConsInduction_cons

@[simp] theorem length_toList : s.toList.length = s.length := by
  induction s
  · simp_rw [toList_nil, List.length_nil, length_nil]
  · simp only [toList_cons, List.length_cons, length_cons, add_left_inj]
    assumption

@[simp] theorem length_ofList {s : List (BTree α)} : (ofList s).length = s.length := by
  induction s
  · simp only [ofList_nil, length_nil, List.length_nil]
  · simp_rw [List.length_cons, ofList_cons, length_cons, add_left_inj]
    assumption

@[simp] theorem length_eq_zero : s.length = 0 ↔ s = nil := by
  rw [← length_toList, List.length_eq_zero, toList_eq_nil_iff]

instance : NeZero ((cons a s).length) := ⟨length_cons ▸ Nat.succ_ne_zero _⟩

theorem length_ne_zero : s.length ≠ 0 ↔ s ≠ nil := length_eq_zero.not

theorem length_pos : 0 < s.length ↔ s ≠ nil := Nat.pos_iff_ne_zero.trans length_ne_zero

theorem one_le_length : 1 ≤ s.length ↔ s ≠ nil := length_pos

theorem exists_of_length_ne_zero (ht : t.length ≠ 0) : ∃ a s, t = cons a s := by
  cases t using nilConsCases
  · exact (ht length_nil).elim
  · exact ⟨_, _, rfl⟩

theorem length_singleton : (singleton a).length = 1 := by
  rw [singleton_def, length_cons, length_nil]

theorem length_eq_one : s.length = 1 ↔ ∃ a, s = singleton a := by
  cases s using nilConsCases
  · simp_rw [length_nil, zero_ne_one, nil_ne_singleton, exists_false]
  · simp_rw [length_cons, add_left_eq_self, length_eq_zero,
      cons_eq_singleton_iff, exists_and_right, exists_eq', true_and]

end Length


def firstHeight (s : BTreeStack α) : ℕ := s.nilConsCases 0 (fun a _ => a.height)

section FirstHeight

@[simp] theorem firstHeight_nil : (nil : BTreeStack α).firstHeight = 0 := nilConsCases_nil

@[simp] theorem firstHeight_cons : (cons a s).firstHeight = a.height := nilConsCases_cons

@[simp] theorem firstHeight_singleton : (singleton a).firstHeight = a.height := by
  rw [singleton_def, firstHeight_cons]

theorem firstHeight_eq_getFirst_height (hs) : s.firstHeight = (s.getFirst hs).height := by
  cases s using nilConsCases
  · exact hs.irrefl.elim
  · simp_rw [getFirst_cons,  firstHeight_cons]

end FirstHeight

def lastHeight (s : BTreeStack α) : ℕ :=
  s.nilConsCases 0
  (fun a s => s.nilConsInduction
    (fun a => a.height)
    (fun b _ lastHeight _ => lastHeight b) a)

def getLast' (s : BTreeStack α) : s ≠ nil → BTree α :=
  s.nilConsCases (fun h => h.irrefl.elim)
  (fun a s => nilConsInduction
    (fun a _ => a)
    (fun b _ getLast _ _ => getLast b (cons_ne_nil)) s a)

section LastHeight

@[simp] theorem lastHeight_nil : (nil : BTreeStack α).lastHeight = 0 := nilConsCases_nil

@[simp] theorem lastHeight_cons_nil : (cons a nil).lastHeight = a.height := by
  exact nilConsCases_cons.trans (nilConsInduction_nil ▸ rfl)

@[simp] theorem lastHeight_singleton : (singleton a).lastHeight = a.height := by
  rw [singleton_def, lastHeight_cons_nil]

@[simp] theorem lastHeight_cons_cons : (cons a (cons b s)).lastHeight = (cons b s).lastHeight := by
  unfold lastHeight
  simp only [nilConsCases_cons, nilConsInduction_cons]

@[simp] theorem lastHeight_cons_of_ne_nil (hs : s ≠ nil) :
    (cons a s).lastHeight = s.lastHeight := by
  cases s using nilConsCases
  · exact hs.irrefl.elim
  · simp_rw [lastHeight_cons_cons]

theorem lastHeight_eq_getLast_height (hs) : s.lastHeight = (s.getLast hs).height := by
  induction s with | nil => _ | cons a s IH => _
  · exact hs.irrefl.elim
  · by_cases hs : s = nil
    · subst hs
      simp_rw [getLast_cons_nil, lastHeight_cons_nil]
    · simp_rw [getLast_cons_of_ne_nil hs, lastHeight_cons_of_ne_nil hs]
      exact IH _

end LastHeight


def IsSMH (s : BTreeStack α) := s.toList.Sorted (fun a b => a.height < b.height)

section IsSMH

instance : IsStrictWeakOrder (BTree α) (fun a b => a.height < b.height) where
  irrefl a := lt_irrefl a.height
  trans _ _ _ := lt_trans
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans _ _ _

instance : DecidableRel (fun (a : BTree α) b => a.height < b.height) :=
    fun a b => a.height.decLt b.height

instance : Decidable (IsSMH s) := List.decidableSorted _

@[simp] theorem IsSMH_cons_iff : (cons a s).IsSMH ↔ (∀ b ∈ s, a.height < b.height) ∧ s.IsSMH :=
  List.sorted_cons

@[simp] theorem IsSMH_nil : (nil (α := α)).IsSMH := List.sorted_nil

@[simp] theorem IsSMH_singleton : (singleton a).IsSMH := List.sorted_singleton _

@[simp] theorem IsSMH_cons_nil : (cons a nil).IsSMH := List.sorted_singleton _

@[simp] theorem IsSMH.cons_of (hsh : s.IsSMH) (h : ∀ b ∈ s, a.height < b.height) :
    (cons a s).IsSMH := List.Pairwise.cons h hsh

theorem IsSMH.of_cons : (cons a s).IsSMH → s.IsSMH := List.Sorted.of_cons

theorem IsSMH.height_lt_height_of_mem (hsh : (cons a s).IsSMH) (hb : b ∈ s) :
    a.height < b.height := List.rel_of_sorted_cons hsh _ hb

theorem IsSMH.height_le_height_of_mem (hsh : (cons a s).IsSMH) (hb : b ∈ s) :
    a.height ≤ b.height := (hsh.height_lt_height_of_mem hb).le

theorem IsSMH.cons_cons {b : BTree α} (hab : a.height < b.height) :
    (cons b s).IsSMH → (cons a (cons b s)).IsSMH := List.Sorted.cons hab

theorem IsSMH.getFirst_height_le (hsh : s.IsSMH) : ∀ (ha : a ∈ s),
    (s.getFirst (fun h => (not_mem_nil (h ▸ ha)))).height ≤ a.height := by
  cases s with | nil => _ | cons a s => _
  · exact fun ha => (not_mem_nil ha).elim
  · simp_rw [getFirst_cons, mem_cons]
    exact fun h => h.elim (fun H => H ▸ le_rfl) hsh.height_le_height_of_mem

theorem IsSMH.getFirst_cons_lt (hsh : (cons a s).IsSMH) (hb : b ∈ s) :
    ((cons a s).getFirst cons_ne_nil).height < b.height := by
  simp_rw [getFirst_cons]
  exact hsh.height_lt_height_of_mem hb

theorem IsSMH.le_getLast_height (hsh : s.IsSMH) : ∀ (ha : a ∈ s),
    a.height ≤ (s.getLast (fun h => (not_mem_nil (h ▸ ha)))).height := by
  induction s using nilConsInduction with | nil => _ | cons a s IH => _
  · exact fun hb => (not_mem_nil hb).elim
  · by_cases hs : s = nil
    · subst hs
      simp_rw [mem_cons, not_mem_nil, or_false, getLast_cons_nil]
      exact fun h => h ▸ le_rfl
    · simp_rw [getLast_cons_of_ne_nil hs, mem_cons]
      exact fun h => h.elim
        (fun H => H ▸ hsh.height_le_height_of_mem getLast_mem)
        (IH hsh.of_cons)

theorem IsSMH.lt_getLast_cons_cons (hsh : (cons a (cons b s)).IsSMH) :
    a.height < ((cons a (cons b s)).getLast cons_ne_nil).height :=
  hsh.height_lt_height_of_mem (getLast_cons_cons.symm ▸ getLast_mem)

theorem IsSMH.cons_cons_getFirst_lt_getLast (hsh : (cons a (cons b s)).IsSMH) :
    ((cons a (cons b s)).getFirst cons_ne_nil).height <
    ((cons a (cons b s)).getLast cons_ne_nil).height := by
  simp_rw [getFirst_cons]
  exact hsh.lt_getLast_cons_cons

theorem IsSMH.getFirst_height_lt_getLast_height_iff_one_lt_length (hsh : s.IsSMH) :
    (s.getFirst hs).height < (s.getLast hs).height ↔ 1 < s.length := by
  cases s using nilConsCases with | nil => _ | cons _ s => _
  · exact hs.irrefl.elim
  · simp_rw [length_cons, lt_add_iff_pos_left]
    cases s using nilConsCases
    · simp_rw [getLast_cons_nil, getFirst_cons, length_nil, lt_irrefl]
    · simp_rw [hsh.cons_cons_getFirst_lt_getLast, length_cons, add_pos_iff, zero_lt_one, or_true]

theorem IsSMH.getFirst_height_le_getLast_height {hs : s ≠ nil} (hsh : s.IsSMH) :
    (s.getFirst hs).height ≤ (s.getLast hs).height := by
  rw [← one_le_length] at hs
  rcases hs.eq_or_gt with (hs | hs)
  · rw [length_eq_one] at hs
    rcases hs with ⟨_, rfl⟩
    simp_rw [ getFirst_singleton, getLast_singleton, le_rfl]
  · exact (hsh.getFirst_height_lt_getLast_height_iff_one_lt_length.mpr hs).le

theorem IsSMH.firstHeight_le (hsh : s.IsSMH) (ha : a ∈ s) : s.firstHeight ≤ a.height := by
  simp_rw [firstHeight_eq_getFirst_height (ne_nil_of_mem ha)]
  exact hsh.getFirst_height_le ha

theorem IsSMH.le_lastHeight (hsh : s.IsSMH) (ha : a ∈ s) : a.height ≤ s.lastHeight := by
  simp_rw [lastHeight_eq_getLast_height (ne_nil_of_mem ha)]
  exact hsh.le_getLast_height ha

theorem IsSMG.firstHeight_le_lastHeight (hsh : s.IsSMH) : s.firstHeight ≤ s.lastHeight := by
  by_cases hs : s = nil
  · subst hs
    simp only [firstHeight_nil, lastHeight_nil, le_refl]
  · simp_rw [firstHeight_eq_getFirst_height hs, lastHeight_eq_getLast_height hs]
    exact hsh.getFirst_height_le_getLast_height

theorem length_le_lastHeight_sub_firstHeight (hsh : s.IsSMH) :
    s.length ≤ (s.lastHeight - s.firstHeight) + 1 := by
  induction s using nilConsInduction with | nil => _ | cons a s IH => _
  · simp_rw [length_nil, lastHeight_nil, firstHeight_nil, tsub_zero, zero_add, zero_le_one]
  · by_cases hs : s = nil
    · subst hs
      simp
    · simp_rw [lastHeight_cons_of_ne_nil hs, firstHeight_cons, length_cons, Nat.succ_le_succ_iff]
      refine (IH hsh.of_cons).trans (Nat.succ_le_of_lt (Nat.sub_lt_sub_left ?_ ?_))
      · simp_rw [lastHeight_eq_getLast_height hs]
        exact hsh.height_lt_height_of_mem getLast_mem
      · simp_rw [firstHeight_eq_getFirst_height hs]
        exact hsh.height_lt_height_of_mem getFirst_mem

end IsSMH


def get (s : BTreeStack α) (n : ℕ) : Option (BTree α) :=
  s.nilConsInduction none
  (fun a _ get => match (cmp n a.height) with
    | .lt => none
    | .eq => some a
    | .gt => get )

section Get

@[simp] theorem get_nil : (nil (α := α)).get n = none := rfl

theorem get_cons_nil_of_ne_height (hn : n ≠ a.height) :
    (cons a nil).get n = none := by
  unfold get
  simp_rw [nilConsInduction_cons, nilConsInduction_nil]
  cases h : cmp n a.height
  · rfl
  · rw [cmp_eq_eq_iff] at h
    contradiction
  · rfl

theorem get_singleton_of_ne_height (hn : n ≠ a.height) :
    (singleton a).get n = none := by
  rw [singleton_def]
  exact get_cons_nil_of_ne_height hn

@[simp] theorem get_cons_of_lt_height (hn : n < a.height) :
    (cons a s).get n = none := by
  unfold get
  simp_rw [nilConsInduction_cons, (cmp_eq_lt_iff _ _).mpr hn]

@[simp] theorem get_cons_of_gt_height (hn : a.height < n) :
    (cons a s).get n = s.get n := by
  unfold get
  simp_rw [nilConsInduction_cons, (cmp_eq_gt_iff _ _).mpr hn]

@[simp] theorem get_cons_height : (cons a s).get a.height = some a := by
  unfold get
  simp_rw [nilConsInduction_cons, cmp_self_eq_eq]

@[simp] theorem get_singleton_height : (singleton a).get a.height = some a := by
  rw [singleton_def]
  exact get_cons_height

theorem get_of_lt_firstHeight (hn : n < s.firstHeight) : s.get n = none := by
  cases s
  · exact get_nil
  · rw [firstHeight_eq_getFirst_height cons_ne_nil, getFirst_cons] at hn
    exact get_cons_of_lt_height hn

theorem get_firstHeight (hs : s ≠ nil) : s.get (s.firstHeight) = some (s.getFirst hs) := by
  cases s
  · exact hs.irrefl.elim
  · simp_rw [firstHeight_eq_getFirst_height hs, getFirst_cons, get_cons_height]

theorem get_eq_none_of_forall_ne_height (hn : ∀ a ∈ s, n ≠ a.height) : s.get n = none := by
  induction s with | nil => _ | cons b s IH => _
  · exact get_nil
  · simp_rw [mem_cons, ne_eq, forall_eq_or_imp] at hn
    rcases Ne.lt_or_lt (hn.left) with hbn | hbn
    · rw [get_cons_of_lt_height hbn]
    · rw [get_cons_of_gt_height hbn]
      exact IH hn.right

theorem exists_mem_eq_height_of_get_isSome (hn : (s.get n).isSome) : ∃ a ∈ s, n = a.height := by
  revert hn
  apply Function.mtr
  simp_rw [not_exists, not_and, Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none]
  exact get_eq_none_of_forall_ne_height

theorem IsSMH.get_height_of_mem (hsh : s.IsSMH) (ha : a ∈ s) : s.get a.height = some a := by
  induction s with | nil => _ | cons b s IH => _
  · exact (not_mem_nil ha).elim
  · rw [mem_cons] at ha
    rcases ha with (rfl | ha)
    · exact get_cons_height
    · rw [isSMH_cons_iff] at hsh
      rw [get_cons_of_gt_height (hsh.left _ ha)]
      exact IH hsh.right ha

theorem IsSMH.get_isSome_iff (hsh : s.IsSMH) : (s.get n).isSome ↔ ∃ a ∈ s, n = a.height := by
  refine ⟨exists_mem_eq_height_of_get_isSome, ?_⟩
  rintro ⟨_, ha, rfl⟩
  rw [hsh.get_height_of_mem ha, Option.isSome_some]

theorem IsSMH.get_isNone_iff (hsh : s.IsSMH) : (s.get n).isNone ↔ ∀ a ∈ s, n ≠ a.height := by
  simp_rw [← Option.not_isSome, Bool.eq_false_iff, ne_eq, hsh.get_isSome_iff, not_exists, not_and]

theorem IsSMH.get_of_lastHeight_lt (hsh : s.IsSMH) (hn : s.lastHeight < n) : s.get n = none := by
  apply Option.eq_none_of_isNone
  rw [hsh.get_isNone_iff]
  intro _ ha hc
  rw [hc] at hn
  exact (hsh.le_lastHeight ha).not_lt hn

end Get

def push (s : BTreeStack α) : (b : BTree α) → BTreeStack α :=
  s.nilConsInduction (singleton) (fun a s push b =>
    if a.height = b.height then push (node a b) else cons b (cons a s))

section Push

@[simp] theorem push_nil : (nil (α := α)).push a = singleton a := by
  unfold push
  rw [nilConsInduction_nil]

@[simp] theorem push_cons_of_height_eq (h : a.height = b.height) :
    (cons a s).push b = s.push (node a b) := by
  unfold push
  simp_rw [nilConsInduction_cons, if_pos h]

@[simp] theorem push_cons_of_height_ne (h : a.height ≠ b.height) :
    (cons a s).push b = cons b (cons a s) := by
  unfold push
  simp_rw [nilConsInduction_cons, if_neg h]

theorem push_firstHeight_of_height_lt_firstHeight (hab : ∀ a ∈ s, b.height < a.height) :
    (s.push b).firstHeight = b.height := by
  cases s
  · simp_rw [push_nil, firstHeight_singleton]
  · rw [push_cons_of_height_ne (hab _ mem_cons_self).ne', firstHeight_cons]

theorem IsSMH.push_of (hsh : s.IsSMH) (habs : ∀ a ∈ s, b.height ≤ a.height) :
    (s.push b).IsSMH := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, IsSMH_singleton]
  · by_cases hab : a.height = b.height
    · simp_rw [push_cons_of_height_eq hab]
      exact IH hsh.of_cons (fun _ h => height_node ▸ Nat.succ_le_of_lt
        (hab ▸ Nat.max_self _ ▸ hsh.height_lt_height_of_mem h))
    · simp_rw [push_cons_of_height_ne hab]
      exact hsh.cons_cons ((habs _ mem_cons_self).lt_of_ne (Ne.symm hab))

theorem IsSMH.push_leaf {a : α} (hsh : s.IsSMH) : (s.push (leaf a)).IsSMH :=
  hsh.push_of (fun _ _ => zero_le _)

theorem IsSMH.push_tuple (hsh : s.IsSMH) {bs : Fin k → α} :
    (Fin.foldl k (fun p i => p.push (leaf (bs i))) s).IsSMH := by
  induction k with | zero => _ | succ k IH => _
  · simp_rw [Fin.foldl_zero, hsh]
  · simp_rw [Fin.foldl_succ_last]
    exact IH.push_leaf

theorem IsSMH.push_foldl_list (hsh : s.IsSMH) {bs : List α} :
    (bs.foldl (fun p a => p.push (leaf a)) s).IsSMH := by
  induction bs using List.list_reverse_induction with | base => _ | ind b bs IH => _
  · simp_rw [List.foldl_nil, hsh]
  · simp_rw [List.foldl_append]
    exact IH.push_leaf

theorem IsSMH.push_foldr_list (hsh : s.IsSMH) {bs : List α} :
    (bs.foldr (fun a p => p.push (leaf a)) s).IsSMH := by
  induction bs with | nil => _ | cons b bs IH => _
  · simp_rw [List.foldr_nil, hsh]
  · exact IH.push_leaf


theorem IsSMH_push_tuple_nil {bs : Fin k → α} :
    (Fin.foldl k (fun p i => p.push (leaf (bs i))) nil).IsSMH := (isSMH_nil).push_tuple

theorem IsPerfect.forall_mem_push_isPerfect_of_forall_mem_isPerfect (hb : b.IsPerfect)
    (has : ∀ a ∈ s, a.IsPerfect) : ∀ a ∈ (s.push b), a.IsPerfect := by
  induction s generalizing b with | nil => _ | cons a s IH => _
  · simp_rw [push_nil, mem_singleton, forall_eq]
    exact hb
  · by_cases hab : a.height = b.height
    · simp_rw [push_cons_of_height_eq hab]
      exact IH (hb.node_of_IsPerfect_left_of_heights_eq (has _ mem_cons_self) hab)
        (fun _ hs => has _ (mem_cons_of_mem hs))
    · simp_rw [push_cons_of_height_ne hab, mem_cons (a := b), forall_eq_or_imp]
      exact ⟨hb, has⟩

end Push


def pushLeaf (s : BTreeStack α) (a : α) : BTreeStack α := s.push (leaf a)

def pushTuple (s : BTreeStack α) (bs : Fin k → α) : BTreeStack α :=
    Fin.foldl k (fun p i => p.pushLeaf (bs i)) s

def ofTuple' (bs : Fin k → α) : BTreeStack α := pushTuple nil bs

    exact ⟨height_ofTuple, toTuple_ofTuple_height_ofTuple_eq_comp_cast⟩


#eval Nat.bitIndices 7

#eval List.foldr (fun (a : ℕ) (p : BTreeStack ℕ) => p.push (leaf a)) nil [6, 5, 4, 3, 2, 1, 0]

#eval List.foldl (fun p a => p.push (leaf a)) nil [0, 1, 2, 3, 4, 5, 6]

def sadsdasd (s : BTreeStack α) (bs : List α) : BTreeStack α :=
    (bs.length.bitIndices).foldl (fun s n => _) s

def count (s : BTreeStack α) : ℕ :=
  s.nilConsInduction 0 (fun a _ m => m + a.count)

/--/



def push (s : BTreeStack α) :
    (b : BTree α) → (has : ∀ a ∈ s, b.height ≤ a.height) → BTreeStack α :=
  s.nilConsInduction (fun b _ => singleton b)
  (fun a s has push b hbs => if hab : a.height = b.height then
  push (node a b) (fun _ h => height_node ▸ Nat.succ_le_of_lt (hab ▸ Nat.max_self _ ▸ (has _ h)))
  else cons b (cons a s has) (fun _ h => (mem_cons.mp h).elim
    (fun h => h ▸ lt_of_le_of_ne' (hbs _ mem_cons_self) hab)
    (fun h => (hbs _ mem_cons_self).trans_lt (has _ h))))

end BTreeStack

def PBTree (α : Type u) := Subtype (BTree.IsPerfect (α := α))

namespace PBTree

open BTree

instance [Repr α] : Repr (PBTree α) := instReprSubtype
instance [DecidableEq α] : DecidableEq (PBTree α) := Subtype.instDecidableEq
instance [Inhabited α] : Inhabited (PBTree α) := ⟨leaf default, IsPerfect_leaf⟩
instance [IsEmpty α] : IsEmpty (PBTree α) := instIsEmptySubtype _

instance [Nonempty α] : Infinite (PBTree α) :=
  Infinite.of_injective (fun (i : ℕ) =>
    i.recOn (⟨leaf (Classical.arbitrary _), IsPerfect_leaf⟩)
    (fun _ t => ⟨node t.1 t.1, t.2.double_node⟩))
    (fun i => i.recOn (fun j => j.recOn (fun _ => rfl)
    (fun _ _ C => BTree.noConfusion (Subtype.ext_iff_val.mp C)))
    (fun _ IH j => j.recOn (fun C => BTree.noConfusion (Subtype.ext_iff_val.mp C))
    fun _ _ H => congrArg _ (IH (Subtype.ext (node.injEq _ _ _ _ ▸ (Subtype.ext_iff_val.mp H)).1))))

variable {a : α} {l r t : PBTree α}

def toBTree (t : PBTree α) := t.1

section ToBTree

@[simp] theorem toBTree_mk : toBTree ⟨bt, ht⟩ = bt := rfl

theorem toBTree_injective : Function.Injective (toBTree (α := α)) := fun _ _ => Subtype.ext

@[simp] theorem toBTree_inj_iff : l.toBTree = r.toBTree ↔ l = r :=
  ⟨fun h => toBTree_injective h, congrArg _⟩

theorem IsPerfect_toBTree : t.toBTree.IsPerfect := t.2

end ToBTree

def height (t : PBTree α) : ℕ := t.toBTree.height

section Height

@[simp] theorem height_toBTree : t.toBTree.height = t.height := rfl

end Height

def leaf (a : α) : PBTree α := ⟨BTree.leaf a, IsPerfect_leaf⟩

section Leaf

@[simp] theorem leaf_default_eq_default [Inhabited α] : leaf (default : α) = default := rfl

theorem leaf_injective : Function.Injective (leaf (α := α)) := fun _ _ H => by
  rw [← leaf.injEq]
  exact Subtype.mk_eq_mk.mp H

theorem leaf_inj_iff : leaf a = leaf b ↔ a = b :=
  ⟨fun h => leaf_injective h, congrArg _⟩

@[simp] theorem height_leaf : height (leaf a) = 0 := rfl

end Leaf

def node (l r : PBTree α) (hlr : l.height = r.height) : PBTree α :=
  ⟨BTree.node l.toBTree r.toBTree,
  IsPerfect_node_of_IsPerfect_of_IsPerfect_of_heights_eq
  l.IsPerfect_toBTree r.IsPerfect_toBTree hlr rfl⟩

section Node

variable {hlr : l.height = r.height}

theorem node_inj_iff : node l r hlr = node l' r' hlr' ↔ ((l = l') ∧ r = r') := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold node at h
    have H := Subtype.mk_eq_mk.mp h
    simp_rw [node.injEq, toBTree_inj_iff] at H
    exact H
  · simp_rw [h.1, h.2]

theorem height_node_of_heights_eq (hl : l.height = n) (hr : r.height = n) :
    height (node l r (hl.trans hr.symm)) = n + 1 :=
  BTree.height_node_of_heights_eq hl hr

theorem height_node_right : height (node l r hlr) = r.height + 1 :=
  height_node_of_heights_eq hlr rfl

theorem height_node_left : height (node l r hlr) = l.height + 1 :=
  height_node_of_heights_eq rfl hlr.symm

theorem height_node_eq_succ_iff_height_left_eq :
    (node l r hlr).height = n + 1 ↔ l.height = n := by
  simp_rw [height_node_left, add_left_inj]

theorem height_node_eq_succ_iff_height_right_eq :
    (node l r hlr).height = n + 1 ↔ r.height = n := by
  simp_rw [height_node_right, add_left_inj]

theorem left_height_lt : l.height < (node l r hlr).height := by
  simp_rw [height_node_left, Nat.lt_succ_self]

theorem right_height_lt : r.height < (node l r hlr).height := by
  simp_rw [height_node_right, Nat.lt_succ_self]

instance : NeZero (node l r hlr).height := ⟨Nat.noConfusion⟩

end Node

section LeafNode

variable {hlr : l.height = r.height}

@[simp] theorem node_ne_leaf : node l r hlr ≠ leaf a := Subtype.coe_ne_coe.mp BTree.noConfusion

@[simp] theorem leaf_ne_node : leaf a ≠ node l r hlr := Subtype.coe_ne_coe.mp BTree.noConfusion

@[elab_as_elim] def leafNodeInduction {motive : PBTree α → Sort _}
    (leaf : (a : α) → motive (leaf a))
    (node : (l r : PBTree α) → (hlr : l.height = r.height) → motive l → motive r →
      motive (node l r hlr)) (t : PBTree α) : motive t :=
  match t with
  | ⟨BTree.leaf a, _⟩ => leaf a
  | ⟨BTree.node l r, hlr⟩ =>
    node ⟨l, hlr.left⟩ ⟨r, hlr.right⟩ hlr.height_eq_height
    (leafNodeInduction leaf node ⟨l, _⟩)
    (leafNodeInduction leaf node ⟨r, _⟩)
  termination_by t.height
  decreasing_by exacts [BTree.left_height_lt, BTree.right_height_lt]

theorem leafNodeInduction_leaf {motive : PBTree α → Sort _}
    {leaf : (a : α) → motive (leaf a)}
    {node : (l r : PBTree α) → (hlr : l.height = r.height) → motive l → motive r →
      motive (node l r hlr)} :
      leafNodeInduction leaf node (PBTree.leaf a) = leaf a := by
  unfold leafNodeInduction
  rfl

theorem leafNodeInduction_node {motive : PBTree α → Sort _}
    {leaf : (a : α) → motive (leaf a)}
    {node : (l r : PBTree α) → (hlr : l.height = r.height) → motive l → motive r →
      motive (node l r hlr)} :
      leafNodeInduction leaf node (PBTree.node l r hlr) =
      node l r hlr (leafNodeInduction leaf node l) (leafNodeInduction leaf node r) := by
  conv =>
    lhs
    unfold PBTree.node leafNodeInduction
  rfl

@[elab_as_elim] def leafNodeCases {motive : PBTree α → Sort _}
    (leaf : (a : α) → motive (leaf a))
    (node : (l r : PBTree α) → (hlr : l.height = r.height) → motive (node l r hlr))
    (t : PBTree α) : motive t := leafNodeInduction leaf (fun l r hlr _ _ => node l r hlr) t

theorem leafNodeCases_leaf {motive : PBTree α → Sort _}
    {leaf : (a : α) → motive (leaf a)}
    {node : (l r : PBTree α) → (hlr : l.height = r.height) → motive (node l r hlr)} :
    leafNodeCases leaf node (PBTree.leaf a) = leaf a := leafNodeInduction_leaf

theorem leafNodeCases_node {motive : PBTree α → Sort _}
    {leaf : (a : α) → motive (leaf a)}
    {node : (l r : PBTree α) → (hlr : l.height = r.height) → motive (node l r hlr)} :
    leafNodeCases leaf node (PBTree.node l r hlr) = node l r hlr := leafNodeInduction_node

theorem exists_leaf_or_exists_node (t : PBTree α) :
    (∃ a, t = leaf a) ∨ (∃ l r hlr, t = node l r hlr) := by
  cases t using leafNodeCases
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, _, _, rfl⟩

theorem exists_of_height_eq_zero (ht : t.height = 0) : ∃ a, t = leaf a := by
  cases t using leafNodeCases
  · exact ⟨_, rfl⟩
  · exact (NeZero.ne _ ht).elim

theorem exists_of_height_ne_zero (ht : t.height ≠ 0) : ∃ l r hlr, t = node l r hlr := by
  cases t using leafNodeCases
  · exact (ht rfl).elim
  · exact ⟨_, _, _, rfl⟩

theorem exists_of_height_eq_succ (ht : t.height = n + 1) :
    ∃ (l r : PBTree α) (hl : l.height = n) (hr : r.height = n),
    t = node l r (hl.trans hr.symm) := by
  cases t using leafNodeCases
  · exact Nat.noConfusion ht
  · have hl := height_node_eq_succ_iff_height_left_eq.mp ht
    have hr := height_node_eq_succ_iff_height_right_eq.mp ht
    exact ⟨_, _, hl, hr, rfl⟩

end LeafNode

instance : Preorder (PBTree α) := Subtype.preorder _

@[simp] theorem lt_iff_height_lt_height : l < r ↔ l.height < r.height := Iff.rfl
@[simp] theorem le_iff_height_le_height : l ≤ r ↔ l.height ≤ r.height := Iff.rfl

instance [Subsingleton α] : PartialOrder (PBTree α) where
  le_antisymm l r hlr hrl := by
    rw [le_iff_height_le_height] at hlr hrl
    have h := le_antisymm hlr hrl
    clear hlr hrl
    induction l using leafNodeInduction generalizing r with
      | leaf => _ | node _ _ _ IHL IHR => _
    · cases r using leafNodeCases
      · simp_rw [leaf_inj_iff]
        exact Subsingleton.elim _ _
      · simp_rw [height_node_right, height_leaf, (Nat.succ_ne_zero _).symm] at h
    · cases r using leafNodeCases
      · simp_rw [height_node_right, height_leaf, (Nat.succ_ne_zero _)] at h
      · simp_rw [node_inj_iff]
        simp_rw [height_node_right, add_left_inj] at h
        refine ⟨IHL _ ?_, IHR _ (by assumption)⟩
        omega

theorem not_IsPartialOrder [Nontrivial α] : ¬ IsPartialOrder (PBTree α) (· ≤ ·) := fun h => by
  rcases Nontrivial.exists_pair_ne (α := α) with ⟨x, y, hxy⟩
  have H := h.antisymm (leaf x) (leaf y) (le_refl 0) (le_refl 0)
  rw [leaf_inj_iff] at H
  contradiction

def count (t : PBTree α) := 2^t.height

section Count

theorem count_eq_two_pow_height : t.count = 2^t.height := rfl

@[simp] theorem count_toBTree : t.toBTree.count = t.count :=
  count_eq_two_pow_height_of_IsPerfect IsPerfect_toBTree

end Count

def ofTupleAux : {n : ℕ} → (Fin (2^n) → α) → {t : PBTree α // t.height = n}
  | 0, bs => ⟨leaf (bs 0), rfl⟩
  | (_ + 1), bs =>
    let (l, r) := Fin.twoPowSuccTupleDivide bs
    ⟨_, height_node_of_heights_eq (ofTupleAux l).prop (ofTupleAux r).prop⟩

def ofTuple (bs : Fin (2^n) → α) : PBTree α := (ofTupleAux bs).1

section OfTuple

variable {bs : Fin (2^n) → α}

open Fin

@[simp] theorem height_ofTuple : (ofTuple bs).height = n := (ofTupleAux bs).2

@[simp] theorem count_ofTuple : (ofTuple bs).count = 2^n := by
  rw [count_eq_two_pow_height, height_ofTuple]

@[simp] theorem ofTuple_zero (bs : Fin (2^0) → α) :
    ofTuple bs = leaf (bs 0) := rfl

@[simp] theorem ofTuple_succ (bs : Fin (2^(n + 1)) → α) :
  ofTuple bs =
  (node (ofTuple (Fin.twoPowSuccTupleDivide bs).1) (ofTuple (Fin.twoPowSuccTupleDivide bs).2))
  (height_ofTuple.trans height_ofTuple.symm) := rfl

end OfTuple

def toTuple (t : PBTree α) : {n : ℕ} → t.height = n → (Fin (2^n) → α)
  | 0 => t.leafNodeCases (fun a _ _ => a) (fun _ _ _ => Nat.noConfusion)
  | (_ + 1) => t.leafNodeCases (fun _ => Nat.noConfusion ) (fun l r hlr hn =>
    (Fin.twoPowSuccTupleDivide.symm (l.toTuple
    (height_left_eq_of_node_eq_succ_of_height_eq_height hn hlr),
    r.toTuple (height_right_eq_of_node_eq_succ_of_height_eq_height hn hlr))))

section ToTuple

@[simp] theorem toTuple_leaf : toTuple (leaf a) (height_leaf) = fun _ => a := by
  unfold toTuple
  rw [leafNodeCases_leaf]

@[simp] theorem toTuple_node (hl : l.height = n) (hr : r.height = n) :
    toTuple (node l r (hl.trans hr.symm)) (height_node_of_heights_eq hl hr) =
    Fin.twoPowSuccTupleDivide.symm (l.toTuple hl, r.toTuple hr) := by
  conv =>
    lhs
    unfold toTuple
    rw [leafNodeCases_node]

end ToTuple

theorem toTuple_ofTuple_eq_comp_cast {bs: Fin (2^n) → α} (h : m = n)
    (hh := (height_ofTuple (n := n)).trans h.symm) (hmn := congrArg (fun x => 2^x) h) :
    toTuple (ofTuple bs) hh = bs ∘ Fin.cast hmn := by
  cases h
  induction n with | zero => _ | succ _ IH => _
  · simp_rw [ofTuple_zero, toTuple_leaf]
    exact funext fun _ => congrArg _ (Fin.fin_one_eq_zero _).symm
  · simp_rw [ofTuple_succ, toTuple_node height_ofTuple height_ofTuple,
      IH, Equiv.symm_apply_eq]
    simp_rw [Fin.twoPowSuccTupleDivide_apply, Prod.ext_iff, funext_iff,  Function.comp_apply,
      Fin.fstTwoPowSuccTuple_apply, Fin.sndTwoPowSuccTuple_apply, Function.comp_apply,
      Fin.cast_eq_self, implies_true, and_self]

@[simp] theorem toTuple_ofTuple {bs: Fin (2^n) → α} : toTuple (ofTuple bs) height_ofTuple = bs :=
  toTuple_ofTuple_eq_comp_cast rfl

@[simp] theorem toTuple_ofTuple_height_ofTuple_eq_comp_cast {bs: Fin (2^n) → α}
    (hmn := congrArg (fun x => 2^x) height_ofTuple) :
    toTuple (ofTuple bs) rfl = bs ∘ Fin.cast hmn := toTuple_ofTuple_eq_comp_cast height_ofTuple

@[simp] theorem ofTuple_toTuple (ht : t.height = n) : ofTuple (toTuple t ht) = t := by
  induction n generalizing t with | zero => _ | succ n IH => _
  · rcases exists_of_height_eq_zero ht with ⟨a, rfl⟩
    simp_rw [toTuple_leaf, ofTuple_zero]
  · rcases exists_of_height_eq_succ ht with ⟨l, r, hl, hr, rfl⟩
    simp_rw [ofTuple_succ, toTuple_node hl hr, Equiv.apply_symm_apply, node_inj_iff]
    exact ⟨IH hl, IH hr⟩

@[simps!]
def equivTupleOfHeightEq : {t : PBTree α // t.height = n} ≃ (Fin (2^n) → α) where
  toFun t := toTuple t.1 t.2
  invFun bs := ⟨ofTuple bs, height_ofTuple⟩
  left_inv _ := Subtype.ext <| ofTuple_toTuple _
  right_inv _ := toTuple_ofTuple

def equivSigmaTuple : PBTree α ≃ (Σ n, (Fin (2^n) → α)) where
  toFun t := ⟨t.height, toTuple t rfl⟩
  invFun bs := ofTuple bs.2
  left_inv t := ofTuple_toTuple _
  right_inv := fun bs => by
    simp_rw [Fin.sigma_eq_iff_eq_comp_cast']
    exact ⟨height_ofTuple, toTuple_ofTuple_height_ofTuple_eq_comp_cast⟩

end PBTree

def PBTreeStack (α : Type u) := {l : List (PBTree α) // l.Sorted (· < ·)}

namespace PBTreeStack

open PBTree

variable {l r a : PBTree α} {s t : PBTreeStack α}

instance [Repr α] : Repr (PBTreeStack α) := instReprSubtype
instance [DecidableEq α] : DecidableEq (PBTreeStack α) := Subtype.instDecidableEq
instance [Inhabited α] : Inhabited (PBTreeStack α) := ⟨[], List.sorted_nil⟩

def toListPBTree (l : PBTreeStack α) := l.1

section ToListPBTree

@[simp] theorem toListPBTree_mk : toListPBTree ⟨ts, hts⟩ = ts := rfl

theorem toListPBTree_injective : Function.Injective (toListPBTree (α := α)) :=
    fun _ _ => Subtype.ext

@[simp] theorem toListPBTree_inj_iff : s.toListPBTree = t.toListPBTree ↔ s = t :=
  ⟨fun h => toListPBTree_injective h, congrArg _⟩

theorem IsSorted_toListPBTree : s.toListPBTree.Sorted (· < ·) := s.2

theorem of_toListPBTree_eq_cons (h : s.toListPBTree = a :: ts) : ts.Sorted (· < ·) :=
  List.Sorted.of_cons (h ▸ IsSorted_toListPBTree)

theorem rel_of_toListPBTree_eq_cons (h : s.toListPBTree = a :: ts) : ∀ b ∈ ts, a < b :=
  List.rel_of_sorted_cons (h ▸ IsSorted_toListPBTree)

end ToListPBTree

instance : Membership (PBTree α) (PBTreeStack α) where
  mem l a := a ∈ l.toListPBTree

section Mem

@[simp] theorem mem_toListPBTree_iff : a ∈ s.toListPBTree ↔ a ∈ s := Iff.rfl

end Mem

def length (s : PBTreeStack α) : ℕ := s.toListPBTree.length

section Length

@[simp] theorem length_toListPBTree : s.toListPBTree.length = s.length := rfl

end Length

def nil : PBTreeStack α := ⟨[], List.sorted_nil⟩

section Nil

theorem toListPBTree_nil : (nil : PBTreeStack α).toListPBTree = [] := rfl

theorem toListPBTree_eq_nil_iff : s.toListPBTree = [] ↔ s = nil := by
  rw [← toListPBTree_nil, toListPBTree_inj_iff]

@[simp] theorem not_mem_nil (t : PBTree α) : ¬ t ∈ nil := List.not_mem_nil _

@[simp] theorem length_nil : length (nil : PBTreeStack α) = 0 := rfl

@[simp] theorem length_eq_zero : s.length = 0 ↔ s = nil := by
  rw [← length_toListPBTree, List.length_eq_zero, toListPBTree_eq_nil_iff]

end Nil

def cons (a : PBTree α) (s : PBTreeStack α) (has : ∀ b ∈ s, a < b) : PBTreeStack α :=
  ⟨a :: s.toListPBTree, List.sorted_cons.mpr ⟨has, s.isSorted_toListPBTree⟩⟩

section Cons

variable {has : ∀ b ∈ s, a < b}

@[simp] theorem cons_inj_iff : cons a s has = cons a' s' has' ↔ ((a = a') ∧ s = s') := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · unfold cons at h
    have H := Subtype.mk_eq_mk.mp h
    simp_rw [List.cons.injEq, toListPBTree_inj_iff] at H
    exact H
  · simp_rw [h.1, h.2]

@[simp] theorem toListPBTree_cons : (cons a s has).toListPBTree = a :: s.toListPBTree := rfl

@[simp] theorem length_cons : (cons a s has).length = s.length + 1 := rfl

instance : NeZero ((cons a s has).length) := ⟨Nat.succ_ne_zero _⟩

theorem length_ne_zero : s.length ≠ 0 ↔ s ≠ nil := length_eq_zero.not

theorem length_pos : 0 < s.length ↔ s ≠ nil := Nat.pos_iff_ne_zero.trans length_ne_zero

theorem one_le_length : 1 ≤ s.length ↔ s ≠ nil := length_pos

@[simp] theorem mem_cons : b ∈ cons a s has ↔ b = a ∨ b ∈ s := List.mem_cons

theorem mem_cons_self : a ∈ cons a s has := List.mem_cons_self _ _

end Cons

section NilCons

variable {has : ∀ b ∈ s, a < b}

@[simp] theorem nil_ne_cons : nil ≠ cons a s has := Subtype.coe_ne_coe.mp List.noConfusion

@[simp] theorem cons_ne_nil : cons a s has ≠ nil := Subtype.coe_ne_coe.mp List.noConfusion

@[elab_as_elim] def nilConsInduction {motive : PBTreeStack α → Sort _}
    (nil : motive nil)
    (cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive s → motive (cons a s has)) (t : PBTreeStack α) : motive t :=
  match t with
  | ⟨[], _⟩ => nil
  | ⟨a :: s, has⟩ =>
    cons a ⟨s, has.of_cons⟩ (List.rel_of_sorted_cons has) (nilConsInduction nil cons _)
  termination_by t.length
  decreasing_by exact Nat.lt_succ_self _

theorem nilConsInduction_nil {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive s → motive (cons a s has)} :
      nilConsInduction nil cons PBTreeStack.nil = nil := by
  unfold nilConsInduction
  rfl

theorem nilConsInduction_cons {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive s → motive (cons a s has)} :
      nilConsInduction nil cons (PBTreeStack.cons a s has) =
      cons a s has (nilConsInduction nil cons s) := by
  conv =>
    lhs
    unfold PBTree.node nilConsInduction
  rfl

@[elab_as_elim] def nilConsCases {motive : PBTreeStack α → Sort _}
    (nil : motive nil)
    (cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive (cons a s has)) (t : PBTreeStack α) : motive t :=
     nilConsInduction nil (fun a s has _ => cons a s has) t

theorem nilConsCases_nil {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive (cons a s has)} :
      nilConsCases nil cons PBTreeStack.nil = nil := nilConsInduction_nil

theorem nilConsCases_cons {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a < b) →
     motive (cons a s has)} :
      nilConsCases nil cons (PBTreeStack.cons a s has) =
      cons a s has := nilConsInduction_cons

theorem nil_or_exists_cons (t : PBTreeStack α) :
    t = nil ∨ (∃ a s has, t = cons a s has) := by
  cases t using nilConsCases
  · exact Or.inl rfl
  · exact Or.inr ⟨_, _, _, rfl⟩

theorem exists_of_length_ne_zero (ht : t.length ≠ 0) : ∃ a s has, t = cons a s has := by
  cases t using nilConsCases
  · exact (ht rfl).elim
  · exact ⟨_, _, _, rfl⟩

end NilCons

def singleton (a : PBTree α) : PBTreeStack α := cons a nil (fun _ H => (not_mem_nil _ H).elim)

section Singleton

@[simp] theorem cons_eq_singleton_iff :
  cons a s has = singleton b ↔ a = b ∧ s = nil := cons_inj_iff

theorem length_singleton : (singleton a).length = 1 := rfl

@[simp] theorem nil_ne_singleton : nil ≠ singleton a := nil_ne_cons

@[simp] theorem singleton_ne_nil : singleton a ≠ nil := cons_ne_nil

theorem length_eq_one : s.length = 1 ↔ ∃ a, s = singleton a := by
  cases s using nilConsCases
  · simp_rw [length_nil, zero_ne_one, nil_ne_singleton, exists_false]
  · simp_rw [length_cons, add_left_eq_self, length_eq_zero, cons_eq_singleton_iff,
    exists_and_right, exists_eq', true_and]

theorem eq_of_mem_singleton : b ∈ singleton a → b = a := List.eq_of_mem_singleton

@[simp] theorem mem_singleton : b ∈ singleton a ↔ b = a := List.mem_singleton

@[simp] theorem mem_singleton_self (a : PBTree α) : a ∈ singleton a := List.mem_singleton_self a

end Singleton

def height (s : PBTreeStack α) : ℕ := s.nilConsCases default (fun a _ _ => a.height)

section Height

theorem height_nil : (nil : PBTreeStack α).height = default := nilConsCases_nil

@[simp] theorem height_cons : (cons a s has).height = a.height := nilConsCases_cons

theorem height_le : ∀ a ∈ s, s.height ≤ a.height := by
  cases s using nilConsCases with | nil => _ | cons a s has => _
  · simp_rw [not_mem_nil, false_implies, implies_true]
  · simp_rw [mem_cons, height_cons, forall_eq_or_imp, le_refl, true_and]
    exact fun _ hs => (has _ hs).le

end Height

def size (s : PBTreeStack α) : ℕ :=
  s.nilConsCases 0 (fun a s _ => s.nilConsInduction (a.height + 1) (fun _ _ _ => id))

def count (s : PBTreeStack α) : ℕ :=
  s.nilConsInduction 0 (fun a _ _ m => m + a.count)

def push (s : PBTreeStack α) :
    (b : PBTree α) → (has : ∀ a ∈ s, b.height ≤ a.height) → PBTreeStack α :=
  s.nilConsInduction (fun b _ => singleton b)
  (fun a s has push b hbs => if hab : a.height = b.height then
  push (node a b hab) (fun _ h => height_node_left ▸ Nat.succ_le_of_lt (has _ h)) else
  cons b (cons a s has) (fun _ h => (mem_cons.mp h).elim
    (fun h => h ▸ lt_of_le_of_ne' (hbs _ mem_cons_self) hab)
    (fun h => (hbs _ mem_cons_self).trans_lt (has _ h))))

def pushLeaf (s : PBTreeStack α) (a : α) : PBTreeStack α := s.push (leaf a) (fun _ _ => zero_le _)

def pushTuple (s : PBTreeStack α) (bs : Fin k → α) : PBTreeStack α :=
    Fin.foldl k (fun p i => p.pushLeaf (bs i)) s

def ofTuple (bs : Fin k → α) : PBTreeStack α := pushTuple nil bs


theorem ofTuple_twoPowTuple' (bs : Fin (2^n) → α) (hs : n ≤ s.height) :
    s.pushTuple bs = s.push (PBTree.ofTuple bs)
    (height_ofTuple ▸ fun _ hs' => hs.trans (height_le _ hs')) := sorry


theorem ofTuple_twoPowTuple (bs : Fin (2^n) → α) :
    ofTuple bs = singleton (PBTree.ofTuple bs) := by
  induction n
  · unfold ofTuple pushTuple pushLeaf push
    simp_rw [Nat.pow_zero, Fin.foldl_succ, Fin.foldl_zero, nilConsInduction_nil, ofTuple_zero]
  · simp_rw [ofTuple_succ]
    sorry

end PBTreeStack

/-
def reduceList : List (PBTree α) → List (PBTree α)
  | [] => []
  | t :: [] => t :: []
  | l :: r :: ts =>
    if h : l.height = r.height then reduceList (node l r h :: ts)
    else reduceList (l :: reduceList (r :: ts))
    termination_by t => t.length
    decreasing_by
      simp
      simp
      simp

section ReduceList

variable {ts : List (PBTree α)}

@[simp] theorem reduceList_nil : reduceList ([] : List (PBTree α)) = [] := by
  unfold reduceList
  rfl

@[simp] theorem reduceList_singleton : reduceList ([t]) = [t] := by
  unfold reduceList
  rfl

theorem reduceList_front : reduceList (l :: r :: ts) =
  if h : l.height = r.height then reduceList (node l r h :: ts)
    else l :: reduceList (r :: ts) := by
  conv =>
    lhs
    unfold reduceList

theorem reduceList_front_of_height_eq_height (hlr : l.height = r.height) :
    reduceList (l :: r :: ts) = reduceList (node l r hlr :: ts) := by
  simp_rw [reduceList_front, dif_pos hlr]

theorem reduceList_front_of_heights_eq (hl : l.height = n) (hr : r.height = n) :
    reduceList (l :: r :: ts) = reduceList (node l r (hl.trans hr.symm) :: ts) :=
  reduceList_front_of_height_eq_height _

theorem reduceList_front_of_height_ne_height (hlr : l.height ≠ r.height) :
    reduceList (l :: r :: ts) = l :: reduceList (r :: ts) := by
  simp_rw [reduceList_front, dif_neg hlr]

theorem reduceList_cons_of_tail_eq_nil (hts : ts = []) :
    reduceList (t :: ts) = [t] := by
  rw [hts, reduceList_singleton]

theorem reduceList_cons_of_tail_ne_nil_of_eq_head_height (hts : ts ≠ [])
    (htts : t.height = (ts.head hts).height) :
    reduceList (t :: ts) = reduceList (t.node (ts.head hts) htts :: ts.tail) := by
  rcases List.exists_cons_of_ne_nil hts with ⟨t', ts, rfl⟩
  simp_rw [List.head_cons, List.tail_cons,
    reduceList_front_of_height_eq_height (List.head_cons ▸ htts)]

theorem reduceList_cons_of_tail_ne_nil_of_ne_head_height (hts : ts ≠ [])
    (htts : t.height ≠ (ts.head hts).height) : reduceList (t :: ts) = t :: reduceList ts := by
  rcases List.exists_cons_of_ne_nil hts with ⟨t', ts, rfl⟩
  simp_rw [List.head_cons] at htts
  rw [reduceList_front_of_height_ne_height htts]

theorem reduceList_cons : reduceList (t :: ts) =
    if hts : ts = [] then [t] else if
    htts : t.height = (ts.head hts).height then
    reduceList (t.node (ts.head hts) htts :: ts.tail) else
    t :: reduceList ts := by
  split_ifs
  · exact reduceList_cons_of_tail_eq_nil (by assumption)
  · exact reduceList_cons_of_tail_ne_nil_of_eq_head_height (by assumption) (by assumption)
  · exact reduceList_cons_of_tail_ne_nil_of_ne_head_height (by assumption) (by assumption)

theorem reduceList_length_le : (reduceList ts).length ≤ ts.length := by
  generalize hts : ts.length = n ; revert hts
  induction n generalizing ts with | zero => _ | succ n IH => _
  · simp_rw [nonpos_iff_eq_zero, List.length_eq_zero]
    rintro rfl ; exact reduceList_nil
  · cases ts with | nil => _ | cons l ts => _
    · simp_rw [reduceList_nil, List.length_nil, (Nat.succ_ne_zero _).symm, false_implies]
    · cases ts with | nil => _ | cons r ts => _
      · simp_rw [reduceList_singleton, List.length_cons, Nat.add_left_inj]
        rintro rfl ; exact le_rfl
      · intro hts
        simp_rw [List.length_cons, Nat.add_left_inj] at hts
        by_cases hlr : l.height = r.height
        · simp_rw [reduceList_front_of_height_eq_height hlr]
          exact (IH (List.length_cons _ _ ▸ hts)).trans (Nat.lt_succ_self _).le
        · simp_rw [reduceList_front_of_height_ne_height hlr]
          exact Nat.succ_le_succ (IH hts)

theorem reduceList_eq_nil_iff : reduceList ts = [] ↔ ts = [] := by
  generalize hts : ts.length = n ; revert hts
  induction n generalizing ts with | zero => _ | succ n IH => _
  · simp_rw [List.length_eq_zero]
    rintro rfl ; simp_rw [reduceList_nil]
  · cases ts with | nil => _ | cons l ts => _
    · simp_rw [reduceList_nil, implies_true]
    · cases ts with | nil => _ | cons r ts => _
      · simp_rw [reduceList_singleton, implies_true]
      · intro hts
        simp_rw [List.length_cons, add_left_inj] at hts
        by_cases hlr : l.height = r.height
        · simp_rw [reduceList_front_of_height_eq_height hlr, IH (List.length_cons _ _ ▸ hts),
            List.cons_ne_nil]
        · simp_rw [reduceList_front_of_height_ne_height hlr, List.cons_ne_nil]

theorem reduceList_reduceList : reduceList (reduceList ts) = reduceList ts := by
  generalize hts : ts.length = n ; revert hts
  induction n generalizing ts with | zero => _ | succ n IH => _
  · simp_rw [List.length_eq_zero]
    rintro rfl ; simp_rw [reduceList_nil]
  · cases ts with | nil => _ | cons l ts => _
    · simp_rw [reduceList_nil, implies_true]
    · cases ts with | nil => _ | cons r ts => _
      · simp_rw [reduceList_singleton, implies_true]
      · intro hts
        simp_rw [List.length_cons, add_left_inj] at hts
        by_cases hlr : l.height = r.height
        · simp_rw [reduceList_front_of_height_eq_height hlr, IH (List.length_cons _ _ ▸ hts)]
        · simp_rw [reduceList_front_of_height_ne_height hlr]
          rw [reduceList_cons]
          cases ts with | nil => _ | cons r' ts => _
          · simp only [reduceList_singleton, reduceList_front_of_height_ne_height hlr]
          · by_cases hrr' : r.height = r'.height
            · simp_rw [reduceList_front_of_height_eq_height hrr']

theorem reduceList_reduceList :
    {ts : List (PBTree α)} → reduceList (reduceList ts) = reduceList ts
  | [] => by simp_rw [reduceList_nil]
  | [t] => by simp_rw [reduceList_singleton]
  | l :: r :: ts => by
    by_cases hlr : l.height = r.height
    · simp_rw [reduceList_front_of_height_eq_height hlr, reduceList_reduceList]
    · simp_rw [reduceList_front_of_height_ne_height hlr]
      cases H : reduceList (r :: ts) with | nil => _ | cons => _
      · simp_rw [reduceList_singleton]
      ·

end ReduceList
-/
