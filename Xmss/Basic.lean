import Xmss.Lib

inductive BTree (α : Type u) : Type u where
  | leaf : α → BTree α
  | node : BTree α → BTree α → BTree α
deriving Repr, DecidableEq, Inhabited

namespace BTree

variable {α : Type u} {a b : α} {t l r : BTree α} {n : ℕ}

instance [IsEmpty α] : IsEmpty (BTree α) := ⟨fun t => t.recOn isEmptyElim (fun _ _ C => C.elim)⟩

instance [Nonempty α] : Infinite (BTree α) :=
  Infinite.of_injective (fun (i : ℕ) =>
    i.recOn (leaf (Classical.arbitrary _)) (fun _ t => node t t))
    (fun i => i.recOn (fun j => j.recOn (fun _ => rfl)
    (fun _ _ C => BTree.noConfusion C))
    (fun _ IH j => j.recOn (fun C => BTree.noConfusion C)
    fun _ _ H => congrArg _ (IH (node.injEq _ _ _ _ ▸ H).1)))

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

@[simp] theorem left_height_lt : l.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_left _ _

@[simp] theorem right_height_lt : r.height < (node l r).height := by
  simp_rw [height_node, Nat.lt_succ_iff]
  exact le_max_right _ _

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

@[simp] theorem isPerfect_leaf : (leaf a).isPerfect := rfl

theorem isPerfect_node_of_height_eq_height (h : l.height = r.height) :
    (node l r).isPerfect ↔ (l.isPerfect ∧ r.isPerfect) := by
  simp_rw [isPerfect_def, height_node, isPerfectOfHeight_succ_node,
    h, max_self,  Bool.and_eq_true]

@[simp] theorem isPerfect_node_iff : (node l r).isPerfect ↔
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

theorem isPerfect.left (hlr : (node l r).isPerfect) : l.isPerfect :=
  (isPerfect_node_iff.mp hlr).1
theorem isPerfect.right (hlr : (node l r).isPerfect) : r.isPerfect :=
  (isPerfect_node_iff.mp hlr).2.1
theorem isPerfect.height_eq_height (hlr : (node l r).isPerfect) : l.height = r.height :=
  (isPerfect_node_iff.mp hlr).2.2
theorem isPerfect.double_node (h : l.isPerfect) : (node l l).isPerfect :=
  isPerfect_node_iff.mpr ⟨h, h, rfl⟩

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

theorem count_eq_two_pow_height_of_isPerfect (ht : t.isPerfect) : t.count = 2^t.height := by
  induction t with | leaf _ => _ | node _ _ IHL IHR => _
  · simp_rw [count_lead, height_leaf, pow_zero]
  · simp_rw [isPerfect_node_iff] at ht
    simp_rw [count_node, height_node, pow_succ', two_mul, ht.2.2, IHL ht.1, IHR ht.2.1, ht.2.2,
      max_self]

end Count

def map (f : α → β) : BTree α → BTree β
  | leaf a => leaf (f a)
  | node l r => node (l.map f) (r.map f)

section Map

variable {f : α → β} {h : β → γ}

@[simp] theorem map_leaf : (leaf a).map f = leaf (f a) := rfl

@[simp] theorem map_node : (node l r).map f = node (l.map f) (r.map f) := rfl

theorem id_map : map id t = t := by
  induction t
  · simp_rw [map_leaf, id_eq]
  · simp_rw [map_node, node.injEq]
    exact And.intro (by assumption) (by assumption)

theorem comp_map : map (f ∘ g) t = map f (map g t) := by
  induction t
  · simp_rw [map_leaf, Function.comp_apply]
  · simp_rw [map_node, node.injEq]
    exact And.intro (by assumption) (by assumption)

instance : Functor BTree where
  map := BTree.map

instance : LawfulFunctor BTree where
  map_const := rfl
  id_map t := id_map
  comp_map g h t := by convert comp_map

end Map



instance : Monad BTree where
  pure a := leaf a
  bind t := _


instance : LawfulMonad BTree

def flatten : BTree (BTree α) → BTree α
  | leaf a => a
  | node l r => node (l.flatten) (r.flatten)



end BTree

def PBTree (α : Type u) := Subtype (BTree.isPerfect (α := α))

namespace PBTree

open BTree

instance [Repr α] : Repr (PBTree α) := instReprSubtype
instance [DecidableEq α] : DecidableEq (PBTree α) := Subtype.instDecidableEq
instance [Inhabited α] : Inhabited (PBTree α) := ⟨leaf default, isPerfect_leaf⟩
instance [IsEmpty α] : IsEmpty (PBTree α) := instIsEmptySubtype _

instance [Nonempty α] : Infinite (PBTree α) :=
  Infinite.of_injective (fun (i : ℕ) =>
    i.recOn (⟨leaf (Classical.arbitrary _), isPerfect_leaf⟩)
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

theorem isPerfect_toBTree : t.toBTree.isPerfect := t.2

end ToBTree

def height (t : PBTree α) : ℕ := t.toBTree.height

section Height

@[simp] theorem height_toBTree : t.toBTree.height = t.height := rfl

end Height

def leaf (a : α) : PBTree α := ⟨BTree.leaf a, isPerfect_leaf⟩

section Leaf

@[simp] theorem leaf_default_eq_default [Inhabited α] : leaf (default : α) = default := rfl

theorem leaf_injective : Function.Injective (leaf (α := α)) := fun _ _ H => by
  rw [← leaf.injEq]
  exact Subtype.mk_eq_mk.mp H

@[simp] theorem leaf_inj_iff : leaf a = leaf b ↔ a = b :=
  ⟨fun h => leaf_injective h, congrArg _⟩

@[simp] theorem height_leaf : height (leaf a) = 0 := rfl

end Leaf

def node (l r : PBTree α) (hlr : l.height = r.height) : PBTree α :=
  ⟨BTree.node l.toBTree r.toBTree,
  isPerfect_node_of_isPerfect_of_isPerfect_of_heights_eq
  l.isPerfect_toBTree r.isPerfect_toBTree hlr rfl⟩

section Node

variable {hlr : l.height = r.height}

@[simp] theorem node_inj_iff : node l r hlr = node l' r' hlr' ↔ ((l = l') ∧ r = r') := by
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

@[simp] theorem left_height_lt : l.height < (node l r hlr).height := by
  simp_rw [height_node_left, Nat.lt_succ_self]

@[simp] theorem right_height_lt : r.height < (node l r hlr).height := by
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

instance : Preorder (PBTree α) where
  lt l r := l.height < r.height
  le l r := l.height ≤ r.height
  le_refl t := le_refl (t.height)
  le_trans _ l r htl (hlr : l.height ≤ r.height) := le_trans htl hlr
  lt_iff_le_not_le _ _ := lt_iff_le_not_le (α := ℕ)

theorem lt_iff_height_lt_height : l < r ↔ l.height < r.height := Iff.rfl
theorem le_iff_height_le_height : l ≤ r ↔ l.height ≤ r.height := Iff.rfl

instance [Subsingleton α] : PartialOrder (PBTree α) where
  le_antisymm l r hlr hrl := by
    rw [le_iff_height_le_height] at hlr hrl
    have h := le_antisymm hlr hrl
    clear hlr hrl
    induction l using leafNodeInduction generalizing r with | leaf => _ | node l r hlr IHL IHR => _
    · cases r using leafNodeCases
      · simp_rw [leaf_inj_iff]
        exact Subsingleton.elim _ _
      · simp_rw [height_node_right, height_leaf, (Nat.succ_ne_zero _).symm] at h
    · cases r using leafNodeCases with | leaf => _ | node l' r' hlr' => _
      · simp_rw [height_node_right, height_leaf, (Nat.succ_ne_zero _)] at h
      · simp_rw [node_inj_iff]
        simp_rw [height_node_right, add_left_inj] at h
        exact ⟨IHL _ (hlr.trans <| h.trans hlr'.symm), IHR _ h⟩

theorem not_IsPartialOrder [Nontrivial α] : ¬ IsPartialOrder (PBTree α) (· ≤ ·) := fun h => by
  rcases Nontrivial.exists_pair_ne (α := α) with ⟨x, y, hxy⟩
  have H := h.antisymm (leaf x) (leaf y) (le_refl 0) (le_refl 0)
  rw [leaf_inj_iff] at H
  contradiction

def count (t : PBTree α) := 2^t.height

section Count

theorem count_eq_two_pow_height : t.count = 2^t.height := rfl

@[simp] theorem count_toBTree : t.toBTree.count = t.count :=
  count_eq_two_pow_height_of_isPerfect isPerfect_toBTree

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

theorem isSorted_toListPBTree : s.toListPBTree.Sorted (· < ·) := s.2

theorem of_toListPBTree_eq_cons (h : s.toListPBTree = a :: ts) : ts.Sorted (· < ·) :=
  List.Sorted.of_cons (h ▸ isSorted_toListPBTree)

theorem rel_of_toListPBTree_eq_cons (h : s.toListPBTree = a :: ts) : ∀ b ∈ ts, a < b :=
  List.rel_of_sorted_cons (h ▸ isSorted_toListPBTree)

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

def cons (a : PBTree α) (s : PBTreeStack α) (has : ∀ b ∈ s, a.height < b.height) : PBTreeStack α :=
  ⟨a :: s.toListPBTree, List.sorted_cons.mpr ⟨has, s.isSorted_toListPBTree⟩⟩

section Cons

variable {has : ∀ b ∈ s, a.height < b.height}

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

@[simp] theorem mem_cons : b ∈ cons a s has ↔ b = a ∨ b ∈ s := List.mem_cons

theorem mem_cons_self : a ∈ cons a s has := List.mem_cons_self _ _

end Cons

section NilCons

variable {has : ∀ b ∈ s, a.height < b.height}

@[simp] theorem nil_ne_cons : nil ≠ cons a s has := Subtype.coe_ne_coe.mp List.noConfusion

@[simp] theorem cons_ne_nil : cons a s has ≠ nil := Subtype.coe_ne_coe.mp List.noConfusion

@[elab_as_elim] def nilConsInduction {motive : PBTreeStack α → Sort _}
    (nil : motive nil)
    (cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
     motive s → motive (cons a s has)) (t : PBTreeStack α) : motive t :=
  match t with
  | ⟨[], _⟩ => nil
  | ⟨a :: s, has⟩ =>
    cons a ⟨s, has.of_cons⟩ (List.rel_of_sorted_cons has) (nilConsInduction nil cons _)
  termination_by t.length
  decreasing_by exact Nat.lt_succ_self _

theorem nilConsInduction_nil {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
     motive s → motive (cons a s has)} :
      nilConsInduction nil cons PBTreeStack.nil = nil := by
  unfold nilConsInduction
  rfl

theorem nilConsInduction_cons {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
     motive s → motive (cons a s has)} :
      nilConsInduction nil cons (PBTreeStack.cons a s has) =
      cons a s has (nilConsInduction nil cons s) := by
  conv =>
    lhs
    unfold PBTree.node nilConsInduction
  rfl

@[elab_as_elim] def nilConsCases {motive : PBTreeStack α → Sort _}
    (nil : motive nil)
    (cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
     motive (cons a s has)) (t : PBTreeStack α) : motive t :=
     nilConsInduction nil (fun a s has _ => cons a s has) t

theorem nilConsCases_nil {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
     motive (cons a s has)} :
      nilConsCases nil cons PBTreeStack.nil = nil := nilConsInduction_nil

theorem nilConsCases_cons {motive : PBTreeStack α → Sort _}
    {nil : motive nil}
    {cons : (a : PBTree α) → (s : PBTreeStack α) → (has : ∀ b ∈ s, a.height < b.height) →
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

def singleLeaf (a : α) : PBTreeStack α := singleton (leaf a)

section SingleLeaf

@[simp] theorem cons_eq_singleLeaf_iff :
  cons a s has = singleLeaf b ↔ a = leaf b ∧ s = nil := cons_eq_singleton_iff

theorem length_singleLeaf : (singleLeaf a).length = 1 := rfl

@[simp] theorem nil_ne_singleLeaf : nil ≠ singleLeaf a := nil_ne_singleton

@[simp] theorem singleLeaf_ne_nil : singleton a ≠ nil := singleton_ne_nil

theorem eq_of_mem_singleLeaf {a : α} : b ∈ singleLeaf a → b = leaf a := List.eq_of_mem_singleton

@[simp] theorem mem_singleLeaf {a : α} : b ∈ singleLeaf a ↔ b = leaf a := List.mem_singleton

@[simp] theorem mem_singleLeaf_self (a : α) : leaf a ∈ singleLeaf a := mem_singleton_self (leaf a)

end SingleLeaf

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
