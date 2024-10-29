import Mathlib

variable {β : Type*} {n : ℕ}

example : 2^n + 2^n = 2^(n + 1) := by exact Eq.symm (Nat.two_pow_succ n)

theorem Bool.cond_apply {α : Type*} {σ : α → Type*} (b : Bool) (f : (a : α) → σ a)
    (g : (a : α) → σ a) (a : α) : (bif b then f else g) a = bif b then f a else g a := b.rec rfl rfl

namespace Fin

def finArrowBoolToNat : {n : ℕ} → (Fin n → Bool) → ℕ
| 0 => fun _ => 0
| (_ + 1) => fun bv => Nat.bit (bv 0) (finArrowBoolToNat (fun i => bv i.succ))

@[simp]
theorem finArrowBoolToNat_zero : finArrowBoolToNat (bv : Fin 0 → Bool) = 0 := rfl

theorem finArrowBoolToNat_succ : finArrowBoolToNat (bv : Fin (n + 1) → Bool) =
    Nat.bit (bv 0) (finArrowBoolToNat (fun i => bv i.succ)) := rfl

theorem finArrowBoolToNat_lt {bv : Fin n → Bool} : finArrowBoolToNat bv < 2^n := by
  induction' n with n IH
  · simp_rw [finArrowBoolToNat_zero, pow_zero, Nat.lt_one_iff]
  · simp_rw [finArrowBoolToNat_succ, Nat.bit_lt_two_pow_succ_iff, IH]

theorem testBit_finArrowBoolToNat_lt {bv : Fin n → Bool} {k : ℕ} (hk : k < n) :
    (finArrowBoolToNat bv).testBit k = bv ⟨k, hk⟩ := by
  induction' n with n IH generalizing k
  · exact (Nat.not_lt_zero _ hk).elim
  · rw [finArrowBoolToNat_succ]
    rcases k with (_ | k)
    · simp_rw [Nat.testBit_bit_zero, zero_eta]
    · simp_rw [Nat.testBit_bit_succ, IH (Nat.lt_of_succ_lt_succ hk), succ_mk]

theorem testBit_finArrowBoolToNat_ge {bv : Fin n → Bool} {k : ℕ} (hk : n ≤ k) :
    (finArrowBoolToNat bv).testBit k = false := Nat.testBit_eq_false_of_lt <|
  (finArrowBoolToNat_lt).trans_le (Nat.pow_le_pow_of_le one_lt_two hk)

theorem testBit_finArrowBoolToNat {bv : Fin n → Bool} {k : ℕ} :
    (finArrowBoolToNat bv).testBit k = if hk : k < n then bv ⟨k, hk⟩ else false := by
  split_ifs with hk
  · exact testBit_finArrowBoolToNat_lt hk
  · exact testBit_finArrowBoolToNat_ge (le_of_not_lt hk)

theorem finArrowBoolToNat_testBit (i : ℕ) :
    (finArrowBoolToNat (fun (k : Fin n) => i.testBit k)) = i % 2^n := by
  apply Nat.eq_of_testBit_eq
  simp_rw [Nat.testBit_mod_two_pow, testBit_finArrowBoolToNat]
  intro k
  split_ifs with hk <;> simp_rw [hk]
  · simp_rw [decide_True, Bool.true_and]
  · simp_rw [decide_False, Bool.false_and]

theorem finArrowBoolToNat_testBit_of_lt {i : ℕ} (hi : i < 2^n):
    (finArrowBoolToNat (fun (k : Fin n) => i.testBit k)) = i := by
  rw [finArrowBoolToNat_testBit, Nat.mod_eq_of_lt hi]

theorem finArrowBoolToNat_inj {bv bv' : Fin n → Bool}
    (h : finArrowBoolToNat bv = finArrowBoolToNat bv') : bv = bv' := by
  ext ⟨k, hk⟩
  rw [← testBit_finArrowBoolToNat_lt (bv := bv) hk, h, testBit_finArrowBoolToNat_lt]

theorem finArrowBoolToNat_injective : Function.Injective (finArrowBoolToNat (n := n)) := by
  exact fun {bv bv'} => finArrowBoolToNat_inj

theorem lt_two_pow_iff_exists_finArrowBoolToNat :
    i < 2^n ↔ ∃ bv : Fin n → Bool, finArrowBoolToNat bv = i :=
  ⟨fun h => ⟨fun (k : Fin n) => i.testBit k, finArrowBoolToNat_testBit_of_lt h⟩,
    fun ⟨_, h⟩ => h ▸ finArrowBoolToNat_lt⟩

theorem range_finArrowBoolToNat : Set.range (finArrowBoolToNat (n := n)) = Finset.range (2^n) := by
  ext
  simp_rw [Set.mem_range, Finset.coe_range, Set.mem_Iio, lt_two_pow_iff_exists_finArrowBoolToNat]

@[simps!]
def finArrowBoolEquivFinTwoPow : (Fin n → Bool) ≃ Fin (2 ^ n) := {
  toFun := fun bv => ⟨finArrowBoolToNat bv, finArrowBoolToNat_lt⟩
  invFun := fun i k => (i : ℕ).testBit k
  left_inv := fun _ => by
    simp_rw [testBit_finArrowBoolToNat, is_lt, dite_true]
  right_inv :=  fun i => by
    simp_rw [Fin.ext_iff, finArrowBoolToNat_testBit_of_lt i.isLt]}

@[simps!]
def finArrowBoolEquivBitVec : (Fin n → Bool) ≃ BitVec n := {
  toFun := fun bv => BitVec.ofNatLt (finArrowBoolToNat bv) finArrowBoolToNat_lt
  invFun := fun i k => i.toNat.testBit k
  left_inv := fun _ => by
    simp_rw [BitVec.toNat_ofNatLt, testBit_finArrowBoolToNat, is_lt, dite_true]
  right_inv :=  fun i => by
    simp_rw [BitVec.toNat_eq, BitVec.toNat_ofNatLt, finArrowBoolToNat_testBit_of_lt i.isLt]}

end Fin

def concatTwoPow : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) := calc
    _ ≃ _ := (Equiv.boolProdEquivSum _).symm
    _ ≃ _ := finTwoEquiv.symm.prodCongr (Equiv.refl _)
    _ ≃ _ := finProdFinEquiv
    _ ≃ _ := finCongr (by omega)

lemma concatTwoPow_inl_apply {i : Fin (2^n)} : (concatTwoPow (Sum.inl i)).val = i := rfl

@[simp]
lemma concatTwoPow_inl_apply_val {i : Fin (2^n)} : (concatTwoPow (Sum.inl i)).val = i := rfl

@[simp]
lemma concatTwoPow_inr_apply_val {i : Fin (2^n)} : (concatTwoPow (Sum.inr i)).val = i + 2^n := by
  trans (i + 2^n*1)
  · rfl
  · rw [mul_one]

theorem concatTwoPow_inl_zero : concatTwoPow (Sum.inl (0 : Fin (2^n))) = 0 := rfl

def interleveTwoPow : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) := calc
    _ ≃ _ := (Equiv.boolProdEquivSum _).symm
    _ ≃ _ := finTwoEquiv.symm.prodCongr (Equiv.refl _)
    _ ≃ _ := Equiv.prodComm ..
    _ ≃ _ := finProdFinEquiv

@[simp]
lemma interleveTwoPow_inl_apply_val {i : Fin (2^n)} :
    (interleveTwoPow (Sum.inl i)).val = 2*i := by
  trans (0 + 2*i)
  · rfl
  · rw [zero_add]

@[simp]
lemma interleveTwoPow_inr_apply_val {i : Fin (2^n)} :
    (interleveTwoPow (Sum.inr i)).val = 2*i + 1 := by
  trans (1 + 2*i)
  · rfl
  · rw [add_comm]

theorem concatTwoPow_inl_interleveTwoPow_inl :
    concatTwoPow (Sum.inl (interleveTwoPow (Sum.inl i))) =
    interleveTwoPow (Sum.inl (concatTwoPow (Sum.inl i))) := rfl

theorem concatTwoPow_inl_interleveTwoPow_inr :
    concatTwoPow (Sum.inl (interleveTwoPow (Sum.inr i))) =
    interleveTwoPow (Sum.inr (concatTwoPow (Sum.inl i))) := rfl

theorem concatTwoPow_inr_interleveTwoPow_inr :
    concatTwoPow (Sum.inr (interleveTwoPow (Sum.inr i))) =
    interleveTwoPow (Sum.inr (concatTwoPow (Sum.inr i))) := by
  ext
  simp only [interleveTwoPow_inr_apply_val, concatTwoPow_inr_apply_val, mul_add, pow_succ',
    add_right_comm]

theorem concatTwoPow_inr_interleveTwoPow_inl :
    concatTwoPow (Sum.inr (interleveTwoPow (Sum.inl i))) =
    interleveTwoPow (Sum.inl (concatTwoPow (Sum.inr i))) := by
  ext
  simp only [interleveTwoPow_inl_apply_val, concatTwoPow_inr_apply_val, mul_add, pow_succ']

def twoPowSuccTupleDivide : (Fin (2 ^ (n + 1)) → β) ≃ (Fin (2 ^ n) → β) × (Fin (2 ^ n) → β) :=
  (concatTwoPow.symm.arrowCongr <| Equiv.refl _).trans <| Equiv.sumArrowEquivProdArrow _ _ _

class Hash (β : Type u) where
  hash : β → β → β

infixl:65 " # " => Hash.hash

inductive BTree (β : Type*) where
  | leaf : β → BTree β
  | node : β → BTree β → BTree β → BTree β

namespace BTree

#check node 3 (leaf 2) (node 1 (leaf 7) (leaf 6))

def root : BTree β → β
  | leaf b => b
  | node b _ _ => b

variable [Hash β]

def listOfTree : {n : ℕ} → (Fin (2^n) → β) → BTree β
  | 0, t => leaf (t 0)
  | (_ + 1), t =>
    let (f, l) := twoPowSuccTupleDivide t
    let t₁ := listOfTree f
    let t₂ := listOfTree l
    node ((root t₁) # (root t₂)) t₁ t₂

def finalHash (n : ℕ) (list : Fin (2^n) → β) : β := root (listOfTree list)

theorem finalHash_zero (list : Fin (2^0) → β) :
  finalHash 0 list = list 0 := rfl

theorem finalHash_succ (n : ℕ) (list : Fin (2^(n + 1)) → β) :
  finalHash (n + 1) list = (finalHash n (fun i => list (concatTwoPow <| Sum.inl i))) #
  (finalHash n (fun i => list (concatTwoPow <| Sum.inr i))) := rfl

theorem finalHash_succ_eq_finalHash (n : ℕ) (list : Fin (2^(n + 1)) → β) :
    finalHash (n + 1) list = finalHash n (fun i =>
    list (interleveTwoPow (Sum.inl i)) # list (interleveTwoPow (Sum.inr i))) := by
  induction' n with n IH
  · exact rfl
  · rw [finalHash_succ (n + 1), IH, IH, finalHash_succ n]
    congr
    simp_rw [concatTwoPow_inr_interleveTwoPow_inl, concatTwoPow_inr_interleveTwoPow_inr]

end BTree

@[reducible]
def SharedStack (β : Type*) := List (Option β)

namespace SharedStack

def addToStack [Hash β] (s : SharedStack β) (b : β) : SharedStack β :=
  match s with
  | [] => []
  | (none :: s) => some b :: s
  | (some a :: s) => none :: addToStack s (a # b)

@[simp]
theorem addToStack_nil [Hash β] (b : β) : addToStack [] b = [] := rfl

@[simp]
theorem addToStack_none_cons [Hash β] (s : SharedStack β) (b : β) :
    addToStack (none :: s) b = some b :: s := rfl

@[simp]
theorem addToStack_some_cons [Hash β] (s : SharedStack β) (b : β) :
    addToStack (some a :: s) b = none :: addToStack s (a # b) := rfl

theorem length_addToStack [Hash β] (s : SharedStack β) (b : β) :
    (addToStack s b).length = s.length := by
  induction' s with a s IH generalizing b
  · rw [addToStack_nil]
  · cases' a
    · simp_rw [addToStack_none_cons, List.length_cons]
    · simp_rw [addToStack_some_cons, List.length_cons, add_left_inj, IH]

theorem mem_addToStack_eq_none_iff_mem_isSome [Hash β] (s : SharedStack β) (b : β) :
    (∀ a ∈ s.addToStack b, a = none) ↔ ∀ a ∈ s, a.isSome := by
  induction' s with a s IH generalizing b
  · simp_rw [addToStack_nil, List.not_mem_nil, false_implies]
  · cases' a
    · simp_rw [addToStack_none_cons, List.mem_cons, forall_eq_or_imp, Option.some_ne_none,
        Option.isSome_none, Bool.false_eq_true, false_and]
    · simp_rw [addToStack_some_cons, List.mem_cons, forall_eq_or_imp, Option.isSome_some, IH]

theorem mem_addToStack_eq_none_iff_mem_isSome' [Hash β] (s : SharedStack β) (b : β) :
    (∃ a ∈ s.addToStack b, a.isSome) ↔ ∃ a ∈ s, a = none := not_iff_not.mp <| by
  simp_rw [not_exists, not_and, Bool.not_eq_true, ← Bool.not_eq_true,
    Option.not_isSome_iff_eq_none, mem_addToStack_eq_none_iff_mem_isSome, ← Bool.not_eq_false,
    Option.not_isSome, Option.isNone_iff_eq_none]

def stackToNat (s : SharedStack β) : ℕ :=
  match s with
  | [] => 0
  | (a :: s) => Nat.bit a.isSome (stackToNat s)

@[simp]
theorem stackToNat_nil : stackToNat ([] : SharedStack β) = 0 := rfl

theorem stackToNat_cons (s : SharedStack β) :
    stackToNat (a :: s) = Nat.bit a.isSome s.stackToNat := rfl

@[simp]
theorem stackToNat_some_cons (s : SharedStack β) :
    stackToNat (some a :: s) = 2 * s.stackToNat + 1 := rfl

@[simp]
theorem stackToNat_none_cons (s : SharedStack β) :
    stackToNat (none :: s) = 2 * s.stackToNat := rfl

@[simp]
theorem testBit_stackToNat {s : SharedStack β} {i : ℕ} :
    s.stackToNat.testBit i = if h : i < s.length then s[i].isSome else false := by
  induction' s with a s IH generalizing i
  · simp_rw [stackToNat_nil, Nat.zero_testBit, List.length_nil, not_lt_zero', dite_false]
  · simp_rw [List.length_cons, stackToNat_cons]
    cases' i
    · simp_rw [Nat.testBit_bit_zero, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
    · simp_rw [Nat.testBit_bit_succ, Nat.succ_lt_succ_iff, List.getElem_cons_succ, IH]

theorem testBit_fin_length {s : SharedStack β} {i : Fin (s.length)} :
    s.stackToNat.testBit i = s[(i : ℕ)].isSome := by simp_rw [testBit_stackToNat, i.isLt, dite_true]

theorem finArrowBoolToNat_isSome_get_eq_stackToNat (s : SharedStack β) :
    Fin.finArrowBoolToNat (fun i => Option.isSome <| s[(i : ℕ)]) = s.stackToNat :=
  Nat.eq_of_testBit_eq (fun _ => Fin.testBit_finArrowBoolToNat.trans testBit_stackToNat.symm)

theorem stackToNat_addToStack_of_none_mem [Hash β] (s : SharedStack β) (hs : none ∈ s) (b : β) :
    stackToNat (addToStack s b) = s.stackToNat + 1 := by
  induction' s with a s IH generalizing b
  · simp at hs
  · cases' a
    · simp_rw [addToStack_none_cons, stackToNat_some_cons, stackToNat_none_cons]
    · simp at hs
      simp_rw [addToStack_some_cons, stackToNat_none_cons, stackToNat_some_cons, IH hs, mul_add]

theorem stackToNat_eq_zero_iff_all_none (s : SharedStack β) :
    s.stackToNat = 0 ↔ ∀ a ∈ s, a = none := by
  induction' s with a s IH
  · simp_rw [stackToNat_nil, List.not_mem_nil, false_implies, implies_true]
  · cases' a
    · simp_rw [stackToNat_none_cons, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, List.mem_cons,
        forall_eq_or_imp, true_and, IH]
    · simp_rw [stackToNat_some_cons, Nat.add_eq_zero_iff, mul_eq_zero,
        two_ne_zero, false_or, one_ne_zero, and_false, List.mem_cons, forall_eq_or_imp,
        Option.some_ne_none, false_and]

theorem stackToNat_addToStack_of_none_nmem [Hash β] (s : SharedStack β) (hs : ¬ none ∈ s) (b : β) :
    stackToNat (addToStack s b) = 0 := by
  rw [stackToNat_eq_zero_iff_all_none]
  induction' s with a s IH generalizing b
  · simp_rw [addToStack_nil, List.not_mem_nil, false_implies, implies_true]
  · cases' a
    · simp_rw [List.mem_cons, true_or, not_true_eq_false] at hs
    · simp_rw [List.mem_cons, fun i => (Option.some_ne_none i).symm, false_or] at hs
      simp_rw [addToStack_some_cons, stackToNat_none_cons, stackToNat_some_cons, IH hs, mul_add]

theorem stackToNat_pos_iff_exists_some (s : SharedStack β) :
    0 < s.stackToNat ↔ ∃ a ∈ s, a.isSome := by
  simp_rw [Nat.pos_iff_ne_zero, ne_eq, stackToNat_eq_zero_iff_all_none,
    not_forall, exists_prop, Option.ne_none_iff_isSome]

theorem stackToNat_lt_two_pow (s : SharedStack β) :
    s.stackToNat < 2^(s.length) := by
  induction' s with a s IH
  · simp_rw [stackToNat_nil, List.length_nil, pow_zero, zero_lt_one]
  · cases' a
    · simp_rw [stackToNat_none_cons, List.length_cons, pow_succ']
      exact Nat.bit_lt_bit false false IH
    · simp_rw [stackToNat_some_cons, List.length_cons, pow_succ']
      exact Nat.bit_lt_bit true false IH

theorem stackToNat_le_two_pow_sub_one (s : SharedStack β) :
    s.stackToNat ≤ 2^(s.length) - 1 := by
  rw [Nat.le_sub_one_iff_lt (Nat.two_pow_pos _)]
  exact s.stackToNat_lt_two_pow

theorem stackToNat_lt_two_pow_pred_iff_none_mem (s : SharedStack β) :
    s.stackToNat < 2^(s.length) - 1 ↔ none ∈ s := by
  simp_rw [Nat.sub_one, Nat.lt_pred_iff]
  induction' s with a s IH
  · simp_rw [stackToNat_nil, Nat.succ_eq_add_one, zero_add, List.length_nil, pow_zero,
      lt_self_iff_false, List.not_mem_nil]
  · cases' a
    · simp_rw [stackToNat_none_cons, Nat.succ_eq_add_one, List.length_cons, List.mem_cons,
        true_or, iff_true, pow_succ',
        ← (Nat.ne_of_odd_add ((odd_two_mul_add_one _).add_even (even_two_mul _))).le_iff_lt,
        Nat.add_one_le_iff, Nat.mul_lt_mul_left (zero_lt_two), stackToNat_lt_two_pow]
    · simp_rw [stackToNat_some_cons, Nat.succ_eq_add_one, List.length_cons, List.mem_cons,
        fun x => (Option.some_ne_none x).symm, false_or, add_assoc, ← two_mul, ← mul_add,
        pow_succ', Nat.mul_lt_mul_left (zero_lt_two), IH]

theorem stackToNat_eq_two_pos_pred_iff_forall_mem_isSome (s : SharedStack β) :
    s.stackToNat = 2^(s.length) - 1 ↔ ∀ a ∈ s, a.isSome := Decidable.not_iff_not.mp <| by
  simp_rw [not_forall, exists_prop, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, exists_eq_right, ← stackToNat_lt_two_pow_pred_iff_none_mem,
    s.stackToNat_le_two_pow_sub_one.lt_iff_ne]

def finalHash' [Hash β] (n : ℕ) (list : List β) : SharedStack β :=
  list.foldl addToStack (List.replicate (n + 1) none)

end SharedStack


instance : Hash UInt64 := ⟨fun a b => hash (a, b)⟩

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).toNat⟩

#eval BTree.finalHash 1 ![234234, 12]

#eval SharedStack.finalHash' 1 ((Fin.list (2^1)).map ![234234, 12])

#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

#eval SharedStack.finalHash' 2 [234234, 12, 44, 5324]

def addToStack [Hash β] (b : β) (s : Array (Option β)) : Array (Option β) :=
  if h : 0 < s.size then
    match s.get ⟨s.size - 1, Nat.pred_lt_self h⟩ with
    | some a => (addToStack (a # b) (s.pop)).push none
    | none => s.set ⟨s.size - 1, Nat.pred_lt_self h⟩ (some b)
  else #[]

theorem addToStack_empty [Hash β] (b : β) :
    addToStack b #[] = #[] := by
  unfold addToStack
  rfl

theorem addToStack_nil_toArray [Hash β] (b : β) :
    addToStack b ⟨[]⟩ = #[] := by
  unfold addToStack
  rfl

@[simp]
theorem size_addToStack [Hash β] (b : β) (s : Array (Option β)) :
    (addToStack b s).size = s.size := by
  cases' s with s
  induction' s using List.list_reverse_induction with s a IH generalizing b
  · unfold addToStack
    rfl
  · unfold addToStack
    simp_rw [Array.size_toArray, List.length_append, List.length_singleton, lt_add_iff_pos_left,
      add_pos_iff, zero_lt_one, or_true, dite_true, add_tsub_cancel_right, Array.get_eq_getElem,
      Array.getElem_mk, List.getElem_concat_length, List.pop_toArray, List.dropLast_concat,
      List.set_toArray, List.set_append_right _ _ le_rfl, Nat.sub_self, List.set_cons_zero]
    cases a
    · simp only [Array.size_toArray, List.length_append, List.length_singleton]
    · simp only [Array.size_push, add_left_inj]
      exact IH _


#eval BTree.finalHash 2 ![0, 0, 0, 0]

def SharedStack (β : Type*) := Array (Option β)

namespace SharedStack


open Fin

variable {n : ℕ} {β : Type*}


def toFin (s : SharedStack n β) : Fin (2^n) := finArrowBoolEquivFinTwoPow <| Option.isSome ∘ s

def toBitVec (s : SharedStack n β) : BitVec n := finArrowBoolEquivBitVec <| Option.isSome ∘ s

def toNat (s : SharedStack n β) : ℕ := finArrowBoolToNat <| Option.isSome ∘ s

def isFull (s : SharedStack n β) : Bool := decide (∀ i : Fin n, Option.isSome <| s i)

def isEmpty (s : SharedStack n β) : Bool := decide (∀ i : Fin n, Option.isNone <| s i)

def hasSpace (s : SharedStack n β) : Bool := decide (∃ i : Fin n, Option.isNone <| s i)

def hasStored (s : SharedStack n β) : Bool := decide (∃ i : Fin n, Option.isSome <| s i)



end SharedStack

def reduceList [Hash β] : List (β × ℕ) → List (β × ℕ)
  | [] => []
  | [x] => [x]
  | (x₁, n) :: (x₂, m) :: xs =>
    (n == m).rec ((x₁, n) :: (x₂, m) :: xs) (reduceList ((x₂ # x₁, n + 1) :: xs))

@[simp]
theorem reduceList_empty : reduceList ([] : List (β × ℕ)) = [] := by
  unfold reduceList
  rfl

@[simp]
theorem reduceList_singleton : reduceList ([x] : List (β × ℕ)) = [x] := by
  unfold reduceList
  rfl

@[simp]
theorem reduceList_eq : reduceList (((x₁ : β), n) :: (x₂, n) :: xs) =
    reduceList ((x₂ # x₁, n + 1) :: xs) := by rw [reduceList, beq_self_eq_true]

@[simp]
theorem reduceList_ne (h : n ≠ m) : reduceList (((x₁ : β), n) :: (x₂, m) :: xs) =
    (x₁, n) :: (x₂, m) :: xs := by simp_rw [reduceList, beq_eq_decide, h, decide_False]

theorem foldl_two_pow_zero {x : α} : Fin.foldl (2^0) f x = f x 0 := by
  simp_rw [Nat.pow_zero, Fin.foldl_succ, Fin.foldl_zero]

def finalHashStacked (n : ℕ) (list : Fin (2^n) → β) :=
  Fin.foldl (2^n) (fun k i => reduceList <| (list i, 0) :: k) []

theorem finalHashStack_zero (list : Fin (2^0) → β) :
    finalHashStacked 0 list = [(list 0, 0)] := by
  unfold finalHashStacked
  simp_rw [Nat.pow_zero, Fin.foldl_succ, Fin.foldl_zero, reduceList_singleton]

theorem finalHashStack_one (list : Fin (2^1) → β) :
    finalHashStacked 1 list = [(list 0 # list 1, 1)] := by
  unfold finalHashStacked
  simp only [Nat.reducePow, Fin.foldl_succ, Fin.foldl_zero, reduceList_singleton, reduceList_eq]
  rfl

theorem finalHashStack_two (list : Fin (2^2) → β) :
    finalHashStacked 2 list = [((list 0 # list 1) # (list 2 # list 3), 2)] := by
  unfold finalHashStacked
  simp only [Nat.reducePow, Fin.isValue]
  simp only [Nat.reducePow, Fin.foldl_succ, Fin.isValue, reduceList_singleton, Fin.succ_zero_eq_one,
    reduceList_eq, zero_add, Fin.succ_one_eq_two, ne_eq, zero_ne_one, not_false_eq_true,
    reduceList_ne, Nat.reduceAdd, Fin.foldl_zero, List.cons.injEq, Prod.mk.injEq, and_true]
  rfl

theorem finalHashStack_eq_finalHash {n : ℕ} (list : Fin (2^n) → β) :
    finalHashStacked n list = [(finalHash n list, n)] := by
  induction' n with n IH
  · rw [finalHashStack_zero, finalHash_zero]
  · rw [finalHash_succ, ← reduceList_singleton, ← reduceList_eq]


#eval finalHash 3 ![0, 1, 2, 234, 4, 5, 6, 7]
#eval finalHashStacked 3 ![0, 1, 2, 234, 4, 5, 6, 7]
