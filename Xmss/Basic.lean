import Mathlib

variable {β : Type*} {n : ℕ}

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

theorem foldl_two_pow_succ {x : α} : Fin.foldl (2^(n + 1)) f x =
    Fin.foldl (2^n) (fun y i => f y (concatTwoPow (Sum.inr i)))
    (Fin.foldl (2^n) (fun y i => f y (concatTwoPow (Sum.inl i))) x) := by
  induction' n with n IH
  · simp_rw [foldl_two_pow_zero, Nat.reduceAdd, Nat.reducePow, Fin.foldl_succ, Fin.foldl_zero]
    rfl
  ·

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

instance : Hash ℕ := ⟨fun a b => (Hashable.hash (a, b)).toNat⟩

#eval finalHash 3 ![0, 1, 2, 234, 4, 5, 6, 7]
#eval finalHashStacked 3 ![0, 1, 2, 234, 4, 5, 6, 7]


end BTree
