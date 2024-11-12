import Mathlib

variable {β : Type*} {n : ℕ}

example : 2^n + 2^n = 2^(n + 1) := by exact Eq.symm (Nat.two_pow_succ n)

theorem Nat.testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

theorem Nat.testBit_ne_iff {q q' : ℕ} : q ≠ q' ↔ (∃ i : ℕ, q.testBit i ≠ q'.testBit i) := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]

theorem Bool.cond_apply {α : Type*} {σ : α → Type*} (b : Bool) (f : (a : α) → σ a)
    (g : (a : α) → σ a) (a : α) : (bif b then f else g) a = bif b then f a else g a := b.rec rfl rfl

theorem Option.none_ne_some (x : α) : none ≠ some x := (some_ne_none _).symm

theorem List.none_not_mem_iff (xs : List (Option α)) :
    none ∉ xs ↔ ∃ xs' : List α, xs'.map some = xs := by
  induction' xs with x xs IH
  · simp_rw [List.not_mem_nil, not_false_eq_true, List.map_eq_nil_iff, exists_eq]
  · cases' x with x
    · simp_rw [List.mem_cons, true_or, not_true_eq_false, false_iff, List.map_eq_cons_iff,
        not_exists, not_and, Option.some_ne_none, false_implies, implies_true]
    · simp_rw [List.mem_cons, Option.none_ne_some, false_or, IH,
        List.map_eq_cons_iff, Option.some_inj]
      exact ⟨fun ⟨l, h⟩ => ⟨_, x, l, rfl, rfl, h⟩, fun ⟨_, _, l, _, _, h⟩ => ⟨l, h⟩⟩

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

def finArrowBoolEquivBitVec : (Fin n → Bool) ≃ BitVec n := {
  toFun := fun bv => BitVec.ofNatLt (finArrowBoolToNat bv) finArrowBoolToNat_lt
  invFun := fun i k => i.toNat.testBit k
  left_inv := fun _ => by
    simp_rw [BitVec.toNat_ofNatLt, testBit_finArrowBoolToNat, is_lt, dite_true]
  right_inv :=  fun i => by
    simp_rw [BitVec.toNat_eq, BitVec.toNat_ofNatLt, finArrowBoolToNat_testBit_of_lt i.isLt]}

theorem zero_tuple (bs : Fin 0 → β) : bs = elim0 := funext finZeroElim

theorem tuple_congr (bs : Fin k → β) (h : k' = k) (f : {k : ℕ} → (Fin k → β) → α) :
    f (fun i => bs (Fin.cast h i)) = f bs := by cases h ; rfl

def tuple_foldl (f : α → β → α) (init : α) (bs : Fin k → β) :=
  foldl k (fun s i => f s (bs i)) init

@[simp]
theorem tuple_foldl_zero (f : α → β → α) (init : α) (bs : Fin 0 → β):
    tuple_foldl f init bs = init := foldl_zero _ _

@[simp]
theorem tuple_foldl_succ (f : α → β → α) (init : α) (bs : Fin (k + 1) → β) :
    tuple_foldl f init bs = tuple_foldl f (f init (bs 0)) (Fin.tail bs) := foldl_succ _ _

theorem tuple_foldl_succ_last (f : α → β → α) (init : α) (bs : Fin (k + 1) → β):
    tuple_foldl f init bs = f (tuple_foldl f init (Fin.init bs)) (bs (last k)) :=
  foldl_succ_last _ _

theorem tuple_foldl_add (f : α → β → α) (init : α) (bs : Fin (m + n) → β) :
    tuple_foldl f init bs = tuple_foldl f (tuple_foldl f init fun i => bs (castAdd n i))
    fun i => bs (natAdd m i) := by
  induction' n with n IH
  · simp_rw [castAdd_zero, cast_eq_self, tuple_foldl_zero]
  · simp_rw [tuple_foldl_succ_last, IH]
    rfl

theorem tuple_foldl_elim0 (f : α → β → α) (init : α) :
    tuple_foldl f init elim0 = init := foldl_zero _ _

theorem tuple_foldl_cons (f : α → β → α) (init : α) (b : β) (bs : Fin k → β) :
    tuple_foldl f init (cons b bs) = tuple_foldl f (f init b) bs := tuple_foldl_succ _ _ _

theorem tuple_foldl_snoc  (f : α → β → α) (init : α) (bs : Fin k → β) (b : β) :
    tuple_foldl f init (snoc bs b) = f (tuple_foldl f init bs) b := by
  simp_rw [tuple_foldl_succ_last, init_snoc, snoc_last]

theorem tuple_foldl_append (bs₁ : Fin m → β) (bs₂ : Fin n → β) (f : α → β → α)
    (init : α) : tuple_foldl f (tuple_foldl f init bs₁) bs₂ =
      tuple_foldl f init (append bs₁ bs₂) := by
  simp_rw [tuple_foldl_add, append_left, append_right]

@[simp]
theorem tuple_foldl_cast (bs : Fin k → β) (h : k' = k) (f : α → β → α) (init : α) :
    tuple_foldl f init (fun i => bs <| Fin.cast h i) = tuple_foldl f init bs :=
  tuple_congr bs h (tuple_foldl f init ·)

def tuple_foldr (f : β → α → α) (init : α) (bs : Fin k → β) :=
  foldr k (fun i s => f (bs i) s) init

@[simp]
theorem tuple_foldr_elim0 (f : β → α → α) (init : α) :
    tuple_foldr f init elim0 = init := foldr_zero _ _

@[simp]
theorem tuple_foldr_cons (bs : Fin k → β) (b : β) (f : β → α → α) (init : α) :
    tuple_foldr f init (cons b bs) = f b (tuple_foldr f init bs) := foldr_succ _ _

@[simp]
theorem tuple_foldr_snoc (b : β) (bs : Fin k → β) (f : β → α → α) (init : α) :
    tuple_foldr f init (snoc bs b) = tuple_foldr f (f b init) bs := by
  simp_rw [tuple_foldr, foldr_succ_last, snoc_castSucc, snoc_last]

theorem tuple_foldr_zero (f : β → α → α) (init : α) (bs : Fin 0 → β) :
    tuple_foldr f init bs = init := by simp_rw [zero_tuple, tuple_foldr_elim0]

theorem tuple_foldr_of_eq_zero {f : β → α → α} {init : α} {bs : Fin k → β}
    (h : k = 0) : tuple_foldr f init bs = init := by
  cases k
  · rw [tuple_foldr_zero]
  · simp_rw [Nat.succ_ne_zero] at h

theorem tuple_foldr_append (bs₁ : Fin m → β) (bs₂ : Fin n → β) (f : β → α → α)
    (init : α) : tuple_foldr f init (Fin.append bs₁ bs₂) =
    tuple_foldr f (tuple_foldr f init bs₂) bs₁ := by
  induction' bs₂ using Fin.snocInduction with n b bs₂ IH generalizing init
  · simp_rw [tuple_foldr_elim0, append_elim0, cast_refl, Function.comp_id]
  · simp_rw [append_snoc, tuple_foldr_snoc, IH]

@[simp]
theorem tuple_foldr_cast (bs : Fin k → β) (h : k' = k) (f : β → α → α) (init : α) :
    tuple_foldr f init (fun i => bs <| Fin.cast h i) = tuple_foldr f init bs :=
  tuple_congr bs h (tuple_foldr f init ·)

theorem tuple_foldr_rev (bs : Fin k → β) (f : β → α → α) (init : α) :
    tuple_foldr f init (fun i => bs (i.rev)) = tuple_foldl (flip f) init bs := by
  induction' bs using Fin.snocInduction with n b bs IH
  · simp_rw [tuple_foldl_elim0]
    exact tuple_foldr_elim0 _ _
  · simp_rw [tuple_foldl_snoc, Fin.snoc_rev, tuple_foldr_cons,
      Function.comp_def, IH, Function.flip_def]

theorem tuple_foldl_rev (bs : Fin k → β) (f : α → β → α) (init : α) :
    tuple_foldl f init (fun i => bs (i.rev)) = tuple_foldr (flip f) init bs := by
  induction' bs using Fin.snocInduction with n b bs IH generalizing init
  · simp_rw [tuple_foldr_elim0]
    exact tuple_foldl_elim0 _ _
  · simp_rw [tuple_foldr_snoc, Fin.snoc_rev, tuple_foldl_cons,
      Function.comp_def, ← IH, Function.flip_def]

end Fin

def concatTwoPow : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) where
  toFun i := i.elim
    (fun (i : Fin (2^n)) => ⟨i, i.isLt.trans <| Nat.pow_lt_pow_succ one_lt_two⟩)
    (fun (i : Fin (2^n)) => ⟨2^n + i, Nat.two_pow_succ _ ▸ (Nat.add_lt_add_left i.isLt _)⟩)
  invFun i := if h : (i : ℕ) < 2^n then Sum.inl ⟨i, h⟩ else
    Sum.inr ⟨i - 2^n, Nat.sub_lt_right_of_lt_add (le_of_not_lt h) (Nat.two_pow_succ _ ▸ i.isLt)⟩
  left_inv i := i.rec
    (fun i => by simp_rw [Sum.elim_inl, Fin.is_lt, dite_true])
    (fun i => by simp_rw [Sum.elim_inr, add_lt_iff_neg_left, not_lt_zero', dite_false,
      add_tsub_cancel_left])
  right_inv i := ((i : ℕ).lt_or_ge (2^n)).elim
    (fun h => by simp_rw [h, dite_true, Sum.elim_inl])
    (fun h => by simp_rw [h.not_lt, dite_false, Sum.elim_inr, Nat.add_sub_cancel' h])

@[simp]
theorem concatTwoPow_inl_apply_val {i : Fin (2^n)} : (concatTwoPow (Sum.inl i)).val = i := rfl

@[simp]
theorem concatTwoPow_inr_apply_val {i : Fin (2^n)} : (concatTwoPow (Sum.inr i)).val = 2^n + i := rfl

theorem concatTwoPow_symm_apply_of_lt (i : Fin (2^(n + 1))) (h : (i : ℕ) < 2^n) :
    concatTwoPow.symm i = Sum.inl ⟨i, h⟩ := by
  simp_rw [Equiv.symm_apply_eq, Fin.ext_iff, concatTwoPow_inl_apply_val]

theorem concatTwoPow_symm_apply_of_ge (i : Fin (2^(n + 1))) (h : 2^n ≤ (i : ℕ)) :
    concatTwoPow.symm i = Sum.inr ⟨i - 2^n,
    Nat.sub_lt_right_of_lt_add h (Nat.two_pow_succ _ ▸ i.isLt)⟩ := by
  simp_rw [Equiv.symm_apply_eq, Fin.ext_iff, concatTwoPow_inr_apply_val, Nat.add_sub_cancel' h]

def interleveTwoPow : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) where
  toFun i := ⟨Nat.bit i.isRight (i.elim Fin.val Fin.val),
    Nat.bit_lt_two_pow_succ_iff.mpr <| i.rec (fun _ => Fin.is_lt _) (fun _ => Fin.is_lt _)⟩
  invFun i :=
    let (j : Fin (2^n)) := ⟨(i : ℕ) >>> 1,
      Nat.shiftRight_one _ ▸ Nat.div_lt_of_lt_mul (Nat.pow_succ' ▸ i.isLt)⟩
    (Nat.testBit i 0).rec (Sum.inl j) (Sum.inr j)
  left_inv i := i.rec
    (fun i => by simp_rw [Sum.isRight_inl, Sum.elim_inl,
      Nat.bit_shiftRight_one, Nat.testBit_bit_zero])
    (fun i => by simp_rw [Sum.isRight_inr, Sum.elim_inr,
      Nat.bit_shiftRight_one, Nat.testBit_bit_zero])
  right_inv i := by
    cases h : Nat.testBit i 0
    · simp_rw [h, Sum.isRight_inl, Sum.elim_inl, ← h, Nat.bit_testBit_zero_shiftRight_one]
    · simp_rw [h, Sum.isRight_inr, Sum.elim_inr, ← h, Nat.bit_testBit_zero_shiftRight_one]

@[simp]
theorem interleveTwoPow_inl_apply_val {i : Fin (2^n)} :
    (interleveTwoPow (Sum.inl i)).val = 2*i := rfl

@[simp]
theorem interleveTwoPow_inr_apply_val {i : Fin (2^n)} :
    (interleveTwoPow (Sum.inr i)).val = 2*i + 1 := rfl

theorem interleveTwoPow_symm_apply_of_mod_two_eq_zero (i : Fin (2^(n + 1))) (h : (i : ℕ) % 2 = 0) :
    interleveTwoPow.symm i = Sum.inl ⟨(i : ℕ) >>> 1,
      Nat.shiftRight_one _ ▸ Nat.div_lt_of_lt_mul (Nat.pow_succ' ▸ i.isLt)⟩ := by
  simp_rw [Equiv.symm_apply_eq, Fin.ext_iff, interleveTwoPow_inl_apply_val, Nat.shiftRight_one,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)]

theorem interleveTwoPow_symm_apply_of_mod_two_eq_one (i : Fin (2^(n + 1))) (h : (i : ℕ) % 2 = 1) :
    interleveTwoPow.symm i = Sum.inr ⟨(i : ℕ) >>> 1,
      Nat.shiftRight_one _ ▸ Nat.div_lt_of_lt_mul (Nat.pow_succ' ▸ i.isLt)⟩ := by
  simp_rw [Equiv.symm_apply_eq, Fin.ext_iff, interleveTwoPow_inr_apply_val, Nat.shiftRight_one]
  exact (h ▸ Nat.div_add_mod _ _).symm

theorem concatTwoPow_inl_interleveTwoPow_inl :
    concatTwoPow (Sum.inl (interleveTwoPow (Sum.inl i))) =
    interleveTwoPow (Sum.inl (concatTwoPow (Sum.inl i))) := rfl

theorem concatTwoPow_inl_interleveTwoPow_inr :
    concatTwoPow (Sum.inl (interleveTwoPow (Sum.inr i))) =
    interleveTwoPow (Sum.inr (concatTwoPow (Sum.inl i))) := rfl

theorem concatTwoPow_inr_interleveTwoPow_inr :
    concatTwoPow (Sum.inr (interleveTwoPow (Sum.inr i))) =
    interleveTwoPow (Sum.inr (concatTwoPow (Sum.inr i))) := by
  simp only [Fin.ext_iff, concatTwoPow_inr_apply_val, interleveTwoPow_inr_apply_val,
    mul_add, pow_succ', add_assoc]

theorem concatTwoPow_inr_interleveTwoPow_inl :
    concatTwoPow (Sum.inr (interleveTwoPow (Sum.inl i))) =
    interleveTwoPow (Sum.inl (concatTwoPow (Sum.inr i))) := by
  simp only [Fin.ext_iff, concatTwoPow_inr_apply_val, interleveTwoPow_inl_apply_val,
    mul_add, pow_succ']

@[simps!]
def twoPowSuccTupleDivide : (Fin (2 ^ (n + 1)) → β) ≃ (Fin (2 ^ n) → β) × (Fin (2 ^ n) → β) where
  toFun t := ⟨fun i => t (concatTwoPow (Sum.inl i)), fun i => t (concatTwoPow (Sum.inr i))⟩
  invFun t i := (concatTwoPow.symm i).elim t.1 t.2
  left_inv t := funext fun x => by
    rcases h : concatTwoPow.symm x
    · simp_rw [h, Sum.elim_inl, ← h, Equiv.apply_symm_apply]
    · simp_rw [h, Sum.elim_inr, ← h, Equiv.apply_symm_apply]
  right_inv t := by
    simp_rw [Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]

theorem twoPowSuccTupleDivide_eq_arrowCongr_trans_appendEquiv :
    twoPowSuccTupleDivide = ((finCongr (Nat.two_pow_succ n)).arrowCongr
    (Equiv.refl β)).trans (Fin.appendEquiv _ _).symm := Equiv.ext <| fun _ => rfl

theorem twoPowSuccTupleDivide_fst (bs : Fin (2 ^ (n + 1)) → β) :
    (twoPowSuccTupleDivide bs).1 =
    fun i => (bs ∘ Fin.cast (Nat.two_pow_succ _).symm) (Fin.castAdd (2^n) i) := rfl

theorem twoPowSuccTupleDivide_snd (bs : Fin (2 ^ (n + 1)) → β) :
    (twoPowSuccTupleDivide bs).2 =
    fun i => (bs ∘ Fin.cast (Nat.two_pow_succ _).symm) (Fin.natAdd (2^n) i) := rfl

theorem twoPowSuccTupleDivide_fst_zero (bs : Fin (2 ^ (n + 1)) → β) :
  (twoPowSuccTupleDivide bs).1 0 = bs 0 := rfl

theorem twoPowSuccTuple_eq_append (bs : Fin (2 ^ (n + 1)) → β) :
    bs = fun i => Fin.append (twoPowSuccTupleDivide bs).1 (twoPowSuccTupleDivide bs).2
    (Fin.cast (Nat.two_pow_succ _) i) := by
  simp_rw [twoPowSuccTupleDivide_fst, twoPowSuccTupleDivide_snd, Fin.append_castAdd_natAdd,
    Function.comp_def, Fin.cast_trans, Fin.cast_eq_self]

theorem append_eq_twoPowSuccTuple_symm (bs₁ : Fin (2 ^ n) → β) (bs₂ : Fin (2 ^ n) → β) :
    Fin.append bs₁ bs₂ = fun i => twoPowSuccTupleDivide.symm (bs₁, bs₂)
    (Fin.cast (Nat.two_pow_succ _).symm i) := by
  simp_rw [twoPowSuccTupleDivide_eq_arrowCongr_trans_appendEquiv]
  rfl

theorem Fin.tuple_foldl_two_pow_succ (bs : Fin (2 ^ (n + 1)) → β) (f : α → β → α)
    (init : α) : tuple_foldl f init bs = tuple_foldl f
    (tuple_foldl f init (twoPowSuccTupleDivide bs).1) (twoPowSuccTupleDivide bs).2 := by
  simp_rw [tuple_foldl_append, append_eq_twoPowSuccTuple_symm,
    Prod.mk.eta, Equiv.symm_apply_apply, tuple_foldl_cast]

class Hash (β : Type u) where
  hash : β → β → β

infixl:65 " # " => Hash.hash

inductive BTree (β : Type*) where
  | leaf : β → BTree β
  | node : β → BTree β → BTree β → BTree β

namespace BTree

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

def finalHash' (n : ℕ) (bs : Fin (2^n) → β) : β := root (listOfTree bs)

def finalHash : (n : ℕ) → (Fin (2^n) → β) → β
  | 0, t => t 0
  | (n + 1), t =>
    let (f, l) := twoPowSuccTupleDivide t
    (finalHash n f) # (finalHash n l)

theorem finalHash_zero (bs : Fin (2^0) → β) :
  finalHash 0 bs = bs 0 := rfl

theorem finalHash_succ (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHash (n + 1) bs =
  (finalHash n (twoPowSuccTupleDivide bs).1) #
  (finalHash n (twoPowSuccTupleDivide bs).2) := rfl

theorem finalHash_succ_eq_finalHash (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
    finalHash (n + 1) bs = finalHash n (fun i =>
    bs (interleveTwoPow (Sum.inl i)) # bs (interleveTwoPow (Sum.inr i))) := by
  induction' n with n IH
  · exact rfl
  · rw [finalHash_succ (n + 1), IH, IH, finalHash_succ n]
    congr
    simp_rw [twoPowSuccTupleDivide_apply, concatTwoPow_inr_interleveTwoPow_inl,
      concatTwoPow_inr_interleveTwoPow_inr]

end BTree

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).toNat⟩

inductive PSharedStack (β : Type u) : Type u
  | sngl : β → PSharedStack β
  | bit0 : PSharedStack β → PSharedStack β
  | bit1 : β → PSharedStack β → PSharedStack β
deriving DecidableEq

namespace PSharedStack

variable {β : Type*} {a b : β} {p : PSharedStack β}

instance [Inhabited β] : Inhabited (PSharedStack β) where
  default := sngl default

def lg2 : PSharedStack β → ℕ
  | sngl _ => 0
  | bit0 p => p.lg2.succ
  | bit1 _ p => p.lg2.succ

section Lg2

@[simp] theorem lg2_sngl : (sngl a).lg2 = 0 := rfl
@[simp] theorem lg2_bit0 : (bit0 p).lg2 = p.lg2 + 1 := rfl
@[simp] theorem lg2_bit1 : (bit1 a p).lg2 = p.lg2 + 1 := rfl

theorem lg2_bit0_ne_zero : (bit0 p).lg2 ≠ 0 := Nat.succ_ne_zero _

theorem lg2_bit1_ne_zero : (bit1 a p).lg2 ≠ 0 := Nat.succ_ne_zero _

end Lg2

def size (p : PSharedStack β) : ℕ := p.lg2 + 1

section Size

@[simp] theorem size_sngl : (sngl a).size = 1 := rfl
@[simp] theorem size_bit0 : (bit0 p).size = p.size + 1 := rfl
@[simp] theorem size_bit1 : (bit1 a p).size = p.size + 1 := rfl

@[simp] theorem size_ne_zero : p.size ≠ 0 := Nat.succ_ne_zero _

@[simp] theorem size_pos : 0 < p.size := Nat.pos_of_ne_zero size_ne_zero

@[simp] theorem one_le_size : 1 ≤ p.size := size_pos

theorem size_eq_lg2_succ : p.size = p.lg2 + 1 := rfl

end Size

def count : PSharedStack β → ℕ
  | sngl _ => 1
  | bit0 p => Nat.bit false p.count
  | bit1 _ p => Nat.bit true p.count

section Count

@[simp] theorem count_sngl : (sngl a).count = 1 := rfl
@[simp] theorem count_bit0 : (bit0 p).count = 2 * p.count := rfl
@[simp] theorem count_bit1 : (bit1 a p).count = 2 * p.count + 1 := rfl

@[simp] theorem count_ne_zero : p.count ≠ 0 :=
  p.recOn (fun _ => Nat.noConfusion) (fun _ => Nat.bit_ne_zero _) (fun _ _ => Nat.bit_ne_zero _)

@[simp] theorem count_pos : 0 < p.count := Nat.pos_of_ne_zero count_ne_zero

@[simp] theorem one_le_count : 1 ≤ p.count := count_pos

theorem count_bit0_ne_one : (bit0 p).count ≠ 1 := by
  simp_rw [count_bit0, mul_ne_one]
  exact Or.inl (Nat.succ_succ_ne_one 0)

theorem count_bit1_ne_one : (bit1 a p).count ≠ 1 := by
  simp_rw [count_bit1, Nat.succ_ne_succ, mul_ne_zero_iff]
  exact ⟨two_ne_zero, count_ne_zero⟩

theorem count_lt_two_pow_size : p.count < 2^p.size := by
  rw [size_eq_lg2_succ]
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [count_sngl, lg2_sngl, pow_one]
    exact one_lt_two
  · rw [pow_succ']
    exact Nat.bit_lt_bit _ false IH
  · rw [pow_succ']
    exact Nat.bit_lt_bit _ false IH

theorem two_pow_lg2_le_count : 2^p.lg2 ≤ p.count := by
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [lg2_sngl, pow_zero, count_sngl]
  · simp_rw [lg2_bit0, count_bit0, pow_succ']
    exact Nat.bit_le false IH
  · simp_rw [lg2_bit1, count_bit1, pow_succ']
    exact (Nat.bit_le false IH).trans (Nat.le_succ _)

@[simp] theorem size_count_eq_size : p.count.size = p.size := by
  refine le_antisymm ((Nat.size_le).mpr count_lt_two_pow_size) ?_
  rw [size_eq_lg2_succ, Nat.succ_le_iff, Nat.lt_size]
  exact two_pow_lg2_le_count

@[simp] theorem log_two_count_eq_lg2 : Nat.log 2 p.count = p.lg2 := by
  exact Nat.log_eq_of_pow_le_of_lt_pow two_pow_lg2_le_count
    (size_eq_lg2_succ ▸ count_lt_two_pow_size)

@[simp] theorem log2_count_eq_lg2 : p.count.log2 = p.lg2 := by
  rw [Nat.log2_eq_log_two, log_two_count_eq_lg2]

end Count

-- sizeCap = "we can push this many without increasing the size"

def sizeCap : PSharedStack β → ℕ
  | sngl _ => 0
  | bit0 p => Nat.bit true p.sizeCap
  | bit1 _ p => Nat.bit false p.sizeCap

section SizeCap

@[simp] theorem sizeCap_sngl : (sngl a).sizeCap = 0 := rfl
@[simp] theorem sizeCap_bit0 : (bit0 p).sizeCap = 2 * p.sizeCap + 1 := rfl
@[simp] theorem sizeCap_bit1 : (bit1 a p).sizeCap = 2 * p.sizeCap := rfl

theorem sizeCap_bit0_ne_zero : (bit0 p).sizeCap ≠ 0 := Nat.succ_ne_zero _

theorem sizeCap_lt_pred_two_pow_size : p.sizeCap ≤ 2^p.lg2 - 1 := by
  rw [le_tsub_iff_right Nat.one_le_two_pow]
  induction p with | sngl => exact le_rfl | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [sizeCap_bit0, lg2_bit0, pow_succ', add_assoc, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ IH
  · rw [sizeCap_bit1, lg2_bit1, pow_succ']
    refine (Nat.le_succ _).trans ?_
    simp_rw [Nat.succ_eq_add_one, add_assoc, one_add_one_eq_two, ← Nat.mul_succ]
    exact Nat.bit_le false IH

theorem count_add_sizeCap_eq_pred_two_pow_size : p.count + p.sizeCap = 2^p.size - 1 := by
  rw [size_eq_lg2_succ, eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow, add_comm (p.count)]
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · simp_rw [sizeCap_sngl, count_sngl, lg2_sngl]
  · simp_rw [sizeCap_bit0, count_bit0, pow_succ', lg2_bit0, add_assoc _ _ 1,
      Nat.add_add_add_comm _ 1, ← Nat.mul_add, ← Nat.mul_add_one, IH]
  · simp_rw [sizeCap_bit1, count_bit1, pow_succ', lg2_bit1, add_assoc,
      one_add_one_eq_two, ← add_assoc, ← Nat.mul_add, ← Nat.mul_add_one, IH]

end SizeCap

-- "if we push this many, we will increase the size"

def sizeInc : PSharedStack β → ℕ := fun p => p.sizeCap + 1

section SizeInc

@[simp] theorem sizeInc_sngl : (sngl a).sizeInc = 1 := rfl
@[simp] theorem sizeInc_bit0 : (bit0 p).sizeInc = 2 * p.sizeInc := rfl
@[simp] theorem sizeInc_bit1 : (bit1 a p).sizeInc = 2 * p.sizeInc - 1 := rfl

theorem sizeInc_ne_zero : p.sizeInc ≠ 0 := Nat.succ_ne_zero _

theorem one_le_sizeInc : 1 ≤ p.sizeInc := Nat.one_le_iff_ne_zero.mpr sizeInc_ne_zero

theorem sizeInc_eq_sizeCap_succ : p.sizeInc = p.sizeCap + 1 := rfl

theorem sizeInc_lt_two_pow_size : p.sizeInc ≤ 2^p.lg2 := by
  rw [sizeInc_eq_sizeCap_succ]
  exact Nat.add_le_of_le_sub Nat.one_le_two_pow sizeCap_lt_pred_two_pow_size

theorem count_add_sizeInc_eq_two_pow_size : p.count + p.sizeInc = 2^p.size := by
  rw [sizeInc_eq_sizeCap_succ, ← Nat.add_assoc,
    count_add_sizeCap_eq_pred_two_pow_size, Nat.sub_add_cancel Nat.one_le_two_pow]

theorem count_add_sizeInc_eq_two_pow_lg2_add_two_pow_lg2 :
    p.count + p.sizeInc = 2^p.lg2 + 2^p.lg2 := by
  rw [← two_mul, ← pow_succ', ← size_eq_lg2_succ]
  exact count_add_sizeInc_eq_two_pow_size

end SizeInc

/-
def ffs : PSharedStack β → ℕ
  | sngl _ => 0
  | bit0 p => p.ffs.succ
  | bit1 _ _ => 0


section Ffs

@[simp] theorem ffs_sngl : (sngl a).ffs = 0 := rfl
@[simp] theorem ffs_bit0 : (bit0 p).ffs = p.ffs + 1 := rfl
@[simp] theorem ffs_bit1 : (bit1 a p).ffs = 0 := rfl

theorem ffs_bit0_ne_zero : (bit0 p).ffs ≠ 0 := Nat.succ_ne_zero _

theorem two_pow_ffs_lt_count : 2^p.ffs ≤ p.count := by
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · simp_rw [ffs_sngl, pow_zero, count_sngl, le_refl]
  · simp_rw [ffs_bit0, count_bit0, pow_succ']
    exact Nat.mul_le_mul_left _ IH
  · simp_rw [ffs_bit1, pow_zero, count_bit1]
    exact Nat.succ_le_succ <| zero_le _

theorem ffs_lt_size : p.ffs < p.size :=
  (Nat.pow_lt_pow_iff_right (one_lt_two)).mp
  (two_pow_ffs_lt_count.trans_lt count_lt_two_pow_size)

theorem ffs_le_lg2 : p.ffs ≤ p.lg2 := by
  rw [← Nat.lt_succ_iff]
  exact ffs_lt_size.trans_eq size_eq_lg2_succ

theorem two_pow_ffs_le_sizeCap : 2^p.ffs - 1 ≤ p.sizeCap := by
  rw [Nat.sub_le_iff_le_add]
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · simp_rw [ffs_sngl, pow_zero, sizeCap_sngl, zero_add, le_refl]
  · simp_rw [ffs_bit0, sizeCap_bit0, pow_succ', add_assoc, one_add_one_eq_two,
      ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ IH
  · simp_rw [ffs_bit1, pow_zero]
    exact Nat.succ_le_succ <| zero_le _

theorem two_pow_ffs_le_sizeInc : 2^p.ffs ≤ p.sizeInc := by
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · simp_rw [ffs_sngl, pow_zero, sizeInc_sngl, le_refl]
  · simp_rw [ffs_bit0, sizeInc_bit0, pow_succ']
    exact Nat.mul_le_mul_left _ IH
  · simp_rw [ffs_bit1, pow_zero]
    exact Nat.succ_le_succ <| zero_le _

theorem pred_two_pow_ffs_le_sizeInc : 2^p.ffs - 1 ≤ p.sizeCap := by
  rw [Nat.sub_le_iff_le_add]
  exact two_pow_ffs_le_sizeInc

end Ffs
-/

def toList : PSharedStack β → List (Option β)
  | sngl a => [some a]
  | bit0 p => none :: p.toList
  | bit1 a p => some a :: p.toList

section ToList

@[simp] theorem toList_sngl : (sngl a).toList = [some a] := rfl
@[simp] theorem toList_bit0 : (bit0 p).toList = none :: p.toList := rfl
@[simp] theorem toList_bit1 : (bit1 a p).toList = some a :: p.toList := rfl

@[simp] theorem toList_ne_nil : p.toList ≠ [] := by
  cases p <;> exact List.noConfusion

@[simp]
theorem length_toList : (toList p).length = p.size :=
  p.recOn (fun _ => rfl) (fun _ => congrArg _) (fun _ _ => congrArg _)

instance [Repr β] : Repr (PSharedStack β) where
  reprPrec := fun p => reprPrec (p.toList)

end ToList


def testBit : PSharedStack β → ℕ → Bool
  | sngl _, 0 => true
  | sngl _, (_ + 1) => false
  | bit0 _, 0 => false
  | bit0 p, (n + 1) => p.testBit n
  | bit1 _ _, 0 => true
  | bit1 _ p, (n + 1) => p.testBit n

section TestBit

@[simp] theorem testBit_sngl_zero : (sngl a).testBit 0 = true := rfl
@[simp] theorem testBit_sngl_succ : (sngl a).testBit (n + 1) = false := rfl

@[simp] theorem testBit_sngl : (sngl a).testBit n = decide (n = 0) :=
  n.casesOn rfl (fun _ => rfl)

@[simp] theorem testBit_bit0_zero : (bit0 p).testBit 0 = false := rfl
@[simp] theorem testBit_bit0_succ : (bit0 p).testBit (n + 1) = p.testBit n := rfl

@[simp] theorem testBit_bit0 : (bit0 p).testBit n = (!decide (n = 0) && p.testBit (n - 1)) :=
  n.casesOn rfl (fun _ => rfl)

@[simp] theorem testBit_bit1_zero : (bit1 a p).testBit 0 = true := rfl
@[simp] theorem testBit_bit1_succ : (bit1 a p).testBit (n + 1) = p.testBit n := rfl

@[simp] theorem testBit_bit1 : (bit1 a p).testBit n = (decide (n = 0) || p.testBit (n - 1)) :=
  n.casesOn rfl (fun _ => rfl)

theorem testBit_of_lg2_gt : p.lg2 < n → p.testBit n = false := by
  induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _
  · simp_rw [lg2_sngl, testBit_sngl, decide_eq_false_iff_not]
    exact ne_of_gt
  · simp_rw [lg2_bit0, testBit_bit0, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    exact fun h _ => IH (Nat.lt_pred_of_succ_lt h)
  · simp_rw [lg2_bit1, testBit_bit1, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact fun h => ⟨Nat.not_eq_zero_of_lt h, IH (Nat.lt_pred_of_succ_lt h)⟩

theorem testBit_of_size_ge : p.size ≤ n → p.testBit n = false := by
  rw [size_eq_lg2_succ, Nat.succ_le_iff]
  exact testBit_of_lg2_gt

theorem testBit_lg2 : p.testBit p.lg2 = true := p.recOn
  (fun _ => rfl)
  (fun _ => by simp_rw [lg2_bit0, testBit_bit0_succ, imp_self])
  (fun _ _ => by simp_rw [lg2_bit1, testBit_bit1_succ, imp_self])

@[simp]
theorem testBit_count : p.count.testBit n = p.testBit n := by
  induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _ <;>
  [rw [count_sngl]; rw [count_bit0]; rw [count_bit1]] <;> cases n
  · simp_rw [testBit_sngl_zero, Nat.testBit_one_zero]
  · simp_rw [testBit_sngl_succ, Nat.testBit_succ, Nat.div_eq_of_lt (one_lt_two), Nat.zero_testBit]
  · simp_rw [testBit_bit0_zero, Nat.testBit_zero, Nat.mul_mod_right, zero_ne_one, decide_False]
  · simp_rw [testBit_bit0_succ, Nat.testBit_succ, Nat.mul_div_cancel_left _ zero_lt_two, IH]
  · simp_rw [testBit_bit1_zero, Nat.testBit_zero, Nat.mul_add_mod, decide_True]
  · simp_rw [testBit_bit1_succ, Nat.testBit_succ, Nat.mul_add_div zero_lt_two,
      Nat.div_eq_of_lt one_lt_two, add_zero, IH]

end TestBit

inductive isRoot : PSharedStack β → Prop
  | protected sngl : (a : β) → isRoot (sngl a)
  | protected bit0 : {p : PSharedStack β} → p.isRoot → isRoot (bit0 p)

section IsRoot

@[simp] theorem isRoot_sngl : (sngl a).isRoot := by constructor

@[simp] theorem not_isRoot_bit1 : ¬ (bit1 a p).isRoot := fun h => by contradiction

@[simp] theorem isRoot_bit0_iff : (bit0 p).isRoot ↔ p.isRoot :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem isRoot_iff_count_eq_two_pow_lg2 : p.isRoot ↔ p.count = 2^p.lg2 := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isRoot_sngl, count_sngl, lg2_sngl, pow_zero]
  · simp_rw [isRoot_bit0_iff, IH, count_bit0, lg2_bit0, pow_succ', mul_eq_mul_left_iff,
      zero_lt_two.ne', or_false]
  · simp_rw [not_isRoot_bit1, count_bit1, lg2_bit1, false_iff, pow_succ']
    exact (Nat.two_mul_ne_two_mul_add_one).symm

theorem isRoot_iff_exists_size_eq_two_pow : p.isRoot ↔ ∃ k, p.count = 2^k := by
  rw [isRoot_iff_count_eq_two_pow_lg2]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨k, hk⟩ => ?_⟩
  have H := hk ▸ p.log_two_count_eq_lg2
  rw [Nat.log_pow one_lt_two] at H
  exact H ▸ hk

theorem isRoot_iff_sizeInc_eq_two_pow_lg2 : p.isRoot ↔ p.sizeInc = 2^p.lg2 := by
  rw [isRoot_iff_count_eq_two_pow_lg2]
  have H := p.count_add_sizeInc_eq_two_pow_lg2_add_two_pow_lg2
  exact ⟨fun h => add_right_injective _ (h ▸ H), fun h => add_left_injective _ (h ▸ H)⟩

theorem isRoot_iff_sizeCap_eq_two_pow_lg2 : p.isRoot ↔ p.sizeCap = 2^p.lg2 - 1 := by
  rw [isRoot_iff_sizeInc_eq_two_pow_lg2, sizeInc_eq_sizeCap_succ,
    eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow]

instance : Decidable (p.isRoot) :=
  decidable_of_iff _ isRoot_iff_count_eq_two_pow_lg2.symm

theorem isRoot_iff_toList_eq_replicate_lg2_append_singleton :
    p.isRoot ↔ p.toList = List.replicate p.lg2 none ++ [some p.pop] := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isRoot_sngl, toList_sngl, lg2_sngl, List.replicate_zero, pop_sngl, List.nil_append]
  · simp_rw [isRoot_bit0_iff, IH, toList_bit0, lg2_bit0, List.replicate_succ, pop_bit0,
    List.cons_append, List.cons_inj_right]
  · simp_rw [not_isRoot_bit1, toList_bit1, lg2_bit1, List.replicate_succ, pop_bit1,
      List.cons_append, List.cons_eq_cons, Option.some_ne_none, false_and]

theorem isRoot_iff_toList_eq_replicate_size_pred_append_singleton :
    p.isRoot ↔ p.toList = List.replicate (p.size - 1) none ++ [some p.pop] := by
 rw [size_eq_lg2_succ, Nat.add_sub_cancel, isRoot_iff_toList_eq_replicate_lg2_append_singleton]

end IsRoot

inductive isMaxed : PSharedStack β → Prop
  | protected sngl : (a : β) → isMaxed (sngl a)
  | protected bit1 : (a : β) → {p : PSharedStack β} → p.isMaxed → isMaxed (bit1 a p)

section IsMaxed

@[simp] theorem isMaxed_sngl : (sngl a).isMaxed := by constructor

@[simp] theorem not_isMaxed_bit0 : ¬ (bit0 p).isMaxed:= fun h => by contradiction

@[simp] theorem isMaxed_bit1_iff : (bit1 a p).isMaxed ↔ p.isMaxed :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem isMaxed_iff_count_eq_pred_two_pow_size :
    p.isMaxed ↔ p.count = 2^p.size - 1 := by
  rw [eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow]
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isMaxed_sngl, count_sngl, size_sngl]
  · simp_rw [not_isMaxed_bit0, count_bit0, false_iff, size_eq_lg2_succ, pow_succ']
    exact (Nat.two_mul_ne_two_mul_add_one).symm
  · simp_rw [isMaxed_bit1_iff, IH, count_bit1, size_bit1, pow_succ', add_assoc,
      ← Nat.mul_succ, mul_eq_mul_left_iff, zero_lt_two.ne', or_false]

instance : Decidable (p.isMaxed) :=
  decidable_of_iff _ isMaxed_iff_count_eq_pred_two_pow_size.symm

theorem isMaxed_iff_sizeCap_eq_zero : p.isMaxed ↔ p.sizeCap = 0 := by
  have H := p.count_add_sizeCap_eq_pred_two_pow_size
  rw [isMaxed_iff_count_eq_pred_two_pow_size]
  exact ⟨fun h => Nat.add_eq_left.mp (h ▸ H), fun h => add_zero p.count ▸ (h ▸ H)⟩

theorem isMaxed_iff_sizeInc_eq_one : p.isMaxed ↔ p.sizeInc = 1 := by
  rw [isMaxed_iff_sizeCap_eq_zero, sizeInc_eq_sizeCap_succ, add_left_eq_self]

end IsMaxed

def isSingle (p : PSharedStack β) : Prop := p.isMaxed ∧ p.isRoot

section IsSingle

@[simp] theorem isSingle_sngl : (sngl a).isSingle := ⟨isMaxed_sngl, isRoot_sngl⟩

@[simp] theorem not_isSingle_bit0 : ¬ (bit0 p).isSingle := fun h => (not_isMaxed_bit0 h.1).elim

@[simp] theorem not_isSingle_bit1 : ¬ (bit1 a p).isSingle := fun h => (not_isRoot_bit1 h.2).elim

theorem isSingle_iff_count_eq_one : p.isSingle ↔ p.count = 1 := by
  cases p
  · exact iff_of_true isSingle_sngl count_sngl
  · exact iff_of_false not_isSingle_bit0 count_bit0_ne_one
  · exact iff_of_false not_isSingle_bit1 count_bit1_ne_one

theorem isSingle_iff_lg2_eq_zero : p.isSingle ↔ p.lg2 = 0 := by
  cases p
  · exact iff_of_true isSingle_sngl lg2_sngl
  · exact iff_of_false not_isSingle_bit0 lg2_bit0_ne_zero
  · exact iff_of_false not_isSingle_bit1 lg2_bit1_ne_zero

theorem isSingle_iff_size_eq_one : p.isSingle ↔ p.size = 1 := by
  rw [isSingle_iff_lg2_eq_zero, size_eq_lg2_succ, add_left_eq_self]

theorem isSingle_iff_exists_sngl : p.isSingle ↔ ∃ a, p = sngl a := by
  cases p
  · exact iff_of_true isSingle_sngl ⟨_, rfl⟩
  · exact iff_of_false not_isSingle_bit0 (fun ⟨_, h⟩ => by contradiction)
  · exact iff_of_false not_isSingle_bit1 (fun ⟨_, h⟩ => by contradiction)

theorem isMaxed_and_isRoot_iff_isSingle : (p.isMaxed ∧ p.isRoot) ↔ p.isSingle := Iff.rfl

instance : Decidable (p.isSingle) := decidable_of_iff _ isMaxed_and_isRoot_iff_isSingle

end IsSingle

def last : PSharedStack β → β
  | sngl a => a
  | bit0 p => p.last
  | bit1 _ p => p.last

section Last

@[simp] theorem last_sngl : (sngl a).last = a := rfl
@[simp] theorem last_bit0 : (bit0 p).last = p.last := rfl
@[simp] theorem last_bit1 : (bit1 a p).last = p.last := rfl

end Last

def pop : PSharedStack β → β
  | sngl a => a
  | bit0 p => p.pop
  | bit1 a _ => a

section Pop

@[simp] theorem pop_sngl : (sngl a).pop = a := rfl
@[simp] theorem pop_bit0 : (bit0 p).pop = p.pop := rfl
@[simp] theorem pop_bit1 : (bit1 a p).pop = a := rfl

theorem pop_eq_last_of_isRoot : p.isRoot → p.pop = p.last := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [pop_sngl, last_sngl, implies_true]
  · simp_rw [isRoot_bit0_iff, pop_bit0, last_bit0]
    exact IH
  · simp_rw [not_isRoot_bit1, false_implies]

end Pop

section Push

variable [Hash β]

def push : PSharedStack β → β → PSharedStack β
  | sngl a, b => bit0 (sngl (a # b))
  | bit0 p, b => bit1 b p
  | bit1 a p, b => bit0 (p.push (a # b))

@[simp] theorem push_sngl : (sngl a).push b = bit0 (sngl (a # b)) := rfl
@[simp] theorem push_bit0 : (bit0 p).push b = bit1 b p := rfl
@[simp] theorem push_bit1 : (bit1 a p).push b = bit0 (p.push (a # b)) := rfl

@[simp] theorem push_ne_sngl : p.push b ≠ sngl a := by
  cases p <;> exact PSharedStack.noConfusion

theorem push_isRoot_iff_isMaxed : (p.push b).isRoot ↔ p.isMaxed := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · simp_rw [push_sngl, isRoot_bit0_iff, isRoot_sngl, isMaxed_sngl]
  · simp_rw [push_bit0, not_isRoot_bit1, not_isMaxed_bit0]
  · simp_rw [push_bit1, isRoot_bit0_iff, isMaxed_bit1_iff, IH]

@[simp]
theorem count_push : (p.push b).count = p.count.succ := by
  induction p generalizing b with | sngl => rfl | bit0 => rfl | bit1 _ _ IH => exact congrArg _ IH

theorem lg2_push : (p.push b).lg2 = p.lg2 + (decide (p.isMaxed)).toNat := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · simp_rw [push_sngl, lg2_bit0, lg2_sngl, isMaxed_sngl, decide_True, Bool.toNat_true]
  · simp_rw [push_bit0, lg2_bit0, lg2_bit1, not_isMaxed_bit0, decide_False, Bool.toNat_false]
  · simp_rw [push_bit1, lg2_bit0, lg2_bit1, isMaxed_bit1_iff, IH, add_assoc, add_comm]

theorem lg2_push_of_isMaxed (hp : p.isMaxed) : (p.push b).lg2 = p.lg2 + 1 := by
  simp_rw [lg2_push, hp]
  rfl

theorem lg2_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).lg2 = p.lg2 := by
  simp_rw [lg2_push, hp]
  rfl

theorem size_push : (p.push b).size = p.size + (decide (p.isMaxed)).toNat := by
  simp_rw [size_eq_lg2_succ, lg2_push, Nat.add_right_comm]

theorem size_push_of_isMaxed (hp : p.isMaxed) : (p.push b).size = p.size + 1 := by
  simp_rw [size_push, hp]
  rfl

theorem size_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).size = p.size := by
  simp_rw [size_push, hp]
  rfl

theorem last_push_eq_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).last = p.last := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · exact (hp isMaxed_sngl).elim
  · simp_rw [push_bit0, last_bit1, last_bit0]
  · simp_rw [isMaxed_bit1_iff] at hp
    simp_rw [push_bit1, last_bit0, IH hp, last_bit1]

theorem last_push_eq_hash_of_isMaxed (hp : p.isMaxed) : (p.push b).last =
    p.last # ((fun p b => _) p b) := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · simp
  · simp at hp
  · simp_rw [isMaxed_bit1_iff] at hp
    simp [IH hp]
    simp_rw [push_bit1, last_bit0, IH hp, last_bit1]

end Push

def pushTuple [Hash β] : PSharedStack β → (Fin k → β) → PSharedStack β := match k with
  | 0 => fun p _ => p
  | (_ + 1) => fun p bs => pushTuple (p.push (bs 0)) (Fin.tail bs)

section PushTuple

variable {k m n : ℕ} {bs : Fin k → β} [Hash β]

open Fin

@[simp] theorem pushTuple_zero {bs : Fin 0 → β} : p.pushTuple bs = p := rfl

@[simp] theorem pushTuple_one {bs : Fin 1 → β} : p.pushTuple bs = p.push (bs 0) := rfl

theorem pushTuple_succ {bs : Fin (k + 1) → β} :
  p.pushTuple bs = (p.push (bs 0)).pushTuple (Fin.tail bs) := rfl

theorem pushTuple_succ_last {bs : Fin (k + 1) → β} :
    p.pushTuple bs = (p.pushTuple (Fin.init bs)).push (bs (Fin.last k)) := by
  induction k generalizing p with | zero => _ | succ k IH => _
  · simp_rw [pushTuple_one, pushTuple_zero, Fin.last_zero]
  · simp_rw [pushTuple_succ (bs := bs), pushTuple_succ (bs := (Fin.init bs)),
      Fin.tail_init_eq_init_tail, IH (bs := Fin.tail bs),
      Fin.init_def, Fin.castSucc_zero, Fin.tail_def, Fin.succ_last]

theorem pushTuple_add {bs : Fin (m + n) → β} :
    p.pushTuple bs = (p.pushTuple fun i => bs (Fin.castAdd n i)).pushTuple
    fun i => bs (Fin.natAdd m i) := by
  induction' n with n IH
  · simp_rw [Fin.castAdd_zero, Fin.cast_eq_self, pushTuple_zero]
  · simp_rw [pushTuple_succ_last, IH]
    rfl

theorem pushTuple_cons :
    p.pushTuple (cons b bs) = (p.push b).pushTuple bs := pushTuple_succ

theorem pushTuple_snoc  :
    p.pushTuple (snoc bs b) = (p.pushTuple bs).push b := by
  simp_rw [pushTuple_succ_last, init_snoc, snoc_last]

theorem pushTuple_append {bs₁ : Fin m → β} {bs₂ : Fin n → β} : (p.pushTuple bs₁).pushTuple bs₂ =
      p.pushTuple (append bs₁ bs₂) := by simp_rw [pushTuple_add, append_left, append_right]

@[simp] theorem pushTuple_cast (h : k' = k) :
    p.pushTuple (fun i => bs <| Fin.cast h i) = p.pushTuple bs := by
  cases h
  rfl

theorem pushTuple_congr {bs' : Fin k' → β} (hp : p = p') (hk : k = k')
  (hb : bs  = bs' ∘ (Fin.cast hk ·)) : p.pushTuple bs = p'.pushTuple bs' := by
  cases hp
  cases hk
  cases hb
  rfl

theorem pushTuple_two_pow_succ {bs : Fin (2 ^ (n + 1)) → β} :
    p.pushTuple bs = (p.pushTuple (twoPowSuccTupleDivide bs).1).pushTuple
    (twoPowSuccTupleDivide bs).2 := by
  simp_rw [pushTuple_append, append_eq_twoPowSuccTuple_symm, Prod.mk.eta,
    Equiv.symm_apply_apply, pushTuple_cast]

theorem pushTuple_sngl {bs : Fin (k + 1) → β} :
  (sngl a).pushTuple bs = (bit0 (sngl (a # bs 0))).pushTuple (tail bs) := rfl

theorem pushTuple_bit0 {bs : Fin (k + 1) → β} :
    (bit0 p).pushTuple bs = (bit1 (bs 0) p).pushTuple (tail bs) := rfl

theorem pushTuple_bit1 {bs : Fin (k + 1) → β} :
    (bit1 a p).pushTuple bs = (bit0 (p.push (a # bs 0))).pushTuple (tail bs) := rfl

@[simp]
theorem count_pushTuple : (p.pushTuple bs).count = p.count + k := by
  induction k generalizing p with | zero => _ | succ k IH => _
  · rfl
  · rw [pushTuple_succ, IH, count_push, Nat.succ_add, Nat.add_succ]

theorem size_pushTuple_of_lt_sizeInc (hk : k < p.sizeInc) : (p.pushTuple bs).size = p.size := by
  induction k generalizing p with | zero => _ | succ k IH => _
  · rfl
  · simp_rw [pushTuple_succ_last, size_push, isMaxed_iff_count_eq_pred_two_pow_size,
    count_pushTuple, IH ((Nat.le_succ _).trans_lt hk), Nat.add_eq_left,
    Bool.toNat_eq_zero, decide_eq_false_iff_not, ← count_add_sizeInc_eq_two_pow_size,
    Nat.add_sub_assoc one_le_sizeInc, add_right_inj]
    exact (Nat.lt_pred_of_succ_lt hk).ne

theorem size_pushTuple_of_le_sizeCap (hk : k ≤ p.sizeCap) : (p.pushTuple bs).size = p.size :=
  size_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem size_pushTuple_sizeCap {bs : Fin k → β} (hk : k = p.sizeCap) :
    (p.pushTuple bs).size = p.size := size_pushTuple_of_le_sizeCap hk.le

theorem lg2_pushTuple_of_lt_sizeInc (hk : k < p.sizeInc) : (p.pushTuple bs).lg2 = p.lg2 := by
  apply add_left_injective 1
  simp_rw [← size_eq_lg2_succ]
  exact size_pushTuple_of_lt_sizeInc hk

theorem lg2_pushTuple_of_le_sizeCap (hk : k ≤ p.sizeCap) : (p.pushTuple bs).lg2 = p.lg2 :=
  lg2_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem lg2_pushTuple_sizeCap {bs : Fin k → β} (hk : k = p.sizeCap) :
    (p.pushTuple bs).lg2 = p.lg2 := lg2_pushTuple_of_le_sizeCap hk.le

theorem isMaxed_pushTuple_sizeCap {bs : Fin k → β} (hk : k = p.sizeCap) :
    (p.pushTuple bs).isMaxed := by
  simp_rw [isMaxed_iff_count_eq_pred_two_pow_size, count_pushTuple, hk,
    count_add_sizeCap_eq_pred_two_pow_size, size_pushTuple_of_le_sizeCap hk.le]

theorem isRoot_pushTuple_sizeInc {bs : Fin k → β} (hk : k = p.sizeInc) :
    (p.pushTuple bs).isRoot := by
  cases k
  · exact ((hk ▸ sizeInc_ne_zero) rfl).elim
  · rw [pushTuple_succ_last, push_isRoot_iff_isMaxed]
    exact isMaxed_pushTuple_sizeCap (add_left_injective 1 hk)

theorem size_pushTuple_sizeInc {bs : Fin k → β} (hk : k = p.sizeInc) :
    (p.pushTuple bs).size = p.size + 1 := by
  rw [sizeInc_eq_sizeCap_succ] at hk
  cases hk
  · rw [pushTuple_succ_last, size_push_of_isMaxed (isMaxed_pushTuple_sizeCap rfl),
      size_pushTuple_sizeCap rfl]

theorem lg2_pushTuple_sizeInc {bs : Fin k → β} (hk : k = p.sizeInc) :
    (p.pushTuple bs).lg2 = p.lg2 + 1 := add_left_injective 1 <| by
  simp_rw [← size_eq_lg2_succ, size_pushTuple_sizeInc hk]

theorem pushTuple_two_pow_lg2_isRoot_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.lg2) : (p.pushTuple bs).isRoot :=
  isRoot_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_lg2.mp hp).symm)

theorem lg2_pushTuple_two_pow_lg2_eq_succ_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.lg2) :
    (p.pushTuple bs).lg2 = p.lg2 + 1 :=
  lg2_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_lg2.mp hp).symm)

theorem size_pushTuple_two_pow_lg2_eq_succ_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.lg2) :
    (p.pushTuple bs).size = p.size + 1 :=
  size_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_lg2.mp hp).symm)

end PushTuple

/-
def stackOfTuple [Hash β] [NeZero k] (bs : Fin k → β) : PSharedStack β :=
  (sngl (bs 0)).pushTuple (fun (i : Fin (k - 1)) => bs
  (Fin.cast (Nat.sub_add_cancel NeZero.one_le) i.succ))

section StackOfTuple

variable {n : ℕ} {bs : Fin k → β} [Hash β]

@[simp] theorem stackOfTuple_one {bs : Fin 1 → β} : stackOfTuple bs = sngl (bs 0) := rfl

theorem stackOfTuple_succ {bs : Fin (k + 1) → β} :
  stackOfTuple bs = (sngl (bs 0)).pushTuple (Fin.tail bs) := rfl

theorem stackOfTuple_succ_last [NeZero k] {bs : Fin (k + 1) → β} :
    stackOfTuple bs = (stackOfTuple (Fin.init bs)).push (bs (Fin.last k)) := by
  rw [stackOfTuple_succ]
  cases k
  · exact (NeZero.ne 0 rfl).elim
  · apply pushTuple_congr

end StackOfTuple


def twoPowStackOfTuple [Hash β] : {n : ℕ} → (Fin (2^n) → β) → PSharedStack β
  | 0 => fun bs => sngl (bs 0)
  | (_ + 1) => fun bs =>
    let (f, l) := twoPowSuccTupleDivide bs
    (twoPowStackOfTuple f).pushTuple l

section TwoPowStackOfTuple

variable {n : ℕ} {bs : Fin (2^n) → β} [Hash β]

@[simp] theorem twoPowStackOfTuple_zero {bs : Fin (2^0) → β} : twoPowStackOfTuple bs = sngl (bs 0) := rfl

@[simp] theorem twoPowStackOfTuple_succ {bs : Fin (2^(n + 1)) → β} :
    twoPowStackOfTuple bs = (twoPowStackOfTuple (twoPowSuccTupleDivide bs).1).pushTuple
    (twoPowSuccTupleDivide bs).2 := rfl

theorem twoPowStackOfTuple_congr {n' : ℕ} (hn : n = n') {bs' : Fin (2^n') → β}
  (hbs : bs = fun i => bs' <| Fin.cast (hn ▸ rfl) i) :
    twoPowStackOfTuple bs = twoPowStackOfTuple bs' := by
  cases hn
  cases hbs
  rfl

theorem twoPowStackOfTuple_count : (twoPowStackOfTuple bs).count = 2^n := by
  induction n with | zero => _ | succ n IH => _
  · rfl
  · simp_rw [twoPowStackOfTuple_succ, count_pushTuple, IH, pow_succ', two_mul]

@[simp] theorem twoPowStackOfTuple_lg2 : (twoPowStackOfTuple bs).lg2 = n :=
  (Nat.log2_two_pow ▸ twoPowStackOfTuple_count (bs := bs) ▸
    (twoPowStackOfTuple bs).log2_count_eq_lg2).symm

@[simp] theorem twoPowStackOfTuple_size : (twoPowStackOfTuple bs).size = n + 1 := by
  rw [size_eq_lg2_succ, twoPowStackOfTuple_lg2]

@[simp] theorem twoPowStackOfTuple_isRoot : (twoPowStackOfTuple bs).isRoot := by
  rw [isRoot_iff_count_eq_two_pow_lg2, twoPowStackOfTuple_count, twoPowStackOfTuple_lg2]

theorem blahj {bs : Fin k → β} (hp : p.isRoot) (hk : k = 2^p.lg2) :
    (p.pushTuple bs).pop = p.pop # (twoPowStackOfTuple (fun i => bs <| Fin.cast hk.symm i)).pop := by


theorem twoPowStackOfTuple_eq_sngl_pushTuple :
    twoPowStackOfTuple bs = (sngl (bs 0)).pushTuple
    (fun i : Fin (2^n - 1) => bs <|
    Fin.cast (tsub_add_cancel_of_le Nat.one_le_two_pow) i.succ) := by
  induction n with | zero => _ | succ n IH => _
  · rfl
  · simp_rw [twoPowStackOfTuple_succ, IH, pushTuple_append]
    refine pushTuple_congr rfl ((Nat.sub_add_comm Nat.one_le_two_pow) ▸
      (congrArg (· - 1) (Nat.two_pow_succ n).symm)) (funext <| fun i => ?_)
    simp_rw [Fin.append]
    cases i using Fin.addCases with | left => _ | right i => _
    · simp_rw [Fin.addCases_left]
      rfl
    · simp_rw [Fin.addCases_right, twoPowSuccTupleDivide_apply, Function.comp_apply,
        Fin.succ_cast_eq, Fin.cast_trans]
      congr
      simp_rw [Fin.ext_iff, concatTwoPow_inr_apply_val, Fin.coe_cast, Fin.val_succ,
        Fin.coe_natAdd, Nat.add_right_comm _ _ 1, tsub_add_cancel_of_le Nat.one_le_two_pow]

theorem twoPowStackOfTuple_pop_eq_last :
    (twoPowStackOfTuple bs).pop = (twoPowStackOfTuple bs).last :=
  pop_eq_last_of_isRoot twoPowStackOfTuple_isRoot

theorem twoPowStackOfTuple_zero_pop {bs : Fin (2^0) → β} :
  (twoPowStackOfTuple bs).pop = bs 0 := rfl

theorem twoPowStackOfTuple_succ_pop {bs : Fin (2^(n + 1)) → β} :
    (twoPowStackOfTuple bs).pop =
    (twoPowStackOfTuple (twoPowSuccTupleDivide bs).1).pop #
    (twoPowStackOfTuple (twoPowSuccTupleDivide bs).2).pop := by
  rw [twoPowStackOfTuple_succ, blahj]
  congr 2
  · simp
    apply twoPowStackOfTuple_congr
    · simp
    · simp
  · simp
  · simp

isRoot_iff_count_eq_two_pow_lg2
 size_count_eq_size
theorem finalHash_zero (bs : Fin (2^0) → β) :
  finalHash 0 bs = bs 0 := rfl

theorem finalHash_succ (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHash (n + 1) bs =
  (finalHash n (twoPowSuccTupleDivide bs).1) #
  (finalHash n (twoPowSuccTupleDivide bs).2) := rfl

end TwoPowStackOfTuple
-/

end PSharedStack

inductive SharedStack (β : Type u) : Type u
  | emp : SharedStack β
  | pst : PSharedStack β → SharedStack β

namespace SharedStack

open PSharedStack

variable {β : Type*} {a b : β} {p : PSharedStack β} {s : SharedStack β}

instance : Inhabited (SharedStack β) where
  default := emp

def lg2 (s : SharedStack β) : ℕ := s.casesOn 0 (fun p => p.lg2)

section Lg2

@[simp] theorem lg2_emp : (emp : SharedStack β).lg2 = 0 := rfl
@[simp] theorem lg2_pst : (pst p).lg2 = p.lg2 := rfl

end Lg2

def size (s : SharedStack β) : ℕ := s.casesOn 0 (fun p => p.size)

section Size

@[simp] theorem size_emp : (emp : SharedStack β).size = 0 := rfl
@[simp] theorem size_pst : (pst p).size = p.size := rfl

@[simp] theorem size_eq_zero : s.size = 0 ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl)
  (fun p => iff_of_false p.size_ne_zero SharedStack.noConfusion)

@[simp] theorem pst_size_pos : 0 < (pst p).size := p.size_pos

@[simp] theorem one_le_size_pos : 1 ≤ (pst p).size := p.size_pos

theorem lg2_eq_size_pred : s.lg2 = s.size - 1 := s.casesOn rfl (fun _ => rfl)

end Size

def toList (s : SharedStack β) : List (Option β) := s.casesOn [] PSharedStack.toList

section ToList

@[simp] theorem toList_emp : (emp : SharedStack β).toList = [] := rfl
@[simp] theorem toList_pst : (pst p).toList = p.toList := rfl

@[simp] theorem toList_eq_nil : s.toList = [] ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl) (fun p => iff_of_false p.toList_ne_nil SharedStack.noConfusion)

@[simp]
theorem length_toList : (toList s).length = s.size := s.recOn rfl fun p => p.length_toList

instance [Repr β] : Repr (SharedStack β) where
  reprPrec := fun s => reprPrec (s.toList)

end ToList

def count (s : SharedStack β) : ℕ := s.casesOn 0 PSharedStack.count

section Count

@[simp] theorem count_emp : (emp : SharedStack β).count = 0 := rfl
@[simp] theorem count_pst : (pst p).count = p.count := rfl

@[simp] theorem count_eq_zero : s.count = 0 ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl) (fun p => iff_of_false p.count_ne_zero SharedStack.noConfusion)

theorem count_lt_two_pow_size : s.count < 2^s.size := by
  cases s with | emp => _ | pst p => _
  · exact zero_lt_one
  · exact p.count_lt_two_pow_size

@[simp] theorem size_count_eq_size : s.count.size = s.size := by
  cases s with | emp => _ | pst p => _
  · exact Nat.size_zero
  · exact p.size_count_eq_size

@[simp] theorem log_two_count_eq_lg2 : Nat.log 2 s.count = s.lg2 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [count_emp, Nat.log_zero_right, lg2_emp]
  · exact p.log_two_count_eq_lg2

@[simp] theorem log2_count_eq_lg2 : s.count.log2 = s.lg2 := by
  rw [Nat.log2_eq_log_two, log_two_count_eq_lg2]

end Count

-- sizeCap = "we can push this many without increasing the size"

def sizeCap (s : SharedStack β) : ℕ := s.casesOn 0 PSharedStack.sizeCap

section SizeCap

@[simp] theorem sizeCap_emp : (emp : SharedStack β).sizeCap = 0 := rfl
@[simp] theorem sizeCap_bit0 : (pst p).sizeCap = p.sizeCap := rfl

theorem sizeCap_lt_pred_two_pow_size : s.sizeCap ≤ 2^(s.lg2) - 1 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [sizeCap_emp, lg2_emp, zero_le]
  · exact p.sizeCap_lt_pred_two_pow_size

theorem count_add_sizeCap_eq_pred_two_pow_size : s.count + s.sizeCap = 2^s.size - 1 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [count_emp, sizeCap_emp, size_emp, pow_zero, Nat.sub_self]
  · exact p.count_add_sizeCap_eq_pred_two_pow_size

end SizeCap

-- "if we push this many, we will increase the size"

def sizeInc : SharedStack β → ℕ := fun s => s.sizeCap + 1

section SizeInc

@[simp] theorem sizeInc_emp : (emp : SharedStack β).sizeInc = 1 := rfl
@[simp] theorem sizeInc_bit0 : (pst p).sizeInc = p.sizeInc := rfl

theorem sizeInc_ne_zero : s.sizeInc ≠ 0 := Nat.succ_ne_zero _

theorem one_le_sizeInc : 1 ≤ s.sizeInc := Nat.one_le_iff_ne_zero.mpr sizeInc_ne_zero

theorem sizeInc_eq_sizeCap_succ : s.sizeInc = s.sizeCap + 1 := rfl

theorem sizeInc_lt_two_pow_size : s.sizeInc ≤ 2^s.lg2 := by
  rw [sizeInc_eq_sizeCap_succ]
  exact Nat.add_le_of_le_sub Nat.one_le_two_pow sizeCap_lt_pred_two_pow_size

theorem count_add_sizeInc_eq_two_pow_size : s.count + s.sizeInc = 2^s.size := by
  rw [sizeInc_eq_sizeCap_succ, ← Nat.add_assoc,
    count_add_sizeCap_eq_pred_two_pow_size, Nat.sub_add_cancel Nat.one_le_two_pow]

end SizeInc

def last? (s : SharedStack β) : Option β := s.casesOn none (fun p => some (p.last))

section Last?

@[simp] theorem last?_emp : (emp : SharedStack β).last? = none := rfl
@[simp] theorem last?_pst : (pst p).last? = some p.last := rfl

def last (s : SharedStack β) (hs : s.count ≠ 0) : β := match s with
  | emp => ((hs count_emp).elim)
  | pst p => p.last

@[simp] theorem last_pst {hs : (pst p).count ≠ 0} : (pst p).last hs = p.last := rfl

end Last?

def pop? (s : SharedStack β) : Option β := s.casesOn none (fun p => some (p.pop))

section Pop?

@[simp] theorem pop?_emp : (emp : SharedStack β).pop? = none := rfl
@[simp] theorem pop?_pst : (pst p).pop? = some p.pop := rfl

end Pop?

def pop (s : SharedStack β) : s.count ≠ 0 → β :=
  s.casesOn (fun hs => ((hs count_emp).elim)) (fun p _ => p.pop)

section Pop

@[simp] theorem pop_pst : (pst p).pop p.count_ne_zero = p.pop := rfl

end Pop

def isRoot (s : SharedStack β) : Prop := s.casesOn False (fun p => p.isRoot)

section IsRoot

@[simp] theorem not_isRoot_emp : ¬ (emp : SharedStack β).isRoot := False.elim

@[simp] theorem isRoot_pst_iff : (pst p).isRoot ↔ p.isRoot := Iff.rfl

theorem isRoot_iff_count_eq_two_pow_lg2 :
    s.isRoot ↔ s.count = 2^s.lg2 := s.casesOn
  (iff_of_false not_isRoot_emp zero_ne_one) (fun p => p.isRoot_iff_count_eq_two_pow_lg2)

instance : Decidable (s.isRoot) :=
  decidable_of_iff _ isRoot_iff_count_eq_two_pow_lg2.symm

theorem isRoot_iff_toList_eq_replicate_size_pred_append_singleton :
    s.isRoot ↔ ∃ (h : s.count ≠ 0), s.toList =
    List.replicate s.lg2 none ++ [some (s.pop h)] := by
  cases s with | emp => _ | pst p => _
  · simp_rw [count_emp, not_isRoot_emp, false_iff, not_exists]
    exact fun h => h.irrefl.elim
  · haveI : Nonempty _ := ⟨p.count_ne_zero⟩
    simp_rw [isRoot_pst_iff, isRoot_iff_toList_eq_replicate_size_pred_append_singleton, count_pst]
    exact (exists_const _).symm

theorem isRoot_iff_exists_size_eq_two_pow : s.isRoot ↔ ∃ k, s.count = 2^k := by
  rw [isRoot_iff_count_eq_two_pow_lg2]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨k, hk⟩ => ?_⟩
  have H := hk ▸ s.log_two_count_eq_lg2
  rw [Nat.log_pow one_lt_two] at H
  exact H ▸ hk

end IsRoot

def isMaxed (s : SharedStack β) : Prop := s.casesOn True (fun p => p.isMaxed)

section IsMaxed

@[simp] theorem isMaxed_emp : (emp : SharedStack β).isMaxed := True.intro

@[simp] theorem isMaxed_pst_iff : (pst p).isMaxed ↔ p.isMaxed := Iff.rfl

theorem isMaxed_iff_count_eq_pred_two_pow_size :
    s.isMaxed ↔ s.count = 2^(s.size) - 1 := s.casesOn
  (by simp_rw [isMaxed_emp, count_emp, size_emp, pow_zero, Nat.sub_self])
  (fun p => p.isMaxed_iff_count_eq_pred_two_pow_size)

instance : Decidable (s.isMaxed) :=
  decidable_of_iff _ isMaxed_iff_count_eq_pred_two_pow_size.symm

end IsMaxed

def isPositive (s : SharedStack β) : Prop := s.casesOn True (fun _ => False)

section IsPositive

@[simp] theorem isPositive_emp : (emp : SharedStack β).isPositive := True.intro

@[simp] theorem not_isPositive_pst : ¬ (pst p).isPositive := False.elim

theorem isPositive_iff_eq_emp : s.isPositive ↔ s = emp :=
  s.casesOn (iff_of_true isPositive_emp rfl)
  (fun _ => iff_of_false not_isPositive_pst SharedStack.noConfusion)

theorem not_isPositive_iff_exists_eq_pst : ¬ s.isPositive ↔ ∃ p, s = pst p :=
  s.casesOn (iff_of_false (not_not_intro isPositive_emp)
    (not_exists_of_forall_not fun _ => SharedStack.noConfusion))
  (fun _ => iff_of_true not_isPositive_pst ⟨_, rfl⟩)

instance : Decidable (s.isPositive) :=
  s.casesOn (isTrue isPositive_emp) (fun _ => isFalse not_isPositive_pst)

end IsPositive

def testBit (s : SharedStack β) (n : ℕ) : Bool := s.casesOn false (fun p => p.testBit n)

section TestBit

@[simp] theorem testBit_emp : (emp : SharedStack β).testBit n = false := rfl
@[simp] theorem testBit_pst : (pst p).testBit n = p.testBit n := rfl

theorem testBit_of_size_ge : s.size ≤ n → s.testBit n = false :=
  s.casesOn (fun _ => rfl) (fun p => p.testBit_of_size_ge)

theorem testBit_count : s.count.testBit n = s.testBit n :=
  s.casesOn (Nat.zero_testBit _) (fun p => p.testBit_count)

end TestBit

def push [Hash β] (s : SharedStack β) : β → SharedStack β :=
  s.casesOn (fun a => pst (sngl a)) (fun p b => pst (p.push b))

section Push

variable [Hash β]

@[simp] theorem push_emp : (emp : SharedStack β).push a = pst (sngl a) := rfl
@[simp] theorem push_pst : (pst p).push b = pst (p.push b) := rfl

@[simp] theorem push_ne_emp : s.push b ≠ emp := by
  cases s <;> exact SharedStack.noConfusion

@[simp]
theorem count_push : (s.push b).count = s.count.succ := s.casesOn rfl (fun p => p.count_push)

theorem size_push : (s.push b).size = s.size + (decide (s.isMaxed)).toNat := s.casesOn rfl
  (fun p => by simp_rw [push_pst, size_pst, isMaxed_pst_iff, p.size_push])

theorem size_push_of_isMaxed (hs : s.isMaxed) : (s.push b).size = s.size + 1 := by
  simp_rw [size_push, hs]
  rfl

theorem size_push_of_not_isMaxed (hs : ¬ s.isMaxed) : (s.push b).size = s.size := by
  simp_rw [size_push, hs]
  rfl

theorem push_isRoot_iff_isMaxed : (s.push b).isRoot ↔ s.isMaxed := s.casesOn
  (by simp_rw [push_emp, isRoot_pst_iff, isRoot_sngl, isMaxed_emp])
  fun p => p.push_isRoot_iff_isMaxed

end Push

def pushTuple [Hash β] : SharedStack β → (Fin k → β) → SharedStack β
  | emp => k.casesOn (fun _ => emp) (fun _ bs => pst ((sngl (bs 0)).pushTuple (Fin.tail bs)))
  | pst p => fun bs => pst (p.pushTuple bs)

section PushTuple

variable {k m n : ℕ} {bs : Fin k → β} [Hash β]

open Fin

@[simp] theorem pushTuple_emp_zero {bs : Fin 0 → β} : (emp : SharedStack β).pushTuple bs = emp :=
  rfl

@[simp] theorem pushTuple_emp_succ {bs : Fin (k + 1) → β} :
    (emp : SharedStack β).pushTuple bs = (pst (sngl (bs 0))).pushTuple (Fin.tail bs) := rfl

@[simp] theorem pushTuple_pst {bs : Fin k → β} :
    (pst p).pushTuple bs = pst (p.pushTuple bs) := rfl

@[simp] theorem pushTuple_zero {bs : Fin 0 → β} : s.pushTuple bs = s :=
  s.casesOn rfl (fun _ => rfl)

@[simp] theorem pushTuple_one {bs : Fin 1 → β} : s.pushTuple bs = s.push (bs 0) :=
  s.casesOn rfl (fun _ => rfl)

theorem pushTuple_succ {bs : Fin (k + 1) → β} :
  s.pushTuple bs = (s.push (bs 0)).pushTuple (Fin.tail bs) := s.casesOn rfl (fun _ => rfl)

theorem pushTuple_succ_last {bs : Fin (k + 1) → β} :
    s.pushTuple bs = (s.pushTuple (Fin.init bs)).push (bs (Fin.last k)) := by
  cases k
  · simp
  · cases s
    · simp_rw [pushTuple_emp_succ, pushTuple_pst, PSharedStack.pushTuple_succ_last,
        push_pst, pst.injEq]
      rfl
    · simp_rw [pushTuple_pst, PSharedStack.pushTuple_succ_last, push_pst]

theorem pushTuple_add {bs : Fin (m + n) → β} :
    s.pushTuple bs = (s.pushTuple fun i => bs (Fin.castAdd n i)).pushTuple
    fun i => bs (Fin.natAdd m i) := by
  induction' n with n IH
  · simp_rw [Fin.castAdd_zero, Fin.cast_eq_self, pushTuple_zero]
  · simp_rw [pushTuple_succ_last, IH]
    rfl

theorem pushTuple_cons : s.pushTuple (cons b bs) = (s.push b).pushTuple bs := pushTuple_succ

theorem pushTuple_snoc : s.pushTuple (snoc bs b) = (s.pushTuple bs).push b := by
  simp_rw [pushTuple_succ_last, init_snoc, snoc_last]

theorem pushTuple_append {bs₁ : Fin m → β} {bs₂ : Fin n → β} : (s.pushTuple bs₁).pushTuple bs₂ =
      s.pushTuple (append bs₁ bs₂) := by simp_rw [pushTuple_add, append_left, append_right]

@[simp] theorem pushTuple_cast (h : k' = k) :
    s.pushTuple (fun i => bs <| Fin.cast h i) = s.pushTuple bs := by
  cases h
  rfl

theorem pushTuple_congr {bs' : Fin k' → β} (hp : s = s') (hk : k = k')
  (hb : bs  = bs' ∘ (Fin.cast hk ·)) : s.pushTuple bs = s'.pushTuple bs' := by
  cases hp
  cases hk
  cases hb
  rfl

theorem pushTuple_two_pow_succ {bs : Fin (2 ^ (n + 1)) → β} :
    s.pushTuple bs = (s.pushTuple (twoPowSuccTupleDivide bs).1).pushTuple
    (twoPowSuccTupleDivide bs).2 := by
  simp_rw [pushTuple_append, append_eq_twoPowSuccTuple_symm, Prod.mk.eta,
    Equiv.symm_apply_apply, pushTuple_cast]

@[simp]
theorem count_pushTuple : (s.pushTuple bs).count = s.count + k := by
  induction k generalizing s with | zero => _ | succ k IH => _
  · simp_rw [pushTuple_zero, add_zero]
  · rw [pushTuple_succ, IH, count_push, Nat.succ_add, Nat.add_succ]

theorem size_pushTuple_of_lt_sizeInc (hk : k < s.sizeInc) : (s.pushTuple bs).size = s.size := by
  cases s with | emp => _ | pst p => _
  · simp_rw [sizeInc_emp, Nat.lt_one_iff] at hk
    cases hk
    simp_rw [pushTuple_zero]
  · exact p.size_pushTuple_of_lt_sizeInc hk

theorem size_pushTuple_of_le_sizeCap (hk : k ≤ s.sizeCap) : (s.pushTuple bs).size = s.size :=
  size_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem size_pushTuple_sizeCap {bs : Fin k → β} (hk : k = s.sizeCap) :
    (s.pushTuple bs).size = s.size := size_pushTuple_of_le_sizeCap hk.le

theorem lg2_pushTuple_of_lt_sizeInc (hk : k < s.sizeInc) : (s.pushTuple bs).lg2 = s.lg2 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [sizeInc_emp, Nat.lt_one_iff] at hk
    cases hk
    simp_rw [pushTuple_zero]
  · exact p.lg2_pushTuple_of_lt_sizeInc hk

theorem lg2_pushTuple_of_le_sizeCap (hk : k ≤ s.sizeCap) : (s.pushTuple bs).lg2 = s.lg2 :=
  lg2_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem lg2_pushTuple_sizeCap {bs : Fin k → β} (hk : k = s.sizeCap) :
    (s.pushTuple bs).lg2 = s.lg2 := lg2_pushTuple_of_le_sizeCap hk.le

theorem isMaxed_pushTuple_sizeCap {bs : Fin k → β} (hk : k = s.sizeCap) :
    (s.pushTuple bs).isMaxed := by
  simp_rw [isMaxed_iff_count_eq_pred_two_pow_size, count_pushTuple, hk,
    count_add_sizeCap_eq_pred_two_pow_size, size_pushTuple_of_le_sizeCap hk.le]

theorem isRoot_pushTuple_sizeInc {bs : Fin k → β} (hk : k = s.sizeInc) :
    (s.pushTuple bs).isRoot := by
  cases k
  · exact ((hk ▸ sizeInc_ne_zero) rfl).elim
  · rw [pushTuple_succ_last, push_isRoot_iff_isMaxed]
    exact isMaxed_pushTuple_sizeCap (add_left_injective 1 hk)

theorem size_pushTuple_sizeInc {bs : Fin k → β} (hk : k = s.sizeInc) :
    (s.pushTuple bs).size = s.size + 1 := by
  rw [sizeInc_eq_sizeCap_succ] at hk
  cases hk
  · rw [pushTuple_succ_last, size_push_of_isMaxed (isMaxed_pushTuple_sizeCap rfl),
      size_pushTuple_sizeCap rfl]

theorem pushTuple_two_pow_lg2_isRoot_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.lg2) : (s.pushTuple bs).isRoot := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.pushTuple_two_pow_lg2_isRoot_of_isRoot hs hk

theorem lg2_pushTuple_two_pow_lg2_eq_succ_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.lg2) : (s.pushTuple bs).lg2 = s.lg2 + 1 := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.lg2_pushTuple_two_pow_lg2_eq_succ_of_isRoot hs hk

theorem size_pushTuple_two_pow_lg2_eq_succ_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.lg2) :
    (s.pushTuple bs).size = s.size + 1 := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.size_pushTuple_two_pow_lg2_eq_succ_of_isRoot hs hk

end PushTuple

def stackOfTuple [Hash β] (bs : Fin k → β) : SharedStack β := emp.pushTuple bs

section StackOfTuple

open Fin

variable {n m k : ℕ} {bs : Fin k → β} [Hash β]

@[simp] theorem stackOfTuple_zero {bs : Fin 0 → β} : stackOfTuple bs = emp := rfl

@[simp] theorem stackOfTuple_one {bs : Fin 1 → β} : stackOfTuple bs = pst (sngl (bs 0)) := rfl

theorem stackOfTuple_succ {bs : Fin (k + 1) → β} :
  stackOfTuple bs = (pst (sngl (bs 0))).pushTuple (Fin.tail bs) := rfl

theorem stackOfTuple_succ_last {bs : Fin (k + 1) → β} :
    stackOfTuple bs = (stackOfTuple (Fin.init bs)).push (bs (Fin.last k)) := pushTuple_succ_last

theorem stackOfTuple_add (bs : Fin (m + n) → β) :
    stackOfTuple bs = (stackOfTuple fun i => bs (Fin.castAdd n i)).pushTuple
    fun i => bs (Fin.natAdd m i) := pushTuple_add

theorem stackOfTuple_cons : stackOfTuple (cons b bs) = (pst (sngl b)).pushTuple bs := pushTuple_cons

theorem stackOfTuple_snoc : stackOfTuple (snoc bs b) = (stackOfTuple bs).push b := pushTuple_snoc

theorem stackOfTuple_append {bs₁ : Fin m → β} {bs₂ : Fin n → β} : (stackOfTuple bs₁).pushTuple bs₂ =
    stackOfTuple (append bs₁ bs₂) := pushTuple_append

theorem count_stackOfTuple : (stackOfTuple bs).count = k := by
  unfold stackOfTuple
  simp_rw [count_pushTuple, count_emp, zero_add]

theorem lg2_stackOfTuple : (stackOfTuple bs).lg2 = k.log2 :=
  (stackOfTuple bs).log2_count_eq_lg2 ▸ (congrArg _ count_stackOfTuple)

theorem size_stackOfTuple : (stackOfTuple bs).size = k.size :=
  (stackOfTuple bs).size_count_eq_size ▸ (congrArg _ count_stackOfTuple)

theorem isRoot_stackOfTuple_iff_two_pow {bs : Fin k → β} :
    (stackOfTuple bs).isRoot ↔ ∃ n, k = 2^n := by
  rw [isRoot_iff_count_eq_two_pow_lg2, count_stackOfTuple, lg2_stackOfTuple]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h ▸ Nat.log2_two_pow ▸ rfl⟩

/-
theorem twoPowStackOfTuple_count : (twoPowStackOfTuple bs).count = 2^n := by
  induction n with | zero => _ | succ n IH => _
  · rfl
  · simp_rw [twoPowStackOfTuple_succ, count_pushTuple, IH, pow_succ', two_mul]

@[simp] theorem twoPowStackOfTuple_lg2 : (twoPowStackOfTuple bs).lg2 = n :=
  (Nat.log2_two_pow ▸ twoPowStackOfTuple_count (bs := bs) ▸
    (twoPowStackOfTuple bs).log2_count_eq_lg2).symm

@[simp] theorem twoPowStackOfTuple_size : (twoPowStackOfTuple bs).size = n + 1 := by
  rw [size_eq_lg2_succ, twoPowStackOfTuple_lg2]

@[simp] theorem twoPowStackOfTuple_isRoot : (twoPowStackOfTuple bs).isRoot := by
  rw [isRoot_iff_count_eq_two_pow_lg2, twoPowStackOfTuple_count, twoPowStackOfTuple_lg2]
-/

end StackOfTuple


#eval (bit0 (sngl 5324))

#eval List.foldl addToStack (sngl 234234) [12, 44, 5324]

#eval 5324 # 12

#eval addToStack (bit1 44 (bit1 12 (sngl 234234))) 5324


#eval BTree.finalHash 1 ![234234, 12]


#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

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


def addListToStack [Hash β] : SharedStack β → List β → SharedStack β :=
  list.foldl addToStack (List.replicate (n + 1) none)

def stackcount (s : SharedStack β) : ℕ :=
  match s with
  | [] => 0
  | (a :: s) => Nat.bit a.isSome (stackcount s)

@[simp]
theorem stackcount_nil : stackcount ([] : SharedStack β) = 0 := rfl

theorem stackcount_cons (s : SharedStack β) :
    stackcount (a :: s) = Nat.bit a.isSome s.stackcount := rfl

@[simp]
theorem stackcount_some_cons (s : SharedStack β) :
    stackcount (some a :: s) = 2 * s.stackcount + 1 := rfl

@[simp]
theorem stackcount_none_cons (s : SharedStack β) :
    stackcount (none :: s) = 2 * s.stackcount := rfl

@[simp]
theorem testBit_stackcount {s : SharedStack β} {i : ℕ} :
    s.stackcount.testBit i = if h : i < s.length then s[i].isSome else false := by
  induction' s with a s IH generalizing i
  · simp_rw [stackcount_nil, Nat.zero_testBit, List.length_nil, not_lt_zero', dite_false]
  · simp_rw [List.length_cons, stackcount_cons]
    cases' i
    · simp_rw [Nat.testBit_bit_zero, Nat.zero_lt_succ, dite_true, List.getElem_cons_zero]
    · simp_rw [Nat.testBit_bit_succ, Nat.succ_lt_succ_iff, List.getElem_cons_succ, IH]

theorem testBit_fin_length {s : SharedStack β} {i : Fin (s.length)} :
    s.stackcount.testBit i = s[(i : ℕ)].isSome := by simp_rw [testBit_stackcount, i.isLt, dite_true]

theorem finArrowBoolToNat_isSome_get_eq_stackcount (s : SharedStack β) :
    Fin.finArrowBoolToNat (fun i => Option.isSome <| s[(i : ℕ)]) = s.stackcount :=
  Nat.eq_of_testBit_eq (fun _ => Fin.testBit_finArrowBoolToNat.trans testBit_stackcount.symm)

theorem stackcount_addToStack_of_none_mem [Hash β] (s : SharedStack β) (hs : none ∈ s) (b : β) :
    stackcount (addToStack s b) = s.stackcount + 1 := by
  induction' s with a s IH generalizing b
  · simp at hs
  · cases' a
    · simp_rw [addToStack_none_cons, stackcount_some_cons, stackcount_none_cons]
    · simp at hs
      simp_rw [addToStack_some_cons, stackcount_none_cons, stackcount_some_cons, IH hs, mul_add]

theorem stackcount_eq_zero_iff_all_none (s : SharedStack β) :
    s.stackcount = 0 ↔ s = List.replicate (s.length) none := by
  induction' s with a s IH
  · simp_rw [stackcount_nil, List.length_nil, List.replicate_zero]
  · cases' a
    · simp_rw [stackcount_none_cons, mul_eq_zero, two_ne_zero, false_or,
        List.length_cons, List.replicate_succ, List.cons_eq_cons, true_and, IH]
    · simp_rw [stackcount_some_cons, Nat.add_eq_zero_iff, mul_eq_zero, one_ne_zero, and_false,
        false_iff, List.length_cons, List.replicate_succ, List.cons_eq_cons, Option.some_ne_none,
        not_and, false_implies]

theorem stackcount_pos_iff_exists_some (s : SharedStack β) :
    0 < s.stackcount ↔ ∃ a ∈ s, a.isSome := by
  simp_rw [Nat.pos_iff_ne_zero, not_iff_comm (a := s.stackcount = 0),
    stackcount_eq_zero_iff_all_none, not_exists, not_and, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, List.eq_replicate_iff, true_and]

theorem stackcount_lt_two_pow (s : SharedStack β) :
    s.stackcount < 2^(s.length) := by
  induction' s with a s IH
  · simp_rw [stackcount_nil, List.length_nil, pow_zero, zero_lt_one]
  · cases' a
    · simp_rw [stackcount_none_cons, List.length_cons, pow_succ']
      exact Nat.bit_lt_bit false false IH
    · simp_rw [stackcount_some_cons, List.length_cons, pow_succ']
      exact Nat.bit_lt_bit true false IH

theorem stackcount_le_two_pow_pred (s : SharedStack β) :
    s.stackcount ≤ 2^(s.length) - 1 := by
  rw [Nat.le_pred_iff_lt (Nat.two_pow_pos _)]
  exact s.stackcount_lt_two_pow

theorem stackcount_lt_two_pow_pred_iff_none_mem (s : SharedStack β) :
    s.stackcount < 2^(s.length) - 1 ↔ none ∈ s := by
  simp_rw [Nat.pred, Nat.lt_pred_iff]
  induction' s with a s IH
  · simp_rw [stackcount_nil, Nat.succ_eq_add_one, zero_add, List.length_nil, pow_zero,
      lt_self_iff_false, List.not_mem_nil]
  · cases' a
    · simp_rw [stackcount_none_cons, Nat.succ_eq_add_one, List.length_cons, List.mem_cons,
        true_or, iff_true, pow_succ',
        ← (Nat.ne_of_odd_add ((odd_two_mul_add_one _).add_even (even_two_mul _))).le_iff_lt,
        Nat.add_one_le_iff, Nat.mul_lt_mul_left (zero_lt_two), stackcount_lt_two_pow]
    · simp_rw [stackcount_some_cons, Nat.succ_eq_add_one, List.length_cons, List.mem_cons,
        fun x => (Option.some_ne_none x).symm, false_or, add_assoc, ← two_mul, ← mul_add,
        pow_succ', Nat.mul_lt_mul_left (zero_lt_two), IH]

theorem stackcount_eq_two_pos_pred_iff_forall_mem_isSome (s : SharedStack β) :
    s.stackcount = 2^(s.length) - 1 ↔ ∀ a ∈ s, a.isSome := Decidable.not_iff_not.mp <| by
  simp_rw [not_forall, exists_prop, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, exists_eq_right, ← stackcount_lt_two_pow_pred_iff_none_mem,
    s.stackcount_le_two_pow_pred.lt_iff_ne]

theorem testBit_stackcount_ge {s : SharedStack β} {i : ℕ} (hi : s.length ≤ i) :
    s.stackcount.testBit i = false := Nat.testBit_eq_false_of_lt <|
      s.stackcount_lt_two_pow.trans_le (Nat.pow_le_pow_of_le_right zero_lt_two hi)

theorem testBit_stackcount_lt {s : SharedStack β} {i : ℕ} (hi : i < s.length) :
    s.stackcount.testBit i = s[i].isSome := by
  induction' s with a s IH generalizing i
  · simp_rw [List.length_nil, not_lt_zero'] at hi
  · rw [List.length_cons] at hi
    simp_rw [stackcount_cons]
    cases' i
    · simp_rw [Nat.testBit_bit_zero, List.getElem_cons_zero]
    · simp_rw [Nat.testBit_bit_succ, List.getElem_cons_succ]
      exact IH _

@[simp]
theorem testBit_stackcount {s : SharedStack β} {i : ℕ} :
    s.stackcount.testBit i = if h : i < s.length then s[i].isSome else false := by
  split_ifs with hi
  · exact testBit_stackcount_lt hi
  · exact testBit_stackcount_ge (le_of_not_lt hi)

theorem testBit_fin_length {s : SharedStack β} {i : Fin (s.length)} :
    s.stackcount.testBit i = s[(i : ℕ)].isSome := by simp_rw [testBit_stackcount, i.isLt, dite_true]

theorem finArrowBoolToNat_isSome_get_eq_stackcount (s : SharedStack β) :
    Fin.finArrowBoolToNat (fun i => Option.isSome <| s[(i : ℕ)]) = s.stackcount :=
  Nat.eq_of_testBit_eq (fun _ => Fin.testBit_finArrowBoolToNat.trans testBit_stackcount.symm)

theorem lt_length_of_stackcount_eq_two_pow [Hash β] {s : SharedStack β} {i : ℕ}
    (hs : s.stackcount = 2^i) : i < s.length := by
  rw [← Nat.pow_lt_pow_iff_right one_lt_two, ← hs]
  exact s.stackcount_lt_two_pow

theorem getElem_isSome_eq_decide_of_stackcount_eq_two_pow [Hash β] {s : SharedStack β} {i k : ℕ}
    (hs : s.stackcount = 2^i) (hk : k < s.length) : s[k].isSome = decide (i = k) := by
  have hs := congrArg (Nat.testBit · k) hs
  simp_rw [testBit_stackcount, Nat.testBit_two_pow, dif_pos hk] at hs
  exact hs

theorem getElem_isSome_of_stackcount_eq_two_pow [Hash β] {s : SharedStack β} {i : ℕ}
    (hs : s.stackcount = 2^i) : (s[i]'(lt_length_of_stackcount_eq_two_pow hs)).isSome := by
  simp_rw [getElem_isSome_eq_decide_of_stackcount_eq_two_pow hs, decide_True]

theorem getElem_eq_none_of_ne_of_stackcount_eq_two_pow [Hash β] {s : SharedStack β} {i k : ℕ}
    (hs : s.stackcount = 2^i) (hk : k < s.length) (hk' : i ≠ k) : s[k] = none := by
  simp_rw [← Option.not_isSome_iff_eq_none,
    getElem_isSome_eq_decide_of_stackcount_eq_two_pow hs, hk', decide_False,
    Bool.false_eq_true, not_false_eq_true]



theorem addToStack_ne_nil [Hash β] (s : SharedStack β) (b : β) :
    addToStack s b ≠ [] := by
  rcases s with (_ | ⟨(_ | _), _⟩) <;> exact List.cons_ne_nil _ _

theorem length_addToStack_pos [Hash β] (s : SharedStack β) (b : β) :
    0 < (addToStack s b).length := List.length_pos.mpr <| addToStack_ne_nil _ _

theorem length_addToStack_of_mem_none [Hash β] (s : SharedStack β) (hs : none ∈ s) :
    ∀ b, (addToStack s b).length = s.length := by
  induction' s with a s IH
  · simp_rw [List.not_mem_nil] at hs
  · cases' a
    · simp_rw [addToStack_none_cons, List.length_cons, implies_true]
    · simp_rw [List.mem_cons, Option.none_ne_some, false_or] at hs
      simp_rw [addToStack_some_cons, List.length_cons, add_left_inj, IH hs, implies_true]

theorem blahj [Hash β] {s : SharedStack β} {i : ℕ} (hi : i < s.length) (hsi : s[i] = none) :
    ∀ b, (addToStack s b).length = s.length := by
  induction' s with a s IH
  · simp_rw [List.not_mem_nil] at hs
  · cases' a
    · simp_rw [addToStack_none_cons, List.length_cons, implies_true]
    · simp_rw [List.mem_cons, Option.none_ne_some, false_or] at hs
      simp_rw [addToStack_some_cons, List.length_cons, add_left_inj, IH hs, implies_true]

theorem addToStack_eq_replicate_append_singleton_of_not_mem_none [Hash β] (s : SharedStack β)
    (hs : none ∉ s) : ∀ b, ∃ b', addToStack s b =
    List.replicate (s.length) none ++ [some b'] := by
  induction' s with a s IH
  · refine fun b => ⟨b, ?_⟩
    simp_rw [addToStack_nil, List.length_nil, List.replicate_zero, List.nil_append]
  · cases' a
    · simp_rw [List.mem_cons, true_or, not_true_eq_false] at hs
    · simp_rw [List.mem_cons, Option.none_ne_some, false_or] at hs
      simp_rw [addToStack_some_cons, List.length_cons, List.replicate_succ,
        List.cons_append, List.cons_eq_cons, true_and]
      exact fun b => IH hs (_ # b)

theorem length_addToStack_of_not_mem_none [Hash β] (s : SharedStack β) (hs : none ∉ s) (b : β) :
    (addToStack s b).length = s.length + 1 := by
  rcases addToStack_eq_replicate_append_singleton_of_not_mem_none _ hs b with ⟨b', h⟩
  rw [h, List.length_append, List.length_replicate, List.length_singleton]

@[simp]
theorem stackcount_addToStack [Hash β] (s : SharedStack β) (b : β) :
    stackcount (addToStack s b) = s.stackcount + 1 := by
  induction' s with a s IH generalizing b
  · simp_rw [addToStack_nil, stackcount_some_cons, stackcount_nil]
  · cases' a
    · simp_rw [addToStack_none_cons, stackcount_some_cons, stackcount_none_cons]
    · simp_rw [addToStack_some_cons, stackcount_none_cons, stackcount_some_cons, IH, mul_add]

theorem stackcount_addToStack_ne_zero [Hash β] (s : SharedStack β) (b : β) :
    stackcount (addToStack s b) ≠ 0 := by
  rw [stackcount_addToStack] ; exact Nat.succ_ne_zero _

def addStackOfTuple [Hash β] (s : SharedStack β) (bs : Fin k → β) : SharedStack β :=
  Fin.tuple_foldl addToStack s bs

@[simp]
theorem addStackOfTuple_zero [Hash β] (s : SharedStack β) (bs : Fin 0 → β) :
    addStackOfTuple s bs = s := Fin.foldl_zero _ _

@[simp]
theorem addStackOfTuple_succ [Hash β] (s : SharedStack β) (bs : Fin (k + 1) → β) :
    addStackOfTuple s bs = addStackOfTuple (addToStack s (bs 0)) (Fin.tail bs) :=
  Fin.foldl_succ _ _

theorem addStackOfTuple_succ_last [Hash β] (s : SharedStack β) (bs : Fin (k + 1) → β) :
    addStackOfTuple s bs = addToStack (addStackOfTuple s (Fin.init bs)) (bs (Fin.last k)) :=
  Fin.foldl_succ_last _ _

theorem length_addStackOfTuple_pos [Hash β] [NeZero k] (s : SharedStack β) (bs : Fin k → β) :
    0 < (addStackOfTuple s bs).length := by
  rcases (Nat.exists_eq_succ_of_ne_zero <| NeZero.ne k) with ⟨k, rfl⟩
  rw [addStackOfTuple_succ_last]
  exact length_addToStack_pos _ _

theorem stackcount_addStackOfTuple [Hash β] (s : SharedStack β) (bs : Fin k → β) :
    stackcount (addStackOfTuple s bs) = s.stackcount + k := by
  induction' k with k IH generalizing s
  · simp_rw [addStackOfTuple_zero, add_zero]
  · simp_rw [addStackOfTuple_succ_last, stackcount_addToStack, IH, add_assoc]

theorem addStackOfTuple_two_pow_succ [Hash β] (s : SharedStack β) (bs : Fin (2 ^ (n + 1)) → β) :
    addStackOfTuple s bs = addStackOfTuple (addStackOfTuple s (twoPowSuccTupleDivide bs).1)
    (twoPowSuccTupleDivide bs).2 :=
  Fin.tuple_foldl_two_pow_succ _ _ _

def finalHashStack [Hash β] (n : ℕ) (bs : Fin (2^n) → β) : SharedStack β := addStackOfTuple [] bs

theorem stackcount_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    stackcount (finalHashStack n bs) = 2^n :=
  (stackcount_addStackOfTuple _ _).trans (zero_add _)

theorem lt_length_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    n < (finalHashStack n bs).length :=
  lt_length_of_stackcount_eq_two_pow stackcount_finalHashStack

theorem getElem_isSome_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    ((finalHashStack n bs)[n]'lt_length_finalHashStack).isSome :=
  getElem_isSome_of_stackcount_eq_two_pow stackcount_finalHashStack

theorem finalHashStack_zero [Hash β] (bs : Fin (2^0) → β) : finalHashStack 0 bs = [some (bs 0)] := by
  refine (addStackOfTuple_succ _ _).trans ?_
  simp_rw [addStackOfTuple_zero, addToStack_nil]

theorem finalHashStack_succ [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHashStack (n + 1) bs =
  addStackOfTuple (finalHashStack n (twoPowSuccTupleDivide bs).1)
  ((twoPowSuccTupleDivide bs).2) := addStackOfTuple_two_pow_succ _ _

end SharedStack


instance : Hash UInt64 := ⟨fun a b => hash (a, b)⟩

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).count⟩


#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

#eval SharedStack.finalHash 2 ![234234, 12, 44, 5324]
