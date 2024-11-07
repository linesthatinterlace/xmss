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

def finalHash : (n : ℕ) → (Fin (2^n) → β) → β
  | 0, t => t 0
  | (n + 1), t =>
    let (f, l) := twoPowSuccTupleDivide t
    (finalHash n f) # (finalHash n l)

def finalHash' (n : ℕ) (bs : Fin (2^n) → β) : β := root (listOfTree bs)

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

inductive PSharedStack (β : Type u) : Type u
  | sngl : β → PSharedStack β
  | bit0 : PSharedStack β → PSharedStack β
  | bit1 : β → PSharedStack β → PSharedStack β
deriving DecidableEq

namespace PSharedStack
variable {β : Type*} {a b : β} {p : PSharedStack β} {n : ℕ}

instance [Inhabited β] : Inhabited (PSharedStack β) where
  default := sngl default

def toList : PSharedStack β → List (Option β)
  | sngl a => [some a]
  | bit0 p => none :: p.toList
  | bit1 a p => some a :: p.toList

@[simp] theorem toList_sngl : (sngl a).toList = [some a] := rfl
@[simp] theorem toList_bit0 : (bit0 p).toList = none :: p.toList := rfl
@[simp] theorem toList_bit1 : (bit1 a p).toList = some a :: p.toList := rfl

@[simp] theorem toList_ne_nil : p.toList ≠ [] := by
  cases p <;> exact List.noConfusion

instance [Repr β] : Repr (PSharedStack β) where
  reprPrec := fun p => reprPrec (p.toList)

def size : PSharedStack β → ℕ
  | sngl _ => 1
  | bit0 p => p.size.succ
  | bit1 _ p => p.size.succ

@[simp] theorem size_sngl : (sngl a).size = 1 := rfl
@[simp] theorem size_bit0 : (bit0 p).size = p.size + 1 := rfl
@[simp] theorem size_bit1 : (bit1 a p).size = p.size + 1 := rfl

@[simp] theorem size_ne_zero : p.size ≠ 0 := by
  cases p <;> exact Nat.noConfusion

@[simp] theorem size_pos : 0 < p.size := Nat.pos_of_ne_zero size_ne_zero

@[simp] theorem one_le_size : 1 ≤ p.size := size_pos

@[simp]
theorem length_toList : (toList p).length = p.size :=
  p.recOn (fun _ => rfl) (fun _ => congrArg _) (fun _ _ => congrArg _)

def count : PSharedStack β → ℕ
  | sngl _ => 1
  | bit0 s => Nat.bit false s.count
  | bit1 _ s => Nat.bit true s.count

@[simp] theorem count_sngl : (sngl a).count = 1 := rfl
@[simp] theorem count_bit0 : (bit0 p).count = Nat.bit false p.count := rfl
@[simp] theorem count_bit1 : (bit1 a p).count = Nat.bit true p.count := rfl

@[simp] theorem count_ne_zero : p.count ≠ 0 :=
  p.recOn (fun _ => Nat.noConfusion) (fun _ => Nat.bit_ne_zero _) (fun _ _ => Nat.bit_ne_zero _)

@[simp] theorem count_pos : 0 < p.count := Nat.pos_of_ne_zero count_ne_zero

@[simp] theorem one_le_count : 1 ≤ p.count := count_pos

theorem bit0_count_ne_one : (bit0 p).count ≠ 1 := by
  simp_rw [count_bit0, Nat.bit_false, mul_ne_one]
  exact Or.inl (Nat.succ_succ_ne_one 0)

theorem bit1_count_ne_one : (bit1 a p).count ≠ 1 := by
  simp_rw [count_bit1, Nat.bit_true, Nat.succ_ne_succ, mul_ne_zero_iff]
  exact ⟨two_ne_zero, count_ne_zero⟩

def testBit : PSharedStack β → ℕ → Bool
  | sngl _, 0 => true
  | sngl _, (_ + 1) => false
  | bit0 _, 0 => false
  | bit0 s, (n + 1) => s.testBit n
  | bit1 _ _, 0 => true
  | bit1 _ s, (n + 1) => s.testBit n

@[simp] theorem testBit_sngl_zero : (sngl a).testBit 0 = true := rfl
@[simp] theorem testBit_sngl_succ : (sngl a).testBit (n + 1) = false := rfl

@[simp] theorem testBit_sngl : (sngl a).testBit n = decide (n = 0) :=
  n.casesOn testBit_sngl_zero (fun _ => testBit_sngl_succ)

@[simp] theorem testBit_bit0_zero : (bit0 p).testBit 0 = false := rfl
@[simp] theorem testBit_bit0_succ : (bit0 p).testBit (n + 1) = p.testBit n := rfl
@[simp] theorem testBit_bit1_zero : (bit1 a p).testBit 0 = true := rfl
@[simp] theorem testBit_bit1_succ : (bit1 a p).testBit (n + 1) = p.testBit n := rfl

theorem testBit_of_ge : p.size ≤ n → p.testBit n = false := by
  · induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _ <;> cases n <;>
    try {exact fun h => (size_ne_zero (Nat.eq_zero_of_le_zero h)).elim} <;>
    try {exact fun h => IH (Nat.le_of_succ_le_succ h)}
    exact fun _ => rfl

@[simp]
theorem testBit_count : p.count.testBit n = p.testBit n := by
  induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _ <;>
  [rw [count_sngl]; rw [count_bit0]; rw [count_bit1]] <;> cases n
  · simp_rw [Nat.testBit_one_zero, testBit_sngl_zero]
  · simp_rw [testBit_sngl_succ, Nat.testBit_succ,
      Nat.div_eq_of_lt (one_lt_two), Nat.zero_testBit]
  · simp_rw [testBit_bit0_zero, Nat.testBit_bit_zero]
  · simp_rw [testBit_bit0_succ, Nat.testBit_bit_succ]
    exact IH
  · simp_rw [testBit_bit1_zero, Nat.testBit_bit_zero]
  · simp_rw [testBit_bit1_succ, Nat.testBit_bit_succ]
    exact IH

def last : PSharedStack β → β
  | sngl a => a
  | bit0 p => p.last
  | bit1 _ p => p.last

@[simp] theorem last_sngl : (sngl a).last = a := rfl
@[simp] theorem last_bit0 : (bit0 p).last = p.last := rfl
@[simp] theorem last_bit1 : (bit1 a p).last = p.last := rfl

def pop : PSharedStack β → β
  | sngl a => a
  | bit0 p => p.pop
  | bit1 a _ => a

@[simp] theorem pop_sngl : (sngl a).pop = a := rfl
@[simp] theorem pop_bit0 : (bit0 p).pop = p.pop := rfl
@[simp] theorem pop_bit1 : (bit1 a p).pop = a := rfl

inductive isSingle : PSharedStack β → Prop
  | sngl : {a : β} → isSingle (sngl a)

attribute [simp] isSingle.sngl

@[simp] theorem isSingle.not_bit0 : ¬ (bit0 p).isSingle := fun h => by contradiction

@[simp] theorem isSingle.not_bit1 : ¬ (bit1 a p).isSingle := fun h => by contradiction

theorem isSingle_iff_count_eq_one : p.isSingle ↔ p.count = 1 := by
  cases p
  · exact iff_of_true isSingle.sngl count_sngl
  · exact iff_of_false isSingle.not_bit0 bit0_count_ne_one
  · exact iff_of_false isSingle.not_bit1 bit1_count_ne_one

inductive isRoot : PSharedStack β → Prop
  | sngl : (a : β) → isRoot (sngl a)
  | bit0_of : (p : PSharedStack β) → p.isRoot → isRoot (bit0 p)

@[simp] theorem isRoot_sngl : (sngl a).isRoot := by constructor

@[simp] theorem not_isRoot_bit1 : ¬ (bit1 a p).isRoot := fun h => by contradiction

@[simp] theorem isRoot_bit0_iff : (bit0 p).isRoot ↔ p.isRoot :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem count_eq_two_pow_size_of_isRoot (h : p.isRoot) : p.count = 2^(p.size - 1) := by
  apply Nat.eq_of_testBit_eq
  simp_rw [testBit_count, Nat.testBit_two_pow]
  induction h with | sngl a => _ | bit0_of p hp IH => _
  · simp_rw [testBit_sngl, size_sngl, Nat.sub_self, decide_eq_decide, eq_comm, implies_true]
  · rintro (_ | i)
    · simp_rw [testBit_bit0_zero, size_bit0, Nat.add_sub_cancel, size_ne_zero, decide_False]
    · simp_rw [testBit_bit0_succ, size_bit0, Nat.add_sub_cancel, IH, decide_eq_decide,
      Nat.sub_eq_iff_eq_add one_le_size]

theorem isRoot_of_count_eq_two_pow_size (h : p.count = 2^(p.size - 1)) : p.isRoot := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · exact isRoot_sngl
  · simp_rw [isRoot_bit0_iff]
    apply IH
    rw [← Nat.pow_div one_le_size zero_lt_two, pow_one]
    exact Nat.eq_div_of_mul_eq_right (two_ne_zero) h
  · have H := congrArg (· % 2) h
    simp_rw [count_bit1, size_bit1, Nat.add_sub_cancel, Nat.bit_true, Nat.mul_add_mod,
      Nat.one_mod, eq_comm (a := 1), Nat.two_pow_mod_two_eq_one, size_ne_zero] at H

theorem isRoot_iff_count_eq_two_pow_size : p.isRoot ↔ p.count = 2^(p.size - 1) :=
  ⟨count_eq_two_pow_size_of_isRoot, isRoot_of_count_eq_two_pow_size⟩

inductive isMaxed : PSharedStack β → Prop
  | sngl : (a : β) → isMaxed (sngl a)
  | bit1_of : (a : β) → (p : PSharedStack β) → p.isMaxed → isMaxed (bit1 a p)

@[simp] theorem isMaxed_sngl : (sngl a).isMaxed := by constructor

@[simp] theorem not_isMaxed_bit0 : ¬ (bit0 p).isMaxed:= fun h => by contradiction

@[simp] theorem isMaxed_bit1_iff : (bit1 a p).isMaxed ↔ p.isMaxed :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem count_eq_two_pow_size_sub_one_of_isMaxed (h : p.isMaxed) : p.count = 2^p.size - 1 := by
  apply Nat.eq_of_testBit_eq
  simp_rw [testBit_count, Nat.testBit_two_pow_sub_one]
  induction h with | sngl a => _ | bit1_of a p hp IH => _
  · simp_rw [testBit_sngl, size_sngl, Nat.lt_one_iff, implies_true]
  · rintro (_ | i)
    · simp_rw [testBit_bit1_zero, size_bit1, Nat.zero_lt_succ, decide_True]
    · simp_rw [testBit_bit1_succ, size_bit1, Nat.succ_lt_succ_iff, IH]

theorem isMaxed_of_count_eq_two_pow_size_sub_one (h : p.count = 2^p.size - 1) : p.isMaxed := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · exact isMaxed_sngl
  · sorry
  · simp_rw [isMaxed_bit1_iff]
    apply IH
    simp at h
    rw [← Nat.pow_div one_le_size zero_lt_two, pow_one]
    exact Nat.eq_div_of_mul_eq_right (two_ne_zero) h
  · have H := congrArg (· % 2) h
    simp_rw [count_bit1, size_bit1, Nat.add_sub_cancel, Nat.bit_true, Nat.mul_add_mod,
      Nat.one_mod, eq_comm (a := 1), Nat.two_pow_mod_two_eq_one, size_ne_zero] at H

theorem isRoot_iff_count_eq_two_pow_size : p.isRoot ↔ p.count = 2^(p.size - 1) :=
  ⟨count_eq_two_pow_size_of_isRoot, isRoot_of_count_eq_two_pow_size⟩

theorem isSingle_iff_isMaxed_and_isRoot : p.isSingle ↔ (p.isMaxed ∧ p.isRoot) := by
  cases p
  · exact iff_of_true isSingle.sngl ⟨isMaxed_sngl, isRoot_sngl⟩
  · exact iff_of_false isSingle.not_bit0 (fun h => not_isMaxed_bit0 h.1)
  · exact iff_of_false isSingle.not_bit1 (fun h => not_isRoot_bit1 h.2)

section variable [Hash β]

def push : PSharedStack β → β → PSharedStack β
  | sngl a, b => bit0 (sngl (a # b))
  | bit0 p, b => bit1 b p
  | bit1 a p, b => bit0 (p.push (a # b))

@[simp] theorem push_sngl : (sngl a).push b = bit0 (sngl (a # b)) := rfl
@[simp] theorem push_bit0 : (bit0 p).push b = bit1 b p := rfl
@[simp] theorem push_bit1 : (bit1 a p).push b = bit0 (p.push (a # b)) := rfl

@[simp] theorem push_ne_sngl : p.push b ≠ sngl a := by
  cases p <;> exact PSharedStack.noConfusion

@[simp]
theorem count_push : (p.push b).count = p.count.succ := by
  induction p generalizing b with | sngl => rfl | bit0 => rfl | bit1 _ _ IH => exact congrArg _ IH

end


end PSharedStack

inductive SharedStack (β : Type u) : Type u
  | emp : SharedStack β
  | pst : PSharedStack β → SharedStack β
deriving DecidableEq

namespace SharedStack

open PSharedStack

variable {β : Type*} {a b : β} {p : PSharedStack β} {s : SharedStack β}

instance : Inhabited (SharedStack β) where
  default := emp

def toList (s : SharedStack β) : List (Option β) := s.casesOn [] PSharedStack.toList

@[simp] theorem toList_emp : (emp : SharedStack β).toList = [] := rfl
@[simp] theorem toList_pst : (pst p).toList = p.toList := rfl

@[simp] theorem toList_eq_nil : s.toList = [] ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl) (fun p => iff_of_false p.toList_ne_nil SharedStack.noConfusion)

def size (s : SharedStack β) : ℕ := s.casesOn 0 PSharedStack.size

@[simp] theorem size_emp : (emp : SharedStack β).size = 0 := rfl
@[simp] theorem size_pst : (pst p).size = p.size := rfl

@[simp] theorem size_eq_zero : s.size = 0 ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl) (fun p => iff_of_false p.size_ne_zero SharedStack.noConfusion)

@[simp] theorem size_pos : 0 < s.size ↔ ∃ p, s = pst p :=
  s.casesOn
    (iff_of_false (lt_irrefl _) (fun ⟨_, h⟩ => SharedStack.noConfusion h))
    (fun p => iff_of_true p.size_pos ⟨p, rfl⟩)

@[simp]
theorem length_toList : (toList s).length = s.size := s.recOn rfl fun p => p.length_toList

instance [Repr β] : Repr (SharedStack β) where
  reprPrec := fun s => reprPrec (s.toList)

def count (s : SharedStack β) : ℕ := s.casesOn 0 PSharedStack.count

@[simp] theorem count_emp : (emp : SharedStack β).count = 0 := rfl
@[simp] theorem count_pst : (pst p).count = p.count := rfl

@[simp] theorem count_eq_zero : s.count = 0 ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl) (fun p => iff_of_false p.count_ne_zero SharedStack.noConfusion)

@[simp] theorem count_pos : 0 < s.count ↔ ∃ p, s = pst p :=
  s.casesOn
    (iff_of_false (lt_irrefl _) (fun ⟨_, h⟩ => SharedStack.noConfusion h))
    (fun p => iff_of_true p.count_pos ⟨p, rfl⟩)

def last? (s : SharedStack β) : Option β := s.casesOn none (fun p => some (p.last))

@[simp] theorem last?_emp : (emp : SharedStack β).last? = none := rfl
@[simp] theorem last?_pst : (pst p).last? = some p.last := rfl

def last (s : SharedStack β) (hs : s.count ≠ 0) : β := match s with
  | emp => ((hs count_emp).elim)
  | pst p => p.last

@[simp] theorem last_pst {hs : (pst p).count ≠ 0} : (pst p).last hs = p.last := rfl

def pop? (s : SharedStack β) : Option β := s.casesOn none (fun p => some (p.pop))

@[simp] theorem pop?_emp : (emp : SharedStack β).pop? = none := rfl
@[simp] theorem pop?_pst : (pst p).pop? = some p.pop := rfl

def pop (s : SharedStack β) (hs : s.count ≠ 0) : β := match s with
  | emp => ((hs count_emp).elim)
  | pst p => p.pop

@[simp] theorem pop_pst {hs : (pst p).count ≠ 0} : (pst p).pop hs = p.pop := rfl

def testBit (s : SharedStack β) (n : ℕ) : Bool := s.casesOn false (fun p => p.testBit n)

@[simp] theorem testBit_emp : (emp : SharedStack β).testBit n = false := rfl
@[simp] theorem testBit_pst : (pst p).testBit n = p.testBit n := rfl

theorem testBit_of_ge : s.size ≤ n → s.testBit n = false :=
  s.casesOn (fun _ => rfl) (fun p => p.testBit_of_ge)

theorem testBit_count : s.count.testBit n = s.testBit n :=
  s.casesOn (Nat.zero_testBit _) (fun p => p.testBit_count)

section variable [Hash β]

def push (s : SharedStack β) : β → SharedStack β :=
  s.casesOn (fun a => pst (sngl a)) (fun p b => pst (p.push b))

@[simp] theorem push_emp : (emp : SharedStack β).push a = pst (sngl a) := rfl
@[simp] theorem push_pst : (pst p).push b = pst (p.push b) := rfl

@[simp] theorem push_ne_emp : s.push b ≠ emp := by
  cases s <;> exact SharedStack.noConfusion

@[simp]
theorem count_push : (s.push b).count = s.count.succ := s.casesOn rfl (fun p => p.count_push)

end

theorem length_toList_ne_zero {s : SharedStack β} : (toList s).length ≠ 0 :=
  length_toList ▸ Nat.noConfusion

theorem toList_ne_nil {s : SharedStack β} : toList s ≠ [] := by
  cases s <;> exact List.noConfusion

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).count⟩

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

theorem stackcount_le_two_pow_sub_one (s : SharedStack β) :
    s.stackcount ≤ 2^(s.length) - 1 := by
  rw [Nat.le_sub_one_iff_lt (Nat.two_pow_pos _)]
  exact s.stackcount_lt_two_pow

theorem stackcount_lt_two_pow_pred_iff_none_mem (s : SharedStack β) :
    s.stackcount < 2^(s.length) - 1 ↔ none ∈ s := by
  simp_rw [Nat.sub_one, Nat.lt_pred_iff]
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
    s.stackcount_le_two_pow_sub_one.lt_iff_ne]

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

def addTupleToStack [Hash β] (s : SharedStack β) (bs : Fin k → β) : SharedStack β :=
  Fin.tuple_foldl addToStack s bs

@[simp]
theorem addTupleToStack_zero [Hash β] (s : SharedStack β) (bs : Fin 0 → β) :
    addTupleToStack s bs = s := Fin.foldl_zero _ _

@[simp]
theorem addTupleToStack_succ [Hash β] (s : SharedStack β) (bs : Fin (k + 1) → β) :
    addTupleToStack s bs = addTupleToStack (addToStack s (bs 0)) (Fin.tail bs) :=
  Fin.foldl_succ _ _

theorem addTupleToStack_succ_last [Hash β] (s : SharedStack β) (bs : Fin (k + 1) → β) :
    addTupleToStack s bs = addToStack (addTupleToStack s (Fin.init bs)) (bs (Fin.last k)) :=
  Fin.foldl_succ_last _ _

theorem length_addTupleToStack_pos [Hash β] [NeZero k] (s : SharedStack β) (bs : Fin k → β) :
    0 < (addTupleToStack s bs).length := by
  rcases (Nat.exists_eq_succ_of_ne_zero <| NeZero.ne k) with ⟨k, rfl⟩
  rw [addTupleToStack_succ_last]
  exact length_addToStack_pos _ _

theorem stackcount_addTupleToStack [Hash β] (s : SharedStack β) (bs : Fin k → β) :
    stackcount (addTupleToStack s bs) = s.stackcount + k := by
  induction' k with k IH generalizing s
  · simp_rw [addTupleToStack_zero, add_zero]
  · simp_rw [addTupleToStack_succ_last, stackcount_addToStack, IH, add_assoc]

theorem addTupleToStack_two_pow_succ [Hash β] (s : SharedStack β) (bs : Fin (2 ^ (n + 1)) → β) :
    addTupleToStack s bs = addTupleToStack (addTupleToStack s (twoPowSuccTupleDivide bs).1)
    (twoPowSuccTupleDivide bs).2 :=
  Fin.tuple_foldl_two_pow_succ _ _ _

def finalHashStack [Hash β] (n : ℕ) (bs : Fin (2^n) → β) : SharedStack β := addTupleToStack [] bs

theorem stackcount_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    stackcount (finalHashStack n bs) = 2^n :=
  (stackcount_addTupleToStack _ _).trans (zero_add _)

theorem lt_length_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    n < (finalHashStack n bs).length :=
  lt_length_of_stackcount_eq_two_pow stackcount_finalHashStack

theorem getElem_isSome_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    ((finalHashStack n bs)[n]'lt_length_finalHashStack).isSome :=
  getElem_isSome_of_stackcount_eq_two_pow stackcount_finalHashStack

theorem finalHashStack_zero [Hash β] (bs : Fin (2^0) → β) : finalHashStack 0 bs = [some (bs 0)] := by
  refine (addTupleToStack_succ _ _).trans ?_
  simp_rw [addTupleToStack_zero, addToStack_nil]

theorem finalHashStack_succ [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHashStack (n + 1) bs =
  addTupleToStack (finalHashStack n (twoPowSuccTupleDivide bs).1)
  ((twoPowSuccTupleDivide bs).2) := addTupleToStack_two_pow_succ _ _

end SharedStack


instance : Hash UInt64 := ⟨fun a b => hash (a, b)⟩

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).count⟩


#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

#eval SharedStack.finalHash 2 ![234234, 12, 44, 5324]
