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

inductive SharedStack (β : Type u) : Type u
  | sngl : β → SharedStack β
  | bit0 : SharedStack β → SharedStack β
  | bit1 : β → SharedStack β → SharedStack β
deriving DecidableEq

namespace SharedStack

variable {n m : ℕ} {β : Type*} {b : β} {s : SharedStack β}

def size : SharedStack β → ℕ
  | sngl _ => 1
  | bit0 s => s.size + 1
  | bit1 _ s => s.size + 1

def toListOption : SharedStack β → List (Option β)
  | sngl b => [some b]
  | bit0 s => none :: toListOption s
  | bit1 b s => some b :: toListOption s

@[simp]
theorem toListOption_sngl : toListOption (sngl b) = ([some b] : List (Option β)) := rfl

@[simp]
theorem toListOption_bit0 : toListOption (bit0 s) = none :: toListOption s := rfl

@[simp]
theorem toListOption_bit1 : toListOption (bit1 b s) = some b :: toListOption s := rfl

@[simp]
theorem length_toListOption : {s : SharedStack β} → (toListOption s).length = s.size
  | sngl _ => rfl
  | bit0 _ => congrArg _ length_toListOption
  | bit1 _ _ => congrArg _ length_toListOption

theorem length_toListOption_ne_zero {s : SharedStack β} : (toListOption s).length ≠ 0 :=
  length_toListOption ▸ Nat.noConfusion

theorem toListOption_ne_nil {s : SharedStack β} : toListOption s ≠ [] := by
  cases s <;> exact List.noConfusion

instance [Repr β] : Repr (SharedStack β) where
  reprPrec := fun s => reprPrec (s.toListOption)

instance  [Inhabited β] : Inhabited (SharedStack β) where
  default := sngl default

def stackToNat (s : SharedStack β) : ℕ := match s with
  | sngl _ => 1
  | bit0 s => Nat.bit false (stackToNat s)
  | bit1 _ s => Nat.bit true (stackToNat s)

@[simp]
theorem stackToNat_sngl : stackToNat (sngl b : SharedStack β) = 1 := rfl

@[simp]
theorem stackToNat_bit0 : stackToNat (bit0 s) = Nat.bit false s.stackToNat := rfl

@[simp]
theorem stackToNat_bit1 : stackToNat (bit1 b s) = Nat.bit true s.stackToNat := rfl


def addToStack [Hash β]  (s : SharedStack β) (b : β) : SharedStack β := match s with
  | sngl a => bit0 (sngl (a # b))
  | bit0 s => bit1 b s
  | bit1 a s => bit0 (addToStack s (a # b))

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).toNat⟩

#eval (bit0 (sngl 5324))

#eval List.foldl addToStack (sngl 234234) [12, 44, 5324]

#eval 5324 # 12

#eval addToStack (bit1 44 (bit1 12 (sngl 234234))) 5324


#eval BTree.finalHash 1 ![234234, 12]


#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

@[simp]
theorem addToStack_nil [Hash β] (b : β) : addToStack [] b = [some b] := rfl

@[simp]
theorem addToStack_none_cons [Hash β] (s : SharedStack β) (b : β) :
    addToStack (none :: s) b = some b :: s := rfl

@[simp]
theorem addToStack_some_cons [Hash β] (s : SharedStack β) (b : β) :
    addToStack (some a :: s) b = none :: addToStack s (a # b) := rfl

theorem stackToNat_eq_zero_iff_all_none (s : SharedStack β) :
    s.stackToNat = 0 ↔ s = List.replicate (s.length) none := by
  induction' s with a s IH
  · simp_rw [stackToNat_nil, List.length_nil, List.replicate_zero]
  · cases' a
    · simp_rw [stackToNat_none_cons, mul_eq_zero, two_ne_zero, false_or,
        List.length_cons, List.replicate_succ, List.cons_eq_cons, true_and, IH]
    · simp_rw [stackToNat_some_cons, Nat.add_eq_zero_iff, mul_eq_zero, one_ne_zero, and_false,
        false_iff, List.length_cons, List.replicate_succ, List.cons_eq_cons, Option.some_ne_none,
        not_and, false_implies]

theorem stackToNat_pos_iff_exists_some (s : SharedStack β) :
    0 < s.stackToNat ↔ ∃ a ∈ s, a.isSome := by
  simp_rw [Nat.pos_iff_ne_zero, not_iff_comm (a := s.stackToNat = 0),
    stackToNat_eq_zero_iff_all_none, not_exists, not_and, Bool.not_eq_true, Option.not_isSome,
    Option.isNone_iff_eq_none, List.eq_replicate_iff, true_and]

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

theorem testBit_stackToNat_ge {s : SharedStack β} {i : ℕ} (hi : s.length ≤ i) :
    s.stackToNat.testBit i = false := Nat.testBit_eq_false_of_lt <|
      s.stackToNat_lt_two_pow.trans_le (Nat.pow_le_pow_of_le_right zero_lt_two hi)

theorem testBit_stackToNat_lt {s : SharedStack β} {i : ℕ} (hi : i < s.length) :
    s.stackToNat.testBit i = s[i].isSome := by
  induction' s with a s IH generalizing i
  · simp_rw [List.length_nil, not_lt_zero'] at hi
  · rw [List.length_cons] at hi
    simp_rw [stackToNat_cons]
    cases' i
    · simp_rw [Nat.testBit_bit_zero, List.getElem_cons_zero]
    · simp_rw [Nat.testBit_bit_succ, List.getElem_cons_succ]
      exact IH _

@[simp]
theorem testBit_stackToNat {s : SharedStack β} {i : ℕ} :
    s.stackToNat.testBit i = if h : i < s.length then s[i].isSome else false := by
  split_ifs with hi
  · exact testBit_stackToNat_lt hi
  · exact testBit_stackToNat_ge (le_of_not_lt hi)

theorem testBit_fin_length {s : SharedStack β} {i : Fin (s.length)} :
    s.stackToNat.testBit i = s[(i : ℕ)].isSome := by simp_rw [testBit_stackToNat, i.isLt, dite_true]

theorem finArrowBoolToNat_isSome_get_eq_stackToNat (s : SharedStack β) :
    Fin.finArrowBoolToNat (fun i => Option.isSome <| s[(i : ℕ)]) = s.stackToNat :=
  Nat.eq_of_testBit_eq (fun _ => Fin.testBit_finArrowBoolToNat.trans testBit_stackToNat.symm)

theorem lt_length_of_stackToNat_eq_two_pow [Hash β] {s : SharedStack β} {i : ℕ}
    (hs : s.stackToNat = 2^i) : i < s.length := by
  rw [← Nat.pow_lt_pow_iff_right one_lt_two, ← hs]
  exact s.stackToNat_lt_two_pow

theorem getElem_isSome_eq_decide_of_stackToNat_eq_two_pow [Hash β] {s : SharedStack β} {i k : ℕ}
    (hs : s.stackToNat = 2^i) (hk : k < s.length) : s[k].isSome = decide (i = k) := by
  have hs := congrArg (Nat.testBit · k) hs
  simp_rw [testBit_stackToNat, Nat.testBit_two_pow, dif_pos hk] at hs
  exact hs

theorem getElem_isSome_of_stackToNat_eq_two_pow [Hash β] {s : SharedStack β} {i : ℕ}
    (hs : s.stackToNat = 2^i) : (s[i]'(lt_length_of_stackToNat_eq_two_pow hs)).isSome := by
  simp_rw [getElem_isSome_eq_decide_of_stackToNat_eq_two_pow hs, decide_True]

theorem getElem_eq_none_of_ne_of_stackToNat_eq_two_pow [Hash β] {s : SharedStack β} {i k : ℕ}
    (hs : s.stackToNat = 2^i) (hk : k < s.length) (hk' : i ≠ k) : s[k] = none := by
  simp_rw [← Option.not_isSome_iff_eq_none,
    getElem_isSome_eq_decide_of_stackToNat_eq_two_pow hs, hk', decide_False,
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
theorem stackToNat_addToStack [Hash β] (s : SharedStack β) (b : β) :
    stackToNat (addToStack s b) = s.stackToNat + 1 := by
  induction' s with a s IH generalizing b
  · simp_rw [addToStack_nil, stackToNat_some_cons, stackToNat_nil]
  · cases' a
    · simp_rw [addToStack_none_cons, stackToNat_some_cons, stackToNat_none_cons]
    · simp_rw [addToStack_some_cons, stackToNat_none_cons, stackToNat_some_cons, IH, mul_add]

theorem stackToNat_addToStack_ne_zero [Hash β] (s : SharedStack β) (b : β) :
    stackToNat (addToStack s b) ≠ 0 := by
  rw [stackToNat_addToStack] ; exact Nat.succ_ne_zero _

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

theorem stackToNat_addTupleToStack [Hash β] (s : SharedStack β) (bs : Fin k → β) :
    stackToNat (addTupleToStack s bs) = s.stackToNat + k := by
  induction' k with k IH generalizing s
  · simp_rw [addTupleToStack_zero, add_zero]
  · simp_rw [addTupleToStack_succ_last, stackToNat_addToStack, IH, add_assoc]

theorem addTupleToStack_two_pow_succ [Hash β] (s : SharedStack β) (bs : Fin (2 ^ (n + 1)) → β) :
    addTupleToStack s bs = addTupleToStack (addTupleToStack s (twoPowSuccTupleDivide bs).1)
    (twoPowSuccTupleDivide bs).2 :=
  Fin.tuple_foldl_two_pow_succ _ _ _

def finalHashStack [Hash β] (n : ℕ) (bs : Fin (2^n) → β) : SharedStack β := addTupleToStack [] bs

theorem stackToNat_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    stackToNat (finalHashStack n bs) = 2^n :=
  (stackToNat_addTupleToStack _ _).trans (zero_add _)

theorem lt_length_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    n < (finalHashStack n bs).length :=
  lt_length_of_stackToNat_eq_two_pow stackToNat_finalHashStack

theorem getElem_isSome_finalHashStack [Hash β] {n : ℕ} {bs : Fin (2^n) → β} :
    ((finalHashStack n bs)[n]'lt_length_finalHashStack).isSome :=
  getElem_isSome_of_stackToNat_eq_two_pow stackToNat_finalHashStack

theorem finalHashStack_zero [Hash β] (bs : Fin (2^0) → β) : finalHashStack 0 bs = [some (bs 0)] := by
  refine (addTupleToStack_succ _ _).trans ?_
  simp_rw [addTupleToStack_zero, addToStack_nil]

theorem finalHashStack_succ [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHashStack (n + 1) bs =
  addTupleToStack (finalHashStack n (twoPowSuccTupleDivide bs).1)
  ((twoPowSuccTupleDivide bs).2) := addTupleToStack_two_pow_succ _ _

end SharedStack


instance : Hash UInt64 := ⟨fun a b => hash (a, b)⟩

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).toNat⟩


#eval BTree.finalHash 2 ![234234, 12, 44, 5324]

#eval SharedStack.finalHash 2 ![234234, 12, 44, 5324]
