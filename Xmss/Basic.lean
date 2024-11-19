import Mathlib

variable {β : Type*} {n : ℕ}

example : 2^n + 2^n = 2^(n + 1) := by exact Eq.symm (Nat.two_pow_succ n)

theorem Nat.testBit_ext_iff {q q' : ℕ} : q = q' ↔ (∀ i : ℕ, q.testBit i = q'.testBit i) :=
  ⟨fun h _ => h ▸ rfl, Nat.eq_of_testBit_eq⟩

theorem Nat.testBit_ne_iff {q q' : ℕ} : q ≠ q' ↔ (∃ i : ℕ, q.testBit i ≠ q'.testBit i) := by
  simp_rw [ne_eq, testBit_ext_iff, not_forall]

instance {n m : ℕ} [NeZero n] [m.AtLeastTwo] : NeZero (m ^ n - 1) :=
    ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (NeZero.ne _) Nat.AtLeastTwo.one_lt)⟩

theorem Nat.size_pred_pow {n : ℕ} : (2^n - 1).size = n := by
  cases n
  · simp_rw [pow_zero, Nat.sub_self, size_zero]
  · exact le_antisymm (size_le.mpr <| Nat.pred_lt_self (Nat.two_pow_pos _))
      (lt_size.mpr <| (Nat.le_pred_iff_lt (Nat.two_pow_pos _)).mpr (Nat.pow_lt_pow_succ one_lt_two))
/-
theorem Nat.log_eq_iff {b : ℕ} {m : ℕ} {n : ℕ} (h : m ≠ 0 ∨ 1 < b ∧ n ≠ 0) :
Nat.log b n = m ↔ b ^ m ≤ n ∧ n < b ^ (m + 1)
-/

@[simp] theorem Nat.log2_one : Nat.log2 1 = 0 := Nat.log2_two_pow (n := 0)

theorem Nat.log2_eq_iff_of_ne_zero (hn : n ≠ 0) : Nat.log2 n = m ↔ 2^m ≤ n ∧ n < 2^(m + 1) := by
  rw [Nat.log2_eq_log_two, Nat.log_eq_iff (Or.inr ⟨one_lt_two, hn⟩)]

theorem Nat.log2_eq_iff_of_ne_zero_right (hm : m ≠ 0) :
    Nat.log2 n = m ↔ 2^m ≤ n ∧ n < 2^(m + 1) := by
  rw [Nat.log2_eq_log_two, Nat.log_eq_iff (Or.inl hm)]

theorem Nat.log2_eq_succ_iff :
    log2 n = m + 1 ↔ 2^(m + 1) ≤ n ∧ n < 2^(m + 2) := log2_eq_iff_of_ne_zero_right (succ_ne_zero _)

theorem Nat.log2_eq_zero_iff : Nat.log2 n = 0 ↔ n = 0 ∨ n = 1 := by
  simp_rw [Nat.log2_eq_log_two, Nat.log_eq_zero_iff, one_lt_two.not_le, or_false,
    Nat.lt_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one]

theorem Nat.log2_pred_two_pow {n : ℕ} : (2^n - 1).log2 = n - 1 := by
  rcases n with (_ | (_ | n))
  · simp_rw [pow_zero, Nat.sub_self, log2_zero]
  · simp_rw [zero_add, pow_one, Nat.add_one_sub_one, log2_one]
  · simp_rw [add_tsub_cancel_right, Nat.log2_eq_succ_iff]
    refine ⟨Nat.le_sub_one_of_lt ?_, Nat.pred_lt_self (Nat.two_pow_pos _)⟩
    simp_rw [pow_succ', Nat.mul_lt_mul_left zero_lt_two,
      lt_mul_iff_one_lt_left (Nat.two_pow_pos _), one_lt_two]

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

theorem concatTwoPow_symm_apply_of_lt {i : Fin (2^(n + 1))} (h : (i : ℕ) < 2^n) :
    concatTwoPow.symm i = Sum.inl ⟨i, h⟩ := by
  simp_rw [Equiv.symm_apply_eq, Fin.ext_iff, concatTwoPow_inl_apply_val]

theorem concatTwoPow_symm_apply_of_ge {i : Fin (2^(n + 1))} (h : 2^n ≤ (i : ℕ)) :
    concatTwoPow.symm i = Sum.inr ⟨i - 2^n,
    Nat.sub_lt_right_of_lt_add h (i.isLt.trans_eq (Nat.two_pow_succ _))⟩ := by
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

@[simp] theorem Fin.val_top [NeZero n] : (⊤ : Fin n).1 = n - 1 := rfl

@[simp] theorem Fin.top_eq_cast_last [NeZero n] : (⊤ : Fin n) =
    Fin.cast (Nat.sub_add_cancel NeZero.one_le) (last (n - 1)) := rfl

@[simp] theorem Fin.top_eq_mk_sub_one [NeZero n] : (⊤ : Fin n) =
  ⟨n - 1, Nat.sub_one_lt <| NeZero.ne _⟩ := rfl

theorem Nat.two_pow_le_sub_one_two_pow_succ : 2^n ≤ 2^(n + 1) - 1 :=
  (le_pred_iff_lt (Nat.two_pow_pos _)).mpr (Nat.pow_lt_pow_succ one_lt_two)

theorem Nat.sub_one_two_pow_succ_sub_two_pow : 2^(n + 1) - 1 - 2 ^ n = 2^n - 1 := by
  rw [pow_succ', two_mul, Nat.sub_right_comm, Nat.add_sub_cancel]

def twoPowEquivSigmaSumUnit : {n : ℕ} → Fin (2 ^ n) ≃ (Σ (i : Fin n), Fin (2^(i : ℕ))) ⊕ Unit
  | 0 =>
    { toFun := fun i => Sum.inr (),
      invFun := fun i => i.casesOn (fun i => i.1.elim0) (fun _ => 0),
      left_inv := fun i => by
        simp_rw [Nat.pow_zero]
        exact (Fin.fin_one_eq_zero _).symm,
      right_inv := fun i => by
        cases i with | inl i => _ | inr => _
        · exact i.1.elim0
        · rfl}
  | (n + 1) => concatTwoPow.symm.trans <|
    (Equiv.sumCongr (Equiv.refl _) twoPowEquivSigmaSumUnit).trans <|
    (Equiv.sumAssoc _ _ _).symm.trans <|
    (Equiv.sumCongr {
      toFun := Sum.elim (fun x => ⟨Fin.last n, x⟩) (fun ⟨i, x⟩ => ⟨i.castSucc, x⟩)
      invFun := fun i => i.casesOn
        fun j => j.lastCases Sum.inl fun j x => Sum.inr ⟨j, x⟩
      left_inv := fun i => by
        rcases i with (x | ⟨i, x⟩)
        · simp_rw [Sum.elim_inl, Fin.lastCases_last]
        · simp_rw [Sum.elim_inr, Fin.lastCases_castSucc]
      right_inv := fun ⟨i, x⟩ => by
        cases i using Fin.lastCases with | last => _ | cast => _
        · simp_rw [Fin.lastCases_last, Sum.elim_inl]
        · simp_rw [Fin.lastCases_castSucc, Sum.elim_inr]} (Equiv.refl _))

theorem twoPowEquivSigmaSumUnit_zero_apply {i : Fin (2^0)} :
    twoPowEquivSigmaSumUnit i = (Sum.inr ()) := rfl

theorem twoPowEquivSigmaSumUnit_zero_symm_apply :
    twoPowEquivSigmaSumUnit (n := 0).symm (Sum.inr ()) = 0 := rfl

theorem twoPowEquivSigmaSumUnit_succ_apply {i : Fin (2^(n + 1))}:
    twoPowEquivSigmaSumUnit i = (concatTwoPow.symm i).elim (fun i => Sum.inl ⟨Fin.last n, i⟩)
    (fun i => (twoPowEquivSigmaSumUnit i).elim
    (fun i => Sum.inl ⟨i.fst.castSucc, i.snd⟩)
    (fun () => Sum.inr ())) := by
  nth_rewrite 1 [twoPowEquivSigmaSumUnit]
  simp_rw [Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map, Equiv.sumAssoc, Function.comp_def,
    Equiv.refl_apply, Equiv.coe_fn_symm_mk, Equiv.coe_fn_mk]
  rcases lt_or_le (i : ℕ) (2^n : ℕ) with hi | hi
  · simp_rw [concatTwoPow_symm_apply_of_lt hi, Sum.elim_inl]
  · simp_rw [concatTwoPow_symm_apply_of_ge hi, Sum.elim_inr]
    cases twoPowEquivSigmaSumUnit _
    · simp_rw [Sum.elim_inl, Sum.elim_inr]
    · simp_rw [Sum.elim_inr]

theorem twoPowEquivSigmaSumUnit_succ_apply_of_lt {i : ℕ} (hi : i < 2^n) :
    twoPowEquivSigmaSumUnit ⟨i, hi.trans (Nat.pow_lt_pow_succ one_lt_two)⟩ =
    Sum.inl ⟨Fin.last n, ⟨i, hi⟩⟩ := by
  rw [twoPowEquivSigmaSumUnit_succ_apply, concatTwoPow_symm_apply_of_lt hi, Sum.elim_inl]

theorem twoPowEquivSigmaSumUnit_succ_apply_of_ge {i : ℕ} {hi₀ : i < 2^ (n + 1)}
    (hi₁ : 2^n ≤ i) : twoPowEquivSigmaSumUnit ⟨i, hi₀⟩ =
    (twoPowEquivSigmaSumUnit ⟨i - 2^n,
      Nat.sub_lt_right_of_lt_add hi₁ (hi₀.trans_eq (Nat.two_pow_succ _))⟩).elim
      (fun i => Sum.inl ⟨i.fst.castSucc, i.snd⟩)
      (fun () => Sum.inr ()) := by
  rw [twoPowEquivSigmaSumUnit_succ_apply, concatTwoPow_symm_apply_of_ge hi₁, Sum.elim_inr]

theorem twoPowEquivSigmaSumUnit_succ_apply_of_eq (hi : i = 2^n - 1) :
    twoPowEquivSigmaSumUnit ⟨i, hi ▸ Nat.sub_one_lt (Nat.two_pow_pos _).ne'⟩ = Sum.inr () := by
  cases hi
  induction n with | zero => _ | succ n IH => _
  · exact twoPowEquivSigmaSumUnit_zero_apply
  · simp_rw [twoPowEquivSigmaSumUnit_succ_apply_of_ge
      Nat.two_pow_le_sub_one_two_pow_succ, Nat.sub_one_two_pow_succ_sub_two_pow, IH, Sum.elim_inr]

theorem twoPowEquivSigmaSumUnit_apply_top :
    twoPowEquivSigmaSumUnit (⊤ : Fin (2^n)) = Sum.inr () :=
  twoPowEquivSigmaSumUnit_succ_apply_of_eq rfl

theorem twoPowEquivSigmaSumUnit_isLeft_of_lt {i : ℕ} (hi : i < 2^n - 1) :
    (twoPowEquivSigmaSumUnit ⟨i, Nat.lt_of_lt_pred hi⟩).isLeft := by
  induction n generalizing i with | zero => _ | succ n IH => _
  · simp_rw [pow_zero, Nat.sub_self, not_lt_zero'] at hi
  · rcases lt_or_le i (2 ^ n) with hi' | hi'
    · rw [twoPowEquivSigmaSumUnit_succ_apply_of_lt hi', Sum.isLeft_inl]
    · rw [twoPowEquivSigmaSumUnit_succ_apply_of_ge hi']
      simp_rw [Sum.isLeft_iff] at IH
      rcases IH (Nat.sub_lt_left_of_lt_add hi'
        ((Nat.add_sub_assoc Nat.one_le_two_pow _) ▸ Nat.two_mul _ ▸ pow_succ' 2 _ ▸ hi))
        with ⟨j, hj⟩
      simp_rw [hj, Sum.elim_inl, Sum.isLeft_inl]

theorem twoPowEquivSigmaSumUnit_isRight_of_eq {i : ℕ} (hi : i = 2^n - 1) :
    (twoPowEquivSigmaSumUnit ⟨i, hi ▸ Nat.sub_one_lt (Nat.two_pow_pos _).ne'⟩).isRight := by
  rw [twoPowEquivSigmaSumUnit_succ_apply_of_eq hi, Sum.isRight_inr]

theorem twoPowEquivSigmaSumUnit_isLeft_iff_lt {i : Fin (2^n)} :
    (twoPowEquivSigmaSumUnit i).isLeft ↔ (i : ℕ) < 2^n - 1 := by
  refine ⟨Function.mtr ?_, twoPowEquivSigmaSumUnit_isLeft_of_lt⟩
  simp_rw [not_lt, le_iff_eq_or_lt, (Nat.le_sub_one_of_lt i.isLt).not_lt, or_false,
    Bool.not_eq_true, Sum.isLeft_eq_false, eq_comm (b := (i : ℕ))]
  exact twoPowEquivSigmaSumUnit_isRight_of_eq

theorem blahj {i k : ℕ} (hk : k < n + 1)
    (hi₁ : i + 2 ^ k < 2 ^ (n + 1)) (hi₂ : 2 ^ (n + 1) ≤ i + 2 ^ (k + 1)) :
    (twoPowEquivSigmaSumUnit (⟨i, Nat.lt_of_lt_pred
    ((Nat.lt_add_of_pos_right (Nat.two_pow_pos k)).trans_le (Nat.le_pred_of_lt hi₁))⟩)) =
    Sum.inl ⟨⟨k, hk⟩,
      ⟨i + 2^(k + 1) - 2^(n + 1), by
        refine Nat.sub_lt_left_of_lt_add hi₂ ?_
        rw [pow_succ' _ k, two_mul, ← add_assoc, add_lt_add_iff_right]
        exact hi₁⟩⟩ := by
  induction n generalizing k i with | zero => _ | succ n IH => _
  · simp_rw [zero_add, Nat.lt_one_iff] at hk
    subst hk
    exact twoPowEquivSigmaSumUnit_succ_apply_of_lt _
  · rcases lt_or_le i (2 ^ n) with (hi | hi)



/-

        simp_rw [Nat.sub_sub]
        apply Nat.sub_lt_left_of_lt_add _ _
        apply Nat.sub_one_lt_of_le (Nat.sub_pos_of_lt hi.1)
        rw [Nat.sub_le_iff_le_add, add_comm (2^k), add_assoc, ← two_mul, ← pow_succ']
        exact hi.2⟩
-/

theorem twoPowEquivSigmaSumUnit_succ_apply_of_ge' {i : ℕ}
  (f : {n : ℕ} → (j : Fin (2^(n + 1))) → (i : Fin (n + 1)) × Fin (2 ^ (i : ℕ)))
    (hi₀ : 2^n ≤ i) (hi₁ : i < 2^(n + 1) - 1) :
    twoPowEquivSigmaSumUnit ⟨i, Nat.lt_of_lt_pred hi₁⟩ = Sum.inl (f i) := by
  induction n generalizing i with | zero => _ | succ n IH => _
  · simp at hi₁
    simp at hi₀
    rw [hi₁] at hi₀
    exact (zero_lt_one.not_le hi₀).elim
  · simp_rw [twoPowEquivSigmaSumUnit_succ_apply_of_ge hi₀]
    rcases lt_or_le ((i : ℕ) - 2 ^ (n + 1)) (2 ^ n) with hi₂ | hi₂
    · simp_rw [twoPowEquivSigmaSumUnit_succ_apply_of_lt hi₂, Sum.elim_inl,
      Sum.inl.injEq]
      sorry
    · have H := IH hi₂ (Nat.sub_lt_left_of_lt_add hi₀ (Nat.add_sub_assoc
        (Nat.one_le_two_pow) _ ▸ Nat.two_mul _ ▸ pow_succ' 2 _ ▸ hi₁))
      rw [H, Sum.elim_inl, Sum.inl.injEq]
    rw [IH, Sum.elim_inl, Sum.inl.injEq]
    · sorry
    · simp
    · simp?



/-
(twoPowEquivSigmaSumUnit ⟨i - 2^n,
      Nat.sub_lt_right_of_lt_add hi (i.isLt.trans_eq (Nat.two_pow_succ _))⟩)

(fun i => Sum.inl ⟨i.fst.castSucc, i.snd⟩)

-/
theorem twoPowEquivSigmaSumUnit_succ_apply_last :
    twoPowEquivSigmaSumUnit (n := n) ⊤ = Sum.inr () := by
  induction n with | zero => _ | succ n IH => _
  · exact twoPowEquivSigmaSumUnit_zero_apply
  · simp_rw [twoPowEquivSigmaSumUnit_succ_apply_of_ge (i := ⊤) Nat.two_pow_le_sub_one_two_pow_succ,
      Fin.val_top, Nat.sub_one_two_pow_succ_sub_two_pow, ← Fin.top_eq_mk_sub_one, IH, Sum.elim_inr]

theorem twoPowEquivSigmaSumUnit_succ_apply {i : Fin (2^(n + 1))} (hi : (i : ℕ) < 2^n) :
    twoPowEquivSigmaSumUnit i = Sum.inl ⟨Fin.last n, ⟨i, hi⟩⟩ := by
  unfold twoPowEquivSigmaSumUnit
  simp_rw [Equiv.trans_apply, concatTwoPow_symm_apply_of_lt hi,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.coe_fn_mk, Sum.map_inl, Sum.elim_inl]

theorem twoPowEquivSigmaSumUnit_succ_apply' {i : Fin (2^(n + 1))} (hk : k ≤ n)
  (hi₁ : 2^(n + 1) - 2^(k + 1) ≤ (i : ℕ)) (hi₂ : (i : ℕ) < 2^(n + 1) - 2^k) :
    twoPowEquivSigmaSumUnit i = Sum.inl ⟨⟨k, Nat.lt_succ_of_le hk⟩,
    ⟨i - (2 ^ (n + 1) - 2 ^ (k + 1)), Nat.sub_lt_left_of_lt_add hi₁ (hi₂.trans_eq <|
    (Nat.sub_add_sub_cancel (Nat.pow_le_pow_of_le_right zero_lt_two (Nat.succ_le_succ hk))
    (Nat.pow_lt_pow_succ one_lt_two).le).symm.trans
    (by simp_rw [pow_succ' _ k, two_mul,Nat.add_sub_cancel]))⟩⟩ := by
  unfold twoPowEquivSigmaSumUnit
  simp_rw [Equiv.trans_apply, concatTwoPow_symm_apply_of_lt hi,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply, Equiv.sumAssoc_symm_apply_inl,
    Equiv.coe_fn_mk, Sum.map_inl, Sum.elim_inl]

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

attribute [-instance] Fin.completeLinearOrder in
@[simps!]
def twoPowTuples : (Fin (2 ^ n) → β) ≃ ((i : Fin n) → Fin (2^(i : ℕ)) → β) × β where
  toFun t := ⟨fun i s => t _, t ⊤⟩
  invFun t i := _
  left_inv t := _
  right_inv t := _

class Hash (β : Type u) where
  hash : β → β → β

infixl:65 " # " => Hash.hash

instance : Hash ℕ := ⟨fun a b => (hash (a, b)).toNat⟩

inductive BTree (β : Type u) : ℕ → Type u where
  | leaf : (n : ℕ) → Option β → BTree β n
  | node : {n : ℕ} → BTree β n → BTree β n → BTree β (n + 1)

namespace BTree

def lift {n : ℕ} : BTree β n → BTree β (n + 1)
  | leaf n a => leaf (n + 1) a
  | node l r => node l.lift r.lift

@[simp] theorem lift_leaf : (leaf n a).lift = leaf (n + 1) a := rfl
@[simp] theorem lift_node : (node l r).lift = node l.lift r.lift := rfl

def drop : {n : ℕ} → BTree β (n + 1) → BTree β n
  | n, leaf _ a => leaf n a
  | (n + 1), node l r => node l.drop r.drop
  | 0, node _ _ => leaf _ none

@[simp] theorem drop_leaf : (leaf (n + 1) a).drop = leaf n a := by
  unfold drop


@[simp] theorem drop_node_succ : (node (l : BTree β (n + 1)) r).drop = node l.drop r.drop := rfl

@[simp] theorem drop_node_zero : (node (l : BTree β 0) r).drop = leaf 0 none := rfl

theorem drop_lift (s : BTree β n) : s.lift.drop = s := by
  induction s
  · simp_rw [lift_leaf, drop_leaf]
  · simp_rw [lift_node, drop_node_succ, node.injEq]
    exact ⟨by assumption, by assumption⟩

def emp (β : Type u) : (n : ℕ) → BTree β n
  | 0 => leaf 0 none
  | (_ + 1) => node (emp _ _) (emp _ _)

def root [Hash β] {n : ℕ} : BTree β n → Option β
  | leaf n b => b
  | node b1 b2 => Option.map₂ (· # ·) (root b1) (root b2)

theorem root_leaf [Hash β] : root (leaf n (b : Option β)) = b := rfl

theorem root_node [Hash β] {l : BTree β n} :
    root (node l r) = Option.map₂ (· # ·) (root l) (root r) := rfl

theorem root_emp [Hash β] : root (emp β n) = none := by
  induction n with | zero => _ | succ n IH => _
  · rfl
  · exact root_node.trans (IH.symm ▸ rfl)

def sngl (a : β) : BTree β 1 := node (leaf 0 (some a)) (leaf 0 none)

theorem root_sngl [Hash β] : (sngl (a : β)).root = none := rfl

def bit0 (p : BTree β n) : BTree β (n + 1) := node p (emp _ _)

theorem root_bit0 [Hash β] (p : BTree β n) : (bit0 p).root = none :=
  root_node.trans ((root_emp (β := β)).symm ▸ Option.map₂_none_right _ _)

def bit1 (a : β) (p : BTree β n) : BTree β (n + 1) := node (leaf n (some a)) p

#eval bit0 (bit1 45 (sngl 32))
#eval sngl 77

theorem root_bit1 [Hash β] (p : BTree β n) : (bit1 a p).root = (some a).map₂ (· # ·) p.root :=
  root_node.trans (root_leaf (β := β) ▸ rfl)

#eval (bit0 (sngl 8))

def listOfTree : {n : ℕ} → (Fin (2^n) → β) → BTree β n
  | 0, t => leaf 0 (t 0)
  | (_ + 1), t =>
    let (f, l) := twoPowSuccTupleDivide t
    node (listOfTree f) (listOfTree l)

theorem listOfTree_zero (bs : Fin (2^0) → β) :
  listOfTree bs = leaf 0 (some (bs 0)) := rfl

theorem listOfTree_succ (bs : Fin (2^(n + 1)) → β) :
  listOfTree bs =
  node (listOfTree (twoPowSuccTupleDivide bs).1)
  (listOfTree (twoPowSuccTupleDivide bs).2) := rfl

def finalHash [Hash β] : {n : ℕ} → (Fin (2^n) → β) → β
  | 0, t => t 0
  | (_ + 1), t =>
    let (f, l) := twoPowSuccTupleDivide t
    (finalHash f) # (finalHash l)

theorem finalHash_zero [Hash β] (bs : Fin (2^0) → β) :
  finalHash bs = bs 0 := rfl

theorem finalHash_succ [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHash bs =
  (finalHash (twoPowSuccTupleDivide bs).1) #
  (finalHash (twoPowSuccTupleDivide bs).2) := rfl

theorem blahj [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
  finalHash bs = _

theorem finalHash_succ_eq_finalHash [Hash β] (n : ℕ) (bs : Fin (2^(n + 1)) → β) :
    finalHash bs = finalHash (fun i =>
    bs (interleveTwoPow (Sum.inl i)) # bs (interleveTwoPow (Sum.inr i))) := by
  induction' n with n IH
  · exact rfl
  · rw [finalHash_succ (n + 1), IH, IH, finalHash_succ n]
    congr
    simp_rw [twoPowSuccTupleDivide_apply, concatTwoPow_inr_interleveTwoPow_inl,
      concatTwoPow_inr_interleveTwoPow_inr]

theorem finalHash_eq_root_listOfTree [Hash β] (bs : Fin (2^n) → β) :
    root (listOfTree bs) = finalHash bs := by
  induction' n with n IH
  · simp_rw [finalHash_zero, listOfTree_zero, root_leaf]
  · simp_rw [finalHash_succ, listOfTree_succ, root_node, IH, Option.map₂_some_some]

theorem isSome_root_listOfTree [Hash β] (bs : Fin (2^n) → β) :
    (root (listOfTree bs)).isSome := by
  rw [Option.isSome_iff_exists]
  exact ⟨_, finalHash_eq_root_listOfTree bs⟩


end BTree

inductive PSharedStack (β : Type u) : Type u
  | sngl : β → PSharedStack β
  | bit0 : PSharedStack β → PSharedStack β
  | bit1 : β → PSharedStack β → PSharedStack β
deriving DecidableEq

namespace PSharedStack

variable {β : Type*} {a b : β} {p : PSharedStack β}

instance [Inhabited β] : Inhabited (PSharedStack β) where
  default := sngl default

def log2 : PSharedStack β → ℕ
  | sngl _ => 0
  | bit0 p => p.log2.succ
  | bit1 _ p => p.log2.succ

section Log2

@[simp] theorem log2_sngl : (sngl a).log2 = 0 := rfl
@[simp] theorem log2_bit0 : (bit0 p).log2 = p.log2 + 1 := rfl
@[simp] theorem log2_bit1 : (bit1 a p).log2 = p.log2 + 1 := rfl

theorem log2_bit0_ne_zero : (bit0 p).log2 ≠ 0 := Nat.succ_ne_zero _

theorem log2_bit1_ne_zero : (bit1 a p).log2 ≠ 0 := Nat.succ_ne_zero _

end Log2

def appendSingle : PSharedStack β → β → PSharedStack β
  | sngl a, b => bit1 a (sngl b)
  | (bit0 p), b => bit0 (appendSingle p b)
  | (bit1 a p), b => bit1 a (appendSingle p b)

section AppendSingle

@[simp] theorem appendSingle_sngl : (sngl a).appendSingle b = bit1 a (sngl b) := rfl
@[simp] theorem appendSingle_bit0 : (bit0 p).appendSingle b = bit0 (p.appendSingle b) := rfl
@[simp] theorem appendSingle_bit1 : (bit1 a p).appendSingle b = bit1 a (p.appendSingle b) := rfl

end AppendSingle

def reverse : PSharedStack β → PSharedStack β
  | sngl a => sngl a
  | bit0 p => reverse p
  | bit1 a p => (reverse p).appendSingle a

section Reverse

@[simp] theorem reverse_sngl : (sngl a).reverse = sngl a := rfl
@[simp] theorem reverse_bit0 : (bit0 p).reverse = p.reverse := rfl
@[simp] theorem reverse_bit1 : (bit1 a p).reverse = p.reverse.appendSingle a := rfl

end Reverse

def size (p : PSharedStack β) : ℕ := p.log2 + 1

section Size

@[simp] theorem size_sngl : (sngl a).size = 1 := rfl
@[simp] theorem size_bit0 : (bit0 p).size = p.size + 1 := rfl
@[simp] theorem size_bit1 : (bit1 a p).size = p.size + 1 := rfl

instance NeZero.size : NeZero (p.size) := ⟨Nat.succ_ne_zero _⟩

@[simp] theorem size_ne_zero : p.size ≠ 0 := NeZero.ne _

@[simp] theorem size_pos : 0 < p.size := NeZero.pos _

@[simp] theorem one_le_size : 1 ≤ p.size := NeZero.one_le

theorem size_eq_log2_succ : p.size = p.log2 + 1 := rfl

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
  rw [size_eq_log2_succ]
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [count_sngl, log2_sngl, pow_one]
    exact one_lt_two
  · rw [pow_succ']
    exact Nat.bit_lt_bit _ false IH
  · rw [pow_succ']
    exact Nat.bit_lt_bit _ false IH

theorem count_le_pred_two_pow_size : p.count ≤ 2^p.size - 1 :=
  Nat.le_pred_of_lt count_lt_two_pow_size

theorem two_pow_log2_le_count : 2^p.log2 ≤ p.count := by
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [log2_sngl, pow_zero, count_sngl]
  · simp_rw [log2_bit0, count_bit0, pow_succ']
    exact Nat.bit_le false IH
  · simp_rw [log2_bit1, count_bit1, pow_succ']
    exact (Nat.bit_le false IH).trans (Nat.le_succ _)

@[simp] theorem size_count_eq_size : p.count.size = p.size := by
  refine le_antisymm ((Nat.size_le).mpr count_lt_two_pow_size) ?_
  rw [size_eq_log2_succ, Nat.succ_le_iff, Nat.lt_size]
  exact two_pow_log2_le_count

@[simp] theorem log_two_count_eq_log2 : Nat.log 2 p.count = p.log2 := by
  exact Nat.log_eq_of_pow_le_of_lt_pow two_pow_log2_le_count
    (size_eq_log2_succ ▸ count_lt_two_pow_size)

@[simp] theorem log2_count_eq_log2 : p.count.log2 = p.log2 := by
  rw [Nat.log2_eq_log_two, log_two_count_eq_log2]

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

theorem sizeCap_lt_pred_two_pow_size : p.sizeCap ≤ 2^p.log2 - 1 := by
  rw [le_tsub_iff_right Nat.one_le_two_pow]
  induction p with | sngl => exact le_rfl | bit0 p IH => _ | bit1 _ _ IH => _
  · rw [sizeCap_bit0, log2_bit0, pow_succ', add_assoc, ← Nat.mul_succ]
    exact Nat.mul_le_mul_left _ IH
  · rw [sizeCap_bit1, log2_bit1, pow_succ']
    refine (Nat.le_succ _).trans ?_
    simp_rw [Nat.succ_eq_add_one, add_assoc, one_add_one_eq_two, ← Nat.mul_succ]
    exact Nat.bit_le false IH

theorem count_add_sizeCap_eq_pred_two_pow_size : p.count + p.sizeCap = 2^p.size - 1 := by
  rw [size_eq_log2_succ, eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow, add_comm (p.count)]
  induction p with | sngl => _ | bit0 p IH => _ | bit1 _ _ IH => _
  · simp_rw [sizeCap_sngl, count_sngl, log2_sngl]
  · simp_rw [sizeCap_bit0, count_bit0, pow_succ', log2_bit0, add_assoc _ _ 1,
      Nat.add_add_add_comm _ 1, ← Nat.mul_add, ← Nat.mul_add_one, IH]
  · simp_rw [sizeCap_bit1, count_bit1, pow_succ', log2_bit1, add_assoc,
      one_add_one_eq_two, ← add_assoc, ← Nat.mul_add, ← Nat.mul_add_one, IH]

theorem sizeCap_eq_pred_two_pow_size_sub_count : p.sizeCap = (2^p.size - 1) - p.count := by
  rw [eq_tsub_iff_add_eq_of_le (count_le_pred_two_pow_size), add_comm]
  exact count_add_sizeCap_eq_pred_two_pow_size

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

theorem sizeInc_lt_two_pow_size : p.sizeInc ≤ 2^p.log2 := by
  rw [sizeInc_eq_sizeCap_succ]
  exact Nat.add_le_of_le_sub Nat.one_le_two_pow sizeCap_lt_pred_two_pow_size

theorem count_add_sizeInc_eq_two_pow_size : p.count + p.sizeInc = 2^p.size := by
  rw [sizeInc_eq_sizeCap_succ, ← Nat.add_assoc,
    count_add_sizeCap_eq_pred_two_pow_size, Nat.sub_add_cancel Nat.one_le_two_pow]

theorem sizeInc_eq_two_pow_size_sub_count : p.sizeInc = 2^p.size - p.count := by
  rw [eq_tsub_iff_add_eq_of_le count_lt_two_pow_size.le, add_comm]
  exact count_add_sizeInc_eq_two_pow_size

theorem count_add_sizeInc_eq_two_pow_log2_add_two_pow_log2 :
    p.count + p.sizeInc = 2^p.log2 + 2^p.log2 := by
  rw [← two_mul, ← pow_succ', ← size_eq_log2_succ]
  exact count_add_sizeInc_eq_two_pow_size

end SizeInc

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

inductive isMaxedN : (p : PSharedStack β) → ℕ → Prop
  | protected sngl : (a : β) → isMaxedN (sngl a) 0
  | protected bit0 : {p : PSharedStack β} → {n : ℕ} →
      p.isMaxedN n → (bit0 p).isMaxedN (n + 1)
  | protected bit1 : (a : β) → {p : PSharedStack β} →
      p.isMaxedN 0 → (bit1 a p).isMaxedN 0

section IsMaxedN

variable {i : ℕ}

theorem le_log2_of_isMaxedN (hp : p.isMaxedN i) : i ≤ p.log2 := by
  induction hp
  · simp_rw [log2_sngl, le_refl]
  · simp_rw [log2_bit0]
    apply Nat.succ_le_succ
    assumption
  · exact zero_le _

theorem lt_size_of_isMaxedN (hp : p.isMaxedN i) : i < p.size :=
  Nat.lt_succ_of_le <| le_log2_of_isMaxedN hp

theorem not_isMaxedNof_size_le (hp : p.size ≤ i) : ¬ p.isMaxedN i :=
  fun h => (lt_size_of_isMaxedN h).not_le hp

theorem not_isMaxedNof_log2_lt (hp : p.log2 < i) : ¬ p.isMaxedN i :=
  fun h => (le_log2_of_isMaxedN h).not_lt hp

theorem isMaxedN_sngl_zero : (sngl a).isMaxedN 0 := by constructor

theorem isMaxedN_sngl_last : (sngl a).isMaxedN ((sngl a).log2) := by constructor

@[simp] theorem isMaxedN_sngl_iff : (sngl a).isMaxedN i ↔ i = 0 :=
  ⟨fun h => by cases h ; rfl, fun h => by cases h ; constructor⟩

theorem isMaxedN_bit0_succ_iff : (bit0 p).isMaxedN (i + 1) ↔ p.isMaxedN i :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem isMaxedN_bit1_iff : (bit1 a p).isMaxedN i ↔ i = 0 ∧ p.isMaxedN i :=
  ⟨fun h => by cases h ; exact ⟨rfl, by assumption⟩,
  fun ⟨h₁, h₂⟩ => by subst h₁ ; constructor ; assumption⟩

theorem isMaxedN_bit1_zero_iff : (bit1 a p).isMaxedN 0 ↔ p.isMaxedN 0 :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

@[simp] theorem not_isMaxedN_bit0 : ¬ (bit0 p).isMaxedN 0 := fun h => by contradiction

@[simp] theorem not_isMaxedN_ne_zero [NeZero i] : ¬ (bit1 a p).isMaxedN i := fun h => by
  simp_rw [isMaxedN_bit1_iff, NeZero.ne i, false_and] at h

theorem isMaxedN_iff_count_eq :
    p.isMaxedN i ↔ p.count = 2^(p.size) - 2^i := by
  induction p generalizing i with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isMaxedN_sngl_iff, count_sngl, size_sngl, pow_one]
    cases i
    · simp_rw [pow_zero, Nat.add_one_sub_one]
    · simp_rw [Nat.succ_ne_zero, false_iff, pow_succ']
      cases (2 ^ _)
      · simp_rw [mul_zero, tsub_zero, one_lt_two.ne, not_false_eq_true]
      · simp_rw [Nat.mul_succ, add_comm, Nat.sub_self_add, zero_ne_one.symm, not_false_eq_true]
  · cases i
    · simp_rw [not_isMaxedN_bit0, false_iff, count_bit0, pow_zero,
        eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow, size_bit0, pow_succ']
      exact (Nat.two_mul_ne_two_mul_add_one).symm
    · simp_rw [isMaxedN_bit0_succ_iff, IH,  count_bit0, size_bit0, pow_succ',
        ← Nat.mul_sub, Nat.mul_left_cancel_iff zero_lt_two]
  · cases i
    · simp_rw [isMaxedN_bit1_zero_iff, IH, count_bit1, size_bit1, pow_zero,
        eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow, pow_succ' (n := p.size),
        add_assoc, ← two_mul, ← mul_add, Nat.mul_left_cancel_iff zero_lt_two]
    · simp_rw [not_isMaxedN_ne_zero, false_iff, count_bit1, size_bit1, pow_succ', ← Nat.mul_sub]
      exact (Nat.two_mul_ne_two_mul_add_one).symm

instance : Decidable (p.isMaxedN i) :=
  decidable_of_iff _ isMaxedN_iff_count_eq.symm

end IsMaxedN

inductive isRoot : PSharedStack β → Prop
  | protected sngl : (a : β) → isRoot (sngl a)
  | protected bit0 : {p : PSharedStack β} → p.isRoot → isRoot (bit0 p)

section IsRoot

@[simp] theorem isRoot_sngl : (sngl a).isRoot := by constructor

@[simp] theorem not_isRoot_bit1 : ¬ (bit1 a p).isRoot := fun h => by contradiction

@[simp] theorem isRoot_bit0_iff : (bit0 p).isRoot ↔ p.isRoot :=
  ⟨fun h => by cases h ; assumption, fun h => by constructor ; assumption⟩

theorem isRoot_iff_count_eq_two_pow_log2 : p.isRoot ↔ p.count = 2^p.log2 := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isRoot_sngl, count_sngl, log2_sngl, pow_zero]
  · simp_rw [isRoot_bit0_iff, IH, count_bit0, log2_bit0, pow_succ', mul_eq_mul_left_iff,
      zero_lt_two.ne', or_false]
  · simp_rw [not_isRoot_bit1, count_bit1, log2_bit1, false_iff, pow_succ']
    exact (Nat.two_mul_ne_two_mul_add_one).symm

instance : Decidable (p.isRoot) :=
  decidable_of_iff _ isRoot_iff_count_eq_two_pow_log2.symm

theorem isRoot_iff_exists_size_eq_two_pow : p.isRoot ↔ ∃ k, p.count = 2^k := by
  rw [isRoot_iff_count_eq_two_pow_log2]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨k, hk⟩ => ?_⟩
  have H := hk ▸ p.log_two_count_eq_log2
  rw [Nat.log_pow one_lt_two] at H
  exact H ▸ hk

theorem isRoot_iff_isMaxedN_plog2 : p.isRoot ↔ p.isMaxedN p.log2 := by
  rw [isMaxedN_iff_count_eq, isRoot_iff_count_eq_two_pow_log2, size_eq_log2_succ,
    pow_succ', two_mul, Nat.add_sub_cancel]

theorem isRoot_iff_sizeInc_eq_two_pow_log2 : p.isRoot ↔ p.sizeInc = 2^p.log2 := by
  rw [isRoot_iff_count_eq_two_pow_log2]
  have H := p.count_add_sizeInc_eq_two_pow_log2_add_two_pow_log2
  exact ⟨fun h => add_right_injective _ (h ▸ H), fun h => add_left_injective _ (h ▸ H)⟩

theorem isRoot_iff_sizeCap_eq_two_pow_log2 : p.isRoot ↔ p.sizeCap = 2^p.log2 - 1 := by
  rw [isRoot_iff_sizeInc_eq_two_pow_log2, sizeInc_eq_sizeCap_succ,
    eq_tsub_iff_add_eq_of_le Nat.one_le_two_pow]

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
  · simp_rw [not_isMaxed_bit0, count_bit0, false_iff, size_eq_log2_succ, pow_succ']
    exact (Nat.two_mul_ne_two_mul_add_one).symm
  · simp_rw [isMaxed_bit1_iff, IH, count_bit1, size_bit1, pow_succ', add_assoc,
      ← Nat.mul_succ, mul_eq_mul_left_iff, zero_lt_two.ne', or_false]

theorem isMaxed_iff_isMaxedN_zero : p.isMaxed ↔ p.isMaxedN 0 := by
  rw [isMaxedN_iff_count_eq, isMaxed_iff_count_eq_pred_two_pow_size, pow_zero]

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

theorem isSingle_iff_log2_eq_zero : p.isSingle ↔ p.log2 = 0 := by
  cases p
  · exact iff_of_true isSingle_sngl log2_sngl
  · exact iff_of_false not_isSingle_bit0 log2_bit0_ne_zero
  · exact iff_of_false not_isSingle_bit1 log2_bit1_ne_zero

theorem isSingle_iff_size_eq_one : p.isSingle ↔ p.size = 1 := by
  rw [isSingle_iff_log2_eq_zero, size_eq_log2_succ, add_left_eq_self]

theorem isSingle_iff_exists_sngl : p.isSingle ↔ ∃ a, p = sngl a := by
  cases p
  · exact iff_of_true isSingle_sngl ⟨_, rfl⟩
  · exact iff_of_false not_isSingle_bit0 (fun ⟨_, h⟩ => by contradiction)
  · exact iff_of_false not_isSingle_bit1 (fun ⟨_, h⟩ => by contradiction)

theorem isMaxed_and_isRoot_iff_isSingle : (p.isMaxed ∧ p.isRoot) ↔ p.isSingle := Iff.rfl

instance : Decidable (p.isSingle) := decidable_of_iff _ isMaxed_and_isRoot_iff_isSingle

end IsSingle

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

theorem testBit_sngl : (sngl a).testBit n = decide (n = 0) :=
  n.casesOn rfl (fun _ => rfl)

@[simp] theorem testBit_bit0_zero : (bit0 p).testBit 0 = false := rfl
@[simp] theorem testBit_bit0_succ : (bit0 p).testBit (n + 1) = p.testBit n := rfl

theorem testBit_bit0 : (bit0 p).testBit n = (!decide (n = 0) && p.testBit (n - 1)) :=
  n.casesOn rfl (fun _ => rfl)

@[simp] theorem testBit_bit1_zero : (bit1 a p).testBit 0 = true := rfl
@[simp] theorem testBit_bit1_succ : (bit1 a p).testBit (n + 1) = p.testBit n := rfl

theorem testBit_bit1 : (bit1 a p).testBit n = (decide (n = 0) || p.testBit (n - 1)) :=
  n.casesOn rfl (fun _ => rfl)

theorem testBit_of_log2_gt : p.log2 < n → p.testBit n = false := by
  induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _
  · simp_rw [log2_sngl, testBit_sngl, decide_eq_false_iff_not]
    exact ne_of_gt
  · simp_rw [log2_bit0, testBit_bit0, Bool.and_eq_false_imp, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not]
    exact fun h _ => IH (Nat.lt_pred_of_succ_lt h)
  · simp_rw [log2_bit1, testBit_bit1, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact fun h => ⟨Nat.not_eq_zero_of_lt h, IH (Nat.lt_pred_of_succ_lt h)⟩

theorem testBit_of_size_ge : p.size ≤ n → p.testBit n = false := by
  rw [size_eq_log2_succ, Nat.succ_le_iff]
  exact testBit_of_log2_gt

theorem testBit_log2 : p.testBit p.log2 = true := p.recOn
  (fun _ => rfl)
  (fun _ => by simp_rw [log2_bit0, testBit_bit0_succ, imp_self])
  (fun _ _ => by simp_rw [log2_bit1, testBit_bit1_succ, imp_self])

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

def get? : PSharedStack β → ℕ → Option β
  | sngl a, 0 => some a
  | sngl _, (_ + 1) => none
  | bit0 _, 0 => none
  | bit0 p, (n + 1) => p.get? n
  | bit1 a _, 0 => some a
  | bit1 _ p, (n + 1) => p.get? n

section Get?

@[simp] theorem get?_sngl_zero : (sngl a).get? 0 = a := rfl
@[simp] theorem get?_sngl_succ : (sngl a).get? (n + 1) = none := rfl

@[simp] theorem get?_bit0_zero : (bit0 p).get? 0 = none := rfl
@[simp] theorem get?_bit0_succ : (bit0 p).get? (n + 1) = p.get? n := rfl

@[simp] theorem get?_bit1_zero : (bit1 a p).get? 0 = a := rfl
@[simp] theorem get?_bit1_succ : (bit1 a p).get? (n + 1) = p.get? n := rfl

open Option in
theorem get?_isSome_eq_testBit : (p.get? n).isSome = p.testBit n := by
  induction p generalizing n with | sngl => _ | bit0 _ IH => _ | bit1 _ _ IH => _ <;> cases n
  · simp_rw [testBit_sngl_zero, get?_sngl_zero, isSome_some]
  · simp_rw [testBit_sngl_succ, get?_sngl_succ, isSome_none]
  · simp_rw [testBit_bit0_zero, get?_bit0_zero, isSome_none]
  · simp_rw [testBit_bit0_succ, get?_bit0_succ, IH]
  · simp_rw [testBit_bit1_zero, get?_bit1_zero, isSome_some]
  · simp_rw [testBit_bit1_succ, get?_bit1_succ, IH]

end Get?

def get (p : PSharedStack β) (n : ℕ) (h : p.testBit n) : β :=
  (p.get? n).get (get?_isSome_eq_testBit ▸ h)

section Get

@[simp] theorem get_sngl_zero : (sngl a).get 0 testBit_sngl_zero = a := rfl

@[simp] theorem get_bit0_succ : (bit0 p).get (n + 1) h = p.get n (testBit_bit0_succ ▸ h) := rfl

@[simp] theorem get_bit1_zero : (bit1 a p).get 0 testBit_bit1_zero = a := rfl
@[simp] theorem get_bit1_succ : (bit1 a p).get (n + 1) h = p.get n (testBit_bit1_succ ▸ h) := rfl

end Get

def last (p : PSharedStack β) : β := p.get p.log2 testBit_log2

section Last

theorem last_eq_get : p.last = p.get p.log2 testBit_log2 := rfl

@[simp] theorem last_sngl : (sngl a).last = a := rfl
@[simp] theorem last_bit0 : (bit0 p).last = p.last := rfl
@[simp] theorem last_bit1 : (bit1 a p).last = p.last := rfl

@[simp] theorem last_appendSingle : (p.appendSingle b).last = b := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [appendSingle_sngl, last_bit1, last_sngl]
  · simp_rw [appendSingle_bit0, last_bit0, IH]
  · simp_rw [appendSingle_bit1, last_bit1, IH]

theorem isRoot_iff_eq_iterate_log2_sngl_last :
    p.isRoot ↔ p = p.log2.iterate bit0 (sngl p.last) := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isRoot_sngl, log2_sngl, last_sngl, Function.iterate_zero, id_eq]
  · simp_rw [isRoot_bit0_iff, log2_bit0, last_bit0, Function.iterate_succ', Function.comp_apply,
      bit0.injEq, IH]
  · simp_rw [not_isRoot_bit1, log2_bit1, last_bit1, Function.iterate_succ', Function.comp_apply,
      false_iff]
    exact PSharedStack.noConfusion

theorem isRoot_iff_toList_eq_replicate_log2_append_singleton :
    p.isRoot ↔ p.toList = List.replicate p.log2 none ++ [some p.last] := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isRoot_sngl, toList_sngl, log2_sngl, List.replicate_zero, last_sngl, List.nil_append]
  · simp_rw [isRoot_bit0_iff, IH, toList_bit0, log2_bit0, List.replicate_succ, last_bit0,
    List.cons_append, List.cons_inj_right]
  · simp_rw [not_isRoot_bit1, toList_bit1, log2_bit1, List.replicate_succ, last_bit1,
      List.cons_append, List.cons_eq_cons, Option.some_ne_none, false_and]

theorem isMaxed_iff_eq_iterate_log2_sngl_pop :
    p.isMaxed ↔ ∃ (bs : Fin (p.log2) → β), p = Fin.foldr p.log2 (bit1 ∘ bs) (sngl p.last) := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [isMaxed_sngl, log2_sngl, last_sngl, Fin.foldr_zero, exists_const]
  · simp_rw [not_isMaxed_bit0, log2_bit0, last_bit0, false_iff, not_exists, Fin.foldr_succ,
      Function.comp_apply]
    exact fun _ => PSharedStack.noConfusion
  · simp_rw [isMaxed_bit1_iff, log2_bit1, last_bit1, Fin.foldr_succ,
      Function.comp_apply, bit1.injEq, IH]
    exact ⟨fun ⟨_, h⟩ => ⟨Fin.cons _ _, ⟨rfl, h⟩⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

end Last

def pop : PSharedStack β → β
  | sngl a => a
  | bit0 p => p.pop
  | bit1 a _ => a

section Pop

@[simp] theorem pop_sngl : (sngl a).pop = a := rfl
@[simp] theorem pop_bit0 : (bit0 p).pop = p.pop := rfl
@[simp] theorem pop_bit1 : (bit1 a p).pop = a := rfl

@[simp] theorem pop_appendSingle : (p.appendSingle b).pop = p.pop := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [appendSingle_sngl, pop_bit1, pop_sngl]
  · simp_rw [appendSingle_bit0, pop_bit0, IH]
  · simp_rw [appendSingle_bit1, pop_bit1]

theorem pop_eq_last_of_isRoot : p.isRoot → p.pop = p.last := by
  induction p with | sngl a => _ | bit0 p IH => _ | bit1 a p IH => _
  · simp_rw [pop_sngl, last_sngl, implies_true]
  · simp_rw [isRoot_bit0_iff, pop_bit0, last_bit0]
    exact IH
  · simp_rw [not_isRoot_bit1, false_implies]

end Pop

def accumulateLower [Hash β] : (p : PSharedStack β) → β → β
  | (bit1 a p), b => accumulateLower p (a # b)
  | _, b => b

section AccumulateLower

variable [Hash β]

@[simp] theorem accumulateLower_sngl : (sngl a).accumulateLower b = b := rfl
@[simp] theorem accumulateLower_bit0 : (bit0 p).accumulateLower b = b := rfl
@[simp] theorem accumulateLower_bit1 :
    (bit1 a p).accumulateLower b = p.accumulateLower (a # b) := rfl

end AccumulateLower

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
theorem count_push : (p.push b).count = p.count + 1 := by
  induction p generalizing b with | sngl => rfl | bit0 => rfl | bit1 _ _ IH => exact congrArg _ IH

theorem log2_push : (p.push b).log2 = p.log2 + (decide (p.isMaxed)).toNat := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · simp_rw [push_sngl, log2_bit0, log2_sngl, isMaxed_sngl, decide_True, Bool.toNat_true]
  · simp_rw [push_bit0, log2_bit0, log2_bit1, not_isMaxed_bit0, decide_False, Bool.toNat_false]
  · simp_rw [push_bit1, log2_bit0, log2_bit1, isMaxed_bit1_iff, IH, add_assoc, add_comm]

theorem log2_push_of_isMaxed (hp : p.isMaxed) : (p.push b).log2 = p.log2 + 1 := by
  simp_rw [log2_push, hp]
  rfl

theorem log2_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).log2 = p.log2 := by
  simp_rw [log2_push, hp]
  rfl

theorem size_push : (p.push b).size = p.size + (decide (p.isMaxed)).toNat := by
  simp_rw [size_eq_log2_succ, log2_push, Nat.add_right_comm]

theorem size_push_of_isMaxed (hp : p.isMaxed) : (p.push b).size = p.size + 1 := by
  simp_rw [size_push, hp]
  rfl

theorem size_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).size = p.size := by
  simp_rw [size_push, hp]
  rfl

theorem sizeInc_push_of_not_isMaxed (hp : ¬ p.isMaxed) :
    (p.push b).sizeInc = p.sizeInc - 1 := by
  simp_rw [sizeInc_eq_two_pow_size_sub_count, count_push, size_push_of_not_isMaxed hp]
  exact Nat.sub_succ' _ _

theorem sizeInc_push_of_isMaxed (hp : p.isMaxed) :
    (p.push b).sizeInc = 2^p.size := by
  simp_rw [sizeInc_eq_two_pow_size_sub_count, count_push, size_push_of_isMaxed hp,
    isMaxed_iff_count_eq_pred_two_pow_size.mp hp, Nat.sub_one_add_one (Nat.two_pow_pos _).ne',
    pow_succ', two_mul, Nat.add_sub_cancel]

theorem last_push_eq_push_of_not_isMaxed (hp : ¬ p.isMaxed) : (p.push b).last = p.last := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · exact (hp isMaxed_sngl).elim
  · simp_rw [push_bit0, last_bit1, last_bit0]
  · simp_rw [isMaxed_bit1_iff] at hp
    simp_rw [push_bit1, last_bit0, IH hp, last_bit1]

theorem last_push_eq_hash_of_isMaxed (hp : p.isMaxed) :
    (p.push b).last = p.last # p.accumulateLower b := by
  induction p generalizing b with | sngl => _ | bit0 => _ | bit1 _ _ IH => _
  · simp_rw [push_sngl, last_bit0, last_sngl, accumulateLower_sngl]
  · simp_rw [not_isMaxed_bit0] at hp
  · simp_rw [isMaxed_bit1_iff] at hp
    simp_rw [push_bit1, last_bit0, IH hp, last_bit1, accumulateLower_bit1]


end Push

def toTree : (p : PSharedStack β) → BTree β (p.size + 1) → BTree β _
  | sngl a, t => _
  | (bit0 p), t => _
  | (bit1 a p), t => (p.toTree t).lift

-- This is wrong - backwards!

#eval (BTree.bit1 45 (BTree.sngl 77))
#eval (bit1 45 (sngl 77)).toTree
#eval toTree <| (((sngl 4).push 7).push 6).push 5
#eval (4 # 7) # (6 # 5)
section ToTree

theorem get?

end ToTree

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

theorem pushTuple_bit0_succ {bs : Fin (k + 1) → β} :
  (bit0 p).pushTuple bs = (bit1 (bs 0) p).pushTuple (Fin.tail bs) := rfl

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

theorem log2_pushTuple_of_lt_sizeInc (hk : k < p.sizeInc) : (p.pushTuple bs).log2 = p.log2 := by
  apply add_left_injective 1
  simp_rw [← size_eq_log2_succ]
  exact size_pushTuple_of_lt_sizeInc hk

theorem log2_pushTuple_of_le_sizeCap (hk : k ≤ p.sizeCap) : (p.pushTuple bs).log2 = p.log2 :=
  log2_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem log2_pushTuple_sizeCap {bs : Fin k → β} (hk : k = p.sizeCap) :
    (p.pushTuple bs).log2 = p.log2 := log2_pushTuple_of_le_sizeCap hk.le

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

theorem log2_pushTuple_sizeInc {bs : Fin k → β} (hk : k = p.sizeInc) :
    (p.pushTuple bs).log2 = p.log2 + 1 := add_left_injective 1 <| by
  simp_rw [← size_eq_log2_succ, size_pushTuple_sizeInc hk]

theorem pushTuple_two_pow_log2_isRoot_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.log2) : (p.pushTuple bs).isRoot :=
  isRoot_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_log2.mp hp).symm)

theorem pushTuple_pred_two_pow_log2_isMaxed_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.log2 - 1) : (p.pushTuple bs).isMaxed :=
  isMaxed_pushTuple_sizeCap (hk ▸ (isRoot_iff_sizeCap_eq_two_pow_log2.mp hp).symm)

theorem log2_pushTuple_two_pow_log2_eq_succ_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.log2) :
    (p.pushTuple bs).log2 = p.log2 + 1 :=
  log2_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_log2.mp hp).symm)

theorem size_pushTuple_two_pow_log2_eq_succ_of_isRoot (hp : p.isRoot) {bs : Fin k → β}
    (hk : k = 2^p.log2) :
    (p.pushTuple bs).size = p.size + 1 :=
  size_pushTuple_sizeInc (hk ▸ (isRoot_iff_sizeInc_eq_two_pow_log2.mp hp).symm)

end PushTuple


def stackOfTuple [Hash β] [NeZero k] (bs : Fin k → β) : PSharedStack β :=
    (sngl (bs 0)).pushTuple (fun ⟨i, hi⟩ => bs ⟨i.succ, Nat.succ_lt_of_lt_pred hi⟩)

section StackOfTuple

open Fin

variable {n m k : ℕ} {bs : Fin k → β} [Hash β]

@[simp] theorem stackOfTuple_one {bs : Fin 1 → β} : stackOfTuple bs = sngl (bs 0) := rfl

theorem stackOfTuple_succ {bs : Fin (k + 1) → β} :
  stackOfTuple bs = (sngl (bs 0)).pushTuple (Fin.tail bs) := rfl

theorem stackOfTuple_succ_last [NeZero k] {bs : Fin (k + 1) → β} :
    stackOfTuple bs = (stackOfTuple (Fin.init bs)).push (bs (Fin.last k)) := by
  cases k
  · exact (NeZero.ne 0 rfl).elim
  · exact pushTuple_succ_last

theorem stackOfTuple_add [NeZero m] (bs : Fin (m + n) → β) :
  haveI : NeZero (m + n) := ⟨add_ne_zero.mpr (Or.inl <| NeZero.ne m)⟩ ;
  stackOfTuple bs = (stackOfTuple fun i => bs (Fin.castAdd n i)).pushTuple
    fun i => bs (Fin.natAdd m i) := by
  induction n generalizing m with | zero => _ | succ n IH => _
  · simp_rw [Fin.castAdd_zero, Fin.cast_eq_self, pushTuple_zero]
  · haveI : NeZero (m + n) := ⟨add_ne_zero.mpr (Or.inl <| NeZero.ne m)⟩
    simp_rw [stackOfTuple_succ_last, IH, pushTuple_succ_last]
    rfl

theorem stackOfTuple_cons : stackOfTuple (cons b bs) = (sngl b).pushTuple bs := stackOfTuple_succ

theorem stackOfTuple_snoc [NeZero k] :
    stackOfTuple (snoc bs b) = (stackOfTuple bs).push b := by
  simp_rw [stackOfTuple_succ_last, init_snoc, snoc_last]

theorem stackOfTuple_append [NeZero m] {bs₁ : Fin m → β} {bs₂ : Fin n → β} :
    haveI : NeZero (m + n) := ⟨add_ne_zero.mpr (Or.inl <| NeZero.ne m)⟩ ;
    (stackOfTuple bs₁).pushTuple bs₂ = stackOfTuple (append bs₁ bs₂) := by
  simp_rw [stackOfTuple_add, append_left, append_right]

@[simp] theorem stackOfTuple_cast (h : k' = k) [NeZero k] :
    haveI : NeZero k' := ⟨h.trans_ne (NeZero.ne _)⟩
    stackOfTuple (fun i => bs <| Fin.cast h i) = stackOfTuple bs := by
  cases h
  rfl

@[simp] theorem count_stackOfTuple [NeZero k] : (stackOfTuple bs).count = k := by
  unfold stackOfTuple
  simp_rw [count_pushTuple, count_sngl, add_comm]
  exact Nat.succ_pred (NeZero.ne _)

@[simp] theorem log2_stackOfTuple [NeZero k] : (stackOfTuple bs).log2 = k.log2 :=
  (stackOfTuple bs).log2_count_eq_log2 ▸ (congrArg _ count_stackOfTuple)

@[simp] theorem size_stackOfTuple [NeZero k] : (stackOfTuple bs).size = k.size :=
  (stackOfTuple bs).size_count_eq_size ▸ (congrArg _ count_stackOfTuple)

theorem isRoot_stackOfTuple_iff_two_pow [NeZero k] :
    (stackOfTuple bs).isRoot ↔ ∃ n, k = 2^n := by
  rw [isRoot_iff_count_eq_two_pow_log2, count_stackOfTuple, log2_stackOfTuple]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h ▸ Nat.log2_two_pow ▸ rfl⟩

theorem isMaxed_stackOfTuple_iff_two_pow_sub_one [NeZero k] :
    (stackOfTuple bs).isMaxed ↔ ∃ n, k = 2^n - 1 := by
  rw [isMaxed_iff_count_eq_pred_two_pow_size, count_stackOfTuple, size_stackOfTuple]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h ▸ Nat.size_pred_pow ▸ rfl⟩

@[simp] theorem stackOfTwoPowTuple_zero {bs : Fin (2^0) → β} :
    stackOfTuple bs = sngl (bs 0) := rfl

@[simp] theorem stackOfTwoPowTuple_succ {bs : Fin (2^(n + 1)) → β} [NeZero k] :
    stackOfTuple bs = (stackOfTuple (twoPowSuccTupleDivide bs).1).pushTuple
    (twoPowSuccTupleDivide bs).2 := by
  simp_rw [stackOfTuple_append, append_eq_twoPowSuccTuple_symm, Prod.mk.eta,
    Equiv.symm_apply_apply, stackOfTuple_cast]

theorem isRoot_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).isRoot :=
  isRoot_stackOfTuple_iff_two_pow.mpr ⟨_, rfl⟩

theorem count_stackOfTwoPowTuple_pos {bs : Fin (2^n) → β} : 0 < (stackOfTuple bs).count := by
  rw [count_stackOfTuple]
  exact Nat.two_pow_pos _

theorem count_stackOfTwoPowTuple_ne {bs : Fin (2^n) → β} : (stackOfTuple bs).count ≠ 0 :=
  count_stackOfTwoPowTuple_pos.ne'

theorem log2_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).log2 = n := by
  rw [log2_stackOfTuple, Nat.log2_two_pow]

theorem size_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).size = n + 1 := by
  rw [size_stackOfTuple, Nat.size_pow]

theorem isMaxed_stackOfPredTwoPowTuple [NeZero n] {bs : Fin (2^n - 1) → β} :
    (stackOfTuple bs).isMaxed := isMaxed_stackOfTuple_iff_two_pow_sub_one.mpr ⟨_, rfl⟩

theorem log2_stackOfPredTwoPowTuple [NeZero n] {bs : Fin (2^n - 1) → β} :
    (stackOfTuple bs).log2 = n - 1 := by
  rw [log2_stackOfTuple, Nat.log2_pred_two_pow]

theorem size_stackOfPredTwoPowTuple {bs : Fin (2^n - 1) → β} [NeZero n] :
    (stackOfTuple bs).size = n := by
  rw [size_stackOfTuple, Nat.size_pred_pow]


end StackOfTuple

end PSharedStack

inductive SharedStack (β : Type u) : Type u
  | emp : SharedStack β
  | pst : PSharedStack β → SharedStack β

namespace SharedStack

open PSharedStack

variable {β : Type*} {a b : β} {p : PSharedStack β} {s : SharedStack β}

instance : Inhabited (SharedStack β) where
  default := emp

def log2 (s : SharedStack β) : ℕ := s.casesOn 0 (fun p => p.log2)

section Log2

@[simp] theorem log2_emp : (emp : SharedStack β).log2 = 0 := rfl
@[simp] theorem log2_pst : (pst p).log2 = p.log2 := rfl

end Log2

def size (s : SharedStack β) : ℕ := s.casesOn 0 (fun p => p.size)

section Size

@[simp] theorem size_emp : (emp : SharedStack β).size = 0 := rfl
@[simp] theorem size_pst : (pst p).size = p.size := rfl

@[simp] theorem size_eq_zero : s.size = 0 ↔ s = emp :=
  s.casesOn (iff_of_true rfl rfl)
  (fun p => iff_of_false p.size_ne_zero SharedStack.noConfusion)

@[simp] theorem pst_size_pos : 0 < (pst p).size := p.size_pos

@[simp] theorem one_le_size_pos : 1 ≤ (pst p).size := p.size_pos

theorem log2_eq_size_pred : s.log2 = s.size - 1 := s.casesOn rfl (fun _ => rfl)

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

@[simp] theorem log_two_count_eq_log2 : Nat.log 2 s.count = s.log2 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [count_emp, Nat.log_zero_right, log2_emp]
  · exact p.log_two_count_eq_log2

@[simp] theorem log2_count_eq_log2 : s.count.log2 = s.log2 := by
  rw [Nat.log2_eq_log_two, log_two_count_eq_log2]

end Count

-- sizeCap = "we can push this many without increasing the size"

def sizeCap (s : SharedStack β) : ℕ := s.casesOn 0 PSharedStack.sizeCap

section SizeCap

@[simp] theorem sizeCap_emp : (emp : SharedStack β).sizeCap = 0 := rfl
@[simp] theorem sizeCap_bit0 : (pst p).sizeCap = p.sizeCap := rfl

theorem sizeCap_lt_pred_two_pow_size : s.sizeCap ≤ 2^(s.log2) - 1 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [sizeCap_emp, log2_emp, zero_le]
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

theorem sizeInc_lt_two_pow_size : s.sizeInc ≤ 2^s.log2 := by
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

theorem isRoot_iff_count_eq_two_pow_log2 :
    s.isRoot ↔ s.count = 2^s.log2 := s.casesOn
  (iff_of_false not_isRoot_emp zero_ne_one) (fun p => p.isRoot_iff_count_eq_two_pow_log2)

instance : Decidable (s.isRoot) :=
  decidable_of_iff _ isRoot_iff_count_eq_two_pow_log2.symm

theorem isRoot_iff_exists_size_eq_two_pow : s.isRoot ↔ ∃ k, s.count = 2^k := by
  rw [isRoot_iff_count_eq_two_pow_log2]
  refine ⟨fun h => ⟨_, h⟩, fun ⟨k, hk⟩ => ?_⟩
  have H := hk ▸ s.log_two_count_eq_log2
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

theorem log2_pushTuple_of_lt_sizeInc (hk : k < s.sizeInc) : (s.pushTuple bs).log2 = s.log2 := by
  cases s with | emp => _ | pst p => _
  · simp_rw [sizeInc_emp, Nat.lt_one_iff] at hk
    cases hk
    simp_rw [pushTuple_zero]
  · exact p.log2_pushTuple_of_lt_sizeInc hk

theorem log2_pushTuple_of_le_sizeCap (hk : k ≤ s.sizeCap) : (s.pushTuple bs).log2 = s.log2 :=
  log2_pushTuple_of_lt_sizeInc (Nat.lt_succ_of_le hk)

theorem log2_pushTuple_sizeCap {bs : Fin k → β} (hk : k = s.sizeCap) :
    (s.pushTuple bs).log2 = s.log2 := log2_pushTuple_of_le_sizeCap hk.le

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

theorem pushTuple_two_pow_log2_isRoot_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.log2) : (s.pushTuple bs).isRoot := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.pushTuple_two_pow_log2_isRoot_of_isRoot hs hk

theorem log2_pushTuple_two_pow_log2_eq_succ_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.log2) : (s.pushTuple bs).log2 = s.log2 + 1 := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.log2_pushTuple_two_pow_log2_eq_succ_of_isRoot hs hk

theorem size_pushTuple_two_pow_log2_eq_succ_of_isRoot (hs : s.isRoot) {bs : Fin k → β}
    (hk : k = 2^s.log2) :
    (s.pushTuple bs).size = s.size + 1 := by
  cases s with | emp => _ | pst p => _
  · exact (not_isRoot_emp hs).elim
  · exact p.size_pushTuple_two_pow_log2_eq_succ_of_isRoot hs hk

end PushTuple

def stackOfTuple [Hash β] : (bs : Fin k → β) → SharedStack β :=
  k.casesOn (fun _ => emp) (fun _ bs => pst (PSharedStack.stackOfTuple bs))

section StackOfTuple

open Fin

variable {n m k : ℕ} {bs : Fin k → β} [Hash β]

theorem stackOfTuple_of_ne_zero [NeZero k] :
    stackOfTuple bs = pst (PSharedStack.stackOfTuple bs) := by
  cases k
  · exact (NeZero.ne 0 rfl).elim
  · rfl

@[simp] theorem stackOfTuple_zero {bs : Fin 0 → β} : stackOfTuple bs = emp := rfl

@[simp] theorem stackOfTuple_one {bs : Fin 1 → β} : stackOfTuple bs = pst (sngl (bs 0)) := rfl

theorem stackOfTuple_succ {bs : Fin (k + 1) → β} :
  stackOfTuple bs = (pst (sngl (bs 0))).pushTuple (Fin.tail bs) := rfl

theorem stackOfTuple_eq_pushTuple (bs : Fin k → β): stackOfTuple bs = emp.pushTuple bs := rfl

theorem stackOfTuple_succ_last {bs : Fin (k + 1) → β} :
    stackOfTuple bs = (stackOfTuple (Fin.init bs)).push (bs (Fin.last k)) :=
  stackOfTuple_eq_pushTuple bs ▸ pushTuple_succ_last

theorem stackOfTuple_add (bs : Fin (m + n) → β) :
    stackOfTuple bs = (stackOfTuple fun i => bs (Fin.castAdd n i)).pushTuple
    fun i => bs (Fin.natAdd m i) := stackOfTuple_eq_pushTuple bs ▸ pushTuple_add

theorem stackOfTuple_cons : stackOfTuple (cons b bs) = (pst (sngl b)).pushTuple bs :=
  stackOfTuple_eq_pushTuple (cons b bs) ▸ pushTuple_cons

theorem stackOfTuple_snoc : stackOfTuple (snoc bs b) = (stackOfTuple bs).push b :=
  stackOfTuple_eq_pushTuple (snoc bs b) ▸ pushTuple_snoc

theorem stackOfTuple_append {bs₁ : Fin m → β} {bs₂ : Fin n → β} :
    (stackOfTuple bs₁).pushTuple bs₂ = stackOfTuple (append bs₁ bs₂) :=
  stackOfTuple_eq_pushTuple bs₁ ▸ stackOfTuple_eq_pushTuple (append bs₁ bs₂) ▸ pushTuple_append

@[simp] theorem count_stackOfTuple : (stackOfTuple bs).count = k := by
  rw [stackOfTuple_eq_pushTuple]
  simp_rw [count_pushTuple, count_emp, zero_add]

@[simp] theorem log2_stackOfTuple : (stackOfTuple bs).log2 = k.log2 :=
  (stackOfTuple bs).log2_count_eq_log2 ▸ (congrArg _ count_stackOfTuple)

@[simp] theorem size_stackOfTuple : (stackOfTuple bs).size = k.size :=
  (stackOfTuple bs).size_count_eq_size ▸ (congrArg _ count_stackOfTuple)

theorem isRoot_stackOfTuple_iff_two_pow :
    (stackOfTuple bs).isRoot ↔ ∃ n, k = 2^n := by
  rw [isRoot_iff_count_eq_two_pow_log2, count_stackOfTuple, log2_stackOfTuple]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h ▸ Nat.log2_two_pow ▸ rfl⟩

theorem isMaxed_stackOfTuple_iff_two_pow_sub_one :
    (stackOfTuple bs).isMaxed ↔ ∃ n, k = 2^n - 1 := by
  rw [isMaxed_iff_count_eq_pred_two_pow_size, count_stackOfTuple, size_stackOfTuple]
  exact ⟨fun h => ⟨_, h⟩, fun ⟨_, h⟩ => h ▸ Nat.size_pred_pow ▸ rfl⟩

@[simp] theorem stackOfTwoPowTuple_zero {bs : Fin (2^0) → β} :
    stackOfTuple bs = pst (sngl (bs 0)) := rfl

@[simp] theorem stackOfTwoPowTuple_succ {bs : Fin (2^(n + 1)) → β} :
    stackOfTuple bs = (stackOfTuple (twoPowSuccTupleDivide bs).1).pushTuple
    (twoPowSuccTupleDivide bs).2 := by
  simp_rw [stackOfTuple_eq_pushTuple, pushTuple_two_pow_succ]

theorem isRoot_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).isRoot :=
  isRoot_stackOfTuple_iff_two_pow.mpr ⟨_, rfl⟩

theorem count_stackOfTwoPowTuple_pos {bs : Fin (2^n) → β} : 0 < (stackOfTuple bs).count := by
  rw [count_stackOfTuple]
  exact Nat.two_pow_pos _

theorem count_stackOfTwoPowTuple_ne {bs : Fin (2^n) → β} : (stackOfTuple bs).count ≠ 0 :=
  count_stackOfTwoPowTuple_pos.ne'

theorem log2_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).log2 = n := by
  rw [log2_stackOfTuple, Nat.log2_two_pow]

theorem size_stackOfTwoPowTuple {bs : Fin (2^n) → β} : (stackOfTuple bs).size = n + 1 := by
  rw [size_stackOfTuple, Nat.size_pow]

theorem isMaxed_stackOfPredTwoPowTuple {bs : Fin (2^n - 1) → β} : (stackOfTuple bs).isMaxed :=
  isMaxed_stackOfTuple_iff_two_pow_sub_one.mpr ⟨_, rfl⟩

theorem log2_stackOfPredTwoPowTuple {bs : Fin (2^n - 1) → β} : (stackOfTuple bs).log2 = n - 1 := by
  rw [log2_stackOfTuple, Nat.log2_pred_two_pow]

theorem size_stackOfPredTwoPowTuple {bs : Fin (2^n - 1) → β} : (stackOfTuple bs).size = n := by
  rw [size_stackOfTuple, Nat.size_pred_pow]

end StackOfTuple

def finalHash [Hash β] (bs : Fin (2^n) → β) : β :=
  (stackOfTuple bs).last count_stackOfTwoPowTuple_ne

section FinalHash

variable [Hash β]

theorem finalHash_zero (bs : Fin (2^0) → β) : finalHash bs = bs 0 := rfl

theorem finalHash_succ (bs : Fin (2^(n + 1)) → β) : finalHash bs =
    (finalHash (twoPowSuccTupleDivide bs).1) #
    (finalHash (twoPowSuccTupleDivide bs).2) := by
  unfold finalHash
  induction n
  · rfl
  · simp_rw [stackOfTwoPowTuple_succ (bs := bs)]

end FinalHash

end SharedStack
