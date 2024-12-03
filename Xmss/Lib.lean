import Mathlib

namespace Fin

variable {α : Type*} {bs : Fin (2 ^ (n + 1)) → α} {bsₗ : Fin (2 ^ n) → α} {bsᵣ : Fin (2 ^ n) → α}

def fstTwoPowSuccTuple (bs : Fin (2 ^ (n + 1)) → α) : Fin (2 ^ n) → α :=
  fun j => bs ⟨j, j.isLt.trans <| Nat.pow_lt_pow_succ one_lt_two⟩

theorem fstTwoPowSuccTuple_apply : (fstTwoPowSuccTuple bs) j =
    bs ⟨j, j.isLt.trans <| Nat.pow_lt_pow_succ one_lt_two⟩ := rfl

theorem fstTwoPowSuccTuple_apply_of_coe_eq {j : Fin (2^n)} {i : Fin (2^(n + 1))}
    (hij : (i : ℕ) = (j : ℕ)) : (fstTwoPowSuccTuple bs) j = bs i :=
  fstTwoPowSuccTuple_apply.trans (congrArg _ (Fin.ext hij.symm))

def sndTwoPowSuccTuple (bs : Fin (2 ^ (n + 1)) → α) : Fin (2 ^ n) → α :=
  fun j => bs ⟨j + 2^n, Nat.two_pow_succ _ ▸ (Nat.add_lt_add_right j.isLt _)⟩

theorem sndTwoPowSuccTuple_apply : (sndTwoPowSuccTuple bs) j =
    bs ⟨j + 2^n, Nat.two_pow_succ _ ▸ (Nat.add_lt_add_right j.isLt _)⟩ := rfl

theorem sndTwoPowSuccTuple_apply_of_coe_eq {j : Fin (2^n)} {i : Fin (2^(n + 1))}
    (hij : (i : ℕ) = (j : ℕ) + 2^n) : (sndTwoPowSuccTuple bs) j = bs i :=
  sndTwoPowSuccTuple_apply.trans (congrArg _ (Fin.ext hij.symm))

def appendTwoPowTuples (bsₗ : Fin (2 ^ n) → α) (bsᵣ : Fin (2 ^ n) → α) : Fin (2 ^ (n + 1)) → α :=
  fun i => (lt_or_le (i : ℕ) (2^n)).by_cases
  (fun hi => bsₗ ⟨i, hi⟩)
  (fun hi => bsᵣ ⟨i - 2^n, Nat.sub_lt_right_of_lt_add hi (Nat.two_pow_succ n ▸ i.isLt)⟩)

theorem appendTwoPowTuples_apply_of_lt {i : Fin (2^(n + 1))} (hi : (i : ℕ) < 2^n) :
    appendTwoPowTuples bsₗ bsᵣ i = bsₗ ⟨i, hi⟩ := dif_pos hi

theorem appendTwoPowTuples_apply_of_lt_of_coe_eq {i : Fin (2^(n + 1))} {j : Fin (2^n)}
    (hi : (i : ℕ) < 2^n) (hij : (i : ℕ) = (j : ℕ)) :
  appendTwoPowTuples bsₗ bsᵣ i = bsₗ j := (dif_pos hi).trans (congrArg _ (Fin.ext hij))

theorem appendTwoPowTuples_apply_of_ge {i : Fin (2^(n + 1))} (hi : 2^n ≤ (i : ℕ)) :
    appendTwoPowTuples bsₗ bsᵣ i =
    bsᵣ ⟨i - 2^n, Nat.sub_lt_right_of_lt_add hi (Nat.two_pow_succ n ▸ i.isLt)⟩ := dif_neg hi.not_lt

theorem appendTwoPowTuples_apply_of_ge_of_coe_eq {i : Fin (2^(n + 1))} {j : Fin (2^n)}
    (hi : 2^n ≤ (i : ℕ)) (hij : (i : ℕ) = (j : ℕ) + 2^n) :
    appendTwoPowTuples bsₗ bsᵣ i = bsᵣ j :=
  (dif_neg hi.not_lt).trans (congrArg _ (Fin.ext (Nat.sub_eq_of_eq_add hij)))

@[simp] theorem appendTwoPowTuples_fstTwoPowSuccTuple_sndTwoPowSuccTuple :
    appendTwoPowTuples (fstTwoPowSuccTuple bs) (sndTwoPowSuccTuple bs) = bs := funext fun i => by
  rcases lt_or_le (i : ℕ) (2^n) with hi | hi
  · simp_rw [appendTwoPowTuples_apply_of_lt hi]
    exact fstTwoPowSuccTuple_apply_of_coe_eq rfl
  · simp_rw [appendTwoPowTuples_apply_of_ge hi]
    exact sndTwoPowSuccTuple_apply_of_coe_eq (Nat.sub_add_cancel hi).symm

@[simp] theorem fstTwoPowSuccTuple_appendTwoPowTuples :
    fstTwoPowSuccTuple (appendTwoPowTuples bsₗ bsᵣ) = bsₗ := funext fun i => by
  simp_rw [fstTwoPowSuccTuple_apply]
  exact appendTwoPowTuples_apply_of_lt_of_coe_eq i.isLt rfl

@[simp] theorem sndTwoPowSuccTuple_appendTwoPowTuples :
    sndTwoPowSuccTuple (appendTwoPowTuples bsₗ bsᵣ) = bsᵣ := funext fun i => by
  simp_rw [sndTwoPowSuccTuple_apply]
  exact appendTwoPowTuples_apply_of_ge_of_coe_eq (Nat.le_add_left _ _) rfl

@[simps!]
def twoPowSuccTupleDivide : (Fin (2 ^ (n + 1)) → α) ≃ (Fin (2 ^ n) → α) × (Fin (2 ^ n) → α) where
  toFun t := ⟨fstTwoPowSuccTuple t, sndTwoPowSuccTuple t⟩
  invFun t := appendTwoPowTuples t.1 t.2
  left_inv _ := appendTwoPowTuples_fstTwoPowSuccTuple_sndTwoPowSuccTuple
  right_inv _ :=
  Prod.ext fstTwoPowSuccTuple_appendTwoPowTuples sndTwoPowSuccTuple_appendTwoPowTuples

theorem twoPowSuccTupleDivide_fst_zero (bs : Fin (2 ^ (n + 1)) → α) :
  (twoPowSuccTupleDivide bs).1 0 = bs 0 := rfl

theorem twoPowSuccTupleDivide_snd_zero (bs : Fin (2 ^ (n + 1)) → α) :
    (twoPowSuccTupleDivide bs).2 0 = bs (⟨2^n, Nat.pow_lt_pow_succ one_lt_two⟩) :=
  sndTwoPowSuccTuple_apply_of_coe_eq (Nat.zero_add _).symm

/-- To show two sigma pairs of tuples agree, it to show the second elements are related via
`Fin.cast`. -/
theorem sigma_eq_of_eq_comp_cast' {α : Type*} {f : ℕ → ℕ} :
    ∀ {a b : Σii, Fin (f ii) → α} (h : a.fst = b.fst),
    a.snd = b.snd ∘ Fin.cast (congrArg _ h) → a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    subst hi
    simpa using h

/-- `Fin.sigma_eq_of_eq_comp_cast'` as an `iff`. -/
theorem sigma_eq_iff_eq_comp_cast' {α : Type*}  {f : ℕ → ℕ} {a b : Σii, Fin (f ii) → α} :
    a = b ↔ ∃ h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast (congrArg _ h) :=
  ⟨fun h ↦ h ▸ ⟨rfl, funext <| Fin.rec fun _ _ ↦ rfl⟩, fun ⟨_, h'⟩ ↦
    sigma_eq_of_eq_comp_cast' (by assumption) h'⟩

end Fin

namespace List


theorem length_take_succ_length_div_two {l : List α} :
    (l.take ((l.length + 1) / 2)).length = (l.length + 1) / 2 := by
  simp_rw [List.length_take, min_eq_left_iff, Nat.div_le_iff_le_mul_add_pred zero_lt_two,
    two_mul, ← one_add_one_eq_two, Nat.add_sub_cancel, Nat.add_le_add_iff_right,
    Nat.le_add_right]

theorem length_drop_succ_length_div_two {l : List α} :
    (l.drop ((l.length + 1) / 2)).length = l.length / 2 := by
  simp_rw [List.length_drop]
  refine Nat.sub_eq_of_eq_add ?_
  by_cases hnp : Even (l.length)
  · rw [Nat.add_div_of_dvd_right hnp.two_dvd, Nat.div_eq_of_lt one_lt_two,
      add_zero, ← two_mul, Nat.two_mul_div_two_of_even hnp]
  · rw [← Nat.add_div_of_dvd_left (Nat.even_add_one.mpr hnp).two_dvd, ← add_assoc,
      ← two_mul, Nat.mul_add_div zero_lt_two, Nat.div_eq_of_lt one_lt_two, add_zero]

theorem length_drop_le_length_take {l : List α} :
    (l.drop k).length ≤ (l.take k).length ↔ (l.length + 1) / 2 ≤ k := by
  simp_rw [length_drop, length_take, le_min_iff, tsub_le_iff_right, le_add_iff_nonneg_right,
    zero_le, and_true, ← two_mul, Nat.div_le_iff_le_mul_add_pred zero_lt_two,
    ← one_add_one_eq_two, Nat.add_sub_cancel, Nat.add_le_add_iff_right]

theorem length_drop_succ_length_div_two_le_length_take_succ_length_div_two {l : List α} :
    (l.drop ((l.length + 1) / 2)).length ≤ (l.take ((l.length + 1) / 2)).length :=
  length_drop_le_length_take.mpr le_rfl

@[simp]
theorem length_take_pos {l : List α} {k : Nat} :
    0 < (l.take k).length ↔ 0 < l.length ∧ 0 < k := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

@[simp]
theorem length_drop_pos {l : List α} {k : Nat} : 0 < (l.drop k).length ↔ k < l.length := by
  cases l <;> cases k <;> simp [Nat.succ_ne_zero]

theorem length_drop_lt_length {l : List α} :
    (List.drop k l).length < l.length ↔ 0 < l.length ∧ 0 < k := by
  simp_rw [length_drop, tsub_lt_self_iff]

theorem length_take_lt_length {l : List α} :
    (List.take k l).length < l.length ↔ k < l.length := by
  simp_rw [length_take, min_lt_iff, lt_self_iff_false, or_false]

theorem length_take_lt_length_drop {l : List α} :
    (l.take k).length < (l.drop k).length ↔ k < (l.length + 1) / 2 := by
  simp_rw [lt_iff_not_le, length_drop_le_length_take]


end List

namespace Nat

@[simp] theorem log2_one : log2 1 = 0 := log2_two_pow (n := 0)

theorem size_eq_log2_succ {n : ℕ} (hn : n ≠ 0) : n.size = n.log2 + 1 := by
  refine le_antisymm ?_ ?_
  · rw [size_le]
    exact lt_log2_self
  · rw [succ_le_iff, log2_lt hn]
    exact lt_size_self _

theorem log2_eq_size_pred {n : ℕ} (hn : n ≠ 0) : n.log2 = n.size - 1 := by
  rw [size_eq_log2_succ hn, Nat.add_sub_cancel]

theorem log2_bit (h : n ≠ 0) : (bit b n).log2 = n.log2.succ := by
  simp_rw [log2_eq_size_pred (bit_ne_zero _ h),
    size_bit (bit_ne_zero _ h), succ_sub_one, size_eq_log2_succ h]

theorem log2_eq_iff_of_ne_zero (hn : n ≠ 0) : log2 n = m ↔ 2^m ≤ n ∧ n < 2^(m + 1) := by
  rw [log2_eq_log_two, log_eq_iff (Or.inr ⟨one_lt_two, hn⟩)]

theorem log2_eq_iff_of_ne_zero_right (hm : m ≠ 0) :
    log2 n = m ↔ 2^m ≤ n ∧ n < 2^(m + 1) := by
  rw [log2_eq_log_two, log_eq_iff (Or.inl hm)]

theorem log2_eq_succ_iff :
    log2 n = m + 1 ↔ 2^(m + 1) ≤ n ∧ n < 2^(m + 2) :=
  log2_eq_iff_of_ne_zero_right (succ_ne_zero _)

theorem log2_eq_zero_iff : log2 n = 0 ↔ n = 0 ∨ n = 1 := by
  simp_rw [log2_eq_log_two, log_eq_zero_iff, one_lt_two.not_le, or_false,
    Nat.lt_succ_iff, le_one_iff_eq_zero_or_eq_one]

theorem log2_pred_two_pow {n : ℕ} : (2^n - 1).log2 = n - 1 := by
  rcases n with (_ | (_ | n))
  · simp_rw [pow_zero, Nat.sub_self, log2_zero]
  · simp_rw [zero_add, pow_one, Nat.add_one_sub_one, log2_one]
  · simp_rw [add_tsub_cancel_right, log2_eq_succ_iff]
    refine ⟨le_sub_one_of_lt ?_, pred_lt_self (Nat.two_pow_pos _)⟩
    simp_rw [pow_succ', mul_lt_mul_left zero_lt_two,
      lt_mul_iff_one_lt_left (Nat.two_pow_pos _), one_lt_two]

theorem size_two_mul [NeZero n] : (2*n).size = n.size + 1 := by
  refine size_bit (b := false) ?_
  simp_rw [bit_false, mul_ne_zero_iff]
  exact ⟨NeZero.ne 2, NeZero.ne n⟩

theorem size_two_mul_add_one : (2*n + 1).size = n.size + 1:= by
  refine size_bit (b := true) ?_
  simp_rw [bit_true, ne_eq, succ_ne_zero, not_false_eq_true]

theorem size_div_two_succ [NeZero n] : (n / 2).size + 1 = n.size := by
  rcases even_or_odd n with h | h
  · have : NeZero (n / 2) := ⟨(Nat.div_ne_zero_iff zero_lt_two.ne').mpr <|
      (NeZero.one_le).lt_of_ne (fun C => (not_even_one (C ▸ h)).elim)⟩
    rw [← size_two_mul, two_mul_div_two_of_even h]
  · rw [← size_two_mul_add_one, two_mul_div_two_add_one_of_odd h]

theorem size_pred_pow {n : ℕ} : (2^n - 1).size = n := by
  cases n
  · simp_rw [pow_zero, Nat.sub_self, size_zero]
  · exact le_antisymm (size_le.mpr <| Nat.pred_lt_self (Nat.two_pow_pos _))
      (lt_size.mpr <| (Nat.le_pred_iff_lt (Nat.two_pow_pos _)).mpr
      (Nat.pow_lt_pow_succ one_lt_two))


end Nat
