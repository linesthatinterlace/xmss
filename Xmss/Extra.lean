import Mathlib

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
