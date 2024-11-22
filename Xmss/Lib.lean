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

-- instance instDecidableEqNil : Decidable (l = []) := decidable_of_iff _ List.length_eq_zero

end List
