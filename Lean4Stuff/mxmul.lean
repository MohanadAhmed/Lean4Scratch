import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

variable {l m α : Type*} [Fintype m]

open BigOperators Matrix
open Equiv Equiv.Perm Finset Function

variable [CommRing α]

example (u v : m → α) (A : Matrix m m α) :
    dotProduct u (mulVec A  v) = ∑ i, (∑ j, u i * A i j * v j) := by
  simp_rw [dotProduct, mulVec, dotProduct, Finset.mul_sum, mul_assoc]

example (n : ℕ) (u v : Fin n → α) (A : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, (∑ j : Fin n, ((-1 : α)^(i + j : ℕ)) * u i * A i j * v j) =
      ∑ i : Fin n, (-1 : α)^(i:ℕ) * (∑ j : Fin n, (-1 : α)^(j : ℕ) * u i * A i j * v j) := by
  simp_rw [Finset.mul_sum, mul_assoc, pow_add, mul_assoc]

example (n : ℕ) (u v : Fin n → α) (A : Matrix (Fin n) (Fin n) α) :
    ∑ i : Fin n, (∑ j : Fin n, ((-1 : α)^(i + j : ℕ)) * u i * A i j * v j) =
      ∑ i : Fin n, (-1 : α)^(i:ℕ) * u i * (∑ j : Fin n, (-1 : α)^(j : ℕ) *  A i j * v j) := by
  simp_rw [Finset.mul_sum, pow_add]
  congr; ext; congr; ext;
  ring

#eval Fin.pred (3 : Fin 5) (by decide)

def unitSumFinEquiv (m : ℕ) [NeZero m]: Unit ⊕ Fin m ≃ Fin (Nat.succ m) where
  toFun := Sum.elim (0) (fun z => Fin.succ z)
  invFun := fun z => match z with
    | 0 => @Sum.inl (Unit) (Fin m) ()
    | ⟨y + 1, _⟩ => @Sum.inr (Unit) (Fin m) (y)
  left_inv := by
    intro z
    cases' z with x x
    dsimp
    rfl
    dsimp
    cases' x with x x
    dsimp
    refine Sum.inr.inj_iff.mpr ?inr.mk.a
    ext
    simp only [Fin.coe_ofNat_eq_mod]
    exact Nat.mod_eq_of_lt x
  right_inv := by
    intro z
    dsimp
    split
    dsimp
    simp only [Sum.elim_inr]
    ext
    dsimp
    simp only [Nat.succ.injEq]
    rw [Nat.succ_eq_add_one] at *
    simp at *
    apply (Nat.mod_eq_iff_lt _).2
    assumption
    apply NeZero.ne _

-- #eval (@unitSumFinEquiv 4).symm 0

theorem det_replace (n : ℕ) [NeZero n] (A : Matrix (Fin n) (Fin n) α) (u v : Fin n → α) :
    det (fromBlocks 1 (row u) (col v) A) =
      det (reindex (unitSumFinEquiv n) (unitSumFinEquiv n) (fromBlocks 1 (row u) (col v) A)) := by
  exact (det_reindex_self (unitSumFinEquiv n) (fromBlocks 1 (row u) (col v) A)).symm
  done

theorem det_replace_scalar (n : ℕ) [NeZero n] (A : Matrix (Fin n) (Fin n) α) (u v : Fin n → α) :
    det (fromBlocks 0 (row u) (col v) A) =
      det (reindex (unitSumFinEquiv n) (unitSumFinEquiv n) (fromBlocks 0 (row u) (col v) A)) := by
  exact (det_reindex_self (unitSumFinEquiv n) (fromBlocks 0 (row u) (col v) A)).symm
  done

@[simp]
theorem unitSumFinEquiv_zero (m : ℕ) [NeZero m] : (unitSumFinEquiv m).symm 0 = Sum.inl () := by
  unfold unitSumFinEquiv
  dsimp
  split
  rfl
  rename_i a b c d
  exfalso
  have hz1 := congr_arg Fin.val d
  simp only [Fin.val_succ, Nat.succ.injEq] at hz1
  apply (Nat.succ_ne_zero b) hz1.symm
  done


#eval ((unitSumFinEquiv 3).symm ∘ Fin.succ) (1 : Fin 3)

@[simp]
theorem unitSumFinEquiv_finSucc (m : ℕ) [NeZero m] (i : Fin m) :
  (unitSumFinEquiv m).symm (Fin.succ i) = Sum.inr i := by
  simp_rw [unitSumFinEquiv, coe_fn_symm_mk]
  split
  simp only
  rename_i _ y hy hz
  have hz1 := congr_arg Fin.val hz
  simp only [Fin.val_succ, Nat.succ.injEq] at hz1
  have hz2 := Nat.add_one_ne_zero (i : ℕ)
  exact hz2 hz1
  rename_i _ y hy hz
  simp only [Sum.inr.injEq]
  rw [Nat.succ_eq_add_one, add_lt_add_iff_right] at hy
  have hz1 := congr_arg Fin.val hz
  simp only [Fin.val_succ, Nat.succ.injEq] at hz1
  rw [← hz1]
  exact Fin.cast_val_eq_self i
  done

theorem finSucc_submatrix (n : ℕ) [NeZero n] (u v : Fin n → α) (A : Matrix (Fin n) (Fin n) α) :
  submatrix (fromBlocks 1 (row u) (col v) A)
    ((unitSumFinEquiv n).symm ∘ Fin.succ) ((unitSumFinEquiv n).symm ∘ Fin.succ) = A := by
  funext i j
  simp
  -- simp only [submatrix_apply, comp_apply, unitSumFinEquiv_finSucc]
  -- rfl

theorem unique_unitSumfinZero (n : ℕ) (hn : n = 0): Unique (Unit ⊕ Fin n) := by
  refine { toInhabited := ?toInhabited, uniq := ?uniq }
  exact Sum.inhabitedLeft
  intro a
  cases' a with a a
  rfl
  simp only
  apply Fin.elim0
  rw [hn] at a
  exact a

theorem detBlock_eq_det_add_det_block_remove (n : ℕ) -- [NeZero n]
    (u v : Fin n → α) (A : Matrix (Fin n) (Fin n) α) :
    det (fromBlocks 1 (row u) (col v) A) = det A + det (fromBlocks 0 (row u) (col v) A) := by
  by_cases hn : n = 0
  letI := unique_unitSumfinZero n hn
  · simp only [det_fromBlocks_one₁₁]
    haveI : IsEmpty (Fin n) := by
      apply isEmpty_iff.2
      intro A
      apply Fin.elim0
      rw [hn] at A
      apply A
    rw [det_isEmpty, det_isEmpty, self_eq_add_right]
    sorry


  · haveI : NeZero n := neZero_iff.2 hn
    rw [det_replace, det_succ_row_zero]
    simp only [unitSumFinEquiv_zero, reindex_apply, submatrix_apply, submatrix_submatrix]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, unitSumFinEquiv_zero, fromBlocks_apply₁₁, one_apply_eq,
      mul_one, Fin.succAbove_zero, one_mul, Fin.val_succ]
    rw [finSucc_submatrix, add_right_inj]
    simp only [unitSumFinEquiv_finSucc, fromBlocks_apply₁₂, row_apply]

    rw [det_replace_scalar, det_succ_row_zero]
    simp only [unitSumFinEquiv_zero, reindex_apply, submatrix_apply, submatrix_submatrix]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, unitSumFinEquiv_zero, fromBlocks_apply₁₁, one_apply_eq,
      mul_one, Fin.succAbove_zero, one_mul, Fin.val_succ]
    simp only [zero_apply, zero_mul, unitSumFinEquiv_finSucc, fromBlocks_apply₁₂,
      row_apply, zero_add]
    rfl

theorem det_fromBlocks₁₁_one_scalar (n : ℕ)
    (u v : Fin n → α) (A : Matrix (Fin n) (Fin n) α) :
    (A - col v * row u).det = (fromBlocks 1 (row u) (col v) A).det := by
  letI invOne : Invertible (1 : Matrix Unit Unit α) := invertibleOne
  rw [det_fromBlocks₁₁]
  simp

lemma det_unit_fin_n (n : ℕ) (e : Unit ⊕ Fin n ≃ Fin (n + 1))
  (A : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) α ) : A.det = (reindex e e A).det := by
  simp only [reindex_apply, det_submatrix_equiv_self]

theorem wierd2 (n : ℕ) [NeZero n] (A : Matrix (Fin n) (Fin n) α) (u v : (Fin n) → α) :
    (A - col v * row u).det = A.det + v ⬝ᵥ (adjugate A).mulVec u := by
  rw [det_fromBlocks₁₁_one_scalar, detBlock_eq_det_add_det_block_remove, add_right_inj]
  rw [det_unit_fin_n _ (unitSumFinEquiv n), det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, reindex_apply, submatrix_apply, unitSumFinEquiv_zero,
    fromBlocks_apply₁₁, zero_apply, mul_zero, Fin.succAbove_zero, submatrix_submatrix, zero_mul,
    Fin.val_succ, Nat.odd_iff_not_even, unitSumFinEquiv_finSucc, fromBlocks_apply₁₂, row_apply,
    zero_add]
  rename_i hn
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (hn.ne)
  simp_rw [dotProduct, mulVec, dotProduct, mul_sum]
  rw [Finset.sum_comm]
  congr
  ext z
  simp_rw [mul_assoc]
