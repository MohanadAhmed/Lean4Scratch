import Mathlib.Data.Matrix.Invertible
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

variable {l m α : Type*}

namespace Matrix

open scoped Matrix

open BigOperators

open Nat

variable [CommRing α]

variable (m n : ℕ)

#check (@Fin.succ n)
#check (@Fin.succAbove n 0)

example : (@Fin.succ n) = (@Fin.succAbove n 0) := rfl

def unitSumFinEquiv {m : ℕ} : Unit ⊕ Fin m ≃ Fin (m + 1) :=
  Equiv.sumComm _ _
    |>.trans <| Equiv.sumCongr (.refl _) (Equiv.equivPUnit _).symm
    |>.trans <| finSumFinEquiv

lemma det_unit_fin_n (n : ℕ) (e : Unit ⊕ Fin n ≃ Fin (n + 1))
  (A : Matrix (Unit ⊕ Fin n) (Unit ⊕ Fin n) α ) : A.det = (reindex e e A).det := by
  simp only [reindex_apply, det_submatrix_equiv_self]

lemma unitSumFinEquiv_sum_inl {m : ℕ} : (@unitSumFinEquiv m) (Sum.inl default) = 0 := by sorry

lemma unitSumFinEquiv_sum_inr {m : ℕ} (i : Fin m) : (@unitSumFinEquiv m) (Sum.inr i) = i := by sorry

lemma subx (Z : Matrix (Fin (n)) (Fin (n)) α) (U V : (Fin (n)) → α) :
  submatrix (fromBlocks 1 ((row V)) (-(col U)) Z)
    ((↑unitSumFinEquiv.symm) ∘ Fin.succ) ((↑unitSumFinEquiv.symm) ∘ Fin.succ) = Z := by
  -- funext x y
  -- unfold unitSumFinEquiv Equiv.sumCongr Sum.map Equiv.equivPUnit Fin.succ
  -- dsimp
  -- simp
  sorry

theorem mdl_without_invertible (Z : Matrix (Fin (n)) (Fin (n)) α)
  (U V : (Fin (n)) → α) :
    (Z + col U * row V).det = Z.det + V ⬝ᵥ (adjugate Z).mulVec U := by

  let Q := fromBlocks Z (col U) (row V) 1
  have : (fromBlocks 1 ((row V)) (-(col U)) Z).det = (Z + col U * row V).det := by sorry
  rw [← this]
  rw [det_unit_fin_n n (@unitSumFinEquiv _)]
  rw [det_succ_row_zero]
  simp_rw [reindex_apply, submatrix_apply]

  have : (@unitSumFinEquiv n).symm (0) = (Sum.inl 0) := by sorry
  rw [this]
  rw [← Equiv.sum_comp (@unitSumFinEquiv n), Fintype.sum_sum_type]
  simp only [Finset.univ_unique, Finset.sum_singleton, Equiv.symm_apply_apply, fromBlocks_apply₁₁,
    submatrix_submatrix, one_apply_eq, mul_one, unitSumFinEquiv_sum_inl]
  simp only [Fin.val_zero, _root_.pow_zero, Fin.succAbove_zero, one_mul, odd_iff_not_even,
    PUnit.zero_eq, fromBlocks_apply₁₂, row_apply, subx]
  simp only [add_right_inj]
  sorry











  -- congr
  -- funext i
  -- let Q : Matrix (Fin 1) (Fin 1) α := fun _ _ => V ⬝ᵥ  (mulVec (adjugate Z) U)
  -- have Q00 : Q 0 0 = V ⬝ᵥ  (mulVec (adjugate Z) U)  := rfl
  -- rw [← Q00, ← Matrix.trace_fin_one Q]


-- theorem mdl_without_A_invertible
--     (A : Matrix m m α) (u v : m → α)  :
--     (A + col u * row v).det = A.det + v ⬝ᵥ (adjugate A).mulVec u := by
--   by_cases h : Nonempty m
--   obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero : Fintype.card m ≠ 0)
--   obtain ⟨e⟩ := Fintype.truncEquivFinOfCardEq hm
--   let Z := reindex e e A
--   let U := (fun i => u (e.symm i))
--   let V := (fun i => v (e.symm i))
--   have : (Z + col U * row V).det = Z.det + V ⬝ᵥ (adjugate Z).mulVec U := by
--     sorry
--   apply this
--   dsimp at Z U
