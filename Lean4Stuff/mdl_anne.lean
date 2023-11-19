import Mathlib

universe z

open Equiv Equiv.Perm Finset Function

namespace Matrix

open Matrix BigOperators

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type z} [CommRing R]

noncomputable def unitSumFinEquiv {m : ℕ} : Unit ⊕ Fin m ≃ Fin (m + 1) :=
  (Equiv.sumComm _ _).trans <|
  (Equiv.sumCongr (.refl _) (Fintype.equivFinOfCardEq rfl)).trans
  finSumFinEquiv

/-- theorem i want to apply: -/

-- theorem det_succ_row_zero {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) :
--     det A = ∑ j : Fin n.succ, (-1) ^ (j : ℕ) * A 0 j * det (A.submatrix Fin.succ j.succAbove)

theorem mdl_without_A_invertible (A : Matrix m m R) (u v : m → R):
    (A + col u * row v).det = A.det + v ⬝ᵥ (adjugate A).mulVec u := by
    have h1 :
      (A + col u * row v).det = (A - (- col u) * row v).det := by
        simp
    rw [h1]
    rw [← det_fromBlocks_one₁₁]
    sorry

theorem mdl_without_A_invertible_Fin? {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (u v : (Fin m) → R):
    (A + col u * row v).det = A.det + v ⬝ᵥ (adjugate A).mulVec u := by
  have h1 :
    (A + col u * row v).det = (A - (- col u) * row v).det := by
      simp
  have h2 : det (A - (- col u) * row v) =
    ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) *
      reindex unitSumFinEquiv unitSumFinEquiv (fromBlocks 1 (row v) (-col u) A) 0 j *
      det (submatrix (reindex unitSumFinEquiv unitSumFinEquiv (fromBlocks 1 (row v) (-col u) A))
        Fin.succ (Fin.succAbove j)) := by
    rw [← det_fromBlocks_one₁₁, ← Matrix.det_reindex_self unitSumFinEquiv, det_succ_row_zero]
  rw [h1, h2]
