/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Triangular matrices with a superdiagonal level

`M.BlockTriangularAtLevel b r` permits nonzero entries only when the column block label is
at least `r` greater than the row block label. Equal labels specify a common block.
Level zero is `M.BlockTriangular b`; level one makes the diagonal blocks vanish as well.
Multiplication adds levels, and transposition negates the labels.
-/

@[expose] public section

namespace Matrix

variable {R S ι κ : Type*}

/-- Entries less than `r` block-label units above the diagonal vanish. -/
def BlockTriangularAtLevel [Zero R] (M : Matrix ι ι R) (b : ι → ℤ) (r : ℕ) : Prop :=
  ∀ ⦃i j⦄, b j < b i + r → M i j = 0

section Zero

variable [Zero R] {M : Matrix ι ι R} {b : ι → ℤ} {r s : ℕ}

instance decidableBlockTriangularAtLevel [Fintype ι] [DecidableEq R] :
    Decidable (M.BlockTriangularAtLevel b r) :=
  decidable_of_iff (∀ ij : ι × ι, b ij.2 < b ij.1 + r → M ij.1 ij.2 = 0)
    ⟨fun h i j hij => h (i, j) hij, fun h _ hij => h hij⟩

@[simp]
theorem blockTriangularAtLevel_zero_iff : M.BlockTriangularAtLevel b 0 ↔ M.BlockTriangular b := by
  simp only [BlockTriangularAtLevel, Nat.cast_zero, add_zero, BlockTriangular]

/-- Level one is strict block triangularity. -/
theorem blockTriangularAtLevel_one_iff :
    M.BlockTriangularAtLevel b 1 ↔ ∀ ⦃i j⦄, b j ≤ b i → M i j = 0 := by
  simp only [BlockTriangularAtLevel, Nat.cast_one, Int.lt_add_one_iff]

@[simp]
theorem blockTriangularAtLevel_zero : (0 : Matrix ι ι R).BlockTriangularAtLevel b r :=
  fun _ _ _ => rfl

protected theorem BlockTriangularAtLevel.of_le (hM : M.BlockTriangularAtLevel b r) (h : s ≤ r) :
    M.BlockTriangularAtLevel b s := fun _ _ hij => hM (by omega)

protected theorem BlockTriangularAtLevel.blockTriangular (hM : M.BlockTriangularAtLevel b r) :
    M.BlockTriangular b := blockTriangularAtLevel_zero_iff.mp (hM.of_le (Nat.zero_le r))

@[simp]
protected theorem BlockTriangularAtLevel.submatrix (hM : M.BlockTriangularAtLevel b r)
    (f : κ → ι) : (M.submatrix f f).BlockTriangularAtLevel (b ∘ f) r := fun _ _ hij => hM hij

theorem blockTriangularAtLevel_reindex_iff {b : κ → ℤ} {e : ι ≃ κ} :
    (M.reindex e e).BlockTriangularAtLevel b r ↔ M.BlockTriangularAtLevel (b ∘ e) r := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simpa using h.submatrix e
  · simpa [Function.comp_assoc] using h.submatrix e.symm

protected theorem BlockTriangularAtLevel.map [Zero S] {F : Type*} [FunLike F R S]
    [ZeroHomClass F R S] (f : F) (hM : M.BlockTriangularAtLevel b r) :
    (M.map f).BlockTriangularAtLevel b r := fun _ _ hij => by simp [hM hij]

protected theorem BlockTriangularAtLevel.smul [SMulZeroClass S R]
    (hM : M.BlockTriangularAtLevel b r) (s : S) : (s • M).BlockTriangularAtLevel b r :=
  fun _ _ hij => by simp [hM hij]

protected theorem BlockTriangularAtLevel.transpose (hM : M.BlockTriangularAtLevel b r) :
    Mᵀ.BlockTriangularAtLevel (fun i => -b i) r := by
  intro i j hij
  exact hM (i := j) (j := i) (by dsimp at hij; omega)

@[simp]
theorem blockTriangularAtLevel_transpose_iff :
    Mᵀ.BlockTriangularAtLevel b r ↔ M.BlockTriangularAtLevel (fun i => -b i) r := by
  constructor <;> intro h <;> simpa using h.transpose

end Zero

protected theorem BlockTriangularAtLevel.add [AddZeroClass R] {M N : Matrix ι ι R}
    {b : ι → ℤ} {r : ℕ} (hM : M.BlockTriangularAtLevel b r)
    (hN : N.BlockTriangularAtLevel b r) : (M + N).BlockTriangularAtLevel b r :=
  fun _ _ hij => by simp [hM hij, hN hij]

protected theorem BlockTriangularAtLevel.neg [NegZeroClass R] {M : Matrix ι ι R}
    {b : ι → ℤ} {r : ℕ} (hM : M.BlockTriangularAtLevel b r) :
    (-M).BlockTriangularAtLevel b r := fun _ _ hij => by simp [hM hij]

protected theorem BlockTriangularAtLevel.sub [SubNegZeroMonoid R] {M N : Matrix ι ι R}
    {b : ι → ℤ} {r : ℕ} (hM : M.BlockTriangularAtLevel b r)
    (hN : N.BlockTriangularAtLevel b r) : (M - N).BlockTriangularAtLevel b r :=
  fun _ _ hij => by simp [hM hij, hN hij]

/-- Multiplication adds superdiagonal levels; coefficients need not commute. -/
protected theorem BlockTriangularAtLevel.mul [Fintype ι] [NonUnitalNonAssocSemiring R]
    {M N : Matrix ι ι R} {b : ι → ℤ} {r s : ℕ}
    (hM : M.BlockTriangularAtLevel b r) (hN : N.BlockTriangularAtLevel b s) :
    (M * N).BlockTriangularAtLevel b (r + s) := by
  intro i j hij
  apply Finset.sum_eq_zero
  intro k _
  by_cases hki : b k < b i + r
  · simp [hM hki]
  · simp [hN (i := k) (j := j) (by omega)]

section Fin

variable [Zero R] {n : ℕ} {M : Matrix (Fin n) (Fin n) R}

theorem blockTriangularAtLevel_fin_zero_iff :
    M.BlockTriangularAtLevel (fun i => (i.val : ℤ)) 0 ↔ M.IsUpperTriangular := by
  simp [blockTriangularAtLevel_zero_iff, BlockTriangular, IsUpperTriangular]

theorem blockTriangularAtLevel_neg_fin_zero_iff :
    M.BlockTriangularAtLevel (fun i => -(i.val : ℤ)) 0 ↔ M.IsLowerTriangular := by
  simp [blockTriangularAtLevel_zero_iff, BlockTriangular, IsLowerTriangular]

theorem blockTriangularAtLevel_fin_one_iff :
    M.BlockTriangularAtLevel (fun i => (i.val : ℤ)) 1 ↔
      ∀ ⦃i j⦄, j ≤ i → M i j = 0 := by
  simp [blockTriangularAtLevel_one_iff]

theorem blockTriangularAtLevel_neg_fin_one_iff :
    M.BlockTriangularAtLevel (fun i => -(i.val : ℤ)) 1 ↔
      ∀ ⦃i j⦄, i ≤ j → M i j = 0 := by
  simp [blockTriangularAtLevel_one_iff]

end Fin
end Matrix
