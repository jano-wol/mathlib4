/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.Algebra.Operations

/-!
# Strictly upper triangular matrices and superdiagonal filtration

The diagonal projection on the upper triangular subalgebra is an algebra homomorphism.
Its kernel consists of strictly upper triangular matrices. The superdiagonal filtration
records how far above the diagonal entries can occur; multiplication adds these distances.
-/

@[expose] public section

namespace Matrix

variable {R A ι : Type*}

/-- A strictly upper triangular matrix vanishes on and below the diagonal. -/
def IsStrictlyUpperTriangular [LE ι] [Zero A] (M : Matrix ι ι A) : Prop :=
  ∀ ⦃i j⦄, j ≤ i → M i j = 0

section Basic
variable [LinearOrder ι] [Zero A] {M N : Matrix ι ι A}

protected theorem IsStrictlyUpperTriangular.isUpperTriangular
    (h : M.IsStrictlyUpperTriangular) : M.IsUpperTriangular := fun _ _ hij => h hij.le

@[simp] theorem isStrictlyUpperTriangular_zero : (0 : Matrix ι ι A).IsStrictlyUpperTriangular :=
  fun _ _ _ => rfl

protected theorem IsStrictlyUpperTriangular.diag_eq_zero (h : M.IsStrictlyUpperTriangular) :
    M.diag = 0 := by
  funext i
  exact h le_rfl

lemma isStrictlyUpperTriangular_iff : M.IsStrictlyUpperTriangular ↔
    M.IsUpperTriangular ∧ M.diag = 0 := by
  refine ⟨fun h => ⟨h.isUpperTriangular, h.diag_eq_zero⟩, ?_⟩
  rintro ⟨hu, hd⟩ i j hij
  rcases hij.eq_or_lt with he | hij
  · subst j
    exact congrFun hd i
  · exact hu hij
end Basic

protected theorem IsStrictlyUpperTriangular.add [LinearOrder ι] [AddZeroClass A]
    {M N : Matrix ι ι A} (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M + N).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij, hN hij]

protected theorem IsStrictlyUpperTriangular.neg [LinearOrder ι] [NegZeroClass A]
    {M : Matrix ι ι A} (hM : M.IsStrictlyUpperTriangular) : (-M).IsStrictlyUpperTriangular :=
  fun _ _ hij => by simp [hM hij]

protected theorem IsStrictlyUpperTriangular.sub [LinearOrder ι] [SubNegZeroMonoid A]
    {M N : Matrix ι ι A} (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M - N).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij, hN hij]

protected theorem IsStrictlyUpperTriangular.smul [LinearOrder ι] [Zero A] [SMulZeroClass R A]
    {M : Matrix ι ι A} (hM : M.IsStrictlyUpperTriangular) (r : R) :
    (r • M).IsStrictlyUpperTriangular := fun _ _ hij => by simp [hM hij]

section Multiplication
variable [Fintype ι] [LinearOrder ι] [Semiring A] {M N : Matrix ι ι A}

/-- Diagonal projection is multiplicative on upper triangular matrices. -/
theorem IsUpperTriangular.diag_mul (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N).diag = M.diag * N.diag := by
  funext i
  apply Finset.sum_eq_single i
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hij | hij
    · simp [hM hij]
    · simp [hN hij]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

protected theorem IsStrictlyUpperTriangular.mul_upperTriangular
    (hM : M.IsStrictlyUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨hM.isUpperTriangular.mul hN, ?_⟩
  rw [hM.isUpperTriangular.diag_mul hN, hM.diag_eq_zero, zero_mul]

protected theorem IsUpperTriangular.mul_strictlyUpperTriangular
    (hM : M.IsUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨hM.mul hN.isUpperTriangular, ?_⟩
  rw [hM.diag_mul hN.isUpperTriangular, hN.diag_eq_zero, mul_zero]

protected theorem IsStrictlyUpperTriangular.mul
    (hM : M.IsStrictlyUpperTriangular) (hN : N.IsStrictlyUpperTriangular) :
    (M * N).IsStrictlyUpperTriangular := hM.mul_upperTriangular hN.isUpperTriangular

protected theorem IsStrictlyUpperTriangular.trace_eq_zero
    (hM : M.IsStrictlyUpperTriangular) : M.trace = 0 := by
  simp [Matrix.trace, show ∀ i, M i i = 0 from fun i => hM le_rfl]

end Multiplication

section DiagonalHom
variable [CommSemiring R] [Semiring A] [Algebra R A]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- The diagonal projection from the upper triangular subalgebra to tuples of coefficients. -/
def upperTriangularDiagAlgHom :
    blockTriangularSubalgebra R A (id : ι → ι) →ₐ[R] (ι → A) where
  toFun M := (M : Matrix ι ι A).diag
  map_zero' := rfl
  map_one' := by ext i; simp
  map_add' := fun _ _ => rfl
  map_mul' := fun M N => IsUpperTriangular.diag_mul M.property N.property
  commutes' r := by ext i; simp [algebraMap_matrix_apply]

@[simp] theorem upperTriangularDiagAlgHom_apply
    (M : blockTriangularSubalgebra R A (id : ι → ι)) :
    upperTriangularDiagAlgHom (R := R) M = (M : Matrix ι ι A).diag := rfl

theorem upperTriangularDiagAlgHom_surjective :
    Function.Surjective (upperTriangularDiagAlgHom (R := R) (A := A) (ι := ι)) := by
  intro d
  refine ⟨⟨diagonal d, blockTriangular_diagonal d⟩, ?_⟩
  ext i
  simp

/-- The strictly upper triangular ideal inside the upper triangular algebra. -/
def strictlyUpperTriangularIdeal : Ideal (blockTriangularSubalgebra R A (id : ι → ι)) :=
  RingHom.ker (upperTriangularDiagAlgHom (R := R) (A := A) (ι := ι)).toRingHom

@[simp] theorem mem_strictlyUpperTriangularIdeal
    (M : blockTriangularSubalgebra R A (id : ι → ι)) :
    M ∈ strictlyUpperTriangularIdeal (R := R) ↔ (M : Matrix ι ι A).IsStrictlyUpperTriangular := by
  change (M : Matrix ι ι A).diag = 0 ↔ _
  exact ⟨fun h => isStrictlyUpperTriangular_iff.mpr ⟨M.property, h⟩,
    IsStrictlyUpperTriangular.diag_eq_zero⟩
instance strictlyUpperTriangularIdeal_isTwoSided :
    (strictlyUpperTriangularIdeal (R := R) (A := A) (ι := ι)).IsTwoSided := by
  unfold strictlyUpperTriangularIdeal
  infer_instance

end DiagonalHom

section Commutator
variable [CommRing R] [Fintype ι] [LinearOrder ι] {M N : Matrix ι ι R}

/-- The diagonal quotient is commutative, so upper triangular commutators are strictly upper
triangular. -/
theorem IsUpperTriangular.commutator (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) :
    (M * N - N * M).IsStrictlyUpperTriangular := by
  apply isStrictlyUpperTriangular_iff.mpr
  refine ⟨(hM.mul hN).sub (hN.mul hM), ?_⟩
  rw [Matrix.diag_sub, hM.diag_mul hN, hN.diag_mul hM, mul_comm, sub_self]
end Commutator

section Nilpotency
variable [CommRing R] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    {M : Matrix ι ι R}

protected theorem IsStrictlyUpperTriangular.charpoly (h : M.IsStrictlyUpperTriangular) :
    M.charpoly = Polynomial.X ^ Fintype.card ι := by
  rw [charpoly_of_isUpperTriangular _ h.isUpperTriangular]
  simp only [h le_rfl, map_zero, sub_zero, Finset.prod_const, Finset.card_univ]

/-- Strictly upper triangular matrices satisfy a uniform nilpotency bound. -/
protected theorem IsStrictlyUpperTriangular.pow_card_eq_zero (h : M.IsStrictlyUpperTriangular) :
    M ^ Fintype.card ι = 0 := by
  rw [← Polynomial.aeval_X_pow (R := R) (x := M), ← h.charpoly]
  exact Matrix.aeval_self_charpoly M

protected theorem IsStrictlyUpperTriangular.isNilpotent (h : M.IsStrictlyUpperTriangular) :
    IsNilpotent M := ⟨Fintype.card ι, h.pow_card_eq_zero⟩
end Nilpotency

section Filtration
variable (R) [CommRing R] (n : ℕ)

/-- Matrices supported at least `r` superdiagonals above the diagonal. -/
def superdiagonalFiltration (r : ℕ) : Submodule R (Matrix (Fin n) (Fin n) R) where
  carrier := {M | ∀ i j, j.val < i.val + r → M i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := fun hM hN i j hij => by simp [hM i j hij, hN i j hij]
  smul_mem' := fun c M hM i j hij => by simp [hM i j hij]

variable {R n}

@[simp] theorem mem_superdiagonalFiltration {r : ℕ} {M : Matrix (Fin n) (Fin n) R} :
    M ∈ superdiagonalFiltration R n r ↔ ∀ i j, j.val < i.val + r → M i j = 0 := Iff.rfl

@[simp] theorem mem_superdiagonalFiltration_zero {M : Matrix (Fin n) (Fin n) R} :
    M ∈ superdiagonalFiltration R n 0 ↔ M.IsUpperTriangular := by
  simp [IsUpperTriangular, BlockTriangular]

@[simp] theorem mem_superdiagonalFiltration_one {M : Matrix (Fin n) (Fin n) R} :
    M ∈ superdiagonalFiltration R n 1 ↔ M.IsStrictlyUpperTriangular := by
  simp [IsStrictlyUpperTriangular]

theorem superdiagonalFiltration_antitone : Antitone (superdiagonalFiltration R n) := by
  intro p q hpq M hM i j hij
  exact hM i j (by omega)

/-- Multiplication adds the distance above the diagonal. -/
theorem mul_mem_superdiagonalFiltration {p q : ℕ} {M N : Matrix (Fin n) (Fin n) R}
    (hM : M ∈ superdiagonalFiltration R n p) (hN : N ∈ superdiagonalFiltration R n q) :
    M * N ∈ superdiagonalFiltration R n (p + q) := by
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k.val < i.val + p
  · simp [hM i k hki]
  · simp [hN k j (by omega)]

theorem superdiagonalFiltration_mul_le (p q : ℕ) :
    superdiagonalFiltration R n p * superdiagonalFiltration R n q ≤
      superdiagonalFiltration R n (p + q) :=
  Submodule.mul_le.mpr fun _ hM _ hN => mul_mem_superdiagonalFiltration hM hN

/-- The commutator respects superdiagonal degree. -/
theorem commutator_mem_superdiagonalFiltration {p q : ℕ}
    {M N : Matrix (Fin n) (Fin n) R}
    (hM : M ∈ superdiagonalFiltration R n p) (hN : N ∈ superdiagonalFiltration R n q) :
    M * N - N * M ∈ superdiagonalFiltration R n (p + q) := by
  apply Submodule.sub_mem _ (mul_mem_superdiagonalFiltration hM hN)
  simpa [Nat.add_comm] using mul_mem_superdiagonalFiltration hN hM

/-- The descending superdiagonal filtration, indexed by the opposite order on the naturals. -/
def superdiagonalRingFiltration (r : ℕᵒᵈ) : Submodule R (Matrix (Fin n) (Fin n) R) :=
  superdiagonalFiltration R n (OrderDual.ofDual r)

instance superdiagonalRingFiltration_gradedMonoid :
    SetLike.GradedMonoid (superdiagonalRingFiltration (R := R) (n := n)) where
  one_mem := by
    change (1 : Matrix (Fin n) (Fin n) R) ∈ superdiagonalFiltration R n 0
    exact mem_superdiagonalFiltration_zero.mpr blockTriangular_one
  mul_mem := by
    intro p q M N hM hN
    exact mul_mem_superdiagonalFiltration hM hN

/-- The support condition gives a ring filtration, with multiplication adding degrees. -/
instance superdiagonalRingFiltration_isRingFiltration :
    IsRingFiltration (superdiagonalRingFiltration (R := R) (n := n))
      (fun r => superdiagonalFiltration R n (OrderDual.ofDual r + 1)) where
  mono := fun _i _j hij => superdiagonalFiltration_antitone hij
  is_le := fun hij => superdiagonalFiltration_antitone (Nat.succ_le_of_lt hij)
  is_sup := fun _B j h => h (OrderDual.toDual (OrderDual.ofDual j + 1))
    (Nat.lt_succ_self (OrderDual.ofDual j))

@[simp] theorem superdiagonalFiltration_eq_bot {r : ℕ} (hr : n ≤ r) :
    superdiagonalFiltration R n r = ⊥ := by
  apply le_antisymm _ bot_le
  intro M hM
  apply (Submodule.mem_bot R).mpr
  ext i j
  exact hM i j (by have := j.isLt; omega)

theorem pow_mem_superdiagonalFiltration {r : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hM : M ∈ superdiagonalFiltration R n r) (m : ℕ) :
    M ^ m ∈ superdiagonalFiltration R n (m * r) := by
  induction m with
  | zero =>
    simp only [zero_mul, pow_zero, mem_superdiagonalFiltration_zero]
    exact blockTriangular_one
  | succ m ih =>
    simpa [pow_succ, Nat.succ_mul] using mul_mem_superdiagonalFiltration ih hM

/-- A product of strictly upper triangular matrices lies on successively higher superdiagonals. -/
theorem list_prod_mem_superdiagonalFiltration (l : List (Matrix (Fin n) (Fin n) R))
    (h : ∀ M ∈ l, M.IsStrictlyUpperTriangular) :
    l.prod ∈ superdiagonalFiltration R n l.length := by
  induction l with
  | nil =>
    simp only [List.length_nil, List.prod_nil, mem_superdiagonalFiltration_zero]
    exact blockTriangular_one
  | cons M l ih =>
    have hM := mem_superdiagonalFiltration_one.mpr (h M (by simp))
    have hl := ih (fun N hN => h N (by simp [hN]))
    simpa [Nat.add_comm] using mul_mem_superdiagonalFiltration hM hl

/-- Every product of at least `n` strictly upper triangular `n × n` matrices is zero. -/
theorem list_prod_eq_zero_of_isStrictlyUpperTriangular
    (l : List (Matrix (Fin n) (Fin n) R)) (h : ∀ M ∈ l, M.IsStrictlyUpperTriangular)
    (hlen : n ≤ l.length) : l.prod = 0 := by
  have hp := list_prod_mem_superdiagonalFiltration l h
  rw [superdiagonalFiltration_eq_bot hlen] at hp
  exact (Submodule.mem_bot R).mp hp

end Filtration
end Matrix
