/-
Humphreys' Lemma (Introduction to Lie Algebras, §4.3)

This file states Humphreys' lemma over algebraically closed fields (with sorry).
The general characteristic zero version (by scalar extension) is in
`Mathlib.Algebra.Lie.HumphreysLemmaGeneral`.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic

open LinearMap

/-- Humphreys' Lemma over algebraically closed fields of characteristic zero.

Given subspaces `A ≤ B` of `gl(V)` and `M = {z ∈ gl(V) : [z, B] ⊆ A}`,
if `x ∈ M` satisfies `tr(xz) = 0` for all `z ∈ M`, then `x` is nilpotent. -/
theorem humphreys_lemma_algClosed
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (htr : ∀ z : Module.End K V, (∀ b ∈ B, ⁅z, b⁆ ∈ A) →
           trace K V (x * z) = 0) :
    IsNilpotent x := by
  sorry
