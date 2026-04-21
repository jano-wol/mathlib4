/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.CartanCriterion
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Trace-nilpotency criterion over arbitrary characteristic-zero fields

This file removes the `IsAlgClosed` hypothesis from
`LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero_algClosed` by scalar extension to the
algebraic closure.

## Main results

* `LieModule.isNilpotent_toEnd_of_traceForm_eq_zero`: the derived ideal `⁅L, L⁆` acts nilpotently
  on any finite-dimensional representation `M` of a Lie algebra `L` whose trace form vanishes,
  over any field of characteristic zero.
-/

@[expose] public section

open scoped TensorProduct
open LinearMap Module

section BaseChange

variable {K : Type*} [Field K] {Kbar : Type*} [Field Kbar] [Algebra K Kbar]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
lemma End.baseChangeHom_injective :
    Function.Injective (End.baseChangeHom K Kbar V) := fun f g hfg ↦ by
  ext v
  simpa using FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := Kbar) V
    (LinearMap.congr_fun hfg ((1 : Kbar) ⊗ₜ[K] v))

end BaseChange

namespace LieModule

private lemma traceForm_baseChange_eq_zero
    {K L M : Type*} [Field K]
    [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K M]
    {Kbar : Type*} [Field Kbar] [Algebra K Kbar]
    (h : traceForm K L M = 0) :
    traceForm Kbar (Kbar ⊗[K] L) (Kbar ⊗[K] M) = 0 := by
  apply LinearMap.ext
  refine fun u => TensorProduct.induction_on u ?_ ?_ ?_
  · simp
  · intro a x
    apply LinearMap.ext
    refine fun v => TensorProduct.induction_on v ?_ ?_ ?_
    · simp
    · intro b y
      rw [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply]
      have hx : toEnd Kbar (Kbar ⊗[K] L) (Kbar ⊗[K] M) (a ⊗ₜ[K] x) =
          a • (toEnd K L M x).baseChange Kbar := by
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, toEnd_baseChange]
      have hy : toEnd Kbar (Kbar ⊗[K] L) (Kbar ⊗[K] M) (b ⊗ₜ[K] y) =
          b • (toEnd K L M y).baseChange Kbar := by
        rw [TensorProduct.tmul_eq_smul_one_tmul, map_smul, toEnd_baseChange]
      rw [hx, hy, LinearMap.smul_comp, LinearMap.comp_smul, smul_smul,
        ← LinearMap.baseChange_comp, map_smul, LinearMap.trace_baseChange]
      have ht : trace K M (toEnd K L M x ∘ₗ toEnd K L M y) = 0 := by
        have := LinearMap.congr_fun (LinearMap.congr_fun h x) y
        rwa [traceForm_apply_apply, LinearMap.zero_apply, LinearMap.zero_apply] at this
      simp [ht]
    · intro v₁ v₂ hv₁ hv₂
      rw [map_add, hv₁, hv₂, map_add]
  · intro u₁ u₂ hu₁ hu₂
    rw [map_add, hu₁, hu₂, map_add]

/-- **Trace-nilpotency criterion** over arbitrary fields of characteristic zero.

Proved by scalar extension to the algebraic closure.
See `isNilpotent_derivedSeries_of_traceForm_eq_zero_algClosed` for the algebraically closed case. -/
theorem isNilpotent_toEnd_of_traceForm_eq_zero
    {K : Type*} [Field K] [CharZero K]
    {L : Type*} [LieRing L] [LieAlgebra K L]
    {M : Type*} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K M]
    (h : traceForm K L M = 0) :
    IsNilpotent (LieAlgebra.derivedSeries K L 1) M := by
  let Kbar := AlgebraicClosure K
  haveI : FiniteDimensional Kbar (Kbar ⊗[K] M) := Module.Finite.base_change K Kbar M
  have key : IsNilpotent (LieAlgebra.derivedSeries Kbar (Kbar ⊗[K] L) 1) (Kbar ⊗[K] M) :=
    isNilpotent_derivedSeries_of_traceForm_eq_zero_algClosed (traceForm_baseChange_eq_zero h)
  rw [LieModule.isNilpotent_iff_forall' (R := K)]
  rw [LieModule.isNilpotent_iff_forall' (R := Kbar)] at key
  intro ⟨x, hx⟩
  rw [show toEnd K (LieAlgebra.derivedSeries K L 1) M ⟨x, hx⟩ = toEnd K L M x from rfl]
  rw [← IsNilpotent.map_iff (f := End.baseChangeHom K Kbar M) End.baseChangeHom_injective]
  have hx_bar : (1 : Kbar) ⊗ₜ[K] x ∈ LieAlgebra.derivedSeries Kbar (Kbar ⊗[K] L) 1 := by
    rw [LieAlgebra.derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have step := key ⟨(1 : Kbar) ⊗ₜ[K] x, hx_bar⟩
  rw [show toEnd Kbar (LieAlgebra.derivedSeries Kbar (Kbar ⊗[K] L) 1) (Kbar ⊗[K] M) ⟨_, hx_bar⟩ =
      toEnd Kbar (Kbar ⊗[K] L) (Kbar ⊗[K] M) ((1 : Kbar) ⊗ₜ[K] x) from rfl] at step
  rw [toEnd_baseChange] at step
  exact step

end LieModule
