/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.HumphreysLemma_target
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Humphreys' Lemma (general characteristic zero case)

This file proves Humphreys' lemma over arbitrary fields of characteristic zero
by scalar extension to the algebraic closure.

## Main results

* `humphreys_lemma`: Humphreys' lemma over arbitrary fields of characteristic zero.
-/

@[expose] public section

open scoped TensorProduct
open LinearMap Module

section BaseChange

variable {K : Type*} [Field K] {Kbar : Type*} [Field Kbar] [Algebra K Kbar]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

-- TODO: belongs in Mathlib/LinearAlgebra/TensorProduct/Tower.lean or similar
omit [FiniteDimensional K V] in
/-- Base change of endomorphisms is injective for field extensions. -/
lemma End.baseChangeHom_injective :
    Function.Injective (End.baseChangeHom K Kbar V) := fun f g hfg ↦ by
  ext v
  simpa using FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := Kbar) V
    (LinearMap.congr_fun hfg ((1 : Kbar) ⊗ₜ[K] v))

private lemma ker_baseChange_eq {N P : Type*} [AddCommGroup N] [AddCommGroup P]
    [Module K N] [Module K P] (f : N →ₗ[K] P) :
    LinearMap.ker (f.baseChange Kbar) = (LinearMap.ker f).baseChange Kbar :=
  Flat.ker_lTensor_eq (M := Kbar) (S := Kbar) f

end BaseChange

/-- **Humphreys' Lemma** over arbitrary fields of characteristic zero.

Proved by scalar extension to the algebraic closure.
See `humphreys_lemma_algClosed` for the algebraically closed case. -/
theorem humphreys_lemma
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K (End K V))
    (hAB : A ≤ B)
    (x : End K V)
    (hxM : x ∈ NilpotentOfTrace.M A B)
    (htr : ∀ z ∈ NilpotentOfTrace.M A B, trace K V (x * z) = 0) :
    IsNilpotent x := by
  let Kbar := AlgebraicClosure K
  haveI : FiniteDimensional Kbar (Kbar ⊗[K] V) := Module.Finite.base_change K Kbar V
  let bc : End K V →ₐ[K] End Kbar (Kbar ⊗[K] V) := End.baseChangeHom K Kbar V
  let e := (TensorProduct.isBaseChange K V Kbar).end.equiv
  have he_tmul : ∀ (a : Kbar) (f : End K V), e (a ⊗ₜ f) = a • bc f := fun a f ↦ by
    apply (TensorProduct.isBaseChange K V Kbar).algHom_ext; intro v
    rw [IsBaseChange.equiv_tmul, LinearMap.smul_apply, IsBaseChange.endHom_comp_apply]; rfl
  have he_one : ∀ f : End K V, e (1 ⊗ₜ f) = bc f := fun f ↦ by rw [he_tmul, one_smul]
  -- Bridge: `span Kbar (bc '' S) = (S.baseChange Kbar).map e.toLinearMap` for any K-submodule S.
  have hspan_bc : ∀ S : Submodule K (End K V),
      Submodule.span Kbar (bc '' (S : Set _)) = (S.baseChange Kbar).map e.toLinearMap := fun S ↦ by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, ← Set.image_comp]
    exact congr_arg _ (Set.image_congr fun f _ ↦ (he_one f).symm)
  rw [← IsNilpotent.map_iff (f := End.baseChangeHom K Kbar V) End.baseChangeHom_injective]
  let A' : Submodule Kbar (End Kbar (Kbar ⊗[K] V)) := Submodule.span Kbar (bc '' ↑A)
  let B' : Submodule Kbar (End Kbar (Kbar ⊗[K] V)) := Submodule.span Kbar (bc '' ↑B)
  apply isNilpotent_of_trace_orthogonal_algClosed A' B'
  · exact Submodule.span_mono (Set.image_mono hAB)
  · refine fun b' hb' ↦ (?_ : B' ≤ A'.comap (LieAlgebra.ad Kbar _ (bc x))) hb'
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    change bc x * bc b - bc b * bc x ∈ A'
    rw [← map_mul bc, ← map_mul bc, ← map_sub bc]
    exact Submodule.subset_span ⟨⁅x, b⁆, hxM b hb, rfl⟩
  · intro z hz
    let bB := finBasis K ↥B
    let Φ : End K V →ₗ[K] (Fin _ → End K V ⧸ A) := LinearMap.pi fun i ↦
      (Submodule.mkQ A).comp (mulRight K (bB i).1 - mulLeft K (bB i).1)
    -- Elements of `ker Φ` satisfy `[w, b] ∈ A` for every `b ∈ B`.
    have hker_le : ∀ w ∈ ker Φ, ∀ b ∈ B, ⁅w, b⁆ ∈ A := fun w hw b hb ↦ by
      simp only [Φ, mem_ker, pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, funext_iff, Pi.zero_apply] at hw
      obtain ⟨c, rfl⟩ := bB.mem_submodule_iff'.mp hb
      simpa [lie_sum, lie_smul] using A.sum_mem fun i _ ↦ A.smul_mem (c i) (hw i)
    suffices hz_mem : z ∈ Submodule.span Kbar (bc '' (ker Φ : Set _)) by
      change z ∈ LinearMap.ker ((trace Kbar _).comp (LinearMap.mulLeft Kbar (bc x)))
      refine Submodule.span_le.mpr ?_ hz_mem
      rintro _ ⟨z₀, hz₀, rfl⟩
      change trace Kbar _ (bc x * bc z₀) = 0
      rw [← map_mul bc, show bc (x * z₀) = (x * z₀).baseChange Kbar from rfl,
        LinearMap.trace_baseChange, htr z₀ (hker_le z₀ hz₀), map_zero]
    rw [hspan_bc (ker Φ), Submodule.mem_map_equiv, ← ker_baseChange_eq, mem_ker]
    -- Check `Φ.baseChange Kbar (e.symm z) = 0` component-wise via `piRight` injectivity.
    refine (TensorProduct.piRight K Kbar Kbar _).injective (funext fun i ↦ ?_)
    rw [show (TensorProduct.piRight K Kbar Kbar _) (Φ.baseChange Kbar (e.symm z)) i =
        ((proj i).comp Φ).baseChange Kbar (e.symm z) from (e.symm z).induction_on (by simp)
      (fun a n ↦ by simp [baseChange_tmul, TensorProduct.piRight])
      (fun u v hu hv ↦ by simp only [map_add, Pi.add_apply, hu, hv]), map_zero, Pi.zero_apply]
    -- Let `L := mulRight - mulLeft` for `(bB i).1`; the `i`-th component of `Φ` is `mkQ A ∘ L`.
    set L : End K V →ₗ[K] End K V := mulRight K (bB i).1 - mulLeft K (bB i).1
    rw [show (proj i).comp Φ = (Submodule.mkQ A).comp L from LinearMap.proj_pi _ i,
      baseChange_comp, comp_apply, ← mem_ker, ker_baseChange_eq, Submodule.ker_mkQ]
    -- Through `e`, the base-changed `L` becomes the commutator with `bc (bB i).1`.
    have hcomm : ∀ w : Kbar ⊗[K] End K V,
        e (L.baseChange Kbar w) = e w * bc (bB i).1 - bc (bB i).1 * e w := fun w ↦
      w.induction_on (by simp)
        (fun a f ↦ by simp [L, baseChange_tmul, he_tmul, map_sub, map_mul])
        (fun u v hu hv ↦ by simp [hu, hv, add_mul, mul_add]; abel)
    rw [← e.symm_apply_apply (L.baseChange Kbar (e.symm z)), ← Submodule.mem_map_equiv,
      ← hspan_bc A, hcomm, e.apply_symm_apply]
    exact hz _ (Submodule.subset_span ⟨(bB i).1, (bB i).2, rfl⟩)
