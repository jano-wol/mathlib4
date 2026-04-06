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

private lemma isBaseChange_end_equiv_tmul (a : Kbar) (f : End K V) :
    ((TensorProduct.isBaseChange K V Kbar).end).equiv (a ⊗ₜ f) = a • f.baseChange Kbar := by
  rw [IsBaseChange.equiv_tmul]
  apply (TensorProduct.isBaseChange K V Kbar).algHom_ext; intro v
  rw [LinearMap.smul_apply, IsBaseChange.endHom_comp_apply]
  simp [baseChange_tmul]

private lemma ker_baseChange_eq {N P : Type*} [AddCommGroup N] [AddCommGroup P]
    [Module K N] [Module K P] (f : N →ₗ[K] P) :
    LinearMap.ker (f.baseChange Kbar) = (LinearMap.ker f).baseChange Kbar :=
  Flat.ker_lTensor_eq (M := Kbar) (S := Kbar) f

private lemma piRight_baseChange_component {N Q : Type*} [AddCommGroup N] [Module K N]
    [AddCommGroup Q] [Module K Q] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Φ : N →ₗ[K] (ι → Q)) (w : Kbar ⊗[K] N) (i : ι) :
    TensorProduct.piRight K Kbar Kbar (fun _ : ι => Q) (Φ.baseChange Kbar w) i =
      ((proj i).comp Φ).baseChange Kbar w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [baseChange_tmul, TensorProduct.piRight]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- If a base-changed `LinearMap.pi` has every component acting by zero on `w`, then it
acts by zero on `w`. -/
private lemma baseChange_pi_eq_zero {N Q : Type*} [AddCommGroup N] [Module K N]
    [AddCommGroup Q] [Module K Q] {ι : Type*} [Finite ι]
    (Φ : N →ₗ[K] (ι → Q)) (w : Kbar ⊗[K] N)
    (h : ∀ i, ((proj i).comp Φ).baseChange Kbar w = 0) :
    Φ.baseChange Kbar w = 0 := by
  have := Fintype.ofFinite ι; classical
  let pR := TensorProduct.piRight K Kbar Kbar (fun _ : ι => Q)
  suffices pR (Φ.baseChange Kbar w) = 0 from pR.injective (this.trans pR.map_zero.symm)
  ext i; rw [piRight_baseChange_component, h i, Pi.zero_apply]

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
  have he_tmul : ∀ (a : Kbar) (f : End K V), e (a ⊗ₜ f) = a • bc f :=
    isBaseChange_end_equiv_tmul
  have he_one : ∀ f : End K V, e (1 ⊗ₜ f) = bc f := fun f => by rw [he_tmul, one_smul]
  -- Bridge: `span Kbar (bc '' S) = (S.baseChange Kbar).map e.toLinearMap` for any K-submodule S.
  have hspan_bc : ∀ S : Submodule K (End K V),
      Submodule.span Kbar (bc '' (S : Set _)) = (S.baseChange Kbar).map e.toLinearMap := fun S ↦ by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe,
      ← Set.image_comp]
    congr 1
    exact Set.image_congr fun f _ ↦ (he_one f).symm
  rw [← IsNilpotent.map_iff (f := End.baseChangeHom K Kbar V) End.baseChangeHom_injective]
  let A' : Submodule Kbar (End Kbar (Kbar ⊗[K] V)) := Submodule.span Kbar (bc '' ↑A)
  let B' : Submodule Kbar (End Kbar (Kbar ⊗[K] V)) := Submodule.span Kbar (bc '' ↑B)
  apply isNilpotent_of_trace_orthogonal_algClosed A' B'
  · exact Submodule.span_mono (Set.image_mono hAB)
  · intro b' hb'
    induction hb' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨b, hb, rfl⟩ := h
      change bc x * bc b - bc b * bc x ∈ A'
      rw [← map_mul bc, ← map_mul bc, ← map_sub bc]
      exact Submodule.subset_span ⟨⁅x, b⁆, hxM b hb, rfl⟩
    | zero => rw [lie_zero]; exact A'.zero_mem
    | add _ _ _ _ ha hb => rw [lie_add]; exact A'.add_mem ha hb
    | smul c _ _ hb => rw [lie_smul]; exact A'.smul_mem c hb
  · intro z hz
    let M_sub : Submodule K (End K V) :=
      { carrier := {w | ∀ b ∈ B, ⁅w, b⁆ ∈ A}
        zero_mem' := fun _ _ => by simp
        add_mem' := fun ha hb c hc => by rw [add_lie]; exact A.add_mem (ha c hc) (hb c hc)
        smul_mem' := fun c _ ha b hb => by rw [smul_lie]; exact A.smul_mem c (ha b hb) }
    suffices hz_mem : z ∈ Submodule.span Kbar (bc '' (M_sub : Set _)) by
      refine (?_ : Submodule.span Kbar (bc '' (M_sub : Set _)) ≤
        LinearMap.ker ((trace Kbar _).comp (LinearMap.mulLeft Kbar (bc x)))) hz_mem
      rw [Submodule.span_le]
      rintro _ ⟨z₀, hz₀, rfl⟩
      change trace Kbar _ (bc x * bc z₀) = 0
      rw [← map_mul bc, show bc (x * z₀) = (x * z₀).baseChange Kbar from rfl,
        LinearMap.trace_baseChange, htr z₀ hz₀, map_zero]
    rw [hspan_bc M_sub, Submodule.mem_map_equiv]
    set s := finrank K ↥B
    let bB := finBasis K ↥B
    let φ : Fin s → (End K V →ₗ[K] End K V ⧸ A) := fun i =>
      (Submodule.mkQ A).comp (mulRight K (bB i).1 - mulLeft K (bB i).1)
    let Φ := LinearMap.pi φ
    have hkerΦ : ker Φ = M_sub := by
      ext w
      simp only [mem_ker, Φ, pi_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, funext_iff, Pi.zero_apply]
      refine ⟨fun h b hb ↦ ?_, fun h i ↦ h (bB i).1 (bB i).2⟩
      obtain ⟨c, rfl⟩ := bB.mem_submodule_iff'.mp hb
      change w * _ - _ * w ∈ A
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact A.sum_mem fun i _ ↦ by
        rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
        exact A.smul_mem _ (h i)
    rw [← hkerΦ, ← ker_baseChange_eq, mem_ker]
    refine baseChange_pi_eq_zero Φ _ fun i ↦ ?_
    -- Let `L := mulRight - mulLeft` for `(bB i).1`; the `i`-th component of `Φ` is `mkQ A ∘ L`.
    set L : End K V →ₗ[K] End K V := mulRight K (bB i).1 - mulLeft K (bB i).1
    rw [show (proj i).comp Φ = (Submodule.mkQ A).comp L from by ext; simp [Φ, φ, L],
      baseChange_comp, comp_apply, ← mem_ker, ker_baseChange_eq, Submodule.ker_mkQ]
    -- Through `e`, the base-changed `L` becomes the commutator with `bc (bB i).1`.
    have hcomm : ∀ w : Kbar ⊗[K] End K V,
        e (L.baseChange Kbar w) = e w * bc (bB i).1 - bc (bB i).1 * e w := fun w ↦ by
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a f =>
        rw [show L.baseChange Kbar (a ⊗ₜ f) = a ⊗ₜ (f * (bB i).1 - (bB i).1 * f) from rfl,
          he_tmul, he_tmul, map_sub, map_mul, map_mul, smul_sub, smul_mul_assoc, mul_smul_comm]
      | add u v hu hv => rw [map_add, map_add, hu, hv, map_add, add_mul, mul_add]; abel
    rw [← e.symm_apply_apply (L.baseChange Kbar (e.symm z)), ← Submodule.mem_map_equiv,
      ← hspan_bc A, hcomm, e.apply_symm_apply]
    exact hz _ (Submodule.subset_span ⟨(bB i).1, (bB i).2, rfl⟩)
