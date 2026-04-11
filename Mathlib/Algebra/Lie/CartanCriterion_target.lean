/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.HumphreysLemmaGeneral_target
public import Mathlib.Algebra.Lie.Engel

/-!
# Cartan's Criterion for Lie algebras

In characteristic zero, the kernel of the Killing form of any finite-dimensional Lie algebra
is contained in the solvable radical (`killingCompl_top_le_radical`). As a corollary, any
finite-dimensional Lie algebra with trivial radical has non-degenerate Killing form
(`HasTrivialRadical.instIsKilling`).

The proof uses Humphreys' lemma together with Engel's theorem.

## Main results

* `LieAlgebra.killingCompl_top_le_radical`
* `LieAlgebra.HasTrivialRadical.instIsKilling`
-/

@[expose] public section

open LieAlgebra LieModule LinearMap Module

namespace LieAlgebra

variable (K L : Type*) [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- **Cartan's criterion**: In characteristic zero, the kernel of the Killing form of a
finite-dimensional Lie algebra is contained in the solvable radical. -/
lemma killingCompl_top_le_radical :
    LieIdeal.killingCompl K L ⊤ ≤ radical K L := by
  rw [← LieIdeal.solvable_iff_le_radical]
  set S := LieIdeal.killingCompl K L ⊤
  set SS : LieIdeal K L := ⁅S, S⁆
  let ad_lin : L →ₗ[K] End K L := ad K L
  have hS_tf : LieModule.traceForm K ↥S L = 0 := by
    ext ⟨x, hxS⟩ ⟨y, hyS⟩
    change trace K L ((ad K L) x ∘ₗ (ad K L) y) = 0
    rw [← killingForm_apply_apply, LieModule.traceForm_comm]
    exact (LieIdeal.mem_killingCompl K L ⊤).mp hxS y (LieSubmodule.mem_top y)
  have key : LieModule.IsNilpotent (LieAlgebra.derivedSeries K ↥S 1) L :=
    LieModule.isNilpotent_toEnd_of_traceForm_eq_zero hS_tf
  rw [LieModule.isNilpotent_iff_forall' (R := K)] at key
  have ad_nil : ∀ x ∈ (SS : LieSubmodule K L L).toSubmodule, IsNilpotent (ad_lin x) := by
    intro x hx
    have hxS : x ∈ S := LieSubmodule.lie_le_left S S hx
    have hxDS : (⟨x, hxS⟩ : ↥S) ∈ LieAlgebra.derivedSeries K ↥S 1 := by
      rw [LieIdeal.derivedSeries_eq_derivedSeriesOfIdeal_comap, LieIdeal.mem_comap]
      exact hx
    exact key ⟨⟨x, hxS⟩, hxDS⟩
  have ss_nilpotent : LieRing.IsNilpotent ↥SS := by
    have : IsNoetherian K ↥SS := isNoetherian_submodule' (SS : LieSubmodule K L L).toSubmodule
    rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
    rintro ⟨x, hx⟩
    rw [show ad K ↥SS ⟨x, hx⟩ = (ad_lin x).restrict fun _ hy ↦ SS.lie_mem hy from
      by ext ⟨_, _⟩; rfl]
    exact Module.End.isNilpotent.restrict _ (ad_nil x hx)
  obtain ⟨k, hk⟩ := IsSolvable.solvable K ↥SS
  rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
  refine .mk (k := k + 1) ((LieIdeal.derivedSeries_eq_bot_iff S (k + 1)).mpr ?_)
  rw [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]; exact hk

/-- In characteristic zero, any finite-dimensional Lie algebra with trivial radical has
non-degenerate Killing form. -/
instance HasTrivialRadical.instIsKilling [HasTrivialRadical K L] : IsKilling K L where
  killingCompl_top_eq_bot := by
    have h := killingCompl_top_le_radical K L
    rwa [HasTrivialRadical.radical_eq_bot, le_bot_iff] at h

end LieAlgebra
