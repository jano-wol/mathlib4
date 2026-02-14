/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.TraceForm

/-!
# Killing complement of Lie ideals

In a Killing Lie algebra, every ideal and its Killing orthogonal complement are complementary.
This provides the key algebraic fact needed for the order isomorphism between Lie ideals and
invariant root submodules.

## Main results

* `LieIdeal.disjoint_killingCompl`: an ideal and its Killing complement are disjoint
* `LieIdeal.codisjoint_killingCompl`: an ideal and its Killing complement are codisjoint
* `LieIdeal.isCompl_killingCompl`: an ideal and its Killing complement are complementary
* `LieIdeal.compl_eq_killingCompl`: the lattice complement equals the Killing complement
-/

@[expose] public section

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

namespace LieIdeal

noncomputable section

omit [CharZero K] [FiniteDimensional K L] in
/-- The bracket of elements in `I ⊓ I.killingCompl` is zero: if `x, y ∈ I ∩ I⊥`, then
`κ(⁅x,y⁆, z) = κ(x, ⁅y,z⁆) = 0` for all `z` (since `⁅y,z⁆ ∈ I` and `x ∈ I⊥`),
so non-degeneracy gives `⁅x,y⁆ = 0`. -/
private lemma lie_mem_inf_killingCompl_eq_zero (I : LieIdeal K L) {x y : L}
    (hx : x ∈ I ⊓ I.killingCompl) (hy : y ∈ I ⊓ I.killingCompl) : ⁅x, y⁆ = 0 := by
  have hxK : x ∈ killingCompl K L I := ((LieSubmodule.mem_inf I I.killingCompl x).mp hx).2
  have hyI : y ∈ I := ((LieSubmodule.mem_inf I I.killingCompl y).mp hy).1
  have h_zero : ∀ z : L, (LieModule.traceForm K L L) ⁅x, y⁆ z = 0 := by
    intro z
    rw [LieModule.traceForm_apply_lie_apply, LieModule.traceForm_comm]
    exact (LieIdeal.mem_killingCompl K L I).mp hxK ⁅y, z⁆ (lie_mem_left K L I y z hyI)
  exact (LieAlgebra.IsKilling.killingForm_nondegenerate K L).1 ⁅x, y⁆ h_zero

omit [CharZero K] in
/-- An ideal in a Killing Lie algebra and its Killing complement are disjoint. The proof shows
that `I ⊓ I.killingCompl` is abelian (using `lie_mem_inf_killingCompl_eq_zero`), hence zero
in a semisimple Lie algebra. -/
theorem disjoint_killingCompl (I : LieIdeal K L) : Disjoint I I.killingCompl := by
  rw [disjoint_iff]
  set J : LieIdeal K L := I ⊓ I.killingCompl
  haveI : IsLieAbelian J :=
    ⟨fun ⟨_, hx⟩ ⟨_, hy⟩ => Subtype.ext (lie_mem_inf_killingCompl_eq_zero I hx hy)⟩
  haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
  exact LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable J

omit [CharZero K] in
/-- The lattice complement of an ideal in a Killing Lie algebra is contained in its
Killing orthogonal complement. The proof shows `ad(x) ∘ ad(y) = 0` for `x ∈ I`, `y ∈ Iᶜ`:
since `⁅y, z⁆ ∈ Iᶜ` (ideal) and `⁅x, ⁅y,z⁆⁆ ∈ I ∩ Iᶜ = ⊥`. -/
theorem compl_le_killingCompl (I : LieIdeal K L) : Iᶜ ≤ I.killingCompl := by
  haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
  intro y hy
  rw [LieIdeal.mem_killingCompl]
  intro x hx
  suffices h : ∀ z : L, ⁅x, ⁅y, z⁆⁆ = 0 by
    have h_comp : (LieModule.toEnd K L L x).comp (LieModule.toEnd K L L y) = 0 := by
      ext z
      simp only [LinearMap.comp_apply, LieModule.toEnd_apply_apply, LinearMap.zero_apply]
      exact h z
    change LieModule.traceForm K L L x y = 0
    rw [LieModule.traceForm_apply_apply, h_comp, map_zero]
  intro z
  have h_yz : ⁅y, z⁆ ∈ (Iᶜ : LieIdeal K L) := lie_mem_left K L Iᶜ y z hy
  have h_mem : ⁅x, ⁅y, z⁆⁆ ∈ (I ⊓ Iᶜ : LieIdeal K L) :=
    (LieSubmodule.mem_inf I Iᶜ _).mpr
      ⟨lie_mem_left K L I x _ hx, lie_mem_right K L Iᶜ x _ h_yz⟩
  rw [inf_compl_eq_bot] at h_mem
  simpa using h_mem

omit [CharZero K] in
/-- An ideal in a Killing Lie algebra and its Killing complement are codisjoint.
This follows from `compl_le_killingCompl` and `I ⊔ Iᶜ = ⊤`. -/
theorem codisjoint_killingCompl (I : LieIdeal K L) :
    Codisjoint I I.killingCompl := by
  haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
  rw [codisjoint_iff_le_sup]
  calc ⊤ = I ⊔ Iᶜ := (sup_compl_eq_top (x := I)).symm
    _ ≤ I ⊔ I.killingCompl := sup_le_sup_left (compl_le_killingCompl I) I

omit [CharZero K] in
/-- An ideal in a Killing Lie algebra and its Killing orthogonal complement are
complementary. -/
theorem isCompl_killingCompl (I : LieIdeal K L) : IsCompl I I.killingCompl :=
  ⟨disjoint_killingCompl I, codisjoint_killingCompl I⟩

omit [CharZero K] in
/-- In a Killing Lie algebra, the lattice complement of an ideal equals its Killing
orthogonal complement. -/
theorem compl_eq_killingCompl (I : LieIdeal K L) : Iᶜ = I.killingCompl := by
  haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
  exact (isCompl_killingCompl I).compl_eq

end

end LieIdeal
