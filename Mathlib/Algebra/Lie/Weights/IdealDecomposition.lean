/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing

/-!
# Decomposition of Lie ideals via root spaces

This file proves a decomposition result for Lie ideals of a finite-dimensional Lie algebra
whose Killing form is non-singular (`IsKilling`): any Lie ideal decomposes as its intersection
with a Cartan subalgebra plus a sum of root spaces corresponding to some subset of roots.

## Main results

* `LieAlgebra.IsKilling.instIsTriangularizableLieIdeal`: a Lie ideal inherits
  triangularizability from the ambient Lie algebra.
* `LieAlgebra.IsKilling.lieIdeal_eq_iSup_inf_genWeightSpace`: a Lie ideal equals the
  supremum of its intersections with the weight spaces.
* `LieAlgebra.IsKilling.lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace`: a Lie ideal equals
  its intersection with the Cartan subalgebra plus a sum of intersections with nonzero root spaces.
* `LieAlgebra.IsKilling.rootSpace_le_or_disjoint`: since root spaces are one-dimensional,
  a Lie ideal either contains a root space entirely or intersects it trivially.
* `LieAlgebra.IsKilling.exists_rootSet_lieIdeal_eq`: a Lie ideal equals its intersection with
  the Cartan subalgebra plus a sum of root spaces for some subset of roots.
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

omit [CharZero K] [IsKilling K L] in
instance instIsTriangularizableLieIdeal (I : LieIdeal K L) : IsTriangularizable K H I :=
  (inferInstance : IsTriangularizable K H
    ({ __ := I.toSubmodule, lie_mem := fun hm => I.lie_mem hm } : LieSubmodule K H L))

omit [CharZero K] [IsKilling K L] in
/-- A Lie ideal decomposes as the supremum of its intersections with the weight spaces.
This follows from the triangularizability of the ideal as a submodule. -/
lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule =
      ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
  refine le_antisymm ?_ (iSup_le fun χ ↦ inf_le_left)
  intro x hx
  have hx_mem : (⟨x, hx⟩ : I) ∈ ⨆ χ : Weight K H I, (genWeightSpace I χ).toSubmodule := by
    have := congr_arg LieSubmodule.toSubmodule (iSup_genWeightSpace_eq_top' K H I)
    simp only [LieSubmodule.iSup_toSubmodule, LieSubmodule.top_toSubmodule] at this
    exact this ▸ Submodule.mem_top
  refine Submodule.iSup_induction _
    (motive := fun z : I ↦
      (z : L) ∈ ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule)
    hx_mem ?_ ?_ ?_
  · intro χ_I z hz
    have hz_L : (z : L) ∈ genWeightSpace L (χ_I : H → K) :=
      map_genWeightSpace_le ((LieSubmodule.incl I).restrictLie H) ⟨z, hz, rfl⟩
    by_cases h : (z : L) = 0
    · rw [h]; exact Submodule.zero_mem _
    · exact Submodule.mem_iSup_of_mem
        ⟨(χ_I : H → K), fun h_eq ↦ h ((LieSubmodule.eq_bot_iff _).mp h_eq _ hz_L)⟩
        (Submodule.mem_inf.mpr ⟨z.property, hz_L⟩)
  · exact Submodule.zero_mem _
  · exact fun _ _ ha hb ↦ Submodule.add_mem _ ha hb

omit [CharZero K] [IsKilling K L] in
/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a sum of
intersections with nonzero weight spaces. -/
lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
        I.toSubmodule ⊓ (genWeightSpace L α).toSubmodule := by
  have h_iSup := lieIdeal_eq_iSup_inf_genWeightSpace (H := H) I
  refine le_antisymm (h_iSup.le.trans (iSup_le fun α ↦ ?_))
    (sup_le inf_le_left (iSup₂_le fun α _ ↦ inf_le_left))
  by_cases hα : α.IsZero
  · rw [show (genWeightSpace L (α : H → K)).toSubmodule = H.toSubmodule by simp [hα.eq]]
    exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)

/-- Since root spaces are one-dimensional, a Lie ideal either contains a root space entirely or
intersects it trivially. -/
lemma rootSpace_le_or_disjoint (I : LieIdeal K L) (α : Weight K H L) (hα : α.IsNonZero) :
    (rootSpace H α).toSubmodule ≤ I.toSubmodule ∨
    I.toSubmodule ⊓ (rootSpace H α).toSubmodule = ⊥ := by
  by_cases h : I.toSubmodule ⊓ (rootSpace H α).toSubmodule = ⊥
  · exact .inr h
  · exact .inl (inf_eq_right.mp (Submodule.eq_of_le_of_finrank_le inf_le_right
      ((finrank_rootSpace_eq_one α hα).symm ▸ Submodule.one_le_finrank_iff.mpr h)))

/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a sum of
root spaces corresponding to some subset of roots. -/
lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  refine ⟨{ α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }, le_antisymm ?_
    (sup_le inf_le_left (iSup₂_le fun _ hα ↦ hα))⟩
  calc I.toSubmodule
      = (I.toSubmodule ⊓ H.toSubmodule) ⊔
          ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
            I.toSubmodule ⊓ (genWeightSpace L α).toSubmodule :=
        lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace I
    _ ≤ _ := sup_le_sup_left (iSup₂_le fun α hα ↦ ?_) _
  obtain h | h := rootSpace_le_or_disjoint I α hα
  · exact le_iSup₂_of_le ⟨α, by simpa [LieSubalgebra.root]⟩ h inf_le_right
  · simp [h]

end

end LieAlgebra.IsKilling
