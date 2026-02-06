/-
This file proves a decomposition result for Lie ideals in a Killing Lie algebra:
any Lie ideal decomposes as its intersection with the Cartan subalgebra plus a direct sum
of root spaces corresponding to some subset of roots.
-/

import Mathlib.Algebra.Lie.Weights.RootSystem

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

instance (I : LieIdeal K L) : IsTriangularizable K H I :=
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
  change x ∈ ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule
  refine Submodule.iSup_induction _
    (motive := fun z : I ↦
      (z : L) ∈ ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule)
    hx_mem ?_ ?_ ?_
  · intro χ_I z hz
    have hz_L : (z : L) ∈ genWeightSpace L (χ_I : H → K) :=
      map_genWeightSpace_le ((LieSubmodule.incl I).restrictLie H) ⟨z, hz, rfl⟩
    by_cases h : (z : L) = 0
    · rw [h]; exact Submodule.zero_mem _
    · have h_ne : genWeightSpace L (χ_I : H → K) ≠ ⊥ := fun h_eq ↦
        h ((LieSubmodule.eq_bot_iff _).mp h_eq _ hz_L)
      exact Submodule.mem_iSup_of_mem ⟨(χ_I : H → K), h_ne⟩
        (Submodule.mem_inf.mpr ⟨z.property, hz_L⟩)
  · exact Submodule.zero_mem _
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

omit [CharZero K] [IsKilling K L] in
/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a sum of
intersections with nonzero weight spaces. -/
lemma lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
        I.toSubmodule ⊓ (genWeightSpace L α).toSubmodule := by
  have h_iSup := lieIdeal_eq_iSup_inf_genWeightSpace (H := H) I
  refine le_antisymm (le_trans h_iSup.le (iSup_le fun α ↦ ?_))
    (sup_le inf_le_left (iSup₂_le fun α _ ↦ inf_le_left))
  by_cases hα : α.IsZero
  · -- Zero weight: genWeightSpace L 0 = H
    have h0 : (genWeightSpace L (α : H → K)).toSubmodule = H.toSubmodule := by
      have := congr_arg LieSubmodule.toSubmodule (rootSpace_zero_eq K L H)
      simp only [LieSubalgebra.coe_toLieSubmodule] at this
      rw [hα.eq]; exact this
    rw [h0]; exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂_of_le α hα le_rfl)

/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a direct sum of
root spaces corresponding to some subset Φ of roots. This follows from the fact that root spaces
are 1-dimensional, so the intersection of I with each root space is either trivial or the full
root space. -/
lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  refine ⟨{ α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }, le_antisymm ?_ ?_⟩
  · -- ≤: use the decomposition, simplify each I ⊓ rootSpace(α) via 1-dimensionality
    calc I.toSubmodule
        = (I.toSubmodule ⊓ H.toSubmodule) ⊔
            ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
              I.toSubmodule ⊓ (genWeightSpace L α).toSubmodule :=
          lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace I
      _ ≤ _ := sup_le_sup_left (iSup₂_le fun α hα ↦ ?_) _
    by_cases h : I.toSubmodule ⊓ (rootSpace H α).toSubmodule = ⊥
    · simp [h]
    · have h_eq : I.toSubmodule ⊓ (rootSpace H α).toSubmodule =
          (rootSpace H α).toSubmodule :=
        Submodule.eq_of_le_of_finrank_le inf_le_right
          ((finrank_rootSpace_eq_one α hα).symm ▸ Submodule.one_le_finrank_iff.mpr h)
      rw [h_eq]
      exact le_iSup₂_of_le ⟨α, by simpa [LieSubalgebra.root]⟩ (inf_eq_right.mp h_eq) le_rfl
  · -- ≥: I ⊓ H ≤ I and each rootSpace in Φ ≤ I by definition
    exact sup_le inf_le_left (iSup₂_le fun _ hα ↦ hα)

end

end LieAlgebra.IsKilling
