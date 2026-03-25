/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.Algebra.Lie.Weights.Killing
public import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! # Order Isomorphism: Lie Ideals and Invariant Root Submodules

This file establishes an order isomorphism between the lattice of Lie ideals of a Killing
Lie algebra and the lattice of invariant root submodules of the associated root system.

## Main definitions

* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.

## Tags

Lie algebra, Killing, root system, ideal, order isomorphism
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Order isomorphism -/

lemma mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (↑α : Dual K H) ∈ I.rootSpan (H := H)) :
    α ∈ I.rootSet (H := H) := by
  by_contra hα_not
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  have h_le : I.rootSpan (H := H) ≤ LinearMap.ker (Dual.eval K H (coroot (↑α : Weight K H L))) := by
    rw [LieIdeal.rootSpan]; apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (h_le hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

lemma sl2SubmoduleOfRoot_le_ideal (I : LieIdeal K L) {α : H.root}
    (hα : α ∈ I.rootSet (H := H)) :
    (sl2SubmoduleOfRoot (H.isNonZero_coe_root α)).toSubmodule ≤ I.toSubmodule := by
  rw [sl2SubmoduleOfRoot_eq_sup]; simp only [LieSubmodule.sup_toSubmodule]
  refine sup_le (sup_le hα (I.rootSpace_le_of_apply_coroot_ne_zero hα ?_))
    (I.corootSubmodule_le hα)
  simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
  exact_mod_cast root_apply_coroot (H.isNonZero_coe_root α) ▸ two_ne_zero

lemma sl2_le_iSup_of_mem_rootSet (I : LieIdeal K L) {β : H.root}
    (hβ : β ∈ I.rootSet (H := H)) (N : LieSubmodule K H L)
    (hN : N ≤ sl2SubmoduleOfRoot (H.isNonZero_coe_root β)) :
    N.toSubmodule ≤ ⨆ x : {α : Weight K H L //
        Weight.toLinear K H L α ∈ I.rootSpan ∧ α.IsNonZero},
      (sl2SubmoduleOfRoot x.2.2).toSubmodule :=
  (show N.toSubmodule ≤ _ from hN).trans
    (le_iSup_of_le ⟨↑β, Submodule.subset_span ⟨β, hβ, rfl⟩, H.isNonZero_coe_root β⟩ le_rfl)

lemma lieIdealOrderIso_left_inv (I : LieIdeal K L) :
    invtSubmoduleToLieIdeal (I.rootSpan (H := H))
      ((rootSystem H).mem_invtRootSubmodule_iff.mp
        (I.rootSpan_mem_invtRootSubmodule)) = I := by
  rw [← LieSubmodule.toSubmodule_inj, coe_invtSubmoduleToLieIdeal_eq_iSup]
  refine le_antisymm ?_ ?_
  · rw [LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun ⟨α, hα_span, hα_nz⟩ ↦
      sl2SubmoduleOfRoot_le_ideal I
        (α := ⟨α, by simpa [LieSubalgebra.root] using hα_nz⟩)
        (mem_rootSet_of_mem_rootSpan I hα_span)
  · rw [LieSubmodule.iSup_toSubmodule]
    have h_decomp := congr_arg LieSubmodule.toSubmodule
      (lieIdeal_eq_inf_cartan_sup_biSup_rootSpace (H := H) I)
    have h_cartan := congr_arg LieSubmodule.toSubmodule
      (I.restr_inf_cartan_eq_biSup_corootSubmodule (H := H))
    simp only [LieSubmodule.restr_toSubmodule, LieSubmodule.sup_toSubmodule,
      LieSubmodule.iSup_toSubmodule, LieSubmodule.inf_toSubmodule,
      LieSubalgebra.coe_toLieSubmodule] at h_decomp h_cartan
    conv_lhs => rw [h_decomp, h_cartan]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ sl2_le_iSup_of_mem_rootSet I hβ _
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα ↦ sl2_le_iSup_of_mem_rootSet I hα _
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)

lemma rootSpace_disjoint_invtSubmoduleToLieIdeal
    (q : (rootSystem H).invtRootSubmodule)
    {α : H.root} (hα_not : (rootSystem H).root α ∉ (q : Submodule K (Dual K H))) :
    (rootSpace H (↑α : Weight K H L)).toSubmodule ⊓
      (invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toSubmodule
        = ⊥ := by
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  rw [coe_invtSubmoduleToLieIdeal_eq_iSup, ← disjoint_iff, LieSubmodule.disjoint_toSubmodule]
  apply Disjoint.mono_right _ (iSupIndep_genWeightSpace K H L (↑(↑α : Weight K H L)))
  apply iSup_le; intro ⟨β, hβ_mem, hβ_nz⟩
  have hβ_ne : (β : H → K) ≠ ((↑α : Weight K H L) : H → K) := fun heq ↦
    hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hβ_mem)
  have hnβ_ne : ((-β : Weight K H L) : H → K) ≠ ((↑α : Weight K H L) : H → K) := by
    intro heq; apply hα_not; rw [rootSystem_root_apply]
    have : Weight.toLinear K H L (-β) ∈ q.1 := by rw [Weight.toLinear_neg]; exact q.1.neg_mem hβ_mem
    rwa [show (-β : Weight K H L) = (↑α : Weight K H L) from DFunLike.coe_injective heq] at this
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact sup_le (sup_le (le_iSup₂_of_le (↑β : H → K) hβ_ne le_rfl)
    (le_iSup₂_of_le (↑(-β : Weight K H L) : H → K) hnβ_ne le_rfl))
    ((LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
      (le_iSup₂_of_le (0 : H → K) (fun h => hα_nz h.symm) le_rfl))

@[gcongr]
lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule,
    coe_invtSubmoduleToLieIdeal_eq_iSup, coe_invtSubmoduleToLieIdeal_eq_iSup,
    LieSubmodule.iSup_toSubmodule, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1
    ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv I := lieIdealOrderIso_left_inv I
  right_inv q := by
    apply Subtype.ext
    simp only [LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨α, hα, rfl⟩
      by_contra hα_not
      have h_bot := rootSpace_disjoint_invtSubmoduleToLieIdeal q hα_not
      rw [inf_eq_left.mpr hα] at h_bot
      exact (↑α : Weight K H L).genWeightSpace_ne_bot L
        ((LieSubmodule.toSubmodule_eq_bot _).mp h_bot)
    · apply (RootPairing.invtRootSubmodule.eq_span_root q).le.trans
      apply Submodule.span_mono; apply Set.image_mono
      intro i hi
      have hi_nz : (↑i : Weight K H L).IsNonZero := (Finset.mem_filter.mp i.property).2
      rw [Set.mem_setOf_eq, rootSystem_root_apply] at hi
      change (rootSpace H (↑i : Weight K H L)).toSubmodule ≤
        (invtSubmoduleToLieIdeal q.1
          ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toSubmodule
      rw [coe_invtSubmoduleToLieIdeal_eq_iSup, LieSubmodule.iSup_toSubmodule]
      exact le_iSup_of_le ⟨(↑i : Weight K H L), hi, hi_nz⟩
        (by rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
            exact le_sup_of_le_left le_sup_left)
  map_rel_iff' {I J} :=
    ⟨fun h ↦ by rw [← lieIdealOrderIso_left_inv (H := H) I,
                    ← lieIdealOrderIso_left_inv (H := H) J]
                exact invtSubmoduleToLieIdeal_mono _ _ h,
     LieIdeal.toInvtRootSubmodule_mono⟩

end

end LieAlgebra.IsKilling
