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

## Main definitions

* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

@[gcongr]
lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  show (invtSubmoduleToLieIdeal q₁ hq₁).restr H ≤ (invtSubmoduleToLieIdeal q₂ hq₂).restr H
  rw [restr_invtSubmoduleToLieIdeal_eq_iSup]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

/-! ### The order isomorphism -/

lemma lieIdealOrderIso_left_inv (I : LieIdeal K L) :
    invtSubmoduleToLieIdeal (I.rootSpan (H := H))
      ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule) = I := by
  set J := invtSubmoduleToLieIdeal (I.rootSpan (H := H))
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : ∀ α : H.root, α ∈ J.rootSet (H := H) ↔ α ∈ I.rootSet (H := H) := fun α ↦ by
    rw [mem_rootSet_invtSubmoduleToLieIdeal, rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h ↦ Submodule.subset_span ⟨α, h, rfl⟩⟩
  have h_restr : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot (H := H), I.restr_eq_iSup_sl2SubmoduleOfRoot (H := H)]
    exact le_antisymm
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj, ← LieSubmodule.restr_toSubmodule J H,
    ← LieSubmodule.restr_toSubmodule I H, h_restr]

lemma lieIdealOrderIso_right_inv (q : (rootSystem H).invtRootSubmodule) :
    (invtSubmoduleToLieIdeal q.1
      ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toInvtRootSubmodule (H := H) = q := by
  apply Subtype.ext
  simp only [LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ ⟨α, hα, hα_eq⟩ ↦ by
      rw [← hα_eq, rootSystem_root_apply]
      exact mem_rootSet_invtSubmoduleToLieIdeal _ _ |>.mp hα
  · exact (RootPairing.invtRootSubmodule.eq_span_root q).le.trans
      (Submodule.span_mono (Set.image_mono fun i hi ↦
        (mem_rootSet_invtSubmoduleToLieIdeal _ _ |>.mpr hi)))

def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1
    ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv I := lieIdealOrderIso_left_inv I
  right_inv q := lieIdealOrderIso_right_inv q
  map_rel_iff' {I J} :=
    ⟨fun h ↦ by rw [← lieIdealOrderIso_left_inv (H := H) I,
                    ← lieIdealOrderIso_left_inv (H := H) J]
                exact invtSubmoduleToLieIdeal_mono _ _ h,
     LieIdeal.toInvtRootSubmodule_mono⟩

end

end LieAlgebra.IsKilling
