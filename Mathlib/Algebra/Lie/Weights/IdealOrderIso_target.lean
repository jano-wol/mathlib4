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

The key structural facts are:

1. An ideal is the sum of its sl₂ triples (`LieIdeal.restr_eq_iSup_sl2SubmoduleOfRoot`).
2. The rootSet of `invtSubmoduleToLieIdeal q` is `{α | root(α) ∈ q}`
   (`LieAlgebra.IsKilling.mem_rootSet_invtSubmoduleToLieIdeal`).

## Main definitions

* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.
-/

@[expose] public section

/-! ### Ideals are sums of sl₂ triples -/

namespace LieIdeal

open LieAlgebra LieAlgebra.IsKilling LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

lemma mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (↑α : Dual K H) ∈ I.rootSpan (H := H)) :
    α ∈ I.rootSet (H := H) := by
  by_contra hα_not
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  have : I.rootSpan (H := H) ≤
      LinearMap.ker (Dual.eval K H (coroot (↑α : Weight K H L))) := by
    rw [LieIdeal.rootSpan]; apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Dual.eval_apply, rootSystem_root_apply]
    exact I.rootSet_apply_coroot_eq_zero_of_notMem_rootSet hγ hα_not
  have := LinearMap.mem_ker.mp (this hα_span)
  simp only [Dual.eval_apply, Weight.toLinear_apply, root_apply_coroot hα_nz] at this
  exact absurd this two_ne_zero

lemma restr_eq_iSup_sl2SubmoduleOfRoot (I : LieIdeal K L) :
    I.restr H = ⨆ (α : H.root) (_ : α ∈ I.rootSet (H := H)),
      sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
  apply le_antisymm
  · rw [lieIdeal_eq_inf_cartan_sup_biSup_rootSpace, restr_inf_cartan_eq_biSup_corootSubmodule]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ le_iSup₂_of_le β hβ
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_right)
    · exact iSup₂_le fun α hα ↦ le_iSup₂_of_le α hα
        (by rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left)
  · exact iSup₂_le fun α hα ↦ by
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact sup_le (sup_le hα (I.rootSpace_le_of_apply_coroot_ne_zero hα (by
        simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
        exact_mod_cast root_apply_coroot (H.isNonZero_coe_root α) ▸ two_ne_zero)))
        (I.corootSubmodule_le hα)

end LieIdeal

/-! ### rootSet of invtSubmoduleToLieIdeal -/

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
  rw [← LieSubmodule.toSubmodule_le_toSubmodule,
    coe_invtSubmoduleToLieIdeal_eq_iSup, coe_invtSubmoduleToLieIdeal_eq_iSup,
    LieSubmodule.iSup_toSubmodule, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

lemma mem_rootSet_invtSubmoduleToLieIdeal (q : Submodule K (Dual K H))
    (hq : ∀ i, q ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    {α : H.root} :
    α ∈ (invtSubmoduleToLieIdeal q hq).rootSet (H := H) ↔
      (rootSystem H).root α ∈ q := by
  set J := invtSubmoduleToLieIdeal q hq
  constructor
  · intro hα_mem; by_contra hα_not
    have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
    have absurd_eq (χ : Weight K H L) (hχ : ↑χ ∈ q)
        (heq : (χ : H → K) = ((↑α : Weight K H L) : H → K)) : False :=
      hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hχ)
    suffices (rootSpace H (↑α : Weight K H L)).toSubmodule ⊓ J.toSubmodule = ⊥ by
      rw [inf_eq_left.mpr hα_mem] at this
      exact (↑α : Weight K H L).genWeightSpace_ne_bot L
        ((LieSubmodule.toSubmodule_eq_bot _).mp this)
    rw [coe_invtSubmoduleToLieIdeal_eq_iSup, ← disjoint_iff, LieSubmodule.disjoint_toSubmodule]
    refine Disjoint.mono_right ?_ (iSupIndep_genWeightSpace K H L (↑(↑α : Weight K H L)))
    exact iSup_le fun ⟨β, hβ_mem, hβ_nz⟩ ↦ by
      rw [sl2SubmoduleOfRoot_eq_sup]
      exact sup_le (sup_le
        (le_iSup₂_of_le _ (fun h ↦ (absurd_eq β hβ_mem h).elim) le_rfl)
        (le_iSup₂_of_le _ (fun h ↦ (absurd_eq (-β)
          (by rw [Weight.toLinear_neg]; exact q.neg_mem hβ_mem) h).elim) le_rfl))
        ((LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
          (le_iSup₂_of_le 0 (fun h ↦ hα_nz h.symm) le_rfl))
  · -- If root(α) ∈ q then rootSpace(α) ≤ sl₂(α) ≤ J.
    intro hα
    rw [rootSystem_root_apply] at hα; rw [LieIdeal.mem_rootSet]
    calc rootSpace H (↑α : Weight K H L)
        ≤ sl2SubmoduleOfRoot (H.isNonZero_coe_root α) := by
          rw [sl2SubmoduleOfRoot_eq_sup]; exact le_sup_of_le_left le_sup_left
      _ ≤ ⨆ x : {β : Weight K H L // ↑β ∈ q ∧ β.IsNonZero}, sl2SubmoduleOfRoot x.2.2 :=
          le_iSup_of_le ⟨↑α, hα, H.isNonZero_coe_root α⟩ le_rfl
      _ = J.restr H := by
          rw [← LieSubmodule.toSubmodule_inj, LieSubmodule.restr_toSubmodule,
            coe_invtSubmoduleToLieIdeal_eq_iSup, LieSubmodule.iSup_toSubmodule]

/-! ### The order isomorphism -/

lemma lieIdealOrderIso_left_inv (I : LieIdeal K L) :
    invtSubmoduleToLieIdeal (I.rootSpan (H := H))
      ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule) = I := by
  set J := invtSubmoduleToLieIdeal (I.rootSpan (H := H))
    ((rootSystem H).mem_invtRootSubmodule_iff.mp I.rootSpan_mem_invtRootSubmodule)
  have h_eq : ∀ α : H.root, α ∈ J.rootSet (H := H) ↔ α ∈ I.rootSet (H := H) := fun α ↦ by
    rw [mem_rootSet_invtSubmoduleToLieIdeal, rootSystem_root_apply]
    exact ⟨I.mem_rootSet_of_mem_rootSpan, fun h ↦ Submodule.subset_span ⟨α, h, rfl⟩⟩
  have : J.restr H = I.restr H := by
    rw [J.restr_eq_iSup_sl2SubmoduleOfRoot (H := H), I.restr_eq_iSup_sl2SubmoduleOfRoot (H := H)]
    exact le_antisymm
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).1 hα) le_rfl)
      (iSup₂_le fun α hα ↦ le_iSup₂_of_le α ((h_eq α).2 hα) le_rfl)
  rw [← LieSubmodule.toSubmodule_inj, ← LieSubmodule.restr_toSubmodule J H,
    ← LieSubmodule.restr_toSubmodule I H, this]

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
