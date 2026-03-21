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

## Main results

* `LieAlgebra.IsKilling.lieIdeal_inf_cartan_eq_coroot_span`: the Cartan part `I ⊓ H` of a Lie
  ideal equals the span of the coroots corresponding to roots in `I.rootSet`.

## Tags

Lie algebra, Killing, root system, ideal, order isomorphism
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Ideal-Cartan intersection -/

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
lemma coroot_span_le_inf_cartan (I : LieIdeal K L) :
    ⨆ α ∈ I.rootSet (H := H), (corootSubmodule α.1).toSubmodule ≤
      I.toSubmodule ⊓ H.toSubmodule :=
  iSup₂_le fun _α hα ↦ le_inf (I.corootSubmodule_le hα) LieSubmodule.map_incl_le

lemma weight_apply_eq_zero_of_not_mem_rootSet (I : LieIdeal K L)
    {x : L} (hxI : x ∈ I.toSubmodule) (hxH : x ∈ H.toSubmodule)
    {β : H.root} (hβ_not : β ∉ I.rootSet (H := H)) :
    (β : Weight K H L) ⟨x, hxH⟩ = 0 := by
  simp only [LieIdeal.mem_rootSet] at hβ_not
  by_contra h; apply hβ_not; intro y hy
  have hsmul : (β : Weight K H L) ⟨x, hxH⟩ • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy ⟨x, hxH⟩]
    exact lie_mem_left K L I x y hxI
  rwa [I.toSubmodule.smul_mem_iff (by exact_mod_cast h)] at hsmul

private lemma biSup_span_coroot_eq_top :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), (K ∙ coroot α : Submodule K H) = ⊤ := by
  simp_rw [← coe_corootSpace_eq_span_singleton, ← LieSubmodule.iSup_toSubmodule,
    biSup_corootSpace_eq_top, LieSubmodule.top_toSubmodule]

private lemma eq_zero_of_traceForm_coroot_eq_zero (h : H)
    (horth : ∀ α : Weight K H L, α.IsNonZero → traceForm K H L h (coroot α) = 0) :
    h = 0 := by
  have hker : ⊤ ≤ LinearMap.ker (traceForm K H L h) := by
    rw [← biSup_span_coroot_eq_top (K := K) (L := L) (H := H)]
    exact iSup₂_le fun α hα ↦ Submodule.span_le.mpr <| by
      simp [Set.singleton_subset_iff, LinearMap.mem_ker, horth α hα]
  apply (cartanEquivDual H).injective; ext y
  simpa [cartanEquivDual_apply_apply] using DFunLike.congr_fun (LinearMap.ker_eq_top.mp
    (eq_top_iff.mpr hker)) y

private lemma traceForm_coroot_eq_zero_of_ideal_complement (I : LieIdeal K L)
    {α : H.root} (hαI : α ∈ I.rootSet (H := H))
    {β : H.root} (hβI : β ∉ I.rootSet (H := H)) :
    traceForm K H L (coroot (α : Weight K H L)) (coroot (β : Weight K H L)) = 0 := by
  refine traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := (β : Weight K H L)) ?_
    (Submodule.mem_span_singleton_self _)
  change ((β : Weight K H L) : H → K) (coroot (α : Weight K H L)) = 0
  exact weight_apply_eq_zero_of_not_mem_rootSet I
    (I.corootSubmodule_le hαI (coe_coroot_mem_corootSubmodule (α : Weight K H L)))
    (coroot (α : Weight K H L)).property hβI

lemma inf_cartan_le_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule ≤
      ⨆ α ∈ I.rootSet (H := H), (corootSubmodule α.1).toSubmodule := by
  intro x hx
  obtain ⟨hxI, hxH⟩ := Submodule.mem_inf.mp hx
  set h : H := ⟨x, hxH⟩
  set S_I : Submodule K H :=
    ⨆ α ∈ I.rootSet (H := H), (K ∙ coroot (α.1 : Weight K H L))
  set S_c : Submodule K H :=
    ⨆ (β : H.root) (_ : β ∉ I.rootSet (H := H)), (K ∙ coroot (β : Weight K H L))
  have h_sup : S_I ⊔ S_c = ⊤ := by
    rw [eq_top_iff, ← biSup_span_coroot_eq_top (K := K) (L := L) (H := H)]
    exact iSup₂_le fun α hα ↦ by
      have hα_root : α ∈ H.root := by simpa [LieSubalgebra.root] using hα
      by_cases hαI : (⟨α, hα_root⟩ : H.root) ∈ I.rootSet (H := H)
      · exact le_sup_of_le_left (le_iSup₂_of_le ⟨α, hα_root⟩ hαI le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le ⟨α, hα_root⟩ hαI le_rfl)
  have hS_I_le : S_I ≤ Submodule.comap H.toSubmodule.subtype
      (⨆ α ∈ I.rootSet (H := H), (corootSubmodule α.1).toSubmodule) :=
    iSup₂_le fun α hα z hz ↦ by
      rw [Submodule.mem_comap]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      simp only [map_smul]
      exact Submodule.smul_mem _ _
        ((le_iSup₂_of_le α hα le_rfl : (corootSubmodule α.1).toSubmodule ≤ _)
          (coe_coroot_mem_corootSubmodule α.1))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h_sup ▸ Submodule.mem_top (x := h))
  have haI : (a : L) ∈ I.toSubmodule :=
    (Submodule.mem_inf.mp (coroot_span_le_inf_cartan I (hS_I_le ha))).1
  have hbI : (b : L) ∈ I.toSubmodule := by
    have : (b : L) = x - (a : L) := by
      have h1 : (a : L) + (b : L) = x := congr_arg Subtype.val hab
      rw [← h1, add_sub_cancel_left]
    rw [this]; exact I.toSubmodule.sub_mem hxI haI
  have hb_zero : b = 0 := by
    apply eq_zero_of_traceForm_coroot_eq_zero
    intro μ hμ
    have hμ_root : μ ∈ H.root := by simpa [LieSubalgebra.root] using hμ
    by_cases hμI : (⟨μ, hμ_root⟩ : H.root) ∈ I.rootSet (H := H)
    · rw [traceForm_comm]
      exact LinearMap.mem_ker.mp ((iSup_le fun γ ↦ iSup_le fun hγI ↦
        Submodule.span_le.mpr <| by
          simp [Set.singleton_subset_iff, LinearMap.mem_ker,
            traceForm_coroot_eq_zero_of_ideal_complement I hμI hγI]) hb)
    · exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := μ)
        (show (μ : H → K) b = 0 from
          weight_apply_eq_zero_of_not_mem_rootSet I hbI b.property hμI)
        (Submodule.mem_span_singleton_self _)
  have hha : h = a := by rw [← hab, hb_zero, add_zero]
  rw [show x = (a : L) from congr_arg Subtype.val hha]
  exact hS_I_le ha

lemma lieIdeal_inf_cartan_eq_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule =
      ⨆ α ∈ I.rootSet (H := H), (corootSubmodule α.1).toSubmodule :=
  le_antisymm (inf_cartan_le_coroot_span I) (coroot_span_le_inf_cartan I)

/-! ### Order isomorphism -/

omit [CharZero K] [IsTriangularizable K H L] in
lemma cartanEquivDual_symm_comm (f g : Dual K H) :
    f ((cartanEquivDual H).symm g) = g ((cartanEquivDual H).symm f) := by
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) f]
  conv_rhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) g]
  simp only [cartanEquivDual_apply_apply]
  exact LieModule.traceForm_comm K H L _ _

lemma mem_rootSet_of_mem_rootSpan (I : LieIdeal K L)
    {α : H.root} (hα_span : (↑α : Dual K H) ∈ I.rootSpan (H := H)) :
    α ∈ I.rootSet (H := H) := by
  by_contra hα_not
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  have h_vanish : ∀ γ ∈ I.rootSet (H := H),
      (↑α : Weight K H L) (coroot (↑γ : Weight K H L)) = 0 := fun γ hγ ↦
    weight_apply_eq_zero_of_not_mem_rootSet I
      (I.corootSubmodule_le hγ (coe_coroot_mem_corootSubmodule (↑γ : Weight K H L)))
      (coroot (↑γ : Weight K H L)).property hα_not
  have h_span_le : I.rootSpan (H := H) ≤
      LinearMap.ker (Module.Dual.eval K H ((cartanEquivDual H).symm (↑α : Dual K H))) := by
    rw [LieIdeal.rootSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    rw [cartanEquivDual_symm_comm]
    have h_mem := cartanEquivDual_symm_apply_mem_corootSpace (↑γ : Weight K H L)
    rw [← LieSubmodule.mem_toSubmodule, coe_corootSpace_eq_span_singleton] at h_mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h_mem
    simp only [rootSystem_root_apply]; rw [← hc]
    change (↑(↑α : Weight K H L) : H →ₗ[K] K) (c • coroot (↑γ : Weight K H L)) = 0
    simp [h_vanish γ hγ]
  exact root_apply_cartanEquivDual_symm_ne_zero hα_nz
    (by simpa [Module.Dual.eval_apply] using LinearMap.mem_ker.mp (h_span_le hα_span))

lemma sl2SubmoduleOfRoot_le_ideal (I : LieIdeal K L) {α : H.root}
    (hα : α ∈ I.rootSet (H := H)) :
    (sl2SubmoduleOfRoot (H.isNonZero_coe_root α)).toSubmodule ≤ I.toSubmodule := by
  rw [sl2SubmoduleOfRoot_eq_sup]; simp only [LieSubmodule.sup_toSubmodule]
  refine sup_le (sup_le hα (I.rootSpace_le_of_apply_coroot_ne_zero hα ?_))
    (I.corootSubmodule_le hα)
  simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
  exact_mod_cast root_apply_coroot (H.isNonZero_coe_root α) ▸ two_ne_zero

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
    simp only [LieSubmodule.restr_toSubmodule, LieSubmodule.sup_toSubmodule,
      LieSubmodule.iSup_toSubmodule, LieSubmodule.inf_toSubmodule,
      LieSubalgebra.coe_toLieSubmodule] at h_decomp
    conv_lhs => rw [h_decomp, lieIdeal_inf_cartan_eq_coroot_span I]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ by
        have hβ_nz : (↑β : Weight K H L).IsNonZero := (Finset.mem_filter.mp β.property).2
        exact (le_iSup_of_le
          ⟨(↑β : Weight K H L), Submodule.subset_span ⟨β, hβ, rfl⟩, hβ_nz⟩
          (by rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
              exact le_sup_right))
    · exact iSup₂_le fun α hα_le ↦ by
        have hα_nz : (α.val : Weight K H L).IsNonZero := by
          simpa [LieSubalgebra.root] using (Finset.mem_filter.mp α.property).2
        exact (le_iSup_of_le ⟨α.val, Submodule.subset_span
            ⟨α, hα_le, rfl⟩, hα_nz⟩
            (by rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
                exact le_sup_of_le_left le_sup_left))

lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule,
      coe_invtSubmoduleToLieIdeal_eq_iSup, coe_invtSubmoduleToLieIdeal_eq_iSup,
      LieSubmodule.iSup_toSubmodule, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

lemma lieIdealOrderIso_map_rel_iff {I J : LieIdeal K L} :
    I.toInvtRootSubmodule (H := H) ≤ J.toInvtRootSubmodule ↔ I ≤ J :=
  ⟨fun h ↦ by rw [← lieIdealOrderIso_left_inv (H := H) I,
      ← lieIdealOrderIso_left_inv (H := H) J]; exact invtSubmoduleToLieIdeal_mono _ _ h,
   LieIdeal.toInvtRootSubmodule_mono⟩

private lemma mem_invtSubmodule_of_rootSpace_le_invtSubmoduleToLieIdeal
    (q : (rootSystem H).invtRootSubmodule)
    {α : H.root} (hα : (rootSpace H (↑α : Weight K H L)).toSubmodule ≤
      (invtSubmoduleToLieIdeal q.1
        ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toSubmodule) :
    (rootSystem H).root α ∈ (q : Submodule K (Dual K H)) := by
  by_contra hα_not
  set I := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  have h_inter_bot : (rootSpace H (↑α : Weight K H L)).toSubmodule ⊓ I.toSubmodule = ⊥ := by
    rw [coe_invtSubmoduleToLieIdeal_eq_iSup, ← disjoint_iff, LieSubmodule.disjoint_toSubmodule]
    apply Disjoint.mono_right _ (iSupIndep_genWeightSpace K H L (↑(↑α : Weight K H L)))
    apply iSup_le; intro ⟨β, hβ_mem, hβ_nz⟩
    have hβ_ne : (β : H → K) ≠ ((↑α : Weight K H L) : H → K) := fun heq ↦ by
      exact hα_not (by simpa [rootSystem_root_apply] using DFunLike.coe_injective heq ▸ hβ_mem)
    have hnβ_ne : ((-β : Weight K H L) : H → K) ≠ ((↑α : Weight K H L) : H → K) := by
      intro heq; apply hα_not; rw [rootSystem_root_apply]
      have h_neg : Weight.toLinear K H L (-β) ∈ q.1 := by
        rw [Weight.toLinear_neg]; exact q.1.neg_mem hβ_mem
      rwa [show (-β : Weight K H L) = (↑α : Weight K H L) from DFunLike.coe_injective heq]
        at h_neg
    rw [sl2SubmoduleOfRoot_eq_sup]
    exact sup_le (sup_le (le_iSup₂_of_le (↑β : H → K) hβ_ne le_rfl)
      (le_iSup₂_of_le (↑(-β : Weight K H L) : H → K) hnβ_ne le_rfl))
      ((LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        (le_iSup₂_of_le (0 : H → K) (fun h => hα_nz h.symm) le_rfl))
  rw [inf_eq_left.mpr hα] at h_inter_bot
  exact Weight.genWeightSpace_ne_bot L (↑α : Weight K H L)
    ((LieSubmodule.toSubmodule_eq_bot _).mp h_inter_bot)

def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := LieIdeal.toInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1
    ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv I := lieIdealOrderIso_left_inv I
  right_inv := by
    intro q
    apply Subtype.ext
    simp only [LieIdeal.toInvtRootSubmodule, LieIdeal.rootSpan, LieIdeal.rootSet]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨α, hα, rfl⟩
      exact mem_invtSubmodule_of_rootSpace_le_invtSubmoduleToLieIdeal q hα
    · apply (RootPairing.invtRootSubmodule.eq_span_root q).le.trans
      apply Submodule.span_mono; apply Set.image_mono
      intro i hi
      have hi_nz : (↑i : Weight K H L).IsNonZero := (Finset.mem_filter.mp i.property).2
      rw [Set.mem_setOf_eq, rootSystem_root_apply] at hi
      change (rootSpace H (↑i : Weight K H L)).toSubmodule ≤
        (invtSubmoduleToLieIdeal q.1
          ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toSubmodule
      rw [coe_invtSubmoduleToLieIdeal_eq_iSup, LieSubmodule.iSup_toSubmodule]
      apply le_iSup_of_le ⟨(↑i : Weight K H L), hi, hi_nz⟩
      rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_of_le_left le_sup_left
  map_rel_iff' := lieIdealOrderIso_map_rel_iff

end

end LieAlgebra.IsKilling
