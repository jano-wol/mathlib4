/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.Algebra.Lie.Weights.RootSystem
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.Algebra.Lie.Weights.IdealDecomposition
public import Mathlib.Algebra.Lie.Killing

/-! # Simplicity from Irreducibility

This file proves that a Killing Lie algebra with an irreducible root system is simple. The main
theorem `isSimple_of_isIrreducible` shows that an irreducible root system forces the Lie algebra
to have no nontrivial ideals.
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
  [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

omit [CharZero K] [IsTriangularizable K H L] in
lemma cartan_is_abelian : IsLieAbelian H := by
  constructor; aesop

omit [CharZero K] in
/-- If the root space of α is contained in a Lie ideal J, then the coroot of α is also in J.
This follows because the coroot is in the corootSpace, which is spanned by brackets ⁅y, z⁆
where y ∈ rootSpace α. Since y ∈ J and J is an ideal, ⁅y, z⁆ ∈ J by lie_mem_left. -/
lemma coroot_mem_lieIdeal_of_rootSpace_le
    (J : LieIdeal K L) (α : Weight K H L)
    (h : (rootSpace H α : Submodule K L) ≤ J.toSubmodule) :
    (coroot α : L) ∈ J.toSubmodule := by
  have h1 := coroot_mem_corootSpace α
  rw [mem_corootSpace] at h1
  refine Submodule.span_le.mpr ?_ h1
  rintro _ ⟨y, hy, z, hz, rfl⟩
  exact lie_mem_left K L J y z (h hy)

set_option linter.flexible false in
omit [CharZero K] [IsTriangularizable K H L] in
lemma cartan_eq_sup_inf_ideal (I : LieIdeal K L)
    (hI : IsCompl I I.killingCompl) :
    H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      (I.killingCompl.toSubmodule ⊓ H.toSubmodule) := by
  have h_le : H.toSubmodule ≤
      (I : Submodule K L) ⊓ H.toSubmodule ⊔
        (LieIdeal.killingCompl K L I : Submodule K L) ⊓ H.toSubmodule := by
    intro x hx
    obtain ⟨i, j, hi, hj, hx_eq⟩ :
        ∃ i j : L, i ∈ I ∧ j ∈ LieIdeal.killingCompl K L I ∧ x = i + j := by
      have := hI.sup_eq_top
      replace this := Submodule.mem_sup.mp
        (this.symm ▸ Submodule.mem_top : x ∈ I ⊔ LieIdeal.killingCompl K L I)
      aesop
    have h_comm : ∀ x ∈ H, ⁅i, x⁆ = 0 ∧ ⁅j, x⁆ = 0 := by
      intro x hx
      have h_comm_i : ⁅i, x⁆ ∈ I :=
        lie_mem_left K L I i x hi
      have h_comm_j : ⁅j, x⁆ ∈ LieIdeal.killingCompl K L I :=
        lie_mem_left K L (LieIdeal.killingCompl K L I) j x hj
      have h_comm_zero : ⁅i, x⁆ + ⁅j, x⁆ = 0 := by
        have h_comm_zero : ⁅x, i + j⁆ = 0 := by
          have h_comm_zero : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ = 0 := by
            have h_comm_zero : IsLieAbelian H := cartan_is_abelian
            intro x hx y hy
            exact (by
              have := h_comm_zero.1 ⟨x, hx⟩ ⟨y, hy⟩
              exact Subtype.ext_iff.mp this)
          aesop
        rw [← neg_eq_zero, ← lie_skew, ← lie_skew]
        simp_all +decide [lie_add, add_comm]
      have h_comm_zero : ⁅i, x⁆ ∈ I ⊓ LieIdeal.killingCompl K L I := by
        simp_all +decide [add_eq_zero_iff_eq_neg]
        intro y hy
        specialize h_comm_j y hy
        simp_all +decide [killingForm]
        simp_all +decide [LieModule.traceForm]
        simp_all +decide [LieRing.of_associative_ring_bracket]
        simp_all +decide [mul_sub]
        rw [sub_eq_zero] at *
        aesop
      have := hI.disjoint.le_bot h_comm_zero
      aesop
    have h_i_j_in_H : i ∈ H ∧ j ∈ H := by
      have h_i_j_in_H : ∀ x : L, (∀ y ∈ H, ⁅x, y⁆ = 0) → x ∈ H := by
        intro x hx_comm
        have h_normalizer : x ∈ LieSubalgebra.normalizer H := by
          simp +decide only [LieSubalgebra.mem_normalizer_iff]
          exact fun y hy => by rw [hx_comm y hy]; exact H.zero_mem
        have h_self : H.normalizer = H :=
          LieSubalgebra.IsCartanSubalgebra.self_normalizing
        exact h_self ▸ h_normalizer
      exact ⟨h_i_j_in_H i fun y hy => h_comm y hy |>.1,
        h_i_j_in_H j fun y hy => h_comm y hy |>.2⟩
    exact Submodule.mem_sup.mpr
      ⟨i, ⟨hi, h_i_j_in_H.1⟩, j, ⟨hj, h_i_j_in_H.2⟩,
        by simp +decide [hx_eq]⟩
  exact le_antisymm h_le (sup_le inf_le_right inf_le_right)

omit [IsKilling K L] in
lemma h_H_le_C_1 (β : Weight K H L) (hβ : β.IsNonZero) :
    H.toSubmodule ≤ ⨆ j ≠ β, (rootSpace H j).toSubmodule := by
  intro x hx
  have h_sum : x ∈ LieAlgebra.rootSpace H 0 := by
    simp_all +decide [LieAlgebra.rootSpace,
      LieSubalgebra.mem_toSubmodule]
  refine Submodule.mem_iSup_of_mem ?_ (Submodule.mem_iSup_of_mem ?_ ?_)
  · exact ⟨0, by
      intro h
      rw [LieSubmodule.eq_bot_iff] at h
      contrapose! hβ
      ext x; specialize h x; aesop⟩
  · generalize_proofs at *
    exact fun h => hβ <| h ▸ rfl
  · generalize_proofs at *
    exact h_sum

theorem isSimple_of_isIrreducible
    (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L := by
  by_contra h_not_simple
  obtain ⟨I, hI_ne_bot, hI_ne_top⟩ :
      ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
    have h_not_simple_def :
        ¬LieAlgebra.IsSimple K L →
          ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
      intro h_not_simple_def
      contrapose! h_not_simple_def
      constructor
      · exact fun I =>
          Classical.or_iff_not_imp_left.2 fun h =>
            h_not_simple_def I h
      · cases subsingleton_or_nontrivial L <;>
          simp_all only [ne_eq]
        · have := hIrr.1
          simp_all +decide only [rootSystem, LinearMap.identityMapOfZeroModuleIsZero,
            nontrivial_dual_iff]
          exact False.elim (this.exists_pair_ne.elim
            fun x hx => hx.elim
              fun y hy => hy <| Subsingleton.elim _ _)
        · intro h_abelian
          have h_center : LieAlgebra.center K L = ⊤ :=
            (isLieAbelian_iff_center_eq_top K L).mp h_abelian
          have h_center_eq_bot : LieAlgebra.center K L = ⊥ :=
            center_eq_bot K L
          exact absurd h_center_eq_bot (by
            simp +decide only [center_eq_bot, not_true_eq_false]
            exact absurd (h_center_eq_bot ▸ h_center)
              (by simp +decide))
    exact h_not_simple_def h_not_simple
  let J := I.killingCompl
  obtain ⟨Φ₁, hΦ₁⟩ := exists_rootSet_lieIdeal_eq (H := H) I
  obtain ⟨Φ₂, hΦ₂⟩ := exists_rootSet_lieIdeal_eq (H := H) J
  have s1 : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      (J.toSubmodule ⊓ H.toSubmodule) := by
    have h_cartan_decomp : H.toSubmodule =
        (I.toSubmodule ⊓ H.toSubmodule) ⊔
          (J.toSubmodule ⊓ H.toSubmodule) := by
      have h_compl : IsCompl I J :=
        LieIdeal.isCompl_killingCompl I
      exact cartan_eq_sup_inf_ideal I h_compl
    exact h_cartan_decomp
  have sup_1 : I.toSubmodule ⊔ J.toSubmodule = ⊤ := by
    have := LieIdeal.isCompl_killingCompl I
    have h_sup : (I : Submodule K L) ⊔ (J : Submodule K L) = ⊤ := by
      have := this.sup_eq_top
      convert congr_arg
        (fun x : LieIdeal K L => x.toLieSubalgebra.toSubmodule)
        this using 1
    convert h_sup using 1
  have hJ_ne_bot : J ≠ ⊥ := by
    by_contra J_bot
    rw [J_bot] at sup_1
    simp only [LieSubmodule.bot_toSubmodule, sup_bot_eq,
      LieSubmodule.toSubmodule_eq_top] at sup_1
    exact Ne.elim hI_ne_top sup_1
  have bot_1 : I.toSubmodule ⊓ J.toSubmodule = ⊥ := by
    have h_compl : I ⊓ J = ⊥ := by
      have h_compl : IsCompl I J :=
        LieIdeal.isCompl_killingCompl I
      exact h_compl.inf_eq_bot
    convert h_compl using 1
    simp +decide [SetLike.ext_iff, LieSubmodule.mem_inf]
  have s2 : Φ₁ ∩ Φ₂ = ∅ := by
    ext α
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hα₁ hα₂
    have h_contra :
        (rootSpace H α.val).toSubmodule ≤
          (I : Submodule K L) ⊓ (J : Submodule K L) := by
      simp +zetaDelta only [LieIdeal.toLieSubalgebra_toSubmodule, le_inf_iff] at *
      exact ⟨hΦ₁.symm ▸
        le_sup_of_le_right (le_iSup₂_of_le α hα₁ le_rfl),
        hΦ₂.symm ▸
          le_sup_of_le_right (le_iSup₂_of_le α hα₂ le_rfl)⟩
    have h_contra : (rootSpace H α.val) ≠ ⊥ := by
      have := α.val.genWeightSpace_ne_bot
      simp only [ne_eq] at this
      simp only [ne_eq]
      dsimp [rootSpace]
      exact this
    exact h_contra (by
      simpa [bot_1] using
        ‹(LieAlgebra.rootSpace H α.val : Submodule K L) ≤
          (I : Submodule K L) ⊓ (J : Submodule K L)›)
  have s3 : Φ₁ ∪ Φ₂ = Set.univ := by
    by_contra h_not_univ
    rw [← ne_eq, Set.ne_univ_iff_exists_notMem] at h_not_univ
    obtain ⟨β, hβ⟩ := h_not_univ
    rw [Set.mem_union, not_or] at hβ
    obtain ⟨hβ_not_Φ₁, hβ_not_Φ₂⟩ := hβ
    have hβ_nonzero : (β : Weight K H L).IsNonZero := by
      have := β.2
      simp only [LieSubalgebra.root, Finset.mem_filter,
        Finset.mem_univ, true_and] at this
      exact this
    have h_indep :
        iSupIndep fun (χ : Weight K H L) =>
          (rootSpace H χ).toSubmodule :=
      LieSubmodule.iSupIndep_toSubmodule.mpr
        (iSupIndep_genWeightSpace' K H L)
    let C := ⨆ j ≠ (β : Weight K H L),
      (rootSpace H j).toSubmodule
    have h_inf_C : (rootSpace H β).toSubmodule ⊓ C = ⊥ :=
      disjoint_iff.mp (h_indep (β : Weight K H L))
    have h_H_le_C : H.toSubmodule ≤ C :=
      h_H_le_C_1 β.val hβ_nonzero
    have h_rootSpace_le_C :
        ∀ α : Weight K H L, α ≠ β →
          (rootSpace H α).toSubmodule ≤ C :=
      fun α hα => le_iSup₂_of_le α hα (le_refl _)
    have h_I_le_C : I.toSubmodule ≤ C := by
      refine le_trans hΦ₁.le ?_
      have hIH_subset_C :
          (I : Submodule K L) ⊓ H.toSubmodule ≤
            ⨆ j ≠ β.val,
              (rootSpace H j).toSubmodule :=
        le_trans inf_le_right h_H_le_C
      refine sup_le hIH_subset_C ?_
      simp +decide only [iSup_le_iff, Subtype.forall,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun a ha ha' =>
        le_iSup₂_of_le a
          (by rintro rfl; exact hβ_not_Φ₁ ha') le_rfl
    have h_J_le_C : J.toSubmodule ≤ C := by
      refine le_trans hΦ₂.le ?_
      have hJH_subset_C :
          (J : Submodule K L) ⊓ H.toSubmodule ≤
            ⨆ j ≠ β.val,
              (rootSpace H j).toSubmodule :=
        le_trans inf_le_right h_H_le_C
      refine sup_le hJH_subset_C ?_
      simp +decide only [iSup_le_iff, Subtype.forall,
        Finset.mem_filter, Finset.mem_univ, true_and]
      exact fun a ha ha' =>
        le_iSup₂_of_le a
          (by rintro rfl; exact hβ_not_Φ₂ ha') le_rfl
    have h_leq : I.toSubmodule ⊔ J.toSubmodule ≤ C :=
      sup_le h_I_le_C h_J_le_C
    have h_inf_I :
        (rootSpace H β).toSubmodule ⊓
          (I.toSubmodule ⊔ J.toSubmodule) = ⊥ :=
      eq_bot_iff.mpr fun x hx =>
        h_inf_C.le ⟨hx.1, h_leq hx.2⟩
    rw [sup_1] at h_inf_I
    have h_rootSpace_nonzero :
        (rootSpace H β : Submodule K L) ≠ ⊥ := by
      have := β.val.genWeightSpace_ne_bot
      simp only [ne_eq] at this
      simp only [ne_eq, LieSubmodule.toSubmodule_eq_bot]
      dsimp [rootSpace]
      exact this
    exact h_rootSpace_nonzero (by simpa using h_inf_I)
  have s4 : Φ₁ ≠ ∅ := by
    by_contra Φ_empty
    rw [Φ_empty] at hΦ₁
    simp only [Set.mem_empty_iff_false, iSup_false,
      iSup_bot, sup_bot_eq] at hΦ₁
    have ttt := cartan_is_abelian (K := K) (H := H) (L := L)
    have rrr : IsLieAbelian I := by
      have hI_abelian : IsLieAbelian (↥I) := by
        have h_submodule : I.toSubmodule ≤ H.toSubmodule :=
          inf_eq_left.mp hΦ₁.symm
        constructor
        have h_abelian :
            ∀ x m : L, x ∈ I.toSubmodule →
              m ∈ I.toSubmodule → ⁅x, m⁆ = 0 := by
          intro x m hx hm
          have := ttt.1 ⟨x, h_submodule hx⟩
            ⟨m, h_submodule hm⟩
          exact congr_arg Subtype.val this
        exact fun x m =>
          Subtype.ext <| h_abelian x m x.2 m.2
      exact hI_abelian
    haveI : LieAlgebra.IsSemisimple K L :=
      LieAlgebra.IsKilling.instSemisimple K L
    exact hI_ne_bot (by
      exact HasTrivialRadical.eq_bot_of_isSolvable I)
  have s5 : Φ₂ ≠ ∅ := by
    by_contra Φ_empty
    rw [Φ_empty] at hΦ₂
    simp only [Set.mem_empty_iff_false, iSup_false,
      iSup_bot, sup_bot_eq] at hΦ₂
    have ttt := cartan_is_abelian (K := K) (H := H) (L := L)
    have rrr : IsLieAbelian J := by
      have hI_abelian : IsLieAbelian (↥J) := by
        have h_submodule : J.toSubmodule ≤ H.toSubmodule :=
          inf_eq_left.mp hΦ₂.symm
        constructor
        have h_abelian :
            ∀ x m : L, x ∈ J.toSubmodule →
              m ∈ J.toSubmodule → ⁅x, m⁆ = 0 := by
          intro x m hx hm
          have := ttt.1 ⟨x, h_submodule hx⟩
            ⟨m, h_submodule hm⟩
          exact congr_arg Subtype.val this
        exact fun x m =>
          Subtype.ext <| h_abelian x m x.2 m.2
      exact hI_abelian
    haveI : LieAlgebra.IsSemisimple K L :=
      LieAlgebra.IsKilling.instSemisimple K L
    exact hJ_ne_bot (by
      exact HasTrivialRadical.eq_bot_of_isSolvable J)
  let S := rootSystem H
  have xxx (i : Φ₁) (j : Φ₂) : S.pairing i j = 0 := by
    have hΦ₁_le :
        ∀ α : H.root, α ∈ Φ₁ →
          (rootSpace H (α : Weight K H L) :
            Submodule K L) ≤ I.toSubmodule := by
      intro α hα
      calc (rootSpace H (α : Weight K H L) :
              Submodule K L)
        _ ≤ ⨆ β ∈ Φ₁, (rootSpace H β.1).toSubmodule :=
            le_iSup₂_of_le α hα le_rfl
        _ ≤ I.toSubmodule := by rw [hΦ₁]; exact le_sup_right
    have hΦ₂_le :
        ∀ α : H.root, α ∈ Φ₂ →
          (rootSpace H (α : Weight K H L) :
            Submodule K L) ≤ J.toSubmodule := by
      intro α hα
      calc (rootSpace H (α : Weight K H L) :
              Submodule K L)
        _ ≤ ⨆ β ∈ Φ₂, (rootSpace H β.1).toSubmodule :=
            le_iSup₂_of_le α hα le_rfl
        _ ≤ J.toSubmodule := by rw [hΦ₂]; exact le_sup_right
    obtain ⟨e_i, he_i_mem, he_i_ne_zero⟩ :=
      (i.val : Weight K H L).exists_ne_zero
    have h_e_i_in_I : e_i ∈ I.toSubmodule :=
      hΦ₁_le i.val i.property he_i_mem
    have h_coroot_j_in_J :
        (coroot (j.val : Weight K H L) : L) ∈ J.toSubmodule :=
      coroot_mem_lieIdeal_of_rootSpace_le J
        (j.val : Weight K H L) (hΦ₂_le j.val j.property)
    have h_bracket_in_I :
        ⁅(coroot (j.val : Weight K H L) : L), e_i⁆ ∈
          I.toSubmodule :=
      lie_mem_right K L I _ _ h_e_i_in_I
    have h_bracket_in_J :
        ⁅(coroot (j.val : Weight K H L) : L), e_i⁆ ∈
          J.toSubmodule :=
      lie_mem_left K L J _ _ h_coroot_j_in_J
    have h_bracket_zero :
        ⁅(coroot (j.val : Weight K H L) : L), e_i⁆ = 0 := by
      have h_in_inf :
          ⁅(coroot (j.val : Weight K H L) : L), e_i⁆ ∈
            I.toSubmodule ⊓ J.toSubmodule :=
        ⟨h_bracket_in_I, h_bracket_in_J⟩
      rw [bot_1] at h_in_inf
      exact h_in_inf
    have h_lie_eq_smul :
        ⁅(coroot (j.val : Weight K H L) : L), e_i⁆ =
          (i.val : Weight K H L)
            (coroot (j.val : Weight K H L)) • e_i :=
      lie_eq_smul_of_mem_rootSpace he_i_mem
        (coroot (j.val : Weight K H L))
    have h_eval_zero :
        (i.val : Weight K H L)
          (coroot (j.val : Weight K H L)) = 0 := by
      rw [h_bracket_zero] at h_lie_eq_smul
      exact smul_eq_zero.mp h_lie_eq_smul.symm |>.resolve_right
        he_i_ne_zero
    change S.pairing i j = 0
    simp only [S, rootSystem_pairing_apply]
    exact h_eval_zero
  have := hIrr
  cases this
  rename_i h₁ h₂ h₃
  contrapose! h₂
  refine ⟨Submodule.span K
    (Set.image
      (fun i : Φ₁ => (LieAlgebra.IsKilling.rootSystem H).root i)
      Set.univ), ?_, ?_, ?_⟩
  · intro i
    simp +decide only [Module.End.mem_invtSubmodule,
      rootSystem_root_apply, Set.image_univ]
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp +decide only [Submodule.comap_coe, LinearEquiv.coe_coe, Set.mem_preimage,
      SetLike.mem_coe, RootPairing.reflection_apply]
    refine Submodule.sub_mem _ ?_ ?_
    · exact Submodule.subset_span ⟨a, rfl⟩
    · by_cases hi : i ∈ Φ₁
      · exact Submodule.smul_mem _ _
          (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · have hi₂ : i ∈ Φ₂ :=
          Or.resolve_left
            (s3.symm.subset (Set.mem_univ i)) hi
        specialize xxx a ⟨i, hi₂⟩
        simp +zetaDelta only [ne_eq, LieIdeal.toSubmodule_killingCompl, nontrivial_dual_iff,
          Subtype.forall, Finset.mem_filter, Finset.mem_univ, true_and, rootSystem_pairing_apply,
          LinearMap.flip_apply, rootSystem_coroot_apply, rootSystem_toLinearMap_apply,
          Weight.toLinear_apply, rootSystem_root_apply] at *
        simp +decide [xxx]
  · simp +decide
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 s4
    grind
  · have h_span_proper :
        Submodule.span K
          (Set.image (fun i : Φ₁ => S.root i)
            Set.univ) ≠ ⊤ := by
      have h_nonzero :
          ∃ j : { x : LieModule.Weight K (↥H) L //
            x ∈ LieSubalgebra.root }, j ∈ Φ₂ :=
        Set.nonempty_iff_ne_empty.2 s5
      obtain ⟨j, hj⟩ := h_nonzero
      intro h
      rw [Submodule.eq_top_iff'] at h
      specialize h (S.root j)
      rw [Finsupp.mem_span_image_iff_linearCombination] at h
      obtain ⟨l, hl₁, hl₂⟩ := h
      replace hl₂ :=
        congr_arg (fun f => f (S.coroot j)) hl₂
      simp +decide only [Finsupp.linearCombination_apply,
        Finsupp.sum] at hl₂
      simp +zetaDelta only [ne_eq, LieIdeal.toSubmodule_killingCompl, rootSystem_pairing_apply,
        Subtype.forall, Finset.mem_filter, Finset.mem_univ, true_and, nontrivial_dual_iff,
        Finsupp.supported_univ, Submodule.mem_top, rootSystem_root_apply,
        rootSystem_coroot_apply, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        Weight.toLinear_apply, smul_eq_mul] at *
      have h_sum_zero :
          ∑ x ∈ l.support,
            (l x) * ((x.val : LieModule.Weight K (↥H) L) :
              ↥H → K)
              (LieAlgebra.IsKilling.coroot (j.val)) = 0 := by
        have h_term_zero :
            ∀ x ∈ l.support,
              (l x) * ((x.val :
                LieModule.Weight K (↥H) L) : ↥H → K)
                (LieAlgebra.IsKilling.coroot (j.val)) = 0 := by
          grind
        exact Finset.sum_eq_zero h_term_zero
      simp +decide [h_sum_zero] at hl₂
      have h_root_coroot :
          (j.val : ↥H → K)
            (LieAlgebra.IsKilling.coroot (j.val)) = 2 := by
        apply LieAlgebra.IsKilling.root_apply_coroot
        grind
      norm_num [h_root_coroot] at hl₂
    exact h_span_proper

end

end LieAlgebra.IsKilling
