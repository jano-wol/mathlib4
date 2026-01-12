import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

lemma cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  admit

lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  admit

theorem isSimple_of_isIrreducible (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L := by
  by_contra h_not_simple
  obtain ⟨I, hI_ne_bot, hI_ne_top⟩ : ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
    admit
  let J := I.killingCompl
  obtain ⟨Φ₁, hΦ₁⟩ := exists_rootSet_lieIdeal_eq (H := H) I
  obtain ⟨Φ₂, hΦ₂⟩ := exists_rootSet_lieIdeal_eq (H := H) J

  have s1 : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
    admit

  have sup_1 : I.toSubmodule ⊔ J.toSubmodule = ⊤ := by
    admit
  /-
    PROVIDED_SOLUTION:
    Lets assume that there is a root β which is not in Φ₁ unio Φ₂.
    Take the rootSpace: rootSpace H β. By iSupIndep_genWeightSpace or iSupIndep_genWeightSpace'
    H β is indepenent of all the other root spaces. This implies it is independent of H (as H is the root space correpsonding to zeor, and β ≠ 0).
    By hΦ₁: rootSpace H β is independent of I. Similarly by hΦ₂ rootSpace H β is independent of J.
    But then rootSpace H β is independent of I ⊔ J. But according to sup_1, I ⊔ J is ⊤. This contradiction shows s₃.
  -/
  have s3 : Φ₁ ∪ Φ₂ = Set.univ := by
    by_contra h_not_univ
    rw [← ne_eq, Set.ne_univ_iff_exists_notMem] at h_not_univ
    obtain ⟨β, hβ⟩ := h_not_univ
    rw [Set.mem_union, not_or] at hβ
    obtain ⟨hβ_not_Φ₁, hβ_not_Φ₂⟩ := hβ

    -- Step 1: β is a nonzero weight (since β ∈ H.root = {α | α.IsNonZero})
    have hβ_nonzero : (β : Weight K H L).IsNonZero := by
      -- Extract IsNonZero from membership in LieSubalgebra.root
      have := β.2
      simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this

    -- Step 2: Independence of weight spaces (rootSpace = genWeightSpace)
    -- Key lemma: iSupIndep_genWeightSpace' gives independence over all weights
    have h_indep : iSupIndep fun (χ : Weight K H L) => (rootSpace H χ).toSubmodule :=
      sorry -- use iSupIndep_genWeightSpace' and the fact that rootSpace = genWeightSpace

    -- Step 3: rootSpace H β is disjoint from ⨆ α ∈ Φ₁, rootSpace H α
    -- Use: iSupIndep.disjoint_biSup with h_indep and hβ_not_Φ₁
    have h_disj_Φ₁ : Disjoint (rootSpace H β).toSubmodule (⨆ α ∈ Φ₁, (rootSpace H α.1).toSubmodule) :=
      sorry

    -- Step 4: rootSpace H β is disjoint from H.toSubmodule
    -- Key: H.toLieSubmodule = rootSpace H 0 (by rootSpace_zero_eq)
    -- Since β.IsNonZero, β ≠ 0, so by h_indep they are disjoint
    have h_disj_H : Disjoint (rootSpace H β).toSubmodule H.toSubmodule :=
      sorry

    -- Step 5: rootSpace H β is disjoint from I.toSubmodule
    -- From hΦ₁: I = (I ⊓ H) ⊔ (⨆ α ∈ Φ₁, rootSpace H α)
    -- rootSpace H β is disjoint from H (step 4), hence from I ⊓ H
    -- rootSpace H β is disjoint from ⨆ α ∈ Φ₁ (step 3)
    -- Therefore disjoint from their sup
    -- Use: Disjoint.sup_right or Submodule.disjoint_def
    have h_disj_I : Disjoint (rootSpace H β).toSubmodule I.toSubmodule := by
      rw [hΦ₁]
      -- Need: Disjoint with (I ⊓ H) ⊔ (⨆ α ∈ Φ₁, rootSpace H α)
      -- We have h_disj_H (disjoint with H) and h_disj_Φ₁ (disjoint with the sup)
      sorry

    -- Step 6: rootSpace H β is disjoint from ⨆ α ∈ Φ₂, rootSpace H α
    -- Similar to step 3, using hβ_not_Φ₂
    have h_disj_Φ₂ : Disjoint (rootSpace H β).toSubmodule (⨆ α ∈ Φ₂, (rootSpace H α.1).toSubmodule) :=
      sorry

    -- Step 7: rootSpace H β is disjoint from J.toSubmodule
    have h_disj_J : Disjoint (rootSpace H β).toSubmodule J.toSubmodule := by
      rw [hΦ₂]
      sorry

    -- Step 8: rootSpace H β is disjoint from I ⊔ J
    have h_disj_IJ : Disjoint (rootSpace H β).toSubmodule (I.toSubmodule ⊔ J.toSubmodule) := by
      -- Use h_disj_I and h_disj_J
      -- For Submodules: x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z) due to IsModularLattice
      -- Disjoint a b ↔ a ⊓ b = ⊥
      -- Disjoint a (b ⊔ c) ← Disjoint a b ∧ Disjoint a c
      sorry

    -- Step 9: But I ⊔ J = ⊤, so rootSpace H β is disjoint from ⊤
    rw [sup_1, disjoint_top] at h_disj_IJ

    -- Step 10: This means rootSpace H β = ⊥
    have h_bot : rootSpace H β = ⊥ := by
      rw [← LieSubmodule.toSubmodule_eq_bot]
      exact h_disj_IJ

    -- Step 11: But rootSpace H β ≠ ⊥ for any weight β
    -- β : ↥LieSubalgebra.root coerces to Weight K H L
    -- rootSpace H β = genWeightSpace L β, and Weight.genWeightSpace_ne_bot' gives ne ⊥
    have h_ne_bot : rootSpace H β ≠ ⊥ := (β : Weight K H L).genWeightSpace_ne_bot'

    exact h_ne_bot h_bot

  admit

end LieAlgebra.IsKilling
