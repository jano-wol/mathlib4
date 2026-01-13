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
    -- rootSpace H χ = genWeightSpace L χ by definition
    have h_indep : iSupIndep fun (χ : Weight K H L) => (rootSpace H χ).toSubmodule :=
      LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' K H L)

    let C := ⨆ j ≠ (β : Weight K H L), (rootSpace H j).toSubmodule

    -- Step 3: (rootSpace H β) ⊓ C = ⊥ (directly from h_indep)
    -- h_indep gives Disjoint, convert to ⊓ = ⊥ using disjoint_iff
    have h_inf_C : (rootSpace H β).toSubmodule ⊓ C = ⊥ := disjoint_iff.mp (h_indep (β : Weight K H L))


    -- (1) H ≤ C: H = rootSpace H 0, and 0 ≠ β (since β is nonzero)
    -- Key: rootSpace_zero_eq, le_iSup₂_of_le
    have h_H_le_C : H.toSubmodule ≤ C := by
      sorry

    -- (2) For any α ≠ β, rootSpace H α ≤ C
    have h_rootSpace_le_C : ∀ α : Weight K H L, α ≠ β → (rootSpace H α).toSubmodule ≤ C :=
      fun α hα => le_iSup₂_of_le α hα (le_refl _)

    -- I ≤ C: From hΦ₁, I = (I ⊓ H) ⊔ ⨆ α ∈ Φ₁, rootSpace H α
    -- (I ⊓ H) ≤ H ≤ C and each rootSpace in Φ₁ ≤ C (since β ∉ Φ₁)
    have h_I_le_C : I.toSubmodule ≤ C := by
      refine' le_trans ( hΦ₁.le ) _;
      -- Since $H \subseteq C$, we have $I \cap H \subseteq C$.
      have hIH_subset_C : (I : Submodule K L) ⊓ H.toSubmodule ≤ ⨆ j ≠ β.val, (rootSpace H j).toSubmodule := by
        refine' le_trans _ ( h_H_le_C);
        exact inf_le_right;
      refine' sup_le hIH_subset_C _;
      simp +decide [ iSup_le_iff ];
      exact fun a ha ha' => le_iSup₂_of_le a ( by rintro rfl; exact hβ_not_Φ₁ ha' ) le_rfl

    -- Now h_inf_I follows from h_I_le_C and h_inf_C via eq_bot_iff.
    have h_inf_I : (rootSpace H β).toSubmodule ⊓ I.toSubmodule = ⊥ :=
      eq_bot_iff.mpr fun x hx => h_inf_C.le ⟨hx.1, h_I_le_C hx.2⟩
    admit
  admit

end LieAlgebra.IsKilling
