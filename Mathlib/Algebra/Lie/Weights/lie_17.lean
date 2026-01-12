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

    -- Step 3: (rootSpace H β) ⊓ (⨆ α ∈ Φ₁, rootSpace H α) = ⊥
    -- Use: iSupIndep.disjoint_biSup with h_indep and hβ_not_Φ₁
    have h_inf_Φ₁ : (rootSpace H β).toSubmodule ⊓ (⨆ α ∈ Φ₁, (rootSpace H α.1).toSubmodule) = ⊥ :=
      by
        have := h_indep ( β : LieModule.Weight K H L );
        -- Since the supremum of the root spaces for Φ₁ is contained within the supremum of the root spaces for all weights except β, and the root space of β is disjoint from that supremum, their intersection is zero.
        have h_contained : ⨆ α ∈ Φ₁, (rootSpace H α.val).toSubmodule ≤ ⨆ j ≠ β.val, (rootSpace H j).toSubmodule := by
          simp +decide [ iSup_le_iff ];
          exact fun a ha ha' => le_iSup₂_of_le a ( by rintro rfl; exact hβ_not_Φ₁ ha' ) le_rfl;
        exact eq_bot_iff.mpr fun x hx => this.le_bot ⟨ hx.1, h_contained hx.2 ⟩

    -- Step 4: (rootSpace H β) ⊓ H = ⊥
    -- Key: H.toLieSubmodule = rootSpace H 0 (by rootSpace_zero_eq)
    -- Since β.IsNonZero, β ≠ 0, so by h_indep they have trivial intersection
    have h_inf_H : (rootSpace H β).toSubmodule ⊓ H.toSubmodule = ⊥ := by
        -- Since β is a non-zero root, the root space LieAlgebra.rootSpace H β is non-zero. However, the Cartan subalgebra H is a subalgebra, and the root spaces are orthogonal to H. Therefore, the intersection of LieAlgebra.rootSpace H β and H.toSubmodule must be zero.
        have h_orthogonal : ∀ x ∈ LieAlgebra.rootSpace H β.val, x ∈ H.toSubmodule → x = 0 := by
          intro x hx₁ hx₂;
          have h_orthogonal : ∀ h : H, β.val h • x = 0 := by
            intro h;
            have h_orthogonal : ∀ h : H, β.val h • x = 0 := by
              intro h
              have h_comm : ⁅h, x⁆ = β.val h • x := by
                exact?
              rw [ ← h_comm, LieSubalgebra.coe_bracket_of_module ];
              -- Since $H$ is a Cartan subalgebra, it is abelian, so $[h, x] = 0$ for any $h, x \in H$.
              have h_abelian : ∀ h x : H, ⁅h, x⁆ = 0 := by
                simp +decide [ LieSubalgebra.IsCartanSubalgebra ];
              exact congr_arg Subtype.val ( h_abelian h ⟨ x, hx₂ ⟩ );
            exact h_orthogonal h;
          contrapose! hβ_nonzero;
          exact funext fun h => by simpa [ hβ_nonzero ] using h_orthogonal h;
        exact eq_bot_iff.mpr fun x hx => h_orthogonal x hx.1 hx.2

    -- Step 5: (rootSpace H β) ⊓ I = ⊥
    -- From hΦ₁: I = (I ⊓ H) ⊔ (⨆ α ∈ Φ₁, rootSpace H α)
    -- (rootSpace H β) ⊓ H = ⊥ (step 4), hence (rootSpace H β) ⊓ (I ⊓ H) = ⊥
    -- (rootSpace H β) ⊓ (⨆ α ∈ Φ₁) = ⊥ (step 3)
    -- Need: a ⊓ (b ⊔ c) = ⊥ when a ⊓ b = ⊥ and a ⊓ c = ⊥
    -- This follows from: a ⊓ (b ⊔ c) ≤ (a ⊓ b) ⊔ (a ⊓ c) in modular lattice? No...
    -- Actually need: I ≤ ⨆ χ ≠ β, rootSpace H χ, then use h_indep
    have h_inf_I : (rootSpace H β).toSubmodule ⊓ I.toSubmodule = ⊥ := by
      sorry

    -- Step 6: (rootSpace H β) ⊓ (⨆ α ∈ Φ₂, rootSpace H α) = ⊥
    -- Similar to step 3, using hβ_not_Φ₂
    have h_inf_Φ₂ : (rootSpace H β).toSubmodule ⊓ (⨆ α ∈ Φ₂, (rootSpace H α.1).toSubmodule) = ⊥ := by
      have := h_indep (β : Weight K H L)
      have h_contained : ⨆ α ∈ Φ₂, (rootSpace H α.val).toSubmodule ≤
          ⨆ j ≠ β.val, (rootSpace H j).toSubmodule := by
        simp +decide [iSup_le_iff]
        exact fun a ha ha' => le_iSup₂_of_le a (by rintro rfl; exact hβ_not_Φ₂ ha') le_rfl
      exact eq_bot_iff.mpr fun x hx => this.le_bot ⟨hx.1, h_contained hx.2⟩

    -- Step 7: (rootSpace H β) ⊓ J = ⊥
    have h_inf_J : (rootSpace H β).toSubmodule ⊓ J.toSubmodule = ⊥ := by
      sorry

    -- Step 8: (rootSpace H β) ⊓ (I ⊔ J) = ⊥
    have h_inf_IJ : (rootSpace H β).toSubmodule ⊓ (I.toSubmodule ⊔ J.toSubmodule) = ⊥ := by
      sorry

    -- Step 9: But I ⊔ J = ⊤, so (rootSpace H β) ⊓ ⊤ = ⊥
    rw [sup_1, inf_top_eq] at h_inf_IJ

    -- Step 10: This means rootSpace H β = ⊥
    have h_bot : rootSpace H β = ⊥ := by
      rw [← LieSubmodule.toSubmodule_eq_bot]
      exact h_inf_IJ

    -- Step 11: But rootSpace H β ≠ ⊥ for any weight β
    have h_ne_bot : rootSpace H β ≠ ⊥ := (β : Weight K H L).genWeightSpace_ne_bot'

    exact h_ne_bot h_bot

  admit

end LieAlgebra.IsKilling
