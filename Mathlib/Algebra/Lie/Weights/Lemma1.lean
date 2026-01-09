/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 46170524-5fc6-4f3a-ab10-62a2e2972948

The following was proved by Aristotle:

- lemma exists_lieIdeal_generating_set_mem_genWeightSpace (I : LieIdeal K L) :
    ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧
      ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ
-/

import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.CategoryTheory.Category.Basic

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]

open LieAlgebra LieModule Module

variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]

variable [IsKilling K L] [IsTriangularizable K H L]

noncomputable section AristotleLemmas

variable (I : LieIdeal K L)

instance : LieModule.IsTriangularizable K H I := by
  -- Since $L$ is triangularizable over $H$, we can apply the fact that any submodule of a triangularizable module is also triangularizable.
  have h_submodule : ∀ (M : LieSubmodule K H L), (LieModule.IsTriangularizable K H L) → (LieModule.IsTriangularizable K H M) := by
    exact?;
  convert h_submodule _ ‹_›;
  rotate_right;
  constructor;
  rotate_left;
  exact I.toSubmodule;
  all_goals { exact? }

lemma mem_genWeightSpace_of_mem_ideal_genWeightSpace (χ : H → K) (x : I)
    (hx : x ∈ LieModule.genWeightSpace I χ) :
    (x : L) ∈ LieModule.genWeightSpace L χ := by
      -- Let `f : I →ₗ⁅K,H⁆ L` be the inclusion map, restricted to `H`. This is `(LieSubmodule.incl I).restrictLie H`.
      set f : I →ₗ⁅K, H⁆ L := (LieSubmodule.incl I).restrictLie H;
      -- By `LieModule.map_genWeightSpace_le`, `(genWeightSpace I χ).map f ≤ genWeightSpace L χ`.
      have h_map : (LieModule.genWeightSpace I χ).map f ≤ LieModule.genWeightSpace L χ := by
        exact?;
      exact h_map ⟨ x, hx, rfl ⟩

lemma span_image_genWeightSpace_eq_toSubmodule :
    Submodule.span K (⋃ (χ : Weight K H L), (LieModule.genWeightSpace I χ : Set I).image (fun (x : I) ↦ (x : L))) = I.toSubmodule := by
  have h_iSup : (⨆ χ : LieModule.Weight K H L, LieModule.genWeightSpace I χ) = ⊤ := by
    convert LieModule.iSup_genWeightSpace_eq_top K H I;
    refine' le_antisymm _ _;
    · exact iSup_mono' fun χ => by aesop;
    · refine' iSup_le fun χ => _;
      by_cases h : ∃ χ' : LieModule.Weight K H I, χ = χ'.toFun;
      · obtain ⟨ χ', rfl ⟩ := h;
        refine' le_iSup_of_le ⟨ χ'.toFun, _ ⟩ le_rfl;
        have := χ'.exists_ne_zero;
        obtain ⟨ x, hx₁, hx₂ ⟩ := this;
        exact fun h => hx₂ <| by simpa [ h ] using mem_genWeightSpace_of_mem_ideal_genWeightSpace I χ'.toFun x hx₁;
      · intro x hx;
        contrapose! h;
        refine' ⟨ ⟨ χ, _ ⟩, rfl ⟩;
        exact fun h_eq => h (by simp_all)
  convert congr_arg ( fun s : LieSubmodule K H I => s.toSubmodule.map ( I.subtype ) ) h_iSup using 1;
  · simp +decide [ Submodule.map_iSup, Submodule.span_iUnion ];
    congr! 2;
    rw [ Submodule.span_eq_of_le ];
    · aesop_cat;
    · exact fun x hx => by rcases hx with ⟨ y, hy, rfl ⟩ ; exact Submodule.subset_span ⟨ y, hy, rfl ⟩ ;
  · aesop

end AristotleLemmas

lemma exists_lieIdeal_generating_set_mem_genWeightSpace (I : LieIdeal K L) :
    ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧
      ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ := by
  by_contra h_contra;
  norm_num +zetaDelta at *;
  -- Let's choose any $x \in I$.
  obtain ⟨S, hS⟩ : ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧ ∀ x ∈ S, ∃ χ : LieModule.Weight K H L, x ∈ LieModule.genWeightSpace L χ := by
    use (⋃ (χ : LieModule.Weight K H L), (LieModule.genWeightSpace I χ : Set I).image (fun (x : I) ↦ (x : L)));
    exact ⟨ by exact? , by rintro x hx; rcases Set.mem_iUnion.mp hx with ⟨ χ, y, hy, rfl ⟩ ; exact ⟨ χ, by exact? ⟩ ⟩;
  obtain ⟨ x, hxS, hx ⟩ := h_contra S hS.1 ; obtain ⟨ χ, hχ ⟩ := hS.2 x hxS ; exact hx χ hχ

lemma lieIdeal_eq_iSup_inf_genWeightSpace (I : LieIdeal K L) :
    I.toSubmodule = ⨆ χ : Weight K H L, I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
  rw [ eq_comm ];
  -- By definition of LieModule.IsTriangularizable, there exists a generating set S such that each element of S lies in some generalized weight space.
  obtain ⟨S, hS⟩ : ∃ S : Set L, Submodule.span K S = I.toSubmodule ∧ ∀ x ∈ S, ∃ χ : Weight K H L, x ∈ genWeightSpace L χ := by
    exact?;
  refine' le_antisymm _ _;
  · exact iSup_le fun χ => inf_le_left;
  · rw [ ← hS.1, Submodule.span_le ];
    intro x hx;
    obtain ⟨ χ, hχ ⟩ := hS.2 x hx;
    exact Submodule.mem_iSup_of_mem χ ( Submodule.mem_inf.mpr ⟨ Submodule.subset_span hx, hχ ⟩ )

lemma lieIdeal_eq_iSup_inf (I : LieIdeal K L) :
    I.toSubmodule = (I.toSubmodule ⊓ H.toLieSubmodule.toSubmodule) ⊔
      ⨆ α : {α : Weight K H L // α.IsNonZero}, I.toSubmodule ⊓ (genWeightSpace L α.1).toSubmodule := by
  -- Apply the hypothesis `h_split` to rewrite the right-hand side of the equation.
  apply le_antisymm;
  · have h_split : I.toSubmodule ≤ ⨆ (χ : Weight K H L), I.toSubmodule ⊓ (genWeightSpace L χ).toSubmodule := by
      convert lieIdeal_eq_iSup_inf_genWeightSpace I |> le_of_eq;
      · infer_instance;
      · infer_instance;
    refine' le_trans h_split _;
    refine' iSup_le _;
    intro χ;
    by_cases hχ : χ.IsZero;
    · simp +decide [ hχ ];
    · exact le_sup_of_le_right ( le_iSup_of_le ⟨ χ, hχ ⟩ le_rfl );
  · aesop

end LieAlgebra.IsKilling
