/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.HumphreysLemmaGeneral
public import Mathlib.Algebra.Lie.Engel

/-!
# Cartan's Criterion: IsSemisimple implies IsKilling

This file proves that in characteristic zero, any semisimple Lie algebra has
non-degenerate Killing form (i.e., is a "Killing Lie algebra").

The proof uses Humphreys' lemma (from `Mathlib.Algebra.Lie.HumphreysLemmaGeneral`)
together with Engel's theorem to show the kernel of the Killing form is a solvable
ideal, hence trivial in a semisimple Lie algebra.
-/

@[expose] public section

open LieAlgebra LieModule LinearMap Module

namespace LieAlgebra

variable (K L : Type*) [Field K] [CharZero K]
  [LieRing L] [LieAlgebra K L] [Module.Finite K L]

/-- In characteristic zero, any semisimple Lie algebra has non-degenerate Killing form. -/
instance IsSemisimple.instIsKilling [IsSemisimple K L] : IsKilling K L where
  killingCompl_top_eq_bot := by
    -- Let S = killingCompl K L ⊤ (kernel of the Killing form)
    set S := LieIdeal.killingCompl K L ⊤
    set SS : LieIdeal K L := ⁅S, S⁆
    -- Set up A ⊆ B in End K L (images of ⁅S,S⁆ and S under ad)
    -- Use the linear map underlying ad
    let ad_lin : L →ₗ[K] End K L := (ad K L : L →ₗ⁅K⁆ End K L)
    set A : Submodule K (End K L) :=
      (SS : LieSubmodule K L L).toSubmodule.map ad_lin
    set B : Submodule K (End K L) :=
      (S : LieSubmodule K L L).toSubmodule.map ad_lin
    have hAB : A ≤ B := Submodule.map_mono
      ((LieSubmodule.toSubmodule_le_toSubmodule SS S).mpr (LieSubmodule.lie_le_left S S))
    -- Step 1: For x ∈ ⁅S,S⁆, ad(x) is nilpotent (via Humphreys' lemma)
    have ad_nil : ∀ x ∈ (SS : LieSubmodule K L L).toSubmodule,
        IsNilpotent (ad_lin x) := by
      intro x hx
      apply humphreys_lemma A B hAB
      -- Goal 1: ad(x) ∈ M(A,B), i.e. ∀ b ∈ B, ⁅ad(x), b⁆ ∈ A
      · intro b hb
        obtain ⟨s, hs, rfl⟩ := hb
        -- Need: ⁅ad_lin x, ad_lin s⁆ ∈ A
        -- ⁅ad_lin x, ad_lin s⁆ = ad_lin ⁅x, s⁆ (since ad is a Lie hom)
        change ⁅ad_lin x, ad_lin s⁆ ∈ A
        have h_lie : ad_lin ⁅x, s⁆ = ⁅ad_lin x, ad_lin s⁆ := LieHom.map_lie (ad K L) x s
        rw [← h_lie]
        apply Submodule.mem_map_of_mem
        -- Need: ⁅x, s⁆ ∈ SS.toSubmodule
        -- x ∈ SS ≤ S (as ideal), s ∈ S, so ⁅x, s⁆ ∈ ⁅S, S⁆ = SS
        -- Actually: SS is an ideal of L, x ∈ SS, so ⁅x, s⁆ ∈ SS
        have hx_SS : x ∈ (SS : LieSubmodule K L L) := hx
        have hs_S : s ∈ (S : LieSubmodule K L L) := hs
        -- ⁅x, s⁆ ∈ ⁅SS, S⁆ ≤ SS (since SS is an ideal)
        exact LieSubmodule.lie_le_left SS S (LieSubmodule.lie_mem_lie hx_SS hs_S)
      -- Goal 2: ∀ z ∈ M(A,B), tr(ad(x) * z) = 0
      · intro z hz
        -- The linear functional y ↦ tr(ad(y) * z) vanishes on ⁅S,S⁆
        -- by linearity, suffices to show it vanishes on generators ⁅a,b⁆ with a,b ∈ S
        have hx' : x ∈ Submodule.span K {⁅a, b⁆ | (a ∈ (S : LieSubmodule K L L))
            (b ∈ (S : LieSubmodule K L L))} := by
          rw [← LieSubmodule.lieIdeal_oper_eq_linear_span']; exact hx
        -- Induction on the span
        refine Submodule.span_induction (p := fun x _ =>
            trace K L (ad_lin x * z) = 0) ?_ ?_ ?_ ?_ hx'
        -- Case: x = ⁅a, b⁆ with a ∈ S, b ∈ S
        · rintro _ ⟨a, ha, b, hb, rfl⟩
          -- ad(⁅a,b⁆) = ⁅ad(a), ad(b)⁆ = ad(a) * ad(b) - ad(b) * ad(a)
          have h_lie : ad_lin ⁅a, b⁆ = ad_lin a * ad_lin b - ad_lin b * ad_lin a := by
            have := LieHom.map_lie (ad K L) a b
            rw [Ring.lie_def] at this
            exact this
          rw [h_lie, sub_mul, map_sub,
            ← trace_mul_cycle (R := K) (M := L) (ad_lin a) z (ad_lin b), ← map_sub,
            show ad_lin a * ad_lin b * z - ad_lin a * z * ad_lin b =
              ad_lin a * (ad_lin b * z - z * ad_lin b)
              from by simp only [mul_sub, mul_assoc]]
          -- ad(b)*z - z*ad(b) = -⁅z, ad(b)⁆ ∈ A (since z ∈ M(A,B) and ad(b) ∈ B)
          have hb_in_B : ad_lin b ∈ B := Submodule.mem_map_of_mem hb
          have hz_comm : ad_lin b * z - z * ad_lin b ∈ A := by
            have h := hz (ad_lin b) hb_in_B
            rw [Ring.lie_def] at h
            have := A.neg_mem h
            rwa [neg_sub] at this
          -- So ad(b)*z - z*ad(b) = ad(w) for some w ∈ ⁅S,S⁆
          obtain ⟨w, hw, hwz⟩ := hz_comm
          rw [← hwz]
          -- tr(ad(a) * ad(w)) = killingForm(a, w) = 0 since a ∈ S
          change (trace K L) ((ad K L) a ∘ₗ (ad K L) w) = 0
          rw [← killingForm_apply_apply, LieModule.traceForm_comm]
          exact (LieIdeal.mem_killingCompl K L ⊤).mp ha w (LieSubmodule.mem_top w)
        -- Case: x = 0
        · simp
        -- Case: x = x₁ + x₂
        · intro x₁ x₂ _ _ h1 h2
          rw [map_add, add_mul, map_add, h1, h2, add_zero]
        -- Case: x = c • x₁
        · intro c x₁ _ h1
          rw [map_smul, smul_mul_assoc, LinearMap.map_smul, h1, smul_zero]
    -- Step 2: ⁅S,S⁆ is nilpotent as a Lie algebra (Engel's theorem)
    have ss_nilpotent : LieRing.IsNilpotent ↥SS := by
      rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
      intro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := ad_nil x hx
      -- ad(x) restricts to SS since SS is a Lie ideal of L
      have h_inv : ∀ y ∈ (SS : LieSubmodule K L L).toSubmodule,
          ad_lin x y ∈ (SS : LieSubmodule K L L).toSubmodule :=
        fun _ hy => SS.lie_mem hy
      -- ad K ↥SS ⟨x, hx⟩ agrees with (ad_lin x).restrict on SS
      have h_eq : ad K ↥SS ⟨x, hx⟩ = (ad_lin x).restrict h_inv := by
        ext ⟨_, _⟩; rfl
      refine ⟨n, ?_⟩
      rw [h_eq, Module.End.pow_restrict n h_inv]
      ext ⟨y, hy⟩
      simp only [LinearMap.restrict_apply]
      exact LinearMap.congr_fun hn y
    -- Step 3: S is solvable
    have ss_solvable : IsSolvable ↥SS := inferInstance
    have s_solvable : IsSolvable ↥S := by
      obtain ⟨k, hk⟩ := (isSolvable_iff K ↥SS).mp ss_solvable
      rw [LieIdeal.derivedSeries_eq_bot_iff] at hk
      apply IsSolvable.mk (R := K) (k := k + 1)
      rw [LieIdeal.derivedSeries_eq_bot_iff, derivedSeriesOfIdeal_add,
        derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
      exact hk
    -- Step 4: S = ⊥ since L has trivial radical
    exact HasTrivialRadical.eq_bot_of_isSolvable S

end LieAlgebra
