/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.Algebra.Lie.Weights.IdealDecomposition
public import Mathlib.LinearAlgebra.RootSystem.Irreducible

/-! # Order Isomorphism: Lie Ideals and Invariant Root Submodules

This file establishes an order isomorphism between the lattice of Lie ideals of a Killing
Lie algebra and the lattice of invariant root submodules of the associated root system.

## Main definitions

* `LieAlgebra.IsKilling.lieIdealRootSet`: the set of roots whose root space is contained in a
  given Lie ideal.
* `LieAlgebra.IsKilling.lieIdealToInvtRootSubmodule`: maps a Lie ideal to its corresponding
  invariant root submodule by taking the span of the roots in `lieIdealRootSet`.
* `LieAlgebra.IsKilling.lieIdealOrderIso`: the order isomorphism between Lie ideals and
  invariant root submodules.

## Main results

* `LieAlgebra.IsKilling.lieIdeal_inf_cartan_eq_coroot_span`: the Cartan part `I ⊓ H` of a Lie
  ideal equals the span of the coroots corresponding to roots in `lieIdealRootSet I`.
* `LieAlgebra.IsKilling.lieIdealRootSet_reflectionPerm_invariant`: the root set of a Lie ideal
  is closed under Weyl reflections.

## Tags

Lie algebra, Killing, root system, ideal, order isomorphism
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Forward map: Lie ideal → invariant root submodule -/

/-- The set of roots whose root space is contained in a given Lie ideal. -/
def lieIdealRootSet (I : LieIdeal K L) : Set H.root :=
  { α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal. -/
def lieIdealToSubmodule (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((↑) '' lieIdealRootSet (H := H) I)

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- If the root space of `α` is contained in a Lie ideal `I`, then the coroot submodule of `α`
is also contained in `I`. -/
lemma corootSubmodule_le_lieIdeal (I : LieIdeal K L) {α : Weight K H L}
    (hα : (rootSpace H α).toSubmodule ≤ I.toSubmodule) :
    (corootSubmodule α).toSubmodule ≤ I.toSubmodule := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  rw [mem_corootSpace] at hh
  refine (Submodule.span_le.mpr ?_) hh
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/-- If the root space of `α` is contained in a Lie ideal `I` and `γ(coroot α) ≠ 0` for
some weight `γ`, then the root space of `γ` is also contained in `I`. -/
lemma rootSpace_le_ideal_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hI : (rootSpace H α).toSubmodule ≤ I.toSubmodule)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    (rootSpace H γ).toSubmodule ≤ I.toSubmodule := by
  have h_coroot_I : (coroot α : L) ∈ I.toSubmodule :=
    corootSubmodule_le_lieIdeal I hI (coroot_mem_corootSubmodule α)
  intro y hy
  have h_lie : ⁅(coroot α : L), y⁆ ∈ I.toSubmodule :=
    lie_mem_left K L I (coroot α : L) y h_coroot_I
  have h_eq : ⁅(coroot α : L), y⁆ = γ ⟨coroot α, (coroot α).property⟩ • y :=
    lie_eq_smul_of_mem_rootSpace hy ⟨coroot α, (coroot α).property⟩
  rwa [h_eq, I.toSubmodule.smul_mem_iff (by exact_mod_cast hγ_ne)] at h_lie

/-- The root set of a Lie ideal is closed under Weyl reflections. -/
lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I := by
  simp only [lieIdealRootSet, Set.mem_setOf_eq] at hα ⊢
  by_cases hp : (rootSystem H).pairing α i = 0
  · rwa [(rootSystem H).reflectionPerm_eq_of_pairing_eq_zero hp]
  · have hi := rootSpace_le_ideal_of_apply_coroot_ne_zero I hα
      (mt (rootSystem H).pairing_eq_zero_iff.mpr hp)
    have h_neg : (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i ≠ 0 := by
      rw [show (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i =
          -(rootSystem H).pairing α i from
        ((rootSystem H).pairing_reflectionPerm i α i).symm.trans
          ((rootSystem H).pairing_reflectionPerm_self_right α i)]
      exact neg_ne_zero.mpr hp
    exact rootSpace_le_ideal_of_apply_coroot_ne_zero I hi h_neg

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealToSubmodule_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealToSubmodule (H := H) I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro i; rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, hα, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [show (↑((rootSystem H).reflection i) : Dual K H →ₗ[K] Dual K H)
      (Weight.toLinear K H L ↑α) = (rootSystem H).reflection i ((rootSystem H).root α) from rfl,
    ← (rootSystem H).root_reflectionPerm i α]
  exact Submodule.subset_span ⟨_, lieIdealRootSet_reflectionPerm_invariant I i hα, rfl⟩

/-- Maps a Lie ideal to its corresponding invariant root submodule. -/
def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealToSubmodule (H := H) I, lieIdealToSubmodule_mem_invtRootSubmodule I⟩

/-- The forward map `lieIdealToInvtRootSubmodule` is monotone. -/
lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J :=
  Submodule.span_mono (Set.image_mono
    fun α (hα : (rootSpace H α.1).toSubmodule ≤ I.toSubmodule) ↦ hα.trans h)

/-! ### Ideal-Cartan intersection -/

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- Coroot submodules lie in the Cartan subalgebra. -/
lemma corootSubmodule_le_cartan (α : Weight K H L) :
    (corootSubmodule α).toSubmodule ≤ H.toSubmodule :=
  LieSubmodule.map_incl_le

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- The coroot span of roots in `lieIdealRootSet I` is contained in `I ⊓ H`. -/
lemma coroot_span_le_inf_cartan (I : LieIdeal K L) :
    ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule ≤
      I.toSubmodule ⊓ H.toSubmodule :=
  iSup₂_le fun α hα ↦ le_inf (corootSubmodule_le_lieIdeal I hα) (corootSubmodule_le_cartan α.1)

/-- If `x ∈ I ∩ H` and the root space of `β` is not contained in `I`, then `β(x) = 0`. -/
lemma weight_apply_eq_zero_of_not_mem_lieIdealRootSet (I : LieIdeal K L)
    {x : L} (hxI : x ∈ I.toSubmodule) (hxH : x ∈ H.toSubmodule)
    {β : Weight K H L} (hβ_not : ¬ (rootSpace H β).toSubmodule ≤ I.toSubmodule) :
    β ⟨x, hxH⟩ = 0 := by
  by_contra h; apply hβ_not; intro y hy
  have hsmul : β ⟨x, hxH⟩ • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy ⟨x, hxH⟩]
    exact lie_mem_left K L I x y hxI
  rwa [I.toSubmodule.smul_mem_iff (by exact_mod_cast h)] at hsmul

private lemma biSup_span_coroot_eq_top :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), (K ∙ coroot α : Submodule K H) = ⊤ := by
  have h1 : (⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
      (corootSpace (⇑α) : LieIdeal K H)) = ⊤ := by simp
  simp_rw [← coe_corootSpace_eq_span_singleton, ← LieSubmodule.iSup_toSubmodule, h1,
    LieSubmodule.top_toSubmodule]

private lemma eq_zero_of_traceForm_coroot_eq_zero (h : H)
    (horth : ∀ α : Weight K H L, α.IsNonZero → traceForm K H L h (coroot α) = 0) :
    h = 0 := by
  have hker : ⊤ ≤ LinearMap.ker (traceForm K H L h) := by
    rw [← biSup_span_coroot_eq_top (K := K) (L := L) (H := H)]
    exact iSup₂_le fun α hα ↦ Submodule.span_le.mpr <| by
      simp [Set.singleton_subset_iff, LinearMap.mem_ker, horth α hα]
  have hzero := LinearMap.ker_eq_top.mp (eq_top_iff.mpr hker)
  have hzero' : cartanEquivDual H h = 0 := by
    ext y; simp only [cartanEquivDual_apply_apply, LinearMap.zero_apply]
    exact DFunLike.congr_fun hzero y
  exact (cartanEquivDual H).injective (by rw [hzero', map_zero])

private lemma traceForm_coroot_eq_zero_of_ideal_complement (I : LieIdeal K L)
    {α : Weight K H L} (hαI : (rootSpace H α).toSubmodule ≤ I.toSubmodule)
    {β : Weight K H L} (_hβ_nz : β.IsNonZero)
    (hβI : ¬ (rootSpace H β).toSubmodule ≤ I.toSubmodule) :
    traceForm K H L (coroot α) (coroot β) = 0 := by
  refine traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := β) ?_
    (Submodule.mem_span_singleton_self _)
  change (β : H → K) (coroot α) = 0
  exact weight_apply_eq_zero_of_not_mem_lieIdealRootSet I
    (corootSubmodule_le_lieIdeal I hαI (coroot_mem_corootSubmodule α))
    (coroot α).property hβI

/-- `I ⊓ H` is contained in the coroot span of roots in `lieIdealRootSet I`. -/
lemma inf_cartan_le_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule ≤
      ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule := by
  intro x hx
  obtain ⟨hxI, hxH⟩ := Submodule.mem_inf.mp hx
  set h : H := ⟨x, hxH⟩
  set S_I : Submodule K H :=
    ⨆ α ∈ lieIdealRootSet (H := H) I, (K ∙ coroot (α.1 : Weight K H L))
  set S_c : Submodule K H :=
    ⨆ (β : Weight K H L) (_ : β.IsNonZero)
      (_ : ¬(rootSpace H β).toSubmodule ≤ I.toSubmodule), (K ∙ coroot β)
  have h_sup : S_I ⊔ S_c = ⊤ := by
    rw [eq_top_iff, ← biSup_span_coroot_eq_top (K := K) (L := L) (H := H)]
    exact iSup₂_le fun α hα ↦ by
      by_cases hαI : (rootSpace H α).toSubmodule ≤ I.toSubmodule
      · exact le_sup_of_le_left
          (le_iSup₂_of_le ⟨α, by simpa [Finset.mem_filter] using hα⟩ hαI le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le α hα (le_iSup_of_le hαI le_rfl))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp (h_sup ▸ Submodule.mem_top (x := h))
  have haI : (a : L) ∈ I.toSubmodule := by
    suffices hle : S_I ≤ Submodule.comap H.toSubmodule.subtype I.toSubmodule from hle ha
    exact iSup₂_le fun α hα z hz ↦ by
      rw [Submodule.mem_comap]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
      simp only [map_smul]
      exact I.toSubmodule.smul_mem _ (corootSubmodule_le_lieIdeal I hα
        (coroot_mem_corootSubmodule α.1))
  have hbI : (b : L) ∈ I.toSubmodule := by
    have : (b : L) = x - (a : L) := by
      have h1 : (a : L) + (b : L) = x := congr_arg Subtype.val hab
      rw [← h1, add_sub_cancel_left]
    rw [this]; exact I.toSubmodule.sub_mem hxI haI
  have hb_zero : b = 0 := by
    apply eq_zero_of_traceForm_coroot_eq_zero
    intro μ hμ
    by_cases hμI : (rootSpace H μ).toSubmodule ≤ I.toSubmodule
    · rw [traceForm_comm]
      exact LinearMap.mem_ker.mp ((iSup_le fun γ ↦ iSup_le fun hγ_nz ↦ iSup_le fun hγI ↦
        Submodule.span_le.mpr <| by
          simp [Set.singleton_subset_iff, LinearMap.mem_ker,
            traceForm_coroot_eq_zero_of_ideal_complement I hμI hγ_nz hγI]) hb)
    · exact traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := μ)
        (show (μ : H → K) b = 0 from
          weight_apply_eq_zero_of_not_mem_lieIdealRootSet I hbI b.property hμI)
        (Submodule.mem_span_singleton_self _)
  have hha : h = a := by rw [← hab, hb_zero, add_zero]
  change x ∈ ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule
  rw [show x = (a : L) from by rw [← hha]]
  suffices hle : S_I ≤ Submodule.comap H.toSubmodule.subtype
      (⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule) from hle ha
  exact iSup₂_le fun α hα z hz ↦ by
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [map_smul]
    exact Submodule.smul_mem _ _
      ((le_iSup₂_of_le α hα le_rfl : (corootSubmodule α.1).toSubmodule ≤ _)
        (coroot_mem_corootSubmodule α.1))

/-- The Cartan part `I ∩ H` equals the span of coroots corresponding to roots in
`lieIdealRootSet I`. -/
lemma lieIdeal_inf_cartan_eq_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule =
      ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule :=
  le_antisymm (inf_cartan_le_coroot_span I) (coroot_span_le_inf_cartan I)

/-! ### Order isomorphism -/

omit [CharZero K] [IsTriangularizable K H L] in
/-- Symmetry of `cartanEquivDual`: `f(h_g) = g(h_f)` where
`h_f = (cartanEquivDual H).symm f`. -/
lemma cartanEquivDual_symm_comm (f g : Dual K H) :
    f ((cartanEquivDual H).symm g) = g ((cartanEquivDual H).symm f) := by
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) f]
  conv_rhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) g]
  simp only [cartanEquivDual_apply_apply]
  exact LieModule.traceForm_comm K H L _ _

/-- If a root's linear form lies in `lieIdealToSubmodule I`, then the root belongs to
`lieIdealRootSet I`. -/
lemma mem_lieIdealRootSet_of_mem_lieIdealToSubmodule (I : LieIdeal K L)
    {α : H.root} (hα_span : (↑α : Dual K H) ∈ lieIdealToSubmodule (H := H) I) :
    α ∈ lieIdealRootSet (H := H) I := by
  by_contra hα_not
  simp only [lieIdealRootSet, Set.mem_setOf_eq] at hα_not
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  have h_vanish : ∀ γ ∈ lieIdealRootSet (H := H) I,
      (↑α : Weight K H L) (coroot (↑γ : Weight K H L)) = 0 := fun γ hγ ↦
    weight_apply_eq_zero_of_not_mem_lieIdealRootSet I
      (corootSubmodule_le_lieIdeal I hγ (coroot_mem_corootSubmodule (↑γ : Weight K H L)))
      (coroot (↑γ : Weight K H L)).property hα_not
  have h_span_le : lieIdealToSubmodule (H := H) I ≤
      LinearMap.ker (Module.Dual.eval K H ((cartanEquivDual H).symm (↑α : Dual K H))) := by
    rw [lieIdealToSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    rw [cartanEquivDual_symm_comm]
    have h_mem := cartanEquivDual_symm_apply_mem_corootSpace (↑γ : Weight K H L)
    rw [← LieSubmodule.mem_toSubmodule, coe_corootSpace_eq_span_singleton] at h_mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h_mem
    rw [← hc]
    change (↑(↑α : Weight K H L) : H →ₗ[K] K) (c • coroot (↑γ : Weight K H L)) = 0
    simp [h_vanish γ hγ]
  exact root_apply_cartanEquivDual_symm_ne_zero hα_nz
    (by simpa [Module.Dual.eval_apply] using LinearMap.mem_ker.mp (h_span_le hα_span))

private lemma rootSpace_le_ideal_of_mem_lieIdealToSubmodule (I : LieIdeal K L)
    {α : Weight K H L} (hα_nz : α.IsNonZero)
    (hα_span : Weight.toLinear K H L α ∈ lieIdealToSubmodule (H := H) I) :
    (rootSpace H α).toSubmodule ≤ I.toSubmodule :=
  mem_lieIdealRootSet_of_mem_lieIdealToSubmodule I
    (α := ⟨α, by simpa [LieSubalgebra.root] using hα_nz⟩) hα_span

/-- If the root space of a nonzero weight `α` is contained in a Lie ideal `I`, then the full
`sl₂` subalgebra `g_α ⊕ g_{-α} ⊕ [g_{-α}, g_α]` is contained in `I`. -/
lemma sl2SubmoduleOfRoot_le_ideal (I : LieIdeal K L) {α : Weight K H L}
    (hα_nz : α.IsNonZero)
    (hα : (rootSpace H α).toSubmodule ≤ I.toSubmodule) :
    (sl2SubmoduleOfRoot hα_nz).toSubmodule ≤ I.toSubmodule := by
  rw [sl2SubmoduleOfRoot_eq_sup]; simp only [LieSubmodule.sup_toSubmodule]
  refine sup_le (sup_le hα (rootSpace_le_ideal_of_apply_coroot_ne_zero I hα ?_))
    (corootSubmodule_le_lieIdeal I hα)
  simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
  exact_mod_cast root_apply_coroot hα_nz ▸ two_ne_zero

/-- The left inverse property: applying `invtSubmoduleToLieIdeal` after
`lieIdealToSubmodule` recovers the original ideal. -/
lemma lieIdealOrderIso_left_inv (I : LieIdeal K L) :
    invtSubmoduleToLieIdeal (lieIdealToSubmodule (H := H) I)
      ((rootSystem H).mem_invtRootSubmodule_iff.mp
        (lieIdealToSubmodule_mem_invtRootSubmodule I)) = I := by
  rw [← LieSubmodule.toSubmodule_inj, coe_invtSubmoduleToLieIdeal_eq_iSup]
  refine le_antisymm ?_ ?_
  · rw [LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun ⟨α, hα_span, hα_nz⟩ ↦
      sl2SubmoduleOfRoot_le_ideal I hα_nz
        (rootSpace_le_ideal_of_mem_lieIdealToSubmodule I hα_nz hα_span)
  · rw [LieSubmodule.iSup_toSubmodule]
    conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (H := H) I,
                     lieIdeal_inf_cartan_eq_coroot_span I]
    apply sup_le
    · exact iSup₂_le fun β hβ ↦ by
        have hβ_nz : (↑β : Weight K H L).IsNonZero := (Finset.mem_filter.mp β.property).2
        exact (le_iSup_of_le
          ⟨(↑β : Weight K H L), Submodule.subset_span ⟨β, hβ, rfl⟩, hβ_nz⟩
          (by rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
              exact le_sup_right))
    · exact iSup₂_le fun α hα ↦ by
        obtain h | h := rootSpace_le_or_disjoint I α hα
        · exact inf_le_right.trans
            (le_iSup_of_le ⟨α, Submodule.subset_span
              ⟨⟨α, by simpa [LieSubalgebra.root] using hα⟩, h, rfl⟩, hα⟩
              (by rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
                  exact le_sup_of_le_left le_sup_left))
        · simp [h]

/-- The backward map `invtSubmoduleToLieIdeal` is monotone. -/
lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule,
      coe_invtSubmoduleToLieIdeal_eq_iSup, coe_invtSubmoduleToLieIdeal_eq_iSup,
      LieSubmodule.iSup_toSubmodule, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

/-- The forward map reflects the ordering. -/
lemma lieIdealOrderIso_map_rel_iff {I J : LieIdeal K L} :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J ↔ I ≤ J :=
  ⟨fun h ↦ by rw [← lieIdealOrderIso_left_inv (H := H) I,
      ← lieIdealOrderIso_left_inv (H := H) J]; exact invtSubmoduleToLieIdeal_mono _ _ h,
   lieIdealToInvtRootSubmodule_mono⟩

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

/-- The lattice of Lie ideals of a Killing Lie algebra is order-isomorphic to the lattice of
invariant root submodules of the associated root system. -/
def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := lieIdealToInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1
    ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv I := lieIdealOrderIso_left_inv I
  right_inv := by
    intro q
    apply Subtype.ext
    simp only [lieIdealToInvtRootSubmodule, lieIdealToSubmodule, lieIdealRootSet]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨α, hα, rfl⟩
      exact mem_invtSubmodule_of_rootSpace_le_invtSubmoduleToLieIdeal q hα
    · apply (RootPairing.invtRootSubmodule.le_span_root q).trans
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
