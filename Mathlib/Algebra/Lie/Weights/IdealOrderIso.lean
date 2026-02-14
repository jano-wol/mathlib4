/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.IsSimple
public import Mathlib.Algebra.Lie.Weights.IdealDecomposition

/-! # Order Isomorphism: Lie Ideals and Invariant Root Submodules

This file defines the order isomorphism between Lie ideals of a Killing Lie algebra
and invariant root submodules of the associated root system.

The main construction is `lieIdealToInvtRootSubmodule`, which maps a Lie ideal `I` to
the submodule of `Dual K H` spanned by the roots whose root spaces lie in `I`.

The full order isomorphism `lieIdealOrderIso` shows that this mapping is bijective
and order-preserving, establishing a lattice isomorphism between these two structures.
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Root set of a Lie ideal -/

/-- The set of roots whose root space is contained in a given Lie ideal. -/
def lieIdealRootSet (I : LieIdeal K L) : Set H.root :=
  { α | (rootSpace H α.1).toSubmodule ≤ I.toSubmodule }

/-! ### Forward map: Lie ideal → invariant root submodule -/

/-- The submodule of `Dual K H` spanned by the roots associated to a Lie ideal.
This maps each root `α ∈ Φ_I` (where `g_α ⊆ I`) to its weight functional `α : H →ₗ[K] K`,
and takes their span. -/
def lieIdealToSubmodule (I : LieIdeal K L) : Submodule K (Dual K H) :=
  Submodule.span K ((↑) '' lieIdealRootSet (H := H) I)

/-! ### Weyl reflection invariance -/

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- If `g_α ⊆ I`, then the coroot submodule of `α` is contained in `I`.
This uses that `I` is a Lie ideal: brackets `⁅g_{-α}, g_α⁆ ⊆ I` since `g_α ⊆ I`. -/
lemma corootSubmodule_le_lieIdeal (I : LieIdeal K L) {α : Weight K H L}
    (hα : (rootSpace H α).toSubmodule ≤ I.toSubmodule) :
    (corootSubmodule α).toSubmodule ≤ I.toSubmodule := by
  intro x hx
  obtain ⟨h, hh, rfl⟩ := (LieSubmodule.mem_map _).mp hx
  rw [mem_corootSpace] at hh
  refine (Submodule.span_le.mpr ?_) hh
  rintro _ ⟨y, hy, _, -, rfl⟩
  exact lie_mem_left K L I y _ (hα hy)

/-- If `g_α ⊆ I` and `γ(coroot α) ≠ 0`, then `g_γ ⊆ I`.
Proof: `coroot α ∈ I` (from `corootSubmodule_le_lieIdeal`), and for `y ∈ g_γ`,
`[coroot α, y] = γ(coroot α) • y ∈ I`, so `y ∈ I`. -/
private lemma rootSpace_le_ideal_of_apply_coroot_ne_zero (I : LieIdeal K L)
    {α : Weight K H L} (hI : (rootSpace H α).toSubmodule ≤ I.toSubmodule)
    {γ : H → K} (hγ_ne : γ (coroot α) ≠ 0) :
    (rootSpace H γ).toSubmodule ≤ I.toSubmodule := by
  have h_coroot_I : (coroot α : L) ∈ I.toSubmodule := by
    apply corootSubmodule_le_lieIdeal I hI
    exact (LieSubmodule.mem_map _).mpr
      ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩
  intro y hy
  have h_lie : ⁅(coroot α : L), y⁆ ∈ I.toSubmodule :=
    lie_mem_left K L I (coroot α : L) y h_coroot_I
  have h_eq : ⁅(coroot α : L), y⁆ = γ ⟨coroot α, (coroot α).property⟩ • y :=
    lie_eq_smul_of_mem_rootSpace hy ⟨coroot α, (coroot α).property⟩
  rwa [h_eq, I.toSubmodule.smul_mem_iff (by exact_mod_cast hγ_ne)] at h_lie

/-- The root set of a Lie ideal is closed under Weyl reflections: if `g_α ⊆ I` and
`i` is any root, then `g_{s_i(α)} ⊆ I`.

The proof walks the `i`-chain through `α` by ℕ-induction. At each step, the nonzero
bracket `[g_i, g_{k•i+α}]` lands in the next root space which is 1-dimensional.
If the path passes through the zero weight (only when `α = ±i`), the coroot argument
is used instead: `coroot α ∈ I` and `γ(coroot α) ≠ 0` gives `g_γ ⊆ I`. -/
lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I := by
  simp only [lieIdealRootSet, Set.mem_setOf_eq] at hα ⊢
  by_cases hp : (rootSystem H).pairing α i = 0
  · rw [(rootSystem H).reflectionPerm_eq_of_pairing_eq_zero hp]; exact hα
  · -- pairing α i ≠ 0 implies pairing i α ≠ 0
    have hq : (rootSystem H).pairing i α ≠ 0 :=
      mt (rootSystem H).pairing_eq_zero_iff.mpr hp
    -- g_i ⊆ I: coroot α ∈ I and i(coroot α) = pairing i α ≠ 0
    have hi_in_I : (rootSpace H (i.1 : Weight K H L)).toSubmodule ≤ I.toSubmodule :=
      rootSpace_le_ideal_of_apply_coroot_ne_zero I hα hq
    -- pairing(s_i(α), i) = -pairing(α, i) ≠ 0
    have h_neg_p : (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i ≠ 0 := by
      rw [show (rootSystem H).pairing ((rootSystem H).reflectionPerm i α) i =
          -(rootSystem H).pairing α i from
        ((rootSystem H).pairing_reflectionPerm i α i).symm.trans
          ((rootSystem H).pairing_reflectionPerm_self_right α i)]
      exact neg_ne_zero.mpr hp
    -- g_{s_i(α)} ⊆ I: coroot i ∈ I and s_i(α)(coroot i) ≠ 0
    exact rootSpace_le_ideal_of_apply_coroot_ne_zero I hi_in_I h_neg_p

/-- The submodule spanned by roots of a Lie ideal is invariant under all root reflections. -/
lemma lieIdealToSubmodule_mem_invtRootSubmodule (I : LieIdeal K L) :
    lieIdealToSubmodule (H := H) I ∈ (rootSystem H).invtRootSubmodule := by
  rw [RootPairing.mem_invtRootSubmodule_iff]
  intro i
  rw [Module.End.mem_invtSubmodule]
  apply Submodule.span_le.mpr
  rintro _ ⟨α, hα, rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_comap]
  rw [show (↑((rootSystem H).reflection i) : Dual K H →ₗ[K] Dual K H)
    (Weight.toLinear K H L ↑α) = (rootSystem H).reflection i ((rootSystem H).root α) from rfl]
  rw [← (rootSystem H).root_reflectionPerm i α]
  exact Submodule.subset_span ⟨_, lieIdealRootSet_reflectionPerm_invariant I i hα, rfl⟩

/-- Maps a Lie ideal to its corresponding invariant root submodule. -/
def lieIdealToInvtRootSubmodule (I : LieIdeal K L) :
    (rootSystem H).invtRootSubmodule :=
  ⟨lieIdealToSubmodule (H := H) I, lieIdealToSubmodule_mem_invtRootSubmodule I⟩

/-! ### Monotonicity -/

/-- The forward map is monotone: if `I ≤ J` then the root set of `I` is contained in that of `J`,
hence the spanned submodule is smaller. -/
lemma lieIdealToInvtRootSubmodule_mono {I J : LieIdeal K L} (h : I ≤ J) :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J := by
  apply Submodule.span_mono
  apply Set.image_mono
  intro α (hα : (rootSpace H α.1).toSubmodule ≤ I.toSubmodule)
  exact hα.trans h

/-! ### Coroot span and I ∩ H -/

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- Coroot submodules of roots in the ideal's root set lie in the Cartan (they are images of H). -/
lemma corootSubmodule_le_cartan (α : Weight K H L) :
    (corootSubmodule α).toSubmodule ≤ H.toSubmodule :=
  LieSubmodule.map_incl_le

omit [CharZero K] [IsKilling K L] [IsTriangularizable K H L] in
/-- ⊇ direction: the coroot span of roots in `Φ_I` is contained in `I ∩ H`. -/
lemma coroot_span_le_inf_cartan (I : LieIdeal K L) :
    ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule ≤
      I.toSubmodule ⊓ H.toSubmodule :=
  iSup₂_le fun α hα ↦ le_inf (corootSubmodule_le_lieIdeal I hα) (corootSubmodule_le_cartan α.1)

/-- If `h ∈ I ∩ H` and `β` is a root with `g_β ⊄ I`, then `β(h) = 0`.
This is because `[h, g_β] = β(h) • g_β ⊆ I ∩ g_β`, and `I ∩ g_β = 0` since `g_β ⊄ I`
and `g_β` is 1-dimensional. -/
lemma weight_apply_eq_zero_of_not_mem_lieIdealRootSet (I : LieIdeal K L)
    {x : L} (hxI : x ∈ I.toSubmodule) (hxH : x ∈ H.toSubmodule)
    {β : Weight K H L} (hβ_not : ¬ (rootSpace H β).toSubmodule ≤ I.toSubmodule) :
    β ⟨x, hxH⟩ = 0 := by
  by_contra h
  apply hβ_not
  intro y hy
  have hsmul : β ⟨x, hxH⟩ • y ∈ I.toSubmodule := by
    rw [← lie_eq_smul_of_mem_rootSpace hy ⟨x, hxH⟩]
    exact lie_mem_left K L I x y hxI
  rwa [I.toSubmodule.smul_mem_iff (by exact_mod_cast h)] at hsmul

/-- The spans of coroots of nonzero weights generate `H` (as a submodule). -/
private lemma biSup_span_coroot_eq_top :
    ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), (K ∙ coroot α : Submodule K H) = ⊤ := by
  have h1 : (⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
      (corootSpace (⇑α) : LieIdeal K H)) = ⊤ := by simp
  have h2 : ∀ α : Weight K H L,
      (corootSpace (⇑α) : LieIdeal K H).toSubmodule = K ∙ coroot α :=
    coe_corootSpace_eq_span_singleton
  simp_rw [← h2, ← LieSubmodule.iSup_toSubmodule, h1, LieSubmodule.top_toSubmodule]

/-- An element of `H` that is trace-form orthogonal to all nonzero coroots is zero. -/
private lemma eq_zero_of_traceForm_coroot_eq_zero (h : H)
    (horth : ∀ α : Weight K H L, α.IsNonZero → traceForm K H L h (coroot α) = 0) :
    h = 0 := by
  have : (⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero),
      (K ∙ coroot α : Submodule K H)) ≤ LinearMap.ker (traceForm K H L h) := by
    apply iSup_le; intro α; apply iSup_le; intro hα
    apply Submodule.span_le.mpr
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
    exact horth α hα
  rw [biSup_span_coroot_eq_top] at this
  have hzero : traceForm K H L h = 0 := LinearMap.ker_eq_top.mp (eq_top_iff.mpr this)
  have hzero' : cartanEquivDual H h = 0 := by
    ext y; simp only [cartanEquivDual_apply_apply, LinearMap.zero_apply]
    exact DFunLike.congr_fun hzero y
  exact (cartanEquivDual H).injective (by rw [hzero', map_zero])

/-- For `α ∈ Φ_I` and nonzero `β ∉ Φ_I`, the coroots are trace-form orthogonal. -/
private lemma traceForm_coroot_eq_zero_of_ideal_complement (I : LieIdeal K L)
    {α : Weight K H L}
    (hαI : (rootSpace H α).toSubmodule ≤ I.toSubmodule)
    {β : Weight K H L} (_hβ_nz : β.IsNonZero)
    (hβI : ¬ (rootSpace H β).toSubmodule ≤ I.toSubmodule) :
    traceForm K H L (coroot α) (coroot β) = 0 := by
  apply traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := β)
  · -- coroot α ∈ β.ker: β(coroot α) = 0 since coroot α ∈ I ∩ H and g_β ⊄ I
    change (β : H → K) (coroot α) = 0
    have hmI : (coroot α : L) ∈ I.toSubmodule := by
      apply corootSubmodule_le_lieIdeal I hαI
      rw [LieSubmodule.mem_toSubmodule]
      exact (LieSubmodule.mem_map _).mpr
        ⟨⟨coroot α, (coroot α).property⟩, coroot_mem_corootSpace α, rfl⟩
    have hmH : (coroot α : L) ∈ H.toSubmodule := (coroot α).property
    exact weight_apply_eq_zero_of_not_mem_lieIdealRootSet I hmI hmH hβI
  · exact Submodule.mem_span_singleton_self _

/-- ⊆ direction: `I ∩ H` is contained in the coroot span of roots in `Φ_I`.

The proof uses trace form non-degeneracy. For `h ∈ I ∩ H`, we decompose `h = a + b` using the
coroot decomposition of `H`, where `a` is in the Φ_I-coroot span and `b` is in the complement
coroot span. Since `a ∈ I` (coroots of Φ_I are in I) and `h ∈ I`, we get `b ∈ I ∩ H`.
Then `β(b) = 0` for all `β ∉ Φ_I` forces `b` to be trace-form orthogonal to all complement
coroots. The orthogonality between ideal and complement coroots (from the same vanishing argument
applied to the coroots of Φ_I) gives trace-form orthogonality to all coroots. By non-degeneracy
of the trace form, `b = 0`, so `h = a` lies in the Φ_I-coroot span. -/
lemma inf_cartan_le_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule ≤
      ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule := by
  intro x hx
  obtain ⟨hxI, hxH⟩ := Submodule.mem_inf.mp hx
  -- Work in H: define the complement coroot span
  set h : H := ⟨x, hxH⟩
  set S_I : Submodule K H :=
    ⨆ α ∈ lieIdealRootSet (H := H) I, (K ∙ coroot (α.1 : Weight K H L))
  set S_c : Submodule K H :=
    ⨆ (β : Weight K H L) (_ : β.IsNonZero)
      (_ : ¬(rootSpace H β).toSubmodule ≤ I.toSubmodule), (K ∙ coroot β)
  -- Step 1: S_I ⊔ S_c = ⊤
  have h_sup : S_I ⊔ S_c = ⊤ := by
    rw [eq_top_iff, ← biSup_span_coroot_eq_top (K := K) (L := L) (H := H)]
    apply iSup_le; intro α; apply iSup_le; intro hα
    by_cases hαI : (rootSpace H α).toSubmodule ≤ I.toSubmodule
    · apply le_sup_of_le_left
      have hα_root : α ∈ H.root := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hα
      exact le_iSup₂_of_le ⟨α, hα_root⟩ hαI le_rfl
    · exact le_sup_of_le_right (le_iSup₂_of_le α hα (le_iSup_of_le hαI le_rfl))
  -- Step 2: Decompose h = a + b
  have hh_top : h ∈ (⊤ : Submodule K H) := Submodule.mem_top
  rw [← h_sup] at hh_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hh_top
  -- Step 3: a ∈ I (the ideal coroot span maps into I)
  have haI : (a : L) ∈ I.toSubmodule := by
    suffices hle : S_I ≤ Submodule.comap H.toSubmodule.subtype I.toSubmodule from hle ha
    apply iSup₂_le; intro α hα z hz
    rw [Submodule.mem_comap]
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp only [map_smul]
    apply I.toSubmodule.smul_mem
    apply corootSubmodule_le_lieIdeal I hα
    exact (LieSubmodule.mem_map _).mpr
      ⟨⟨coroot α.1, (coroot α.1).property⟩, coroot_mem_corootSpace α.1, rfl⟩
  -- Step 4: b ∈ I ∩ H
  have hbI : (b : L) ∈ I.toSubmodule := by
    have : (b : L) = x - (a : L) := by
      have h1 : (a : L) + (b : L) = x := congr_arg Subtype.val hab
      rw [← h1, add_sub_cancel_left]
    rw [this]; exact I.toSubmodule.sub_mem hxI haI
  -- Step 5: b is trace-form orthogonal to ALL nonzero coroots, hence b = 0
  have hb_zero : b = 0 := by
    apply eq_zero_of_traceForm_coroot_eq_zero
    intro μ hμ
    by_cases hμI : (rootSpace H μ).toSubmodule ≤ I.toSubmodule
    · -- μ ∈ Φ_I: use orthogonality of ideal coroots with complement coroot span
      rw [traceForm_comm]
      -- traceForm(coroot μ, b) = 0 since b ∈ S_c and coroot μ is orthogonal to S_c
      have hker : S_c ≤ LinearMap.ker (traceForm K H L (coroot μ)) := by
        apply iSup_le; intro γ; apply iSup_le; intro hγ_nz; apply iSup_le; intro hγI
        apply Submodule.span_le.mpr
        simp only [Set.singleton_subset_iff, SetLike.mem_coe, LinearMap.mem_ker]
        exact traceForm_coroot_eq_zero_of_ideal_complement I hμI hγ_nz hγI
      exact (LinearMap.mem_ker.mp (hker hb))
    · -- μ ∉ Φ_I: μ(b) = 0 since b ∈ I ∩ H
      apply traceForm_eq_zero_of_mem_ker_of_mem_span_coroot (α := μ)
      · change (μ : H → K) b = 0
        exact weight_apply_eq_zero_of_not_mem_lieIdealRootSet I hbI b.property hμI
      · exact Submodule.mem_span_singleton_self _
  -- Step 6: h = a ∈ S_I
  have hha : h = a := by rw [← hab, hb_zero, add_zero]
  -- Step 7: Transfer from H to L
  change x ∈ ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule
  rw [show x = (a : L) from by rw [← hha]]
  -- a ∈ S_I (in H) implies (a : L) ∈ ⨆ corootSubmodule (in L)
  suffices hle : S_I ≤ Submodule.comap H.toSubmodule.subtype
      (⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule) from hle ha
  apply iSup₂_le; intro α hα z hz
  rw [Submodule.mem_comap]
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp only [map_smul]
  apply Submodule.smul_mem
  apply (le_iSup₂_of_le α hα le_rfl : (corootSubmodule α.1).toSubmodule ≤ _)
  exact (LieSubmodule.mem_map _).mpr
    ⟨⟨coroot α.1, (coroot α.1).property⟩, coroot_mem_corootSpace α.1, rfl⟩

/-- The Cartan part `I ∩ H` is determined by the root set: it equals the span of the coroots
corresponding to roots in `Φ_I`. This is the key fact that makes the forward map injective. -/
lemma lieIdeal_inf_cartan_eq_coroot_span (I : LieIdeal K L) :
    I.toSubmodule ⊓ H.toSubmodule =
      ⨆ α ∈ lieIdealRootSet (H := H) I, (corootSubmodule α.1).toSubmodule :=
  le_antisymm (inf_cartan_le_coroot_span I) (coroot_span_le_inf_cartan I)

/-! ### Key lemma: span membership implies root set membership -/

omit [CharZero K] [IsTriangularizable K H L] in
/-- Symmetry of `cartanEquivDual`: `f(h_g) = g(h_f)` where `h_f = (cartanEquivDual H).symm f`.
This follows from the symmetry of the trace form. -/
private lemma cartanEquivDual_symm_comm (f g : Dual K H) :
    f ((cartanEquivDual H).symm g) = g ((cartanEquivDual H).symm f) := by
  conv_lhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) f]
  conv_rhs => rw [← LinearEquiv.apply_symm_apply (cartanEquivDual H) g]
  simp only [cartanEquivDual_apply_apply]
  exact LieModule.traceForm_comm K H L _ _

/-- If `α` is a root whose linear form lies in `lieIdealToSubmodule I`, then
`α ∈ lieIdealRootSet I` (i.e., the root space `g_α ⊆ I`).

The proof uses the symmetry of the trace form. For `α ∉ Φ_I`, the coroots of Φ_I lie in `I ∩ H`,
so `α` vanishes on them. By trace form symmetry, this implies that each generator `↑γ ∈ Φ_I`
vanishes at `(cartanEquivDual H).symm(↑α)`. Since `↑α` lies in their span, we get
`α((cartanEquivDual H).symm α) = 0`, contradicting `root_apply_cartanEquivDual_symm_ne_zero`. -/
private lemma mem_lieIdealRootSet_of_mem_lieIdealToSubmodule (I : LieIdeal K L)
    {α : H.root} (hα_span : (↑α : Dual K H) ∈ lieIdealToSubmodule (H := H) I) :
    α ∈ lieIdealRootSet (H := H) I := by
  by_contra hα_not
  simp only [lieIdealRootSet, Set.mem_setOf_eq] at hα_not
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  -- Step 1: α vanishes on coroot γ for each γ ∈ Φ_I (since coroot γ ∈ I ∩ H and α ∉ Φ_I)
  have h_vanish : ∀ γ ∈ lieIdealRootSet (H := H) I,
      (↑α : Weight K H L) (coroot (↑γ : Weight K H L)) = 0 := by
    intro γ hγ
    have h_coroot_I : (coroot (↑γ : Weight K H L) : L) ∈ I.toSubmodule := by
      apply corootSubmodule_le_lieIdeal I hγ
      exact (LieSubmodule.mem_map _).mpr
        ⟨⟨coroot (↑γ : Weight K H L), (coroot (↑γ : Weight K H L)).property⟩,
         coroot_mem_corootSpace (↑γ : Weight K H L), rfl⟩
    exact weight_apply_eq_zero_of_not_mem_lieIdealRootSet I h_coroot_I
      (coroot (↑γ : Weight K H L)).property hα_not
  -- Step 2: Each generator ↑γ of the span vanishes at (cartanEquivDual H).symm α,
  -- using trace form symmetry and the fact that (cartanEquivDual H).symm γ ∈ K ∙ coroot γ
  have h_span_le : lieIdealToSubmodule (H := H) I ≤
      LinearMap.ker (Module.Dual.eval K H ((cartanEquivDual H).symm (↑α : Dual K H))) := by
    rw [lieIdealToSubmodule]
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, Module.Dual.eval_apply]
    -- By trace form symmetry: γ(h_α) = α(h_γ)
    rw [cartanEquivDual_symm_comm]
    -- α(h_γ) = 0 since h_γ ∈ K ∙ coroot γ and α(coroot γ) = 0
    have h_mem := cartanEquivDual_symm_apply_mem_corootSpace (↑γ : Weight K H L)
    rw [← LieSubmodule.mem_toSubmodule, coe_corootSpace_eq_span_singleton] at h_mem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h_mem
    rw [← hc]
    change (↑(↑α : Weight K H L) : H →ₗ[K] K) (c • coroot (↑γ : Weight K H L)) = 0
    simp [h_vanish γ hγ]
  -- Step 3: Since ↑α ∈ the span, α(h_α) = 0, contradicting root_apply_cartanEquivDual_symm_ne_zero
  exact root_apply_cartanEquivDual_symm_ne_zero hα_nz
    (by simpa [Module.Dual.eval_apply] using LinearMap.mem_ker.mp (h_span_le hα_span))

/-- Variant with `Weight K H L` arguments: if a nonzero weight's linear functional
lies in `lieIdealToSubmodule I`, then its root space is contained in `I`. -/
private lemma rootSpace_le_ideal_of_mem_lieIdealToSubmodule (I : LieIdeal K L)
    {α : Weight K H L} (hα_nz : α.IsNonZero)
    (hα_span : Weight.toLinear K H L α ∈ lieIdealToSubmodule (H := H) I) :
    (rootSpace H α).toSubmodule ≤ I.toSubmodule :=
  mem_lieIdealRootSet_of_mem_lieIdealToSubmodule I
    (α := ⟨α, by simpa [LieSubalgebra.root] using hα_nz⟩) hα_span

/-- If `α` is a root in `lieIdealRootSet I`, then `sl2SubmoduleOfRoot(α) ≤ I`. -/
private lemma sl2SubmoduleOfRoot_le_ideal (I : LieIdeal K L) {α : Weight K H L}
    (hα_nz : α.IsNonZero)
    (hα : (rootSpace H α).toSubmodule ≤ I.toSubmodule) :
    (sl2SubmoduleOfRoot hα_nz).toSubmodule ≤ I.toSubmodule := by
  rw [sl2SubmoduleOfRoot_eq_sup]
  simp only [LieSubmodule.sup_toSubmodule]
  apply sup_le (sup_le hα ?_) (corootSubmodule_le_lieIdeal I hα)
  -- g_{-α} ≤ I: use coroot α ∈ I and (-α)(coroot α) = -2 ≠ 0
  apply rootSpace_le_ideal_of_apply_coroot_ne_zero I hα
  simp only [Pi.neg_apply, ne_eq, neg_eq_zero]
  exact_mod_cast root_apply_coroot hα_nz ▸ two_ne_zero

/-! ### Order isomorphism -/

lemma lieIdealOrderIso_left_inv (I : LieIdeal K L) :
    invtSubmoduleToLieIdeal (lieIdealToSubmodule (H := H) I)
      ((rootSystem H).mem_invtRootSubmodule_iff.mp
        (lieIdealToSubmodule_mem_invtRootSubmodule I)) = I := by
  rw [← LieSubmodule.toSubmodule_inj, coe_invtSubmoduleToLieIdeal_eq_iSup]
  refine le_antisymm ?_ ?_
  · -- ≤: each sl2(α) ≤ I
    rw [LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun ⟨α, hα_span, hα_nz⟩ ↦
      sl2SubmoduleOfRoot_le_ideal I hα_nz
        (rootSpace_le_ideal_of_mem_lieIdealToSubmodule I hα_nz hα_span)
  · -- ≥: I ≤ ⨆ sl2(α), using weight space decomposition directly
    rw [LieSubmodule.iSup_toSubmodule]
    conv_lhs => rw [lieIdeal_eq_inf_cartan_sup_biSup_inf_rootSpace (H := H) I,
                     lieIdeal_inf_cartan_eq_coroot_span I]
    apply sup_le
    · -- Coroot span ≤ ⨆ sl2(α): β ∈ lieIdealRootSet I directly
      apply iSup₂_le; intro β hβ
      have hβ_nz : (↑β : Weight K H L).IsNonZero := (Finset.mem_filter.mp β.property).2
      apply le_iSup_of_le ⟨(↑β : Weight K H L), Submodule.subset_span ⟨β, hβ, rfl⟩, hβ_nz⟩
      rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
      exact le_sup_right
    · -- ⨆ (α nonzero) I ∩ rootSpace α ≤ ⨆ sl2(α)
      apply iSup₂_le; intro α hα
      obtain h | h := rootSpace_le_or_disjoint I α hα
      · have hα_root : (⟨α, by simpa [LieSubalgebra.root] using hα⟩ : H.root) ∈
            lieIdealRootSet (H := H) I := h
        apply inf_le_right.trans
        apply le_iSup_of_le ⟨α, Submodule.subset_span ⟨_, hα_root, rfl⟩, hα⟩
        rw [LieSubmodule.toSubmodule_le_toSubmodule, sl2SubmoduleOfRoot_eq_sup]
        exact le_sup_of_le_left le_sup_left
      · simp [h]

private lemma invtSubmoduleToLieIdeal_mono {q₁ q₂ : Submodule K (Dual K H)}
    (hq₁ : ∀ i, q₁ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (hq₂ : ∀ i, q₂ ∈ End.invtSubmodule ((rootSystem H).reflection i).toLinearMap)
    (h : q₁ ≤ q₂) :
    invtSubmoduleToLieIdeal q₁ hq₁ ≤ invtSubmoduleToLieIdeal q₂ hq₂ := by
  rw [← LieSubmodule.toSubmodule_le_toSubmodule,
      coe_invtSubmoduleToLieIdeal_eq_iSup, coe_invtSubmoduleToLieIdeal_eq_iSup,
      LieSubmodule.iSup_toSubmodule, LieSubmodule.iSup_toSubmodule]
  exact iSup_le fun ⟨α, hα_mem, hα_nz⟩ ↦ le_iSup_of_le ⟨α, h hα_mem, hα_nz⟩ le_rfl

lemma lieIdealOrderIso_map_rel_iff {I J : LieIdeal K L} :
    lieIdealToInvtRootSubmodule (H := H) I ≤ lieIdealToInvtRootSubmodule J ↔ I ≤ J := by
  constructor
  · -- → direction: use left_inv + monotonicity of invtSubmoduleToLieIdeal
    intro h
    rw [← lieIdealOrderIso_left_inv (H := H) I, ← lieIdealOrderIso_left_inv (H := H) J]
    exact invtSubmoduleToLieIdeal_mono _ _ h
  · intro h; exact lieIdealToInvtRootSubmodule_mono h

/-- If `rootSpace α ≤ invtSubmoduleToLieIdeal q`, then `↑α ∈ q`.
Proof: if `↑α ∉ q`, then `(α : H → K) ≠ (β : H → K)` and `≠ -(β : H → K)` for all `β`
with `↑β ∈ q`. Since each sl₂(β) ≤ genWeightSpace β ⊔ genWeightSpace (-β) ⊔ genWeightSpace 0
and rootSpace α = genWeightSpace α, weight space independence gives
rootSpace α ⊓ sl₂(β) = ⊥ for each β. Then rootSpace α ⊓ I = ⊥, contradicting dim = 1. -/
private lemma mem_invtSubmodule_of_rootSpace_le_invtSubmoduleToLieIdeal
    (q : (rootSystem H).invtRootSubmodule)
    {α : H.root} (hα : (rootSpace H (↑α : Weight K H L)).toSubmodule ≤
      (invtSubmoduleToLieIdeal q.1
        ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)).toSubmodule) :
    (rootSystem H).root α ∈ (q : Submodule K (Dual K H)) := by
  by_contra hα_not
  set I := invtSubmoduleToLieIdeal q.1 ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  have hα_nz : (↑α : Weight K H L).IsNonZero := (Finset.mem_filter.mp α.property).2
  -- rootSpace α ⊓ I = ⊥ by weight space independence:
  -- I = ⨆ sl2(β), and rootSpace α ⊓ sl2(β) = ⊥ for each β since α ≠ ±β, 0
  have h_inter_bot : (rootSpace H (↑α : Weight K H L)).toSubmodule ⊓ I.toSubmodule = ⊥ := by
    rw [coe_invtSubmoduleToLieIdeal_eq_iSup, ← disjoint_iff, LieSubmodule.disjoint_toSubmodule]
    -- Use weight space independence indexed by H → K (avoids needing 0 : Weight)
    apply Disjoint.mono_right _ (iSupIndep_genWeightSpace K H L (↑(↑α : Weight K H L)))
    -- It suffices to show each sl₂(β) ≤ ⨆ φ ≠ ↑α, genWeightSpace φ
    apply iSup_le; intro ⟨β, hβ_mem, hβ_nz⟩
    -- β ≠ α (else α ∈ q), -β ≠ α (else -α ∈ q so α ∈ q), 0 ≠ α (since α nonzero)
    have hβ_ne : (β : H → K) ≠ ((↑α : Weight K H L) : H → K) := by
      intro heq; have h_eq := DFunLike.coe_injective heq; subst h_eq
      exact hα_not (by simpa [rootSystem_root_apply] using hβ_mem)
    have hnβ_ne : ((-β : Weight K H L) : H → K) ≠ ((↑α : Weight K H L) : H → K) := by
      intro heq; apply hα_not; rw [rootSystem_root_apply]
      have h_neg : Weight.toLinear K H L (-β) ∈ q.1 := by
        rw [Weight.toLinear_neg]; exact q.1.neg_mem hβ_mem
      rwa [show (-β : Weight K H L) = (↑α : Weight K H L) from DFunLike.coe_injective heq]
        at h_neg
    have h0_ne : (0 : H → K) ≠ ((↑α : Weight K H L) : H → K) := fun h => hα_nz h.symm
    rw [sl2SubmoduleOfRoot_eq_sup]
    apply sup_le (sup_le _ _) _
    · exact le_iSup₂_of_le (↑β : H → K) hβ_ne le_rfl
    · exact le_iSup₂_of_le (↑(-β : Weight K H L) : H → K) hnβ_ne le_rfl
    · exact (LieSubmodule.map_incl_le.trans (rootSpace_zero_eq K L H).symm.le).trans
        (le_iSup₂_of_le (0 : H → K) h0_ne le_rfl)
  -- But rootSpace α ≤ I, so rootSpace α = ⊥, contradicting nonzero weight
  rw [inf_eq_left.mpr hα] at h_inter_bot
  exact Weight.genWeightSpace_ne_bot L (↑α : Weight K H L)
    ((LieSubmodule.toSubmodule_eq_bot _).mp h_inter_bot)

/-- An invariant root submodule is spanned by the roots it contains.
The proof uses the block-diagonal structure of the pairing matrix:
if `P(i,j) = 0` for roots `i ∈ q` and `j ∉ q` (from invariance),
then `P(j,i) = 0` by `pairing_eq_zero_iff'`, so any element of `q`
decomposes as a sum of roots in `q` (the complement part vanishes
because it lies in the kernel of all `coroot'`). -/
private lemma invtSubmodule_le_span_roots (q : (rootSystem H).invtRootSubmodule) :
    (q : Submodule K (Dual K H)) ≤
      Submodule.span K ((rootSystem H).root ''
        {i | (rootSystem H).root i ∈ (q : Submodule K _)}) := by
  -- Key: coroot' ℓ vanishes on q when root ℓ ∉ q
  have hq_ker : ∀ ℓ, (rootSystem H).root ℓ ∉ (q : Submodule K _) →
      (q : Submodule K _) ≤ LinearMap.ker ((rootSystem H).coroot' ℓ) := by
    intro ℓ hℓ w hw
    rw [LinearMap.mem_ker]; by_contra h; apply hℓ
    have h_refl : ((rootSystem H).reflection ℓ) w ∈ (q : Submodule K _) :=
      (rootSystem H).mem_invtRootSubmodule_iff.mp q.property ℓ hw
    rw [(rootSystem H).reflection_apply] at h_refl
    have h_smul : ((rootSystem H).coroot' ℓ w) • (rootSystem H).root ℓ ∈
        (q : Submodule K _) := by
      have h_sub := sub_mem hw h_refl; rwa [sub_sub_cancel] at h_sub
    exact (Submodule.smul_mem_iff _ h).mp h_smul
  -- Abbreviations for the two spans
  set S := Submodule.span K ((rootSystem H).root ''
    {i | (rootSystem H).root i ∈ (q : Submodule K _)})
  set T := Submodule.span K ((rootSystem H).root ''
    {i | (rootSystem H).root i ∉ (q : Submodule K _)})
  -- coroot' ℓ vanishes on S when root ℓ ∉ q
  have hS_ker : ∀ ℓ, (rootSystem H).root ℓ ∉ (q : Submodule K _) →
      S ≤ LinearMap.ker ((rootSystem H).coroot' ℓ) := by
    intro ℓ hℓ; apply Submodule.span_le.mpr; rintro _ ⟨i, hi, rfl⟩
    exact hq_ker ℓ hℓ hi
  -- coroot' i vanishes on T when root i ∈ q (by pairing symmetry)
  have hT_ker : ∀ i, (rootSystem H).root i ∈ (q : Submodule K _) →
      T ≤ LinearMap.ker ((rootSystem H).coroot' i) := by
    intro i hi; apply Submodule.span_le.mpr; rintro _ ⟨j, hj, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, (rootSystem H).root_coroot'_eq_pairing]
    have h₁ := LinearMap.mem_ker.mp (hq_ker j hj hi)
    rw [(rootSystem H).root_coroot'_eq_pairing] at h₁
    exact (rootSystem H).pairing_eq_zero_iff'.mpr h₁
  -- S ⊔ T = ⊤
  have h_sup : S ⊔ T = ⊤ := by
    rw [← Submodule.span_union, ← Set.image_union]
    have : {i | (rootSystem H).root i ∈ (q : Submodule K _)} ∪
        {i | (rootSystem H).root i ∉ (q : Submodule K _)} = Set.univ := by
      ext; exact ⟨fun _ => trivial, fun _ => em _⟩
    rw [this, Set.image_univ]; simp
  -- Main: decompose v = s + t and show t = 0
  intro v hv
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp (h_sup ▸ Submodule.mem_top (x := v))
  suffices t = 0 by rw [this, add_zero]; exact hs
  have h_ker : ∀ ℓ, (rootSystem H).coroot' ℓ t = 0 := by
    intro ℓ; by_cases hℓ : (rootSystem H).root ℓ ∈ (q : Submodule K _)
    · exact LinearMap.mem_ker.mp (hT_ker ℓ hℓ ht)
    · have h1 := LinearMap.mem_ker.mp (hq_ker ℓ hℓ hv)
      have h2 := LinearMap.mem_ker.mp (hS_ker ℓ hℓ hs)
      rw [map_add, h2, zero_add] at h1; exact h1
  have : IsReflexive K (Dual K H) := .of_isPerfPair (rootSystem H).toLinearMap
  exact ((Module.Dual.eval K _).map_eq_zero_iff
    (bijective_dual_eval K _).injective).mp
    (LinearMap.ext_on_range (rootSystem H).span_coroot'_eq_top h_ker)

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
    · -- ≤: each root whose rootSpace ≤ g(q) is in q
      apply Submodule.span_le.mpr
      rintro _ ⟨α, hα, rfl⟩
      exact mem_invtSubmodule_of_rootSpace_le_invtSubmoduleToLieIdeal q hα
    · -- ≥: q ≤ span (by invtSubmodule_le_span_roots + set inclusion)
      apply (invtSubmodule_le_span_roots q).trans
      apply Submodule.span_mono; apply Set.image_mono
      intro i hi
      -- root i ∈ q and i.IsNonZero → rootSpace H ↑i ≤ invtSubmoduleToLieIdeal q
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
