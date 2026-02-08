/-
This file defines the forward direction of the order isomorphism between Lie ideals
of a Killing Lie algebra and invariant root submodules of the associated root system.

The main construction is `lieIdealToInvtRootSubmodule`, which maps a Lie ideal `I` to
the submodule of `Dual K H` spanned by the roots whose root spaces lie in `I`.

The full order isomorphism `lieIdealOrderIso` is sketched with sorry'd proofs.
-/

import Mathlib.Algebra.Lie.Weights.IsSimple

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule Module

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

noncomputable section

/-! ### Lie ideal decomposition (sorry'd; proved in Lemma1) -/

/-- A Lie ideal decomposes as its intersection with the Cartan subalgebra plus a direct sum of
root spaces corresponding to some subset Φ of roots. -/
lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := sorry

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

/-- In a root chain, bracketing with `g_β` maps `g_{k•β + α}` to a nonzero subspace of
`g_{(k+1)•β + α}` when `k` is strictly below the chain top. This is a consequence of the
irreducibility of the sl₂(β)-module structure on the chain.

Proof sketch: The chain `⨁_{-b ≤ k ≤ t} g_{k•β+α}` is an irreducible sl₂(β)-module because
each weight space is 1-dimensional and the weights form a consecutive string. The raising
operator (bracket with `e_β`) is therefore nonzero on all weight spaces except the highest. -/
lemma exists_bracket_ne_zero_of_lt_chainTopCoeff
    {α β : Weight K H L} (hβ : β.IsNonZero)
    {k : ℤ} (hk_bot : -k ≤ chainBotCoeff β α) (hk_top : k < chainTopCoeff β α) :
    ∃ x ∈ rootSpace H β, ∃ y ∈ rootSpace H (k • β + α),
      ⁅(x : L), (y : L)⁆ ≠ 0 := by
  -- Get sl₂ triple for β
  obtain ⟨_, e, f, isSl2, he, hf⟩ := exists_isSl2Triple_of_weight_isNonZero hβ
  obtain rfl := isSl2.h_eq_coroot hβ he hf
  -- Get primitive vector at chain top
  obtain ⟨v, hv, v_ne0⟩ := (chainTop β α).exists_ne_zero
  have prim : isSl2.HasPrimitiveVectorWith v (chainLength β α : K) :=
    have := lie_mem_genWeightSpace_of_mem_genWeightSpace he hv
    ⟨v_ne0, (chainLength_smul _ _ hv).symm, by rwa [genWeightSpace_add_chainTop _ _ hβ] at this⟩
  -- Define chain index n = chainTopCoeff β α - k (as ℕ)
  have h_pos : (0 : ℤ) < chainTopCoeff β α - k := by omega
  set n := (chainTopCoeff β α - k).toNat with hn_def
  have hn : (n : ℤ) = chainTopCoeff β α - k := Int.toNat_of_nonneg h_pos.le
  -- f^n v is in the root space g_{k•β+α}
  have hfnv_mem : ((toEnd K L L f) ^ n) v ∈
      genWeightSpace L (k • (β : H → K) + (α : H → K)) := by
    have h1 := toEnd_pow_apply_mem hf hv n
    suffices n • (-(β : H → K)) + (chainTop (β : H → K) α : H → K) =
        k • (β : H → K) + (α : H → K) by rwa [this] at h1
    rw [← Nat.cast_smul_eq_nsmul ℤ, smul_neg, coe_chainTop]
    have hk : ((chainTopCoeff (β : H → K) α : ℤ) - (n : ℤ) : ℤ) = k := by omega
    -- rw [show -(↑n • (β : H → K)) + (↑(chainTopCoeff (β : H → K) α) • (β : H → K) + (α : H → K)) =
    --    ((↑(chainTopCoeff (β : H → K) α) - ↑n) • (β : H → K) + (α : H → K)) from by
    --  rw [← sub_smul]; ring_nf, hk]
    -- Substitute $n = (chainTopCoeff β α) - k$ into the expression and simplify.
    rw [hn]
    simp [sub_eq_add_neg];
    grind
  -- f^n v is nonzero
  have hn_le : n ≤ chainLength β α := by
    suffices (n : ℤ) ≤ chainLength β α by exact Int.le_of_ofNat_le_ofNat this
    rw [← chainBotCoeff_add_chainTopCoeff]; push_cast; omega
  have hfnv_ne : ((toEnd K L L f) ^ n) v ≠ 0 :=
    prim.pow_toEnd_f_ne_zero_of_eq_nat rfl hn_le
  -- n ≥ 1 so we can apply lie_e_pow_succ_toEnd_f
  have hn_pos : 0 < n := by omega
  clear_value n
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨e, he, _, hfnv_mem, ?_⟩
  rw [prim.lie_e_pow_succ_toEnd_f m]
  refine smul_ne_zero ?_ (prim.pow_toEnd_f_ne_zero_of_eq_nat rfl (by omega))
  apply mul_ne_zero
  · exact_mod_cast (show (m + 1 : ℕ) ≠ 0 by omega)
  · rw [sub_ne_zero]
    exact_mod_cast (show (chainLength β α : ℤ) ≠ (m : ℤ) by
      rw [← chainBotCoeff_add_chainTopCoeff]; push_cast; omega)

/-- In a root chain, bracketing with `g_{-β}` maps `g_{k•β + α}` to a nonzero subspace of
`g_{(k-1)•β + α}` when `k` is strictly above the chain bottom.

Proof sketch: Same as `exists_bracket_ne_zero_of_lt_chainTopCoeff`, using the lowering
operator `f_{-β}` in place of the raising operator. -/
lemma exists_bracket_ne_zero_of_neg_lt_chainBotCoeff
    {α β : Weight K H L} (hβ : β.IsNonZero)
    {k : ℤ} (hk_top : k ≤ chainTopCoeff β α) (hk_bot : -k < chainBotCoeff β α) :
    ∃ x ∈ rootSpace H (-β), ∃ y ∈ rootSpace H (k • β + α),
      ⁅(x : L), (y : L)⁆ ≠ 0 :=
  sorry

/-- The root set of a Lie ideal is closed under Weyl reflections: if `g_α ⊆ I` and `i` is any
root, then `g_{s_i(α)} ⊆ I`.

Proof sketch: The reflected root `s_i(α) = α + m•i` (where `m = chainTopCoeff i α -
chainBotCoeff i α`) lies in the i-chain through α. We show all chain members are in `I`
by induction: starting from `g_α ⊆ I` (given), each step uses:
1. `[g_i, g_{k•i+α}] ⊆ g_{(k+1)•i+α}` (weight space product) and `⊆ I` (ideal property)
2. `[g_i, g_{k•i+α}] ≠ 0` (`exists_bracket_ne_zero_of_lt_chainTopCoeff`)
3. `g_{(k+1)•i+α}` is 1-dimensional (`finrank_rootSpace_eq_one`)
Together these give `g_{(k+1)•i+α} ⊆ I`. The downward direction uses `g_{-i}` analogously. -/
lemma lieIdealRootSet_reflectionPerm_invariant (I : LieIdeal K L) (i : H.root)
    {α : H.root} (hα : α ∈ lieIdealRootSet (H := H) I) :
    (rootSystem H).reflectionPerm i α ∈ lieIdealRootSet (H := H) I :=
  sorry

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

/-! ### Order isomorphism -/

/-- The lattice of Lie ideals of a Killing Lie algebra is order-isomorphic to the lattice of
invariant root submodules of the associated root system. -/
def lieIdealOrderIso :
    LieIdeal K L ≃o (rootSystem H).invtRootSubmodule where
  toFun := lieIdealToInvtRootSubmodule
  invFun q := invtSubmoduleToLieIdeal q.1
    ((rootSystem H).mem_invtRootSubmodule_iff.mp q.2)
  left_inv := sorry
  right_inv := sorry
  map_rel_iff' := sorry

end

end LieAlgebra.IsKilling
