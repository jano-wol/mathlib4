/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield, Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.RingTheory.Finiteness.Nilpotent
public import Mathlib.Algebra.Lie.Rank
public import Mathlib.Algebra.Lie.Engel
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Basis.Flag
public import Mathlib.LinearAlgebra.Matrix.Triangular
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Lie's theorem for Solvable Lie algebras.

Lie's theorem asserts that Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.
This result is named `LieModule.exists_forall_lie_eq_smul_of_isSolvable`.

This file also provides complete flag and basis forms of Lie's and Engel's theorems.
For Engel's theorem, `LieModule.exists_flag_of_isNilpotent` constructs a flag that every action
lowers by one step, and `LieModule.isNilpotent_iff_exists_basis_isStrictlyUpperTriangular`
characterizes nilpotent representations by simultaneous strictly upper triangular matrices.
-/

@[expose] public section

/-- Rank-nullity for the restriction of a linear map to a subspace. -/
theorem LinearMap.finrank_map_add_finrank_inf_ker
    {k V W : Type*} [DivisionRing k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W]
    (f : V →ₗ[k] W) (p : Submodule k V) [FiniteDimensional k p] :
    Module.finrank k (p.map f) + Module.finrank k (p ⊓ f.ker : Submodule k V) =
      Module.finrank k p := by
  have h := (f.domRestrict p).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  rw [← Submodule.finrank_map_subtype_eq p (f.ker.comap p.subtype),
    Submodule.map_comap_subtype] at h
  exact h

/-- The preimage of a subspace under a surjective linear map has dimension equal to
its dimension plus the dimension of the kernel. -/
theorem LinearMap.finrank_comap_of_surjective
    {k V W : Type*} [DivisionRing k] [AddCommGroup V] [AddCommGroup W]
    [Module k V] [Module k W] [FiniteDimensional k V]
    (f : V →ₗ[k] W) (hf : Function.Surjective f) (p : Submodule k W) :
    Module.finrank k (p.comap f) =
      Module.finrank k p + Module.finrank k f.ker := by
  have hker : f.ker ≤ p.comap f := by
    intro x hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker.mp hx]
    exact p.zero_mem
  have h := f.finrank_map_add_finrank_inf_ker (p.comap f)
  rw [Submodule.map_comap_eq_of_surjective hf, inf_eq_right.mpr hker] at h
  exact h.symm

open Module (Basis finrank)


/-- A complete flag admits a basis whose initial spans are the prescribed subspaces. -/
theorem exists_basis_adapted_to_flag
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (F : Fin (finrank k V + 1) → Submodule k V)
    (hmono : Monotone F) (hdim : ∀ i, finrank k (F i) = i.val) :
    ∃ b : Basis (Fin (finrank k V)) k V, ∀ i, b.flag i = F i := by
  classical
  let n := finrank k V
  have hex (i : Fin n) : ∃ v : V, v ∈ F i.succ ∧ v ∉ F i.castSucc := by
    have hnot : ¬ F i.succ ≤ F i.castSucc := by
      intro h
      have hh := Submodule.finrank_mono h
      rw [hdim, hdim] at hh
      simp at hh
    exact IsConcreteLE.not_le_iff_exists.mp hnot
  choose v hv using hex
  have hli : ∀ m (hm : m ≤ n), LinearIndependent k (fun i : Fin m => v (i.castLE hm)) := by
    intro m
    induction m with
    | zero => intro hm; exact linearIndependent_empty_type
    | succ m ih =>
      intro hm
      have hm' : m ≤ n := Nat.le_trans (Nat.le_succ m) hm
      let j : Fin n := ⟨m, Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hm⟩
      have hspan : Submodule.span k (Set.range (fun i : Fin m => v (i.castLE hm'))) ≤
          F j.castSucc := by
        apply Submodule.span_le.mpr
        rintro _ ⟨i, rfl⟩
        exact hmono (by change i.val + 1 ≤ m; omega) (hv (i.castLE hm')).1
      have hnew : v j ∉ Submodule.span k (Set.range (fun i : Fin m => v (i.castLE hm'))) :=
        fun h => (hv j).2 (hspan h)
      have hh := (ih hm').finSnoc hnew
      convert hh using 1
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
        exact congrArg v (Fin.ext rfl)
      · simp
  have hi : LinearIndependent k v := by simpa using hli n le_rfl
  have htop : Submodule.span k (Set.range v) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [n] using finrank_span_eq_card hi
  let b : Basis (Fin n) k V := Basis.mk hi (by rw [htop])
  refine ⟨b, ?_⟩
  intro i
  have hm : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have heq : b.flag i = Submodule.span k (Set.range (fun j : Fin i.val => v (j.castLE hm))) := by
    unfold Basis.flag
    apply congrArg (Submodule.span k)
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j.val, hj⟩, by simp [b]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.castLE hm, j.isLt, by simp [b]⟩
  apply Submodule.eq_of_le_of_finrank_eq
  · rw [heq]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hmono (by change j.val + 1 ≤ i.val; omega) (hv (j.castLE hm)).1
  · rw [heq, finrank_span_eq_card (hli i.val hm), Fintype.card_fin, hdim]

/-- An endomorphism preserving every initial span has an upper triangular matrix. -/
theorem upperTriangular_of_preserves_flag
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] {n : ℕ}
    (b : Basis (Fin n) k V) (f : V →ₗ[k] V)
    (h : ∀ m, ∀ v ∈ b.flag m, f v ∈ b.flag m) :
    (LinearMap.toMatrix b b f).IsUpperTriangular := by
  intro i j hij
  rw [LinearMap.toMatrix_apply]
  have hv := h j.succ (b j) (b.self_mem_flag (by simp))
  exact (b.mem_flag_iff_repr_eq_zero.mp hv) i (by
    change j.val + 1 ≤ i.val
    exact hij)

namespace LieModule

section

/-
The following variables generalize the setting where:
- `R` is a principal ideal domain of characteristic zero,
- `L` is a Lie algebra over `R`,
- `V` is a Lie algebra module over `L`
- `A` is a Lie ideal of `L`.
Besides generalizing, it also make the proof of `lie_stable` syntactically smoother.
-/
variable {R L A V : Type*} [CommRing R]
variable [IsPrincipalIdealRing R] [IsDomain R] [CharZero R]
variable [LieRing L] [LieAlgebra R L]
variable [LieRing A] [LieAlgebra R A]
variable [Bracket L A] [Bracket A L]
variable [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
variable [LieRingModule L V] [LieModule R L V]
variable [LieRingModule A V] [LieModule R A V]
variable [IsLieTower L A V] [IsLieTower A L V]

variable (χ : A → R)

open Module (finrank)
open LieModule

local notation "π" => LieModule.toEnd R _ V

private abbrev T (w : A) : Module.End R V := (π w) - χ w • 1

set_option backward.isDefEq.respectTransparency.types false in
/-- An auxiliary lemma used only in the definition `LieModule.weightSpaceOfIsLieTower` below. -/
private lemma weightSpaceOfIsLieTower_aux (z : L) (v : V) (hv : v ∈ weightSpace V χ) :
    ⁅z, v⁆ ∈ weightSpace V χ := by
  rw [mem_weightSpace] at hv ⊢
  intro a
  rcases eq_or_ne v 0 with (rfl | hv')
  · simp only [lie_zero, smul_zero]
  suffices χ ⁅z, a⁆ = 0 by
    rw [leibniz_lie, hv a, lie_smul, lie_swap_lie, hv, this, zero_smul, neg_zero, zero_add]
  let U' : ℕ →o Submodule R V :=
  { toFun n := Submodule.span R {((π z)^i) v | i < n},
    monotone' i j h := Submodule.span_mono (fun _ ⟨c, hc, hw⟩ ↦ ⟨c, lt_of_lt_of_le hc h, hw⟩) }
  have map_U'_le (n : ℕ) : Submodule.map (π z) (U' n) ≤ U' (n + 1) := by
    simp only [OrderHom.coe_mk, Submodule.map_span, toEnd_apply_apply, U']
    apply Submodule.span_mono
    suffices ∀ a < n, ∃ b < n + 1, ((π z) ^ b) v = ((π z) ^ (a + 1)) v by simpa [pow_succ']
    aesop
  have T_apply_succ (w : A) (n : ℕ) :
      Submodule.map (T χ w) (U' (n + 1)) ≤ U' n := by
    simp only [OrderHom.coe_mk, U', Submodule.map_span, Submodule.span_le, Set.image_subset_iff]
    simp only [Set.subset_def, Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    induction n generalizing w
    · simp only [zero_add, Nat.lt_one_iff, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
        LinearMap.smul_apply, Module.End.one_apply, forall_eq, pow_zero, hv w, sub_self, zero_mem]
    · next n hn =>
      intro m hm
      obtain (hm | rfl) : m < n + 1 ∨ m = n + 1 := by lia
      · exact U'.mono (Nat.le_succ n) (hn w m hm)
      have H : ∀ w, ⁅w, (π z ^ n) v⁆ = (T χ w) ((π z ^ n) v) + χ w • ((π z ^ n) v) := by simp
      rw [T, LinearMap.sub_apply, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply,
        LieModule.toEnd_apply_apply, LinearMap.smul_apply, Module.End.one_apply, leibniz_lie,
        lie_swap_lie w z, H, H, lie_add, lie_smul, add_sub_assoc, add_sub_assoc, sub_self, add_zero]
      refine add_mem (neg_mem <| add_mem ?_ ?_) ?_
      · exact U'.mono n.le_succ (hn _ n n.lt_succ_self)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, n.lt_succ_self, rfl⟩)
      · exact map_U'_le _ <| Submodule.mem_map_of_mem <| hn w n n.lt_succ_self
  set U : LieSubmodule R A V :=
  { toSubmodule := ⨆ k : ℕ, U' k
    lie_mem {w} x hx := by
      rw [show ⁅w, x⁆ = (T χ w) x + χ w • x by simp]
      apply add_mem _ (Submodule.smul_mem _ _ hx)
      set U := ⨆ k : ℕ, U' k
      suffices Submodule.map (T χ w) U ≤ U from this <| Submodule.mem_map_of_mem hx
      rw [Submodule.map_iSup, iSup_le_iff]
      rintro (_ | i)
      · simp [U']
      · exact (T_apply_succ w i).trans (le_iSup _ _) }
  have hzU (x : V) (hx : x ∈ U) : (π z) x ∈ U := by
    suffices Submodule.map (π z) U ≤ U from this <| Submodule.mem_map_of_mem hx
    simp only [U, Submodule.map_iSup, iSup_le_iff]
    exact fun i ↦ (map_U'_le i).trans (le_iSup _ _)
  have trace_za_zero : (LieModule.toEnd R A _ ⁅z, a⁆).trace R U = 0 := by
    have hres : LieModule.toEnd R A U ⁅z, a⁆ = ⁅(π z).restrict hzU, LieModule.toEnd R A U a⁆ := by
      ext ⟨x, hx⟩
      change ⁅⁅z, a⁆, x⁆ = ⁅z, ⁅a, x⁆⁆ - ⁅a, ⁅z, x⁆⁆
      simp only [leibniz_lie z a, add_sub_cancel_right]
    rw [hres, LinearMap.trace_lie]
  have trace_T_U_zero (w : A) : (T χ w).trace R U = 0 := by
    have key (i : ℕ) (hi : i ≠ 0) : ∃ j < i, Submodule.map (T χ w) (U' i) ≤ U' j := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact ⟨j, j.lt_succ_self, T_apply_succ w j⟩
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    suffices ⨆ i, U' i ≤ Module.End.maxGenEigenspace (T χ w) 0 by
      intro x
      specialize this x.2
      simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero] at this
      gconvert this with n hn
      ext
      simp only [ZeroMemClass.coe_zero, ← hn]; clear hn
      induction n <;> simp_all [pow_succ']
    apply iSup_le
    intro i x hx
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
    induction i using Nat.strong_induction_on generalizing x
    next i ih =>
    obtain rfl | hi := eq_or_ne i 0
    · simp_all [U']
    obtain ⟨j, hj, hj'⟩ := key i hi
    obtain ⟨k, hk⟩ := ih j hj (hj' <| Submodule.mem_map_of_mem hx)
    use k + 1
    rw [pow_succ, Module.End.mul_apply, hk]
  have trace_za : (toEnd R A _ ⁅z, a⁆).trace R U = χ ⁅z, a⁆ • (finrank R U) := by
    simpa [T, sub_eq_zero] using trace_T_U_zero ⁅z, a⁆
  suffices finrank R U ≠ 0 by simp_all
  suffices Nontrivial U from Module.finrank_pos.ne'
  have hvU : v ∈ U := by
    apply Submodule.mem_iSup_of_mem 1
    apply Submodule.subset_span
    use 0, zero_lt_one
    rw [pow_zero, Module.End.one_apply]
  exact nontrivial_of_ne ⟨v, hvU⟩ 0 <| by simp [hv']

variable (R V) in
/-- The weight space of `V` with respect to `χ : A → R`, a priori a Lie submodule for `A`, is also a
Lie submodule for `L`. -/
def weightSpaceOfIsLieTower (χ : A → R) : LieSubmodule R L V :=
  { toSubmodule := weightSpace V χ
    lie_mem {z v} hv := private weightSpaceOfIsLieTower_aux χ z v hv }

end

section

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

variable [CharZero k] [Module.Finite k V]

set_option linter.style.whitespace false in -- manual alignment is not recognised
open Submodule in
theorem exists_nontrivial_weightSpace_of_lieIdeal [LieModule.IsTriangularizable k L V]
    (A : LieIdeal k L) (hA : IsCoatom A.toSubmodule)
    (χ₀ : Module.Dual k A) [Nontrivial (weightSpace V χ₀)] :
    ∃ (χ : Module.Dual k L), Nontrivial (weightSpace V χ) := by
  obtain ⟨z, -, hz⟩ := IsConcreteLE.exists_of_lt (hA.lt_top)
  let e : (k ∙ z) ≃ₗ[k] k := (LinearEquiv.toSpanNonzeroSingleton k L z <| by aesop).symm
  have he : ∀ x, e x • z = x := by simp [e]
  have hA : IsCompl A.toSubmodule (k ∙ z) := isCompl_span_singleton_of_isCoatom_of_notMem hA hz
  let π₁ : L →ₗ[k] A       := A.toSubmodule.projectionOnto (k ∙ z) hA
  let π₂ : L →ₗ[k] (k ∙ z) := (k ∙ z).projectionOnto ↑A hA.symm
  set W : LieSubmodule k L V := weightSpaceOfIsLieTower k V χ₀
  obtain ⟨c, hc⟩ : ∃ c, (toEnd k _ W z).HasEigenvalue c := by
    have : Nontrivial W := inferInstanceAs (Nontrivial (weightSpace V χ₀))
    apply Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top
    exact LieModule.IsTriangularizable.maxGenEigenspace_eq_top z
  obtain ⟨⟨v, hv⟩, hvc⟩ := hc.exists_hasEigenvector
  have hv' : ∀ (x : ↥A), ⁅x, v⁆ = χ₀ x • v := by
    simpa [W, weightSpaceOfIsLieTower, mem_weightSpace] using hv
  use (χ₀.comp π₁) + c • (e.comp π₂)
  refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
  · rw [mem_weightSpace]
    intro x
    have hπ : (π₁ x : L) + π₂ x = x := projection_add_projection_eq_self hA x
    suffices ⁅projection _ _ hA.symm x, v⁆ = (c • e (π₂ x)) • v by
      calc ⁅x, v⁆
          = ⁅π₁ x, v⁆ + ⁅projection _ _ hA.symm x, v⁆ := congr(⁅$hπ.symm, v⁆) ▸ add_lie _ _ _
        _ = χ₀ (π₁ x) • v + (c • e (π₂ x)) • v    := by rw [hv' (π₁ x), this]
        _ = _ := by simp [add_smul]
    calc ⁅projection _ _ hA.symm x, v⁆
        = e (π₂ x) • ↑(c • ⟨v, hv⟩ : W) := by
          rw [projection_apply, ← he, smul_lie, ← hvc.apply_eq_smul]; rfl
      _ = (c • e (π₂ x)) • v            := by rw [smul_assoc, smul_comm]; rfl
  · simpa [ne_eq, LieSubmodule.mk_eq_zero] using hvc.right

variable (k L V)
variable [Nontrivial V]

open LieAlgebra

-- This lemma is the central inductive argument in the proof of Lie's theorem below.
-- The statement is identical to `LieModule.exists_forall_lie_eq_smul_of_isSolvable`
-- except that it additionally assumes a finiteness hypothesis.
private lemma exists_forall_lie_eq_smul_of_isSolvable_of_finite
    (L : Type*) [LieRing L] [LieAlgebra k L] [LieRingModule L V] [LieModule k L V]
    [IsSolvable L] [LieModule.IsTriangularizable k L V] [Module.Finite k L] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace V χ) := by
  obtain H | ⟨A, hA, hAL⟩ := eq_top_or_exists_le_coatom (derivedSeries k L 1).toSubmodule
  · obtain _ | _ := subsingleton_or_nontrivial L
    · use 0
      simpa [trivial_lie_zero, mem_weightSpace, nontrivial_iff] using exists_pair_ne V
    · rw [LieSubmodule.toSubmodule_eq_top] at H
      exact ((derivedSeries_lt_top_of_solvable k L).ne H).elim
  lift A to LieIdeal k L
  · intros
    exact hAL <| LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  obtain ⟨χ', _⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite A
  exact exists_nontrivial_weightSpace_of_lieIdeal A hA χ'
termination_by Module.finrank k L
decreasing_by
  rw [← finrank_top k L]
  apply Submodule.finrank_lt_finrank_of_lt
  exact hA.lt_top

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Lie's theorem**: Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.

See `LieModule.exists_nontrivial_weightSpace_of_isNilpotent` for the variant that
assumes that `L` is nilpotent and drops the condition that `k` is of characteristic zero. -/
theorem exists_nontrivial_weightSpace_of_isSolvable
    [IsSolvable L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace V χ) := by
  let imL := (toEnd k L V).range
  let toEndo : L →ₗ[k] imL := LinearMap.codRestrict imL.toSubmodule (toEnd k L V)
      (fun x ↦ LinearMap.mem_range.mpr ⟨x, rfl⟩ : ∀ x : L, (toEnd k L V) x ∈ imL)
  have ⟨χ, h⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite k V imL
  use χ.comp toEndo
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : weightSpace V χ)
  refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
  · rw [mem_weightSpace] at hv ⊢
    intro x
    apply hv (toEndo x)
  · simpa using hv0

theorem my_proof_this
    [IsSolvable L] [LieModule.IsTriangularizable k L V] :
    ∃ f : Fin (Module.finrank k V + 1) → LieSubmodule k L V, (∀ n, Module.finrank k (f n) = n.1) ∧
      StrictMono f := by
  induction hn : Module.finrank k V generalizing V with
  | zero =>
  · let f : Fin 1 → LieSubmodule k L V
    | 0 => ⊥
    have m : f 0 = ⊥ := by
      exact (LieSubmodule.toSubmodule_eq_bot (f 0)).mp rfl
    use f
    constructor
    · intro n
      let qq := Set.range f
      have mm2 (s : Fin 1) : s = 0 := by exact Fin.fin_one_eq_zero s
      have mm1 (s : Fin 1) : f s = ⊥ := by
        have := mm2 s
        rw [this]
      rw [mm1]
      have tt : Module.finrank k (⊥ : LieSubmodule k L V) = 0 := by
        exact Module.finrank_eq_zero_of_subsingleton k (⊥ : LieSubmodule k L V)
      rw [tt]
      rw [mm2 n]
      exact Nat.eq_of_beq_eq_true rfl
    intro p q
    have p0 := Fin.fin_one_eq_zero p
    have q0 := Fin.fin_one_eq_zero q
    intro c
    rw [p0, q0] at c
    have := Nat.not_succ_le_zero 0 c
    contradiction
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | hpos
    · rw [h]
      let f : Fin 2 → LieSubmodule k L V
      | 0 => ⊥
      | 1 => ⊤
      use f
      constructor
      · intro i
        have mm : i = 0 ∨ i = 1 := by
          grind
        rcases mm with hz | hz1
        · rw [hz]
          apply finrank_bot
        rw [hz1]
        simp only [Fin.isValue, Nat.reduceAdd, Fin.coe_ofNat_eq_mod, Nat.mod_succ]
        dsimp [f]
        rw [h] at hn
        simp only [zero_add] at hn
        have := finrank_top k V
        rw [hn] at this
        exact this
      intro p q hpq
      have : p = 0 ∧ q = 1 := by
        grind
      rw [this.1, this.2]
      simp_all only [Nat.reduceAdd, Fin.isValue, zero_add, zero_lt_one, bot_lt_top, f]
    obtain ⟨r, h⟩ := exists_nontrivial_weightSpace_of_isSolvable k L V
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : weightSpace V r)
    have : v ≠ 0 := by
      simp_all only [ne_eq, LieSubmodule.mk_eq_zero, not_false_eq_true]
    let g : LieSubmodule k L V := {
      carrier := {s • v | s : k}
      add_mem' := by
        intro x y c d
        simp only [Set.mem_ofPred_eq] at c
        simp only [Set.mem_ofPred_eq] at d
        simp only [Set.mem_ofPred_eq]
        obtain ⟨p, pp⟩ := c
        obtain ⟨q, qq⟩ := d
        use p + q
        rw [add_smul, pp, qq]
      zero_mem' := by
        simp
      smul_mem' := by
        intro x y c
        simp only [Set.mem_ofPred_eq] at c
        simp only [Set.mem_ofPred_eq]
        obtain ⟨p, pp⟩ := c
        use p • x
        rw [← pp, smul_comm]
        exact smul_assoc p x v
      lie_mem := by
        intro x y hx
        simp only [Set.mem_ofPred_eq] at hx
        simp only [Set.mem_ofPred_eq]
        obtain ⟨p, pp⟩ := hx
        rw [← pp]
        simp only [lie_smul]
        have : ⁅x, v⁆ = (r x) • v := by
          exact (mem_weightSpace r v).1 hv x
        rw [this]
        use p • r x
        exact smul_assoc p (r x) v
    }
    have tt : Module.finrank k g.toSubmodule = 1 := by
      refine Module.rank_eq_one_iff_finrank_eq_one.mp ?_
      refine rank_eq_one_iff.mpr ?_
      let vg : g := {
        val := by
          exact v
        property := by
          use 1
          exact one_smul k v
      }
      use vg
      constructor
      · exact Subtype.coe_ne_coe.mp this
      intro w
      obtain ⟨h1, ⟨h2, h3⟩⟩ := w
      use h2
      exact SetLike.coe_eq_coe.mp h3
    let f : V →ₗ⁅k,L⁆ V ⧸ g := by
      exact LieSubmodule.Quotient.mk' g
    have hqf : Function.Surjective f := LieSubmodule.Quotient.surjective_mk' g
    --have cc : f.ker = g := by
    --  exact LieSubmodule.Quotient.mk'_ker g
    --have cc2 := LieSubmodule.Quotient.range_mk' g
    have := Submodule.finrank_quotient_add_finrank g.toSubmodule
    rw [hn] at this
    rw [tt] at this
    simp only [Nat.add_right_cancel_iff] at this
    have goal : Module.finrank k (V ⧸ g) = n := this
    have _i : Nontrivial (V ⧸ g) := by
      have k : Module.finrank k (V ⧸ g) > 0 := by
        rw [goal]
        exact hpos
      exact Module.nontrivial_of_finrank_pos k
    have _j : IsTriangularizable k L (V ⧸ g) := by
      let q : V →ₗ[k] V ⧸ g := (LieSubmodule.Quotient.mk' g).toLinearMap
      have hq : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' g
      constructor
      intro x
      have rr : IsTriangularizable k L V := by
        infer_instance
      have tt : ∀ x, ⨆ φ, (toEnd k L V x).maxGenEigenspace φ = ⊤ := by
        exact rr.maxGenEigenspace_eq_top
      have m : ⨆ φ, (toEnd k L V x).maxGenEigenspace φ = ⊤ := by
        exact tt x
      apply top_unique
      calc
        ⊤ = Submodule.map q ⊤ := by
          simp only [Submodule.map_top]
          have := (LinearMap.range_eq_top_of_surjective q hq)
          exact this.symm
        _ = Submodule.map q (⨆ φ, (toEnd k L V x).maxGenEigenspace φ) := by
          rw [tt]
        _ = ⨆ φ, Submodule.map q ((toEnd k L V x).maxGenEigenspace φ) := by
          simp only [Submodule.map_iSup]
        _ ≤ ⨆ φ, ((toEnd k L (V ⧸ g)) x).maxGenEigenspace φ := by
          apply iSup_mono
          intro μ
          apply Module.End.map_genEigenspace_le q
          exact LieSubmodule.Quotient.toEnd_comp_mk' g x
    have ihh := ih (V ⧸ g) goal
    obtain ⟨E, ⟨a1, a2⟩⟩ := ihh
    let F : Fin (n + 1) → LieSubmodule k L V := by
      intro a
      exact LieSubmodule.comap f (E a)
    have Fh0 (m : Fin (n + 1)) : Module.finrank k (F m) = m + 1 := by
      have hk : LinearMap.ker f.toLinearMap = g.toSubmodule := by
        exact congrArg LieSubmodule.toSubmodule
          (LieSubmodule.Quotient.mk'_ker g)
      change Module.finrank k ((E m).toSubmodule.comap f.toLinearMap) = m + 1
      rw [LinearMap.finrank_comap_of_surjective f.toLinearMap hqf, hk, tt]
      exact congrArg (· + 1) (a1 m)
    have Fh1 : StrictMono F := by
      intro x y hxy
      have k : E x ≤ E y := by
        have := a2 hxy
        exact Std.le_of_lt (a2 hxy)
      have := Submodule.comap_mono (f := f.toLinearMap) k
      dsimp [F]
      have s1 : LieSubmodule.comap f (E x) ≤ LieSubmodule.comap f (E y) := by
        exact
          (LieSubmodule.toSubmodule_le_toSubmodule (LieSubmodule.comap f (E x))
                (LieSubmodule.comap f (E y))).mp
            this
      have s15 : F x ≠ F y := by
        intro hc
        have s1 := Fh0 x
        have s2 := Fh0 y
        rw [hc] at s1
        rw [s1] at s2
        grind
      have s2 : LieSubmodule.comap f (E x) ≠ LieSubmodule.comap f (E y) := by
        apply s15
      exact Std.lt_of_le_of_ne this s2
    let ff : Fin (n + 2) → LieSubmodule k L V := Fin.cons ⊥ F
    have ff0 : ff 0 = ⊥ := by
          exact (LieSubmodule.toSubmodule_eq_bot (ff 0)).mp rfl
    have ffpos (m : Fin (n + 2)) (h1 : m ≠ 0) : ∃(p : Fin (n + 1)), ff m = F p ∧ m = p.succ := by
      have keyvvv : ∃(i : Fin (n + 1)), i.succ = m := by
        exact Fin.exists_succ_eq_of_ne_zero h1
      obtain ⟨p, q⟩ := keyvvv
      use p
      constructor
      · rw [← q]
        dsimp [ff]
        simp only [Fin.cons_succ]
      exact q.symm
    use ff
    constructor
    · intro nn
      have mr1 : nn = 0 ∨ nn ≠ 0 := by exact Decidable.eq_or_ne nn 0
      rcases mr1 with hz | hnz
      · rw [hz]
        apply finrank_bot
      obtain ⟨d1, ⟨d2, d3⟩⟩ := ffpos nn hnz
      rw [d2]
      rw [d3]
      exact Nat.succ_inj.mp (congrArg Nat.succ (Fh0 d1))
    intro x y hxy
    have pmp : x = 0 ∨ 0 < x := by exact eq_zero_or_pos x
    rcases pmp with pmp1 | pmp2
    · rw [pmp1]
      rw [ff0]
      have t1 : Nontrivial (ff y) := by
        have hny : y ≠ 0 := by exact Fin.ne_zero_of_lt hxy
        obtain ⟨d1, ⟨d2, d3⟩⟩ := ffpos y hny
        rw [d2]
        have help := Fh0 d1
        have help2 : Module.finrank k (F d1) > 0 := by
          rw [help]
          exact Nat.zero_lt_succ ↑d1
        have help3 := Module.finrank_pos_iff (R := k) (M := F d1)
        apply help3.1
        exact help2
      have t2 : ff y ≠ ⊥ := by
        exact (LieSubmodule.nontrivial_iff_ne_bot k L V).mp t1
      exact bot_lt_iff_ne_bot.mpr t2
    have in1 : x ≠ 0 := by
      exact Fin.pos_iff_ne_zero.mp pmp2
    have in2 : y ≠ 0 := by
      have tr: 0 < y := by
        calc
         0 < x := by exact pmp2
         _ < y := by exact hxy
      exact Fin.pos_iff_ne_zero.mp tr
    obtain ⟨d1, ⟨d2, d3⟩⟩ := ffpos x in1
    obtain ⟨e1, ⟨e2, e3⟩⟩ := ffpos y in2
    rw [d2, e2]
    have in3 : d1 < e1 := by
      grind
    exact Fh1 in3

/-- A finite ordered basis index admits a basis simultaneously upper triangularizing
all actions of a solvable Lie algebra. The input basis supplies the dimension of the index. -/
theorem lie_class {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [IsSolvable L]
    [LieModule.IsTriangularizable k L V] (b : Basis ι k V) :
    ∃ B : Basis ι k V, ∀ x : L,
      (LinearMap.toMatrix B B (toEnd k L V x)).IsUpperTriangular := by
  classical
  obtain ⟨F, hdim, hmono⟩ := my_proof_this (k := k) (L := L) (V := V)
  obtain ⟨B, hB⟩ := exists_basis_adapted_to_flag
    (fun i => (F i).toSubmodule) (fun i j hij => hmono.monotone hij) hdim
  have htri : ∀ x : L, (LinearMap.toMatrix B B (toEnd k L V x)).IsUpperTriangular := by
    intro x
    apply upperTriangular_of_preserves_flag B (toEnd k L V x)
    intro i v hv
    rw [hB] at hv ⊢
    exact (F i).lie_mem hv
  let e := Fintype.orderIsoFinOfCardEq ι (Module.finrank_eq_card_basis b).symm
  refine ⟨B.reindex e.toEquiv, ?_⟩
  intro x i j hij
  simpa [LinearMap.toMatrix_apply] using
    htri x ((e.symm.lt_iff_lt).mpr hij)

omit [Nontrivial V] [Module.Finite k V] [CharZero k] in
/-- In a simultaneous upper triangular basis, the derived algebra acts by strictly upper
triangular matrices. -/
theorem lie_class2 {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : Module.Basis ι k V)
    (h : ∀ x : L, (LinearMap.toMatrix B B (toEnd k L V x)).IsUpperTriangular) :
    ∀ y : derivedSeries k L 1,
      (LinearMap.toMatrix B B (toEnd k L V y)).IsStrictlyUpperTriangular := by
  rintro ⟨y, hy⟩
  change (LinearMap.toMatrix B B (toEnd k L V y)).IsStrictlyUpperTriangular
  change y ∈ (derivedSeries k L 1 : LieSubalgebra k L).toSubmodule at hy
  rw [coe_derivedSeries_one_eq] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, y, rfl⟩ := hz
    rw [LieHom.map_lie, Ring.lie_def, map_sub,
      LinearMap.toMatrix_mul B, LinearMap.toMatrix_mul B]
    exact (h x).commutator (h y)
  | zero =>
    simp only [map_zero]
    exact Matrix.isStrictlyUpperTriangular_zero
  | add x y hx hy ihx ihy =>
    simp only [map_add]
    exact ihx.add ihy
  | smul c x hx ih =>
    simp only [map_smul]
    exact ih.smul c

end

end LieModule

section Engel

namespace LieModule

variable {k L V : Type*} [Field k] [LieRing L] [LieAlgebra k L]
    [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]
    [FiniteDimensional k V]

/-- A nilpotent representation admits a complete flag that every action lowers by one step. -/
theorem exists_flag_of_isNilpotent [IsNilpotent L V] :
    ∃ F : Fin (finrank k V + 1) → LieSubmodule k L V,
      (∀ i, finrank k (F i) = i.val) ∧ Monotone F ∧
      ∀ (i : Fin (finrank k V)) (x : L) (v : V), v ∈ F i.succ → ⁅x,v⁆ ∈ F i.castSucc := by
  classical
  induction hn : finrank k V generalizing V with
  | zero =>
    refine ⟨fun _ => ⊥, ?_, ?_, ?_⟩
    · intro i
      have hi : i = 0 := Fin.fin_one_eq_zero i
      subst i
      exact Module.finrank_eq_zero_of_subsingleton k (⊥ : LieSubmodule k L V)
    · exact monotone_const
    · intro i
      exact Fin.elim0 i
  | succ n ih =>
    have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hn]; omega)
    have : Nontrivial (maxTrivSubmodule k L V) := nontrivial_max_triv_of_isNilpotent k L V
    obtain ⟨v, hv⟩ := exists_ne (0 : maxTrivSubmodule k L V)
    have hv0 : (v : V) ≠ 0 := by simpa using hv
    have hvlie (x : L) : ⁅x,(v : V)⁆ = 0 :=
      (mem_maxTrivSubmodule k L V v).mp v.property x
    let g : LieSubmodule k L V :=
      { toSubmodule := k ∙ (v : V)
        lie_mem := by
          intro x w hw
          obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
          simp [lie_smul, hvlie] }
    have hg : finrank k g.toSubmodule = 1 := finrank_span_singleton hv0
    have hgzero (x : L) (w : V) (hw : w ∈ g) : ⁅x,w⁆ = 0 := by
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hw
      simp [lie_smul, hvlie]
    have : IsNilpotent L (V ⧸ g) := by
      apply (isNilpotent_quotient_iff k L V g).mpr
      obtain ⟨m,hm⟩ := IsNilpotent.nilpotent k L V
      exact ⟨m, by rw [hm]; exact bot_le⟩
    have hq : finrank k (V ⧸ g) = n := by
      have h := Submodule.finrank_quotient_add_finrank g.toSubmodule
      change finrank k (V ⧸ g) + finrank k g.toSubmodule = finrank k V at h
      rw [hg, hn] at h
      omega
    obtain ⟨E, hdim, hmono, hlower⟩ := ih (V := V ⧸ g) hq
    let q := LieSubmodule.Quotient.mk' g
    have hsurj : Function.Surjective q := LieSubmodule.Quotient.surjective_mk' g
    have hk : LinearMap.ker q.toLinearMap = g.toSubmodule :=
      congrArg LieSubmodule.toSubmodule (LieSubmodule.Quotient.mk'_ker g)
    have hE0 : E 0 = ⊥ := by
      apply LieSubmodule.toSubmodule_injective
      apply Submodule.finrank_eq_zero.mp
      exact hdim 0
    let F : Fin (n + 2) → LieSubmodule k L V :=
      Fin.cases ⊥ (fun i => LieSubmodule.comap q (E i))
    refine ⟨F, ?_, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact Module.finrank_eq_zero_of_subsingleton k (⊥ : LieSubmodule k L V)
      · change finrank k ((E j).toSubmodule.comap q.toLinearMap) = j.val + 1
        rw [LinearMap.finrank_comap_of_surjective q.toLinearMap hsurj, hk, hg]
        exact congrArg (· + 1) (hdim j)
    · intro i
      induction i using Fin.cases with
      | zero => intro j hij; exact bot_le
      | succ i =>
        intro j
        induction j using Fin.cases with
        | zero => intro hij; simp at hij
        | succ j =>
          intro hij w hw
          exact hmono (Fin.succ_le_succ_iff.mp hij) hw
    · intro i
      induction i using Fin.cases with
      | zero =>
        intro x w hw
        change ⁅x,w⁆ ∈ (⊥ : LieSubmodule k L V)
        have hwg : w ∈ g := by
          change q w ∈ E 0 at hw
          rw [hE0] at hw
          change w ∈ LinearMap.ker q.toLinearMap at hw
          rwa [hk] at hw
        simp [hgzero x w hwg]
      | succ j =>
        intro x w hw
        change q ⁅x,w⁆ ∈ E j.castSucc
        rw [q.map_lie]
        apply hlower j x (q w)
        exact hw

omit [FiniteDimensional k V] in
/-- An endomorphism lowering each initial span has a strictly upper triangular matrix. -/
theorem strictTriangular_of_lowers_flag {n : ℕ}
    (B : Basis (Fin n) k V) (f : V →ₗ[k] V)
    (h : ∀ (i : Fin n) (v : V), v ∈ B.flag i.succ → f v ∈ B.flag i.castSucc) :
    Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B f) := by
  intro i j hij
  rw [LinearMap.toMatrix_apply]
  exact (B.mem_flag_iff_repr_eq_zero.mp
    (h j (B j) (B.self_mem_flag (by simp)))) i hij

/-- Engel's theorem in basis form: nilpotent action operators admit a simultaneous
strictly upper triangular basis, with the same ordered index as the supplied basis. -/
theorem exists_basis_isStrictlyUpperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (b : Basis ι k V) (h : ∀ x : L, _root_.IsNilpotent (toEnd k L V x)) :
    ∃ B : Basis ι k V, ∀ x : L,
      Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B (toEnd k L V x)) := by
  classical
  have : IsNilpotent L V := (isNilpotent_iff_forall' (R := k)).mpr h
  obtain ⟨F, hdim, hmono, hlower⟩ := exists_flag_of_isNilpotent (k := k) (L := L) (V := V)
  obtain ⟨B, hB⟩ := exists_basis_adapted_to_flag
    (fun i => (F i).toSubmodule) (fun i j hij => hmono hij) hdim
  have hstrict (x : L) :
      Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B (toEnd k L V x)) := by
    apply strictTriangular_of_lowers_flag B (toEnd k L V x)
    intro j v hv
    rw [hB] at hv ⊢
    exact hlower j x v hv
  let e := Fintype.orderIsoFinOfCardEq ι (Module.finrank_eq_card_basis b).symm
  refine ⟨B.reindex e.toEquiv, ?_⟩
  intro x i j hij
  simpa [LinearMap.toMatrix_apply] using hstrict x ((e.symm.le_iff_le).mpr hij)

omit [FiniteDimensional k V] in
/-- A strictly upper triangular matrix represents a nilpotent endomorphism. -/
theorem isNilpotent_of_toMatrix_strictTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : Basis ι k V) (f : V →ₗ[k] V)
    (h : Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B f)) : _root_.IsNilpotent f := by
  exact (IsNilpotent.map_iff (LinearMap.toMatrixAlgEquiv B).injective).mp h.isNilpotent

/-- Engel's theorem expressed as the existence of a simultaneous strictly upper triangular basis. -/
theorem isNilpotent_iff_exists_basis_isStrictlyUpperTriangular
    {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (b : Basis ι k V) :
    IsNilpotent L V ↔ ∃ B : Basis ι k V, ∀ x : L,
      Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B (toEnd k L V x)) := by
  constructor
  · intro h
    exact exists_basis_isStrictlyUpperTriangular b (isNilpotent_toEnd_of_isNilpotent k L V)
  · rintro ⟨B, hB⟩
    apply (isNilpotent_iff_forall' (R := k)).mpr
    intro x
    exact isNilpotent_of_toMatrix_strictTriangular B (toEnd k L V x) (hB x)

/-- Nilpotency of a finite-dimensional representation is equivalent to a complete flag
that every action lowers by one step. -/
theorem isNilpotent_iff_exists_flag :
    IsNilpotent L V ↔
      ∃ F : Fin (finrank k V + 1) → LieSubmodule k L V,
        (∀ i, finrank k (F i) = i.val) ∧ Monotone F ∧
        ∀ (i : Fin (finrank k V)) (x : L) (v : V), v ∈ F i.succ → ⁅x,v⁆ ∈ F i.castSucc := by
  constructor
  · intro h
    exact exists_flag_of_isNilpotent
  · rintro ⟨F, hdim, hmono, hlower⟩
    obtain ⟨B, hB⟩ := exists_basis_adapted_to_flag
      (fun i => (F i).toSubmodule) (fun i j hij => hmono hij) hdim
    apply (isNilpotent_iff_forall' (R := k)).mpr
    intro x
    apply isNilpotent_of_toMatrix_strictTriangular B (toEnd k L V x)
    apply strictTriangular_of_lowers_flag B (toEnd k L V x)
    intro i v hv
    rw [hB] at hv ⊢
    exact hlower i x v hv

end LieModule

/-- Engel's theorem for the adjoint representation in simultaneous strictly upper triangular
basis form. -/
theorem LieAlgebra.isNilpotent_iff_exists_basis_isStrictlyUpperTriangular
    {k L ι : Type*} [Field k] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (b : Module.Basis ι k L) :
    LieRing.IsNilpotent L ↔ ∃ B : Module.Basis ι k L, ∀ x : L,
      Matrix.IsStrictlyUpperTriangular (LinearMap.toMatrix B B (LieAlgebra.ad k L x)) :=
  LieModule.isNilpotent_iff_exists_basis_isStrictlyUpperTriangular b

end Engel
