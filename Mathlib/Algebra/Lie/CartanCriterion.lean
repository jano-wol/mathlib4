/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Lie.AdjointAction.JordanChevalley
public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.LieTheorem
public import Mathlib.Algebra.Lie.TraceForm
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Cartan's criteria

The two **Cartan criteria** characterise solvability and semisimplicity of finite-dimensional
Lie algebras over fields of characteristic zero in terms of the Killing form: solvability
via its vanishing on `L × ⁅L, L⁆`, semisimplicity via its non-degeneracy.

## Main results

* `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`: over a field of characteristic zero,
  if a finite-dimensional representation `M` of `L` has trivial trace form, then `M` is nilpotent
  as a `⁅L, L⁆`-module.
* `LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero`: **Cartan's criterion for solvability**:
  if the Killing form of a Lie algebra `L` vanishes on `L × ⁅L, L⁆`, then `L` is solvable.
* `LieAlgebra.radical_eq_killingCompl_derived`: the solvable radical is the Killing-orthogonal
  complement of the derived algebra.
* `LieAlgebra.killingForm_apply_lie_eq_zero_of_IsSolvable`: the converse of the solvability
  criterion, obtained from the radical characterization.
* `LieAlgebra.killingCompl_top_le_radical`: the Killing radical of a finite-dimensional Lie algebra
  is contained in the solvable radical.
* `LieAlgebra.HasTrivialRadical.instIsKilling`: **Cartan's criterion for semisimplicity**: if a
  finite-dimensional Lie algebra has trivial solvable radical, then its Killing form is
  non-degenerate.

## References

* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975) Chapter I. §5.4
* [J. Humphreys, *Introduction to Lie Algebras and ...*](humphreys1972) Chapter II 4.3
-/

variable {R L M : Type*} [CommRing R] [CharZero R] [IsDomain R] [LieRing L] [LieAlgebra R L]

namespace LieModule

open Algebra Function LieAlgebra LinearMap Module Module.End Polynomial
open scoped TensorProduct

lemma exists_polynomial_eval_sub_aux
    {ι R K : Type*} [Finite ι] [CommRing R] [Field K] [Algebra R K]
    {E : Submodule R K} (a : ι → K) (ha : ∀ i, a i ∈ E) (f : E →+ R) :
    ∃ r : K[X], ∀ i j, r.eval (a i - a j) =
      algebraMap R K (f ⟨a i, ha i⟩) - algebraMap R K (f ⟨a j, ha j⟩) := by
  suffices ∀ (ij kl : ι × ι) (hij : a ij.1 - a ij.2 = a kl.1 - a kl.2),
      algebraMap R K (f ⟨a ij.1, ha ij.1⟩) - algebraMap R K (f ⟨a ij.2, ha ij.2⟩) =
      algebraMap R K (f ⟨a kl.1, ha kl.1⟩) - algebraMap R K (f ⟨a kl.2, ha kl.2⟩) by
    obtain ⟨r, hr⟩ := (Polynomial.exists_eval_eq_iff _ _).mpr this
    exact ⟨r, fun i j ↦ hr (i, j)⟩
  rintro ⟨i, j⟩ ⟨k, l⟩ hij
  have heq : (⟨a i, ha i⟩ - ⟨a j, ha j⟩ : E) = ⟨a k, ha k⟩ - ⟨a l, ha l⟩ := Subtype.ext hij
  rw [← (algebraMap R K).map_sub, ← (algebraMap R K).map_sub, ← map_sub, ← map_sub, heq]

variable [AddCommGroup M] [LieRingModule L M]
attribute [local instance 100] LieRing.ofAssociativeRing

/-- An auxiliary lemma used to prove `LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`
which proves the same result except without the algebraically closed assumption. -/
theorem isNilpotent_derivedSeries_of_traceForm_eq_zero_aux {K : Type*}
    [Field K] [CharZero K] [IsAlgClosed K]
    [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]
    (h : traceForm K L M = 0) :
    IsNilpotent (derivedSeries K L 1) M := by
  set φ := toEnd K L M
  /- By Engel's theorem it suffices to prove that `⁅L, L⁆` acts nilpotently on `M`. -/
  suffices ∀ x ∈ derivedSeries K L 1, _root_.IsNilpotent (φ x) from
    isNilpotent_iff_forall'.mpr fun ⟨x, hx⟩ ↦ this x hx
  intro x hx
  /- Using Jordan-Chevalley, let `s` and `n` be the semisimple and nilpotent parts of `φ x`. -/
  obtain ⟨n, hn_adj, s, hns, hn_nil, hs_ss, hX_ns⟩ := (φ x).exists_isNilpotent_isSemisimple
  replace hns : Commute n s :=
    commute_of_mem_adjoin_singleton_of_commute hns (commute_of_mem_adjoin_self hn_adj).symm
  /- It suffices to prove `s = 0`. -/
  suffices s = 0 by aesop
  classical
  /- Decompose `M` as a direct sum of eigenspaces of `s`. -/
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hs_ss.iSup_eigenspace_eq_top
  let I := (ν : K) × Fin (finrank K (s.eigenspace ν))
  let v : Basis I K M := eigenDecomp.collectedBasis fun μ ↦ finBasis K (s.eigenspace μ)
  have : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → K := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  /- Let `E ⊆ K` be the `ℚ`-submodule of scalars spanned by the eigenvalues of `s`. -/
  let E : Submodule ℚ K := Submodule.span ℚ (Set.range μ)
  have hμ (i : I) : μ i ∈ E := Submodule.subset_span (Set.mem_range_self i)
  /- It suffices to prove that the `ℚ`-dual of `E` is trivial.  This can be regarded as a trick to
     handle the fact that our scalars `K` are not ordered. -/
  suffices ∀ f : Dual ℚ E, f = 0 by
    suffices ∀ ν, s.HasEigenvalue ν → ν = 0 from hs_ss.eq_zero_iff_forall_eigenvalue.mpr this
    intro ν hν
    have : Nontrivial (s.eigenspace ν) :=
      Submodule.nontrivial_iff_ne_bot.mpr (hasEigenvalue_iff.mp hν)
    replace hν : ν ∈ E := Submodule.subset_span ⟨⟨ν, ⟨0, finrank_pos⟩⟩, rfl⟩
    have : Subsingleton E := (subsingleton_dual_iff ℚ).mp ⟨by aesop⟩
    simpa using! Subsingleton.elim (⟨ν, hν⟩ : E) 0
  intro f
  /- It suffices to show that any `f : Dual ℚ E` vanishes on all the eigenvalues of `s`. -/
  suffices ∀ i, f ⟨μ i, hμ i⟩ = 0 by
    rw [Submodule.linearMap_eq_zero_iff_of_eq_span f rfl]
    rintro ⟨-, ⟨i, rfl⟩⟩
    exact this i
  /- We will deduce this by proving that the sum of the squares of all such values vanishes. -/
  suffices ∑ i, f ⟨μ i, hμ i⟩ ^ 2 = 0 from fun i ↦ eq_zero_of_pow_eq_zero <|
    (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ sq_nonneg _)).mp this i (Finset.mem_univ _)
  /- Which will follow from the fact that the following `f`-linear expression vanishes. -/
  suffices ∑ i, (f ⟨μ i, hμ i⟩) • (⟨μ i, hμ i⟩ : E) = 0 by
    simpa only [map_sum, map_zero, map_smul, sq] using! f.congr_arg this
  let fμ (i : I) : K := f ⟨μ i, hμ i⟩
  /- Defining `fμ i = f ⟨μ i, hμ i⟩`, we can restate our goal as `∑ i, fμ i * μ i = 0`. -/
  suffices ∑ i, fμ i * μ i = 0 by simp [Subtype.ext_iff, fμ, ← this, smul_def]
  /- We will do this by constructing endomorphism `y` such that `trace K M (φ x * y) = 0` and also
     `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices ∃ y : End K M, trace K M (φ x * y) = 0 ∧ trace K M (φ x * y) = ∑ i, fμ i * μ i by grind
  /- We define `y` diagonal wrt our basis `v` and takes the values `fμ` on the diagonal. -/
  let y : End K M := (Matrix.diagonal fμ).toLin v v
  have hyv (i : I) : y (v i) = fμ i • v i :=
    mem_eigenspace_iff.mp (hasEigenvector_toLin_diagonal fμ i v).1
  /- Using Lagrange interpolation, we can show that the representation is stable under `y`. -/
  have hy_range (z : End K M) (hz : z ∈ LieHom.range φ) : ⁅y, z⁆ ∈ LieHom.range φ := by
    obtain ⟨q, hq⟩ : ∃ q : K[X], q.aeval (ad K _ (φ x)) = ad K _ y := by
      obtain ⟨r, hr⟩ : ∃ r : K[X], r.aeval (ad K _ s) = ad K _ y := by
        have h₁ (i j : I) : ⁅s, v.end (i, j)⁆ = (μ i - μ j) • v.end (i, j) := by
          rw [instLieRingModule_eq, v.lie_end_of_apply_eq_smul μ s hsv]
        have h₂ (i j : I) : ⁅y, v.end (i, j)⁆ = (fμ i - fμ j) • v.end (i, j) := by
          rw [instLieRingModule_eq, v.lie_end_of_apply_eq_smul fμ y hyv]
        obtain ⟨r, hr⟩ := exists_polynomial_eval_sub_aux μ hμ f
        refine ⟨r, v.end.ext fun ⟨i, j⟩ ↦ ?_⟩
        rw [ad_apply, ← instLieRingModule_eq, aeval_apply_of_mem_apply_eq_smul (h₁ i j), hr, h₂]
        rfl
      obtain ⟨p, hp⟩ : ∃ p : K[X], p.aeval (ad K _ (φ x)) = ad K _ s :=
        adjoin_mem_exists_aeval K _ <| by
          simpa only [← hX_ns] using! ad_mem_adjoin_of_isSemisimple hns hn_nil hs_ss
      exact ⟨r.comp p, by rw [aeval_comp, hp, hr]⟩
    rw [instLieRingModule_eq, ← ad_apply K, ← hq]
    apply q.aeval_apply_smul_mem_of_le_comap hz _ ?_
    rintro - ⟨w, rfl⟩
    exact ⟨⁅x, w⁆, LieHom.map_lie φ x w⟩
  /- Using Lagrange interpolation again we can show that `n` and `y` commute. -/
  have hny_comm : Commute n y := by
    suffices y ∈ K[s] from commute_of_mem_adjoin_singleton_of_commute this hns
    rw [adjoin_singleton_eq_range_aeval]
    obtain ⟨q, hq⟩ : ∃ q : K[X], ∀ i, q.eval (μ i) = fμ i :=
      (Polynomial.exists_eval_eq_iff μ fμ).mpr <| by aesop
    refine ⟨q, v.ext fun i ↦ ?_⟩
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_apply_of_mem_apply_eq_smul (hsv i), hq, hyv]
  /- By general results we need only prove `trace K M (φ x * y) = ∑ i, fμ i * μ i`. -/
  suffices trace K M (φ x * y) = ∑ i, fμ i * μ i from
    ⟨y, trace_toEnd_mul_eq_zero_of_traceForm_eq_zero h y hy_range x hx, this⟩
  /- And this is an easy calculation. -/
  have htr_n : trace K M (n * y) = 0 :=
    (isNilpotent_trace_of_isNilpotent (hny_comm.isNilpotent_mul_right hn_nil)).eq_zero
  have htr_s : trace K M (s * y) = ∑ i, fμ i * μ i := by
    rw [trace_eq_matrix_trace _ v, Matrix.trace]
    exact Finset.sum_congr rfl <| by simp [toMatrix_apply, hyv, hsv]
  rw [hX_ns, add_mul, map_add, htr_n, htr_s, zero_add]


/-- If the trace form of `M` is zero, then the `⁅L, L⁆`-module `M` is nilpotent. -/
public theorem isNilpotent_derivedSeries_of_traceForm_eq_zero
    [Module R M] [LieModule R L M] [IsNoetherian R M] [Module.Free R M]
    (h : traceForm R L M = 0) :
    IsNilpotent (derivedSeries R L 1) M := by
  set A := AlgebraicClosure (FractionRing R)
  have _i : FaithfulSMul R A := FaithfulSMul.trans R (FractionRing R) A
  have nilp_ext : IsNilpotent (derivedSeries A (A ⊗[R] L) 1) (A ⊗[R] M) := by
    apply isNilpotent_derivedSeries_of_traceForm_eq_zero_aux
    simpa
  rw [isNilpotent_iff_forall' (R := R)]
  rw [isNilpotent_iff_forall' (R := A)] at nilp_ext
  intro ⟨x, hx⟩
  have hx_ext : 1 ⊗ₜ[R] x ∈ derivedSeries A (A ⊗[R] L) 1 := by
    rw [derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have hbc_inj : Injective (End.baseChangeHom R A M) := LinearMap.baseChangeHom_injective R M A
  have aux : (toEnd R (derivedSeries R L 1) M ⟨x, hx⟩).baseChangeHom R A M =
      (toEnd R L M x).baseChange A := rfl
  rw [← IsNilpotent.map_iff hbc_inj, aux, ← toEnd_baseChange]
  exact nilp_ext ⟨_, hx_ext⟩

section
variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

private lemma bracket_mem_ideal_sup_span (I : LieIdeal K L) (a : L)
    {x y : L} (hx : x ∈ I.toSubmodule ⊔ K ∙ a) (hy : y ∈ I.toSubmodule ⊔ K ∙ a) :
    ⁅x,y⁆ ∈ I := by
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hw
  simp only [add_lie, lie_add, lie_smul, smul_lie, lie_self, smul_zero, add_zero]
  exact I.add_mem (I.add_mem (I.lie_mem hv) (I.smul_mem c (I.lie_mem hv)))
    (I.smul_mem d (lie_mem_left K L I u a hu))

private def idealSupSpan (I : LieIdeal K L) (a : L) : LieSubalgebra K L :=
  { I.toSubmodule ⊔ K ∙ a with
    lie_mem' := fun hx hy =>
      show ⁅_,_⁆ ∈ I.toSubmodule ⊔ K ∙ a from
        (show I.toSubmodule ≤ I.toSubmodule ⊔ K ∙ a from le_sup_left)
          (bracket_mem_ideal_sup_span I a hx hy) }

private lemma idealSupSpan_solvable (I : LieIdeal K L) [IsSolvable I] (a : L) :
    IsSolvable (idealSupSpan I a) := by
  let S := idealSupSpan I a
  let J := I.comap S.incl
  let f : J →ₗ⁅K⁆ I :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      map_lie' := rfl }
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    change (f x).val = (f y).val
    exact congrArg Subtype.val h
  have : IsSolvable J := hf.lieAlgebra_isSolvable
  have hder : derivedSeries K S 1 ≤ J := by
    change (derivedSeries K S 1 : LieSubalgebra K S).toSubmodule ≤ J.toSubmodule
    rw [coe_derivedSeries_one_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨x,y,rfl⟩
    exact bracket_mem_ideal_sup_span I a x.property y.property
  obtain ⟨n, hn⟩ := IsSolvable.solvable K J
  have hn' := (J.derivedSeries_eq_bot_iff n).mp hn
  apply IsSolvable.mk (R := K) (k := n + 1)
  apply le_antisymm _ bot_le
  calc
    derivedSeries K S (n + 1) = derivedSeriesOfIdeal K S n (derivedSeries K S 1) :=
      derivedSeriesOfIdeal_add ⊤ n 1
    _ ≤ derivedSeriesOfIdeal K S n J := derivedSeriesOfIdeal_mono hder n
    _ = ⊥ := hn'
end

private lemma strictTriangular_of_charpoly_eq_X_pow
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype ι] [DecidableEq ι] [LinearOrder ι]
    (B : Basis ι K V) (f : V →ₗ[K] V)
    (h : (toMatrix B B f).IsUpperTriangular)
    (hc : f.charpoly = X ^ finrank K V) :
    Matrix.IsStrictlyUpperTriangular (toMatrix B B f) := by
  have hd (i : ι) : toMatrix B B f i i = 0 := by
    have he : ((toMatrix B B f).charpoly).eval (toMatrix B B f i i) = 0 := by
      rw [Matrix.charpoly_of_isUpperTriangular _ h, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [f.charpoly_toMatrix B, hc, Polynomial.eval_pow, Polynomial.eval_X] at he
    exact (eq_zero_of_pow_eq_zero he)
  intro i j hij
  rcases hij.eq_or_lt with he | he
  · subst j
    exact hd i
  · exact h he

section
variable {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
  [LieRing L] [LieAlgebra K L] [FiniteDimensional K L] [Nontrivial L]

/-- The two triangularizations show that a solvable ideal is orthogonal to brackets. -/
private lemma killingForm_lie_of_solvable_ideal (I : LieIdeal K L) [IsSolvable I]
    (r : L) (hr : r ∈ I) (a b : L) : killingForm K L r ⁅a,b⁆ = 0 := by
  let S := idealSupSpan I a
  have : IsSolvable S := idealSupSpan_solvable I a
  obtain ⟨B, hB⟩ := LieModule.lie_class K S (V := L) (Module.finBasis K L)
  let rS : S := ⟨r, (show I.toSubmodule ≤ I.toSubmodule ⊔ K ∙ a from le_sup_left) hr⟩
  let aS : S := ⟨a, (show K ∙ a ≤ I.toSubmodule ⊔ K ∙ a from le_sup_right)
    (Submodule.mem_span_singleton_self a)⟩
  have hz : ⁅rS,aS⁆ ∈ derivedSeries K S 1 := by
    rw [derivedSeries_def, show (1 : ℕ) = 0 + 1 from rfl,
      derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  have hs := LieModule.lie_class2 K S (V := L) B hB ⟨⁅rS,aS⁆, hz⟩
  change Matrix.IsStrictlyUpperTriangular (toMatrix B B (ad K L ⁅r,a⁆)) at hs
  have hc : (ad K L ⁅r,a⁆).charpoly = X ^ finrank K L := by
    rw [← (ad K L ⁅r,a⁆).charpoly_toMatrix B]
    have hupper : (toMatrix B B (ad K L ⁅r,a⁆)).IsUpperTriangular :=
      fun i j hij => hs hij.le
    rw [Matrix.charpoly_of_isUpperTriangular _ hupper]
    simp only [hs le_rfl, map_zero, sub_zero, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  let T := idealSupSpan I b
  have : IsSolvable T := idealSupSpan_solvable I b
  obtain ⟨C, hC⟩ := LieModule.lie_class K T (V := L) (Module.finBasis K L)
  let zT : T := ⟨⁅r,a⁆, (show I.toSubmodule ≤ I.toSubmodule ⊔ K ∙ b from le_sup_left)
    (lie_mem_left K L I r a hr)⟩
  let bT : T := ⟨b, (show K ∙ b ≤ I.toSubmodule ⊔ K ∙ b from le_sup_right)
    (Submodule.mem_span_singleton_self b)⟩
  have hstrict := strictTriangular_of_charpoly_eq_X_pow C (ad K L ⁅r,a⁆) (hC zT) hc
  rw [← LieModule.traceForm_apply_lie_apply K L L, killingForm_apply_apply,
    trace_eq_matrix_trace K C, toMatrix_comp C C C]
  rw [Matrix.trace_mul_comm]
  exact ((hC bT).mul_strictlyUpperTriangular hstrict).trace_eq_zero
end

private lemma killingForm_eq_zero_of_solvable_ideal_aux
    {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    (I : LieIdeal K L) [IsSolvable I] (r : L) (hr : r ∈ I)
    (y : L) (hy : y ∈ derivedSeries K L 1) : killingForm K L r y = 0 := by
  rcases subsingleton_or_nontrivial L with h | h
  · have : r = 0 := Subsingleton.elim _ _
    simp [this]
  · change y ∈ (derivedSeries K L 1 : LieSubalgebra K L).toSubmodule at hy
    rw [coe_derivedSeries_one_eq] at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a,b,rfl⟩ := hz
      exact killingForm_lie_of_solvable_ideal I r hr a b
    | zero => simp
    | add z w hz hw ihz ihw => simp [map_add, ihz, ihw]
    | smul c z hz ih => simp [map_smul, ih]

end LieModule

open LieAlgebra
open scoped TensorProduct

/-- A solvable ideal is orthogonal to the derived algebra for the ambient Killing form. -/
public lemma LieIdeal.le_killingCompl_derived_of_isSolvable
    {R L : Type*} [CommRing R] [CharZero R] [IsDomain R]
    [LieRing L] [LieAlgebra R L] [IsNoetherian R L] [Module.Free R L]
    (I : LieIdeal R L) [IsSolvable I] :
    I ≤ (derivedSeries R L 1).killingCompl R L := by
  let A := AlgebraicClosure (FractionRing R)
  have : FaithfulSMul R A := FaithfulSMul.trans R (FractionRing R) A
  let IA : LieIdeal A (A ⊗[R] L) := I.baseChange A
  have : IsSolvable IA := by
    obtain ⟨n, hn⟩ := IsSolvable.solvable R I
    apply (isSolvable_iff A _).mpr
    refine ⟨n, (IA.derivedSeries_eq_bot_iff n).mpr ?_⟩
    change derivedSeriesOfIdeal A (A ⊗[R] L) n (I.baseChange A) = ⊥
    rw [derivedSeriesOfIdeal_baseChange, (I.derivedSeries_eq_bot_iff n).mp hn,
      LieSubmodule.baseChange_bot]
  intro r hr
  rw [LieIdeal.mem_killingCompl]
  intro y hy
  have hr_ext : 1 ⊗ₜ[R] r ∈ I.baseChange A :=
    LieSubmodule.tmul_mem_baseChange_of_mem 1 hr
  have hy_ext : 1 ⊗ₜ[R] y ∈ derivedSeries A (A ⊗[R] L) 1 := by
    rw [derivedSeries_baseChange]
    exact LieSubmodule.tmul_mem_baseChange_of_mem 1 hy
  have key := LieModule.killingForm_eq_zero_of_solvable_ideal_aux IA
    (1 ⊗ₜ[R] r) hr_ext (1 ⊗ₜ[R] y) hy_ext
  simp only [killingForm, LieModule.traceForm_baseChange,
    LinearMap.BilinForm.baseChange_tmul, mul_one, ← Algebra.algebraMap_eq_smul_one] at key
  rw [LieModule.traceForm_comm]
  exact FaithfulSMul.algebraMap_injective R A (by rwa [map_zero])

variable [IsNoetherian R L] [Module.Free R L]

open LieAlgebra in
/-- A convenience variation of `LieAlgebra.isSolvable_of_forall_derived_killingForm_eq_zero` for
working with ideals.

Over a principal ideal domain by `LieIdeal.killingForm_eq` this is just a specialisation of
`LieAlgebra.isSolvable_of_killingForm_apply_lie_eq_zero` but since it does not require the PID
assumption, it is a slightly stronger result. -/
public theorem LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero (I : LieIdeal R L)
    (h : ∀ x ∈ I, ∀ y ∈ ⁅I, I⁆, killingForm R L x y = 0) :
    IsSolvable I := by
  set DI : LieIdeal R L := ⁅I, I⁆
  set DDI : LieIdeal R L := ⁅DI, DI⁆
  have tf_eq_zero : LieModule.traceForm R DI L = 0 := by
    ext ⟨x, hx⟩ ⟨y, hy⟩
    change killingForm R L x y = 0
    exact h x (LieSubmodule.lie_le_left I I hx) y hy
  have module_nilp : LieModule.IsNilpotent (derivedSeries R DI 1) L :=
    LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero tf_eq_zero
  have ring_nilp : LieRing.IsNilpotent DDI := by
    rw [LieAlgebra.isNilpotent_iff_forall (R := R)]
    rintro ⟨x, hx⟩
    apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad (DDI : LieSubalgebra R L) (x := ⟨x, hx⟩)
    refine (LieModule.isNilpotent_iff_forall' (R := R)).mp module_nilp
      ⟨⟨x, LieSubmodule.lie_le_left DI DI hx⟩, ?_⟩
    rwa [derivedSeries_eq_derivedSeriesOfIdeal_comap, mem_comap]
  obtain ⟨k, hk⟩ := IsSolvable.solvable R DDI
  rw [derivedSeries_eq_bot_iff] at hk
  refine IsSolvable.mk (k := k + 2) ((derivedSeries_eq_bot_iff I (k + 2)).mpr ?_)
  rwa [derivedSeriesOfIdeal_add, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_succ,
    derivedSeriesOfIdeal_zero]

namespace LieAlgebra

/-- **Cartan's criterion for solvability**: if the Killing form of `L` vanishes on `L × ⁅L, L⁆`,
then `L` is solvable. -/
public lemma isSolvable_of_killingForm_apply_lie_eq_zero
    (h : ∀ x, ∀ y ∈ derivedSeries R L 1, killingForm R L x y = 0) :
    IsSolvable L := by
  suffices IsSolvable (⊤ : LieIdeal R L) by
    rwa [← solvable_iff_equiv_solvable LieSubalgebra.topEquiv (R := R)]
  apply LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero
  aesop

/-- The solvable radical is the Killing-orthogonal complement of the derived algebra. -/
public lemma radical_eq_killingCompl_derived :
    radical R L = (derivedSeries R L 1).killingCompl R L := by
  apply le_antisymm
  · exact LieIdeal.le_killingCompl_derived_of_isSolvable (radical R L)
  · rw [← LieIdeal.solvable_iff_le_radical]
    apply LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero
    intro x hx y hy
    rw [LieModule.traceForm_comm]
    apply (LieIdeal.mem_killingCompl R L _).mp hx y
    change y ∈ ⁅(⊤ : LieIdeal R L), ⊤⁆
    exact LieSubmodule.mono_lie le_top le_top hy

/-- The converse of Cartan's criterion for solvability: the Killing form of a solvable
Lie algebra vanishes on `L × ⁅L, L⁆`. -/
public lemma killingForm_apply_lie_eq_zero_of_IsSolvable
    [IsSolvable L] : ∀ x, ∀ y ∈ derivedSeries R L 1, killingForm R L x y = 0 := by
  have htop : (derivedSeries R L 1).killingCompl R L = ⊤ := by
    rw [← radical_eq_killingCompl_derived, radical_eq_top_of_isSolvable]
  intro x y hy
  rw [LieModule.traceForm_comm]
  exact (LieIdeal.mem_killingCompl R L _).mp (htop ▸ LieSubmodule.mem_top x) y hy


variable (R L)

/-- The Killing radical of a finite-dimensional Lie algebra is contained in the solvable radical. -/
public lemma killingCompl_top_le_radical :
    LieIdeal.killingCompl R L ⊤ ≤ radical R L := by
  rw [← LieIdeal.solvable_iff_le_radical]
  refine LieIdeal.isSolvable_of_killingForm_apply_lie_eq_zero _ ?_
  intro x hx y _
  rw [LieModule.traceForm_comm]
  exact (LieIdeal.mem_killingCompl R L ⊤).mp hx y (LieSubmodule.mem_top y)

/-- **Cartan's criterion for semisimplicity**: if a finite-dimensional Lie algebra has trivial
solvable radical, then its Killing form is non-degenerate.

See also `LieAlgebra.hasTrivialRadical_iff_isKilling`. -/
public instance HasTrivialRadical.instIsKilling [HasTrivialRadical R L] : IsKilling R L where
  killingCompl_top_eq_bot := by simpa using killingCompl_top_le_radical R L

public lemma hasTrivialRadical_iff_isKilling [IsPrincipalIdealRing R] :
    HasTrivialRadical R L ↔ IsKilling R L :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩

example (A : Type*) [LieRing A] [Module.Finite ℤ A] [Module.Free ℤ A] :
    HasTrivialRadical ℤ A ↔ IsKilling ℤ A :=
  hasTrivialRadical_iff_isKilling ℤ A

end LieAlgebra
