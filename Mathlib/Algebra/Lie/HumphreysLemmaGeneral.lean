/-
Humphreys' Lemma — General case (Introduction to Lie Algebras, §4.3)

This file proves Humphreys' lemma over arbitrary fields of characteristic zero
by scalar extension to the algebraic closure, reducing to the algebraically closed
version stated in `Mathlib.HumphreysLemma`.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Algebra.Lie.HumphreysLemma

open scoped TensorProduct
open LinearMap


-- Obstacle 1: baseChangeHom is injective for field extensions.
-- This follows from: over a field, v ↦ 1 ⊗ v is injective (free modules).
-- Mathlib has Algebra.TensorProduct.mk_one_injective_of_isScalarTower
-- but it requires [Module S M] [IsScalarTower R S M] which doesn't apply here.
-- TODO: prove using a basis argument or Module.Flat/FaithfullyFlat.
lemma Module.End.baseChangeHom_injective
    (K : Type*) [Field K]
    (Kbar : Type*) [Field Kbar] [Algebra K Kbar]
    (V : Type*) [AddCommGroup V] [Module K V] [FiniteDimensional K V] :
    Function.Injective (Module.End.baseChangeHom K Kbar V) := by
  intro f g hfg
  ext v
  -- f.baseChange Kbar (1 ⊗ v) = g.baseChange Kbar (1 ⊗ v)
  have h : (1 : Kbar) ⊗ₜ[K] f v = (1 : Kbar) ⊗ₜ[K] g v := by
    have := LinearMap.congr_fun hfg ((1 : Kbar) ⊗ₜ[K] v)
    change (f.baseChange Kbar) (1 ⊗ₜ v) = (g.baseChange Kbar) (1 ⊗ₜ v) at this
    simp only [LinearMap.baseChange_tmul] at this
    exact this
  -- Use injectivity of v ↦ 1 ⊗ₜ v (FaithfullyFlat over a field)
  exact Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := Kbar) V h

section BaseChangeLemmas

variable {K : Type*} [Field K] {Kbar : Type*} [Field Kbar] [Algebra K Kbar]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The IsBaseChange equivalence `Kbar ⊗ End_K(V) ≃ End_Kbar(Kbar ⊗ V)` sends
`1 ⊗ₜ f` to `f.baseChange Kbar`. -/
private lemma isBaseChange_end_equiv_tmul_one (f : Module.End K V) :
    ((TensorProduct.isBaseChange K V Kbar).end).equiv (1 ⊗ₜ f) = f.baseChange Kbar := by
  rw [IsBaseChange.equiv_tmul, one_smul]
  apply (TensorProduct.isBaseChange K V Kbar).algHom_ext
  intro v
  rw [IsBaseChange.endHom_comp_apply]
  change (1 : Kbar) ⊗ₜ[K] f v = f.baseChange Kbar ((1 : Kbar) ⊗ₜ[K] v)
  simp [baseChange_tmul]

/-- For flat `Kbar/K`, `ker(f.baseChange Kbar) = (ker f).baseChange Kbar`. -/
private lemma ker_baseChange_eq {N P : Type*} [AddCommGroup N] [AddCommGroup P]
    [Module K N] [Module K P] (f : N →ₗ[K] P) :
    LinearMap.ker (f.baseChange Kbar) =
      (LinearMap.ker f).baseChange (Kbar) := by
  change LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor Kbar Kbar f) = _
  rw [Module.Flat.ker_lTensor_eq]
  rfl

/-- The piRight equivalence relates `Φ.baseChange` to component-wise `baseChange`. -/
private lemma piRight_baseChange_component {N : Type*} [AddCommGroup N] [Module K N]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (Φ : N →ₗ[K] (ι → Q)) (w : Kbar ⊗[K] N) (i : ι) :
    TensorProduct.piRight K Kbar Kbar (fun _ : ι => Q) (Φ.baseChange Kbar w) i =
      ((LinearMap.proj i).comp Φ).baseChange Kbar w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => simp [LinearMap.baseChange_tmul, TensorProduct.piRight]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- If each Pi component of `Φ.baseChange` vanishes, then `Φ.baseChange` vanishes. -/
private lemma baseChange_pi_eq_zero {N : Type*} [AddCommGroup N] [Module K N]
    {ι : Type*} [Finite ι]
    {Q : Type*} [AddCommGroup Q] [Module K Q]
    (Φ : N →ₗ[K] (ι → Q)) (w : Kbar ⊗[K] N)
    (h : ∀ i, ((LinearMap.proj i).comp Φ).baseChange Kbar w = 0) :
    Φ.baseChange Kbar w = 0 := by
  have := Fintype.ofFinite ι
  classical
  let e := TensorProduct.piRight K Kbar Kbar (fun _ : ι => Q)
  suffices e (Φ.baseChange Kbar w) = 0 from
    e.injective.eq_iff.mp (this.trans e.map_zero.symm)
  ext i
  rw [piRight_baseChange_component, h i, Pi.zero_apply]

end BaseChangeLemmas

/-- Humphreys' Lemma over arbitrary fields of characteristic zero.

Proved by scalar extension to the algebraic closure, then applying the
algebraically closed version. -/
theorem humphreys_lemma
    {K : Type*} [Field K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (htr : ∀ z : Module.End K V, (∀ b ∈ B, ⁅z, b⁆ ∈ A) →
           trace K V (x * z) = 0) :
    IsNilpotent x := by
  -- Set up the algebraic closure
  let Kbar := AlgebraicClosure K
  -- Step 1: x is nilpotent iff x.baseChange Kbar is nilpotent
  rw [show IsNilpotent x ↔ IsNilpotent (Module.End.baseChangeHom K Kbar V x) from
    (IsNilpotent.map_iff (Module.End.baseChangeHom_injective K Kbar V)).symm]
  -- Now our goal is: IsNilpotent (x.baseChange Kbar)
  -- Step 2: Define A', B' as Kbar-submodules of End Kbar Vbar via base change
  let Vbar := Kbar ⊗[K] V
  let bc : Module.End K V → Module.End Kbar Vbar := fun f => f.baseChange Kbar
  let A' : Submodule Kbar (Module.End Kbar Vbar) := Submodule.span Kbar (bc '' ↑A)
  let B' : Submodule Kbar (Module.End Kbar Vbar) := Submodule.span Kbar (bc '' ↑B)
  -- Step 3: Apply the algebraically closed version
  apply humphreys_lemma_algClosed A' B'
  -- Subgoal 1: A' ≤ B'
  · exact Submodule.span_mono (Set.image_mono hAB)
  -- Subgoal 2: ∀ b' ∈ B', ⁅x.baseChange Kbar, b'⁆ ∈ A'
  · -- Obstacle 2: Lie bracket commutes with baseChange, then extend by linearity
    intro b' hb'
    induction hb' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨b, hb, rfl⟩ := h
      rw [show ⁅(Module.End.baseChangeHom K Kbar V) x, bc b⁆ =
            (Module.End.baseChangeHom K Kbar V) ⁅x, b⁆ from by
        change ⁅(Module.End.baseChangeHom K Kbar V) x,
               (Module.End.baseChangeHom K Kbar V) b⁆ = _
        simp only [Ring.lie_def, map_sub, map_mul]]
      exact Submodule.subset_span ⟨⁅x, b⁆, hxM b hb, rfl⟩
    | zero => rw [lie_zero]; exact A'.zero_mem
    | add _ _ _ _ ha hb => rw [lie_add]; exact A'.add_mem ha hb
    | smul c _ _ hb => rw [lie_smul]; exact A'.smul_mem c hb
  -- Subgoal 3: trace condition on the algebraic closure
  · -- Obstacle 3: trace condition extends to the algebraic closure
    intro z hz
    -- Step 1: tr(x' * ·) vanishes on span_Kbar(bc '' M) where M = {w | [w,B] ⊆ A}
    have trace_vanish : ∀ w ∈ Submodule.span Kbar
        (bc '' {w : Module.End K V | ∀ b ∈ B, ⁅w, b⁆ ∈ A}),
        (trace Kbar Vbar) ((Module.End.baseChangeHom K Kbar V) x * w) = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem _ hm =>
        obtain ⟨z₀, hz₀, rfl⟩ := hm
        have h1 : (Module.End.baseChangeHom K Kbar V) x * bc z₀ =
            (x * z₀).baseChange Kbar := by
          change (Module.End.baseChangeHom K Kbar V) x *
            (Module.End.baseChangeHom K Kbar V) z₀ = _
          exact (map_mul _ x z₀).symm
        rw [h1, LinearMap.trace_baseChange, htr z₀ hz₀, map_zero]
      | zero => rw [mul_zero, map_zero]
      | add _ _ _ _ ha hb => rw [mul_add, map_add, ha, hb, add_zero]
      | smul c _ _ hb => rw [mul_smul_comm, map_smul, hb, smul_zero]
    -- Step 2: z ∈ M' implies z ∈ span_Kbar(bc '' M) (flat base change)
    -- Then trace_vanish gives the result.
    apply trace_vanish
    -- Goal: z ∈ span_Kbar(bc '' {w | ∀ b ∈ B, ⁅w, b⁆ ∈ A})
    -- Strategy: use IsBaseChange equiv, flat base change, Pi decomposition.
    -- Set up the IsBaseChange equivalence e : Kbar ⊗ End_K(V) ≃ End_Kbar(Vbar)
    let e := (TensorProduct.isBaseChange K V Kbar).end.equiv
    -- Define M_sub as a K-submodule
    let M_sub : Submodule K (Module.End K V) :=
      { carrier := {w | ∀ b ∈ B, ⁅w, b⁆ ∈ A}
        zero_mem' := fun _ _ => by simp [A.zero_mem]
        add_mem' := fun ha hb c hc => by rw [add_lie]; exact A.add_mem (ha c hc) (hb c hc)
        smul_mem' := fun c _ ha b hb => by rw [smul_lie]; exact A.smul_mem c (ha b hb) }
    change z ∈ Submodule.span Kbar (bc '' ↑M_sub)
    -- Step 1: Rewrite span(bc '' M_sub) = map e (M_sub.baseChange)
    have hbc_eq : (bc '' ↑M_sub : Set _) =
        e '' (TensorProduct.mk K Kbar (Module.End K V) 1 '' ↑M_sub) := by
      ext y; constructor
      · rintro ⟨f, hf, rfl⟩
        exact ⟨1 ⊗ₜ f, ⟨f, hf, rfl⟩, isBaseChange_end_equiv_tmul_one f⟩
      · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
        exact ⟨f, hf, (isBaseChange_end_equiv_tmul_one f).symm⟩
    rw [hbc_eq]
    -- Convert ⇑e to ⇑e.toLinearMap (defeq but syntactically different for rw)
    change z ∈ Submodule.span Kbar (e.toLinearMap ''
      (⇑(TensorProduct.mk K Kbar (Module.End K V) 1) '' ↑M_sub))
    rw [Submodule.span_image, ← Submodule.baseChange_span, Submodule.span_eq,
        Submodule.mem_map_equiv]
    -- Goal: e.symm z ∈ M_sub.baseChange Kbar
    -- Step 2: Define Φ with ker Φ = M_sub
    set s := Module.finrank K ↥B
    let bB := Module.finBasis K ↥B
    let lieR : Fin s → (Module.End K V →ₗ[K] Module.End K V) := fun i =>
      LinearMap.mulRight K (bB i).1 - LinearMap.mulLeft K (bB i).1
    let φ : Fin s → (Module.End K V →ₗ[K] Module.End K V ⧸ A) := fun i =>
      (Submodule.mkQ A).comp (lieR i)
    let Φ := LinearMap.pi φ
    -- Step 3: ker Φ = M_sub
    have hkerΦ : LinearMap.ker Φ = M_sub := by
      ext w; constructor
      · intro hw
        change ∀ b ∈ B, ⁅w, b⁆ ∈ A
        -- Extract component info: ∀ i, lieR i w ∈ A
        have hbase : ∀ i : Fin s, ⁅w, (bB i).1⁆ ∈ A := by
          intro i
          have hi : φ i w = 0 := congr_fun (LinearMap.mem_ker.mp hw) i
          simp only [φ, LinearMap.comp_apply, Submodule.mkQ_apply,
            Submodule.Quotient.mk_eq_zero] at hi
          exact hi
        intro b hb
        -- Express b in terms of basis
        have hb_val : b = ∑ i : Fin s, (bB.repr ⟨b, hb⟩) i • (bB i).1 := by
          have h := bB.sum_repr ⟨b, hb⟩
          apply_fun B.subtype at h
          simp only [map_sum, map_smul, Submodule.subtype_apply] at h
          exact h.symm
        rw [Ring.lie_def, hb_val, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact A.sum_mem fun i _ => by
          rw [mul_smul_comm, smul_mul_assoc, ← smul_sub]
          exact A.smul_mem _ (by rw [← Ring.lie_def]; exact hbase i)
      · intro hw
        rw [LinearMap.mem_ker]; ext i
        simp only [Φ, LinearMap.pi_apply, φ, LinearMap.comp_apply, Submodule.mkQ_apply,
          Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        change (lieR i) w ∈ A
        have : (lieR i) w = ⁅w, (bB i).1⁆ := by
          simp [lieR, Ring.lie_def]
        rw [this]; exact hw (bB i).1 (bB i).2
    -- Step 4: By flat base change
    rw [← hkerΦ, ← ker_baseChange_eq, LinearMap.mem_ker]
    -- Goal: Φ.baseChange Kbar (e.symm z) = 0
    -- Step 5: Each Pi component is zero
    apply baseChange_pi_eq_zero; intro i
    have hcomp : (LinearMap.proj i).comp Φ = φ i := by ext; simp [Φ, φ]
    rw [hcomp]
    -- Goal: (φ i).baseChange Kbar (e.symm z) = 0
    -- Step 6: Decompose φ i = mkQ A ∘ lieR i
    change ((Submodule.mkQ A).comp (lieR i)).baseChange Kbar (e.symm z) = 0
    rw [LinearMap.baseChange_comp, LinearMap.comp_apply,
        ← LinearMap.mem_ker, ker_baseChange_eq, Submodule.ker_mkQ]
    -- Goal: (lieR i).baseChange Kbar (e.symm z) ∈ A.baseChange Kbar
    -- Step 7: How e acts on pure tensors
    have e_tmul : ∀ (a : Kbar) (g : Module.End K V),
        e (a ⊗ₜ g) = a • bc g := by
      intro a g
      have : a ⊗ₜ[K] g = a • ((1 : Kbar) ⊗ₜ[K] g) := by
        simp [TensorProduct.smul_tmul']
      rw [this, map_smul, isBaseChange_end_equiv_tmul_one]
    -- Step 8: Commutation relation: e((lieR i).baseChange(w)) = ⁅e(w), bc(bB i)⁆
    have hcomm : ∀ (w : Kbar ⊗[K] Module.End K V),
        e ((lieR i).baseChange Kbar w) = ⁅e w, bc (bB i).1⁆ := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero, zero_lie]
      | tmul a f =>
        simp only [LinearMap.baseChange_tmul, lieR, LinearMap.sub_apply,
          LinearMap.mulRight_apply, LinearMap.mulLeft_apply]
        rw [e_tmul, e_tmul]
        have : bc (f * ↑(bB i) - ↑(bB i) * f) = bc f * bc ↑(bB i) - bc ↑(bB i) * bc f := by
          have hbc : bc = ⇑(Module.End.baseChangeHom K Kbar V) := rfl
          simp only [hbc, map_sub, map_mul]
        rw [this, Ring.lie_def, smul_sub, smul_mul_assoc, mul_smul_comm]
      | add x y hx hy => rw [map_add, map_add, map_add, add_lie, hx, hy]
    -- Step 9: A' = map e (A.baseChange)
    have hA'_eq : A' = Submodule.map e.toLinearMap (A.baseChange Kbar) := by
      apply le_antisymm
      · -- A' ≤ map e (A.baseChange)
        apply Submodule.span_le.mpr
        rintro _ ⟨a, ha, rfl⟩
        change bc a ∈ Submodule.map e.toLinearMap (A.baseChange Kbar)
        exact ⟨1 ⊗ₜ a, Submodule.tmul_mem_baseChange_of_mem 1 ha,
          isBaseChange_end_equiv_tmul_one a⟩
      · -- map e (A.baseChange) ≤ A'
        rw [Submodule.baseChange_eq_span, ← Submodule.span_image]
        apply Submodule.span_mono
        rintro _ ⟨w, hw, rfl⟩
        obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hw
        exact ⟨a, ha, (isBaseChange_end_equiv_tmul_one a).symm⟩
    -- Step 10: Combine via suffices
    suffices e ((lieR i).baseChange Kbar (e.symm z)) ∈
        Submodule.map e.toLinearMap (A.baseChange Kbar) by
      rwa [Submodule.mem_map_equiv, e.symm_apply_apply] at this
    rw [← hA'_eq, hcomm (e.symm z), e.apply_symm_apply]
    exact hz (bc (bB i).1) (Submodule.subset_span ⟨(bB i).1, (bB i).2, rfl⟩)
