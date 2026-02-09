/-
Copyright (c) 2025 [Authors]. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Authors]
-/
module

import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Jordan-Chevalley decomposition and the adjoint representation

This file proves that the Jordan-Chevalley decomposition commutes with the adjoint
representation: if `a = s + n` is the decomposition into semisimple and nilpotent parts
in an associative algebra `A`, then `ad(a) = ad(s) + ad(n)` is the Jordan-Chevalley
decomposition of `ad(a)` in `End(A)`.

The key result is `LieAlgebra.ad_isSemisimple_of_isSemisimple`, the semisimple analogue of the
existing `LieAlgebra.ad_nilpotent_of_nilpotent`.

## Main results

* `LinearMap.isSemisimple_mulLeft_of_isSemisimple`: left multiplication by a semisimple element
  is semisimple.
* `LinearMap.isSemisimple_mulRight_of_isSemisimple`: right multiplication by a semisimple element
  is semisimple.
* `LieAlgebra.ad_isSemisimple_of_isSemisimple`: the adjoint of a semisimple element is semisimple.

## References

* [Humphreys, *Introduction to Lie Algebras and Representation Theory*, §4.2]
-/

set_option linter.privateModule false

open Algebra Polynomial LinearMap Module.End

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

section MulLeftRight

omit [FiniteDimensional K V] in
/-- Polynomial evaluation of `mulRight K a` applied to `T` equals `T * (aeval a p)`.
This is the key identity for `mulRight`, proved using `pow_mulRight`. -/
private lemma aeval_mulRight_apply (a : Module.End K V) (p : K[X]) (T : Module.End K V) :
    (aeval (mulRight K a) p) T = T * aeval a p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, add_apply, hp, hq, mul_add]
  | monomial n c =>
    simp only [aeval_monomial, ← Algebra.smul_def, smul_apply, mul_smul_comm,
        pow_mulRight, mulRight_apply]

/-- Left multiplication by a semisimple element is semisimple.

If `a : End K V` is a semisimple endomorphism, then `mulLeft K a : End K (End K V)` is
semisimple. The proof uses that `Algebra.lmul` is an algebra homomorphism, so it preserves
the squarefreeness of the minimal polynomial. -/
theorem LinearMap.isSemisimple_mulLeft_of_isSemisimple
    {a : Module.End K V} (ha : a.IsSemisimple) :
    IsSemisimple (mulLeft K a) := by
  apply isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  have : aeval (Algebra.lmul K (Module.End K V) a) (minpoly K a) = 0 := by
    rw [aeval_algHom_apply, minpoly.aeval, map_zero]
  simpa using this

/-- Right multiplication by a semisimple element is semisimple.

If `a : End K V` is a semisimple endomorphism, then `mulRight K a : End K (End K V)` is
semisimple. The proof uses `pow_mulRight` to show that polynomial evaluation commutes
with `mulRight`. -/
theorem LinearMap.isSemisimple_mulRight_of_isSemisimple
    {a : Module.End K V} (ha : a.IsSemisimple) :
    IsSemisimple (mulRight K a) := by
  apply isSemisimple_of_squarefree_aeval_eq_zero ha.minpoly_squarefree
  ext1 T
  simp only [zero_apply, aeval_mulRight_apply, minpoly.aeval, mul_zero]

end MulLeftRight

section Ad

/-- **The adjoint of a semisimple element is semisimple.**

If `a : End K V` is a semisimple endomorphism, then `ad K (End K V) a` (the Lie bracket
`[a, ·]`) is a semisimple endomorphism of `End K V`.

The proof uses:
* `ad = mulLeft - mulRight` (`LieAlgebra.ad_eq_lmul_left_sub_lmul_right`)
* `mulLeft K a` is semisimple (`isSemisimple_mulLeft_of_isSemisimple`)
* `mulRight K a` is semisimple (`isSemisimple_mulRight_of_isSemisimple`)
* `mulLeft K a` and `mulRight K a` commute (`commute_mulLeft_right`)
* Difference of commuting semisimple endomorphisms is semisimple
  (`IsSemisimple.sub_of_commute`, requires `PerfectField`)

This is the semisimple analogue of `LieAlgebra.ad_nilpotent_of_nilpotent`. -/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple [PerfectField K]
    {a : Module.End K V} (ha : a.IsSemisimple) :
    (LieAlgebra.ad K (Module.End K V) a).IsSemisimple := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  exact (isSemisimple_mulLeft_of_isSemisimple ha).sub_of_commute
    (LinearMap.commute_mulLeft_right a a)
    (isSemisimple_mulRight_of_isSemisimple ha)

end Ad
