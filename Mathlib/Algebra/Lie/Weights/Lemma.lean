/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 211c7d16-4c18-4317-a033-6615ade2680a

The following was proved by Aristotle:

- theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl
-/

import Mathlib.Algebra.Lie.Killing

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieAlgebra.IsKilling K L]

namespace LieIdeal

/-- An ideal in a Killing Lie algebra is disjoint from its Killing orthogonal complement. -/
theorem disjoint_killingCompl (I : LieIdeal K L) : Disjoint I I.killingCompl := by
  rw [disjoint_iff]
  suffices IsLieAbelian (I ⊓ I.killingCompl : LieIdeal K L) from
    LieAlgebra.IsKilling.ideal_eq_bot_of_isLieAbelian _
  rw [LieSubmodule.lie_abelian_iff_lie_self_eq_bot, LieSubmodule.lie_eq_bot_iff]
  intro x ⟨_, hx⟩ y ⟨hy, _⟩
  suffices h : ∀ z, (LieModule.traceForm K L L) ⁅x, y⁆ z = 0 from
    (LieAlgebra.IsKilling.killingForm_nondegenerate K L).1 _ h
  intro z
  rw [LieModule.traceForm_apply_lie_apply K L L x y z, LieModule.traceForm_comm K L L]
  exact I.mem_killingCompl.mp hx _ (lie_mem_left K L I y z hy)

/-- An ideal in a Killing Lie algebra and its Killing orthogonal complement are complementary. -/
theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  rw [← LieSubmodule.isCompl_toSubmodule, I.toSubmodule_killingCompl]
  exact (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (LieModule.traceForm_isSymm K L L).isRefl).mpr
    (I.toSubmodule_killingCompl ▸ LieSubmodule.disjoint_toSubmodule.mpr (disjoint_killingCompl I))

/-- In a Killing Lie algebra, the lattice complement of an ideal equals its Killing orthogonal
complement. -/
theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl :=
  IsCompl.compl_eq (isCompl_killingCompl I)

end LieIdeal
