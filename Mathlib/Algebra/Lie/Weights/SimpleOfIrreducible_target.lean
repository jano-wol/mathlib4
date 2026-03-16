/-
Copyright (c) 2026 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
module

public import Mathlib.Algebra.Lie.Weights.IdealOrderIso_target
public import Mathlib.Algebra.Lie.Weights.Basic

/-! # Simplicity from irreducibility

A Killing Lie algebra with an irreducible root system is simple. This follows from the
order isomorphism between Lie ideals and invariant root submodules (`lieIdealOrderIso`).
-/

@[expose] public section

namespace LieAlgebra.IsKilling

open LieAlgebra LieModule RootPairing

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsKilling K L] [IsTriangularizable K H L]

theorem isSimple_of_isIrreducible (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L := by
  have : Nontrivial (Module.Dual K H) := hIrr.1
  have : IsSimpleOrder (LieIdeal K L) :=
    (lieIdealOrderIso (H := H)).isSimpleOrder_iff.mpr
      ((isIrreducible_iff_invtRootSubmodule _).mp hIrr)
  exact { eq_bot_or_eq_top := this.eq_bot_or_eq_top,
          non_abelian := fun h => by
            have : (⊤ : LieIdeal K L) = ⊥ :=
              @ideal_eq_bot_of_isLieAbelian K L _ _ _ _ _ _ _ _ ⊤
                ⟨fun ⟨x, _⟩ ⟨y, _⟩ => Subtype.ext (h.trivial x y)⟩
            exact absurd this top_ne_bot }

end LieAlgebra.IsKilling
