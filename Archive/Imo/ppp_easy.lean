/-
Copyright (c) 2025 Janos Wolosz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Janos Wolosz
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Card

/-!
# PPP easy

Let 2 ≤ n and let P be a set of permutations acting on [n] = {0, 1, 2, ..., n-1}.
Assume that the set P acts transitively (that is, in a finite number of steps any element
of [n] can be moved to any other element). Assume that we color red more than half of the
elements of [n]. Take two distinct elements of [n], {a, b}. We will act on these with the
elements of P. Show that in a finite number of steps {a, b} can be pushed to a red-red position.

## Main results

* `pppeasy`: Given a transitive permutation group action with more than half elements colored red,
  any pair of distinct elements can be moved to a position where both land on red elements.
-/

namespace PPPEasy

/-- Given a transitive set of permutations on Fin n, if more than n/2 elements
are colored red, then any two distinct elements a and b can be moved by a composition
of permutations from P to positions that are both red. -/
theorem pppeasy (n : ℕ) (hn : 2 ≤ n) (P : Set (Equiv.Perm (Fin n)))
    (h_trans : ∀ i j : Fin n, ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))), (∀ p ∈ perms, p ∈ P) ∧ σ = perms.foldl (· * ·) 1) ∧
      σ i = j)
    (red : Set (Fin n)) (h_red : (n : ℚ) / 2 < (red.ncard : ℚ))
    (a b : Fin n) (hab : a ≠ b) :
    ∃ (σ : Equiv.Perm (Fin n)),
      (∃ (perms : List (Equiv.Perm (Fin n))), (∀ p ∈ perms, p ∈ P) ∧ σ = perms.foldl (· * ·) 1) ∧
      σ a ∈ red ∧ σ b ∈ red := by
  sorry

end PPPEasy
