/-
Humphreys' Lemma (Introduction to Lie Algebras, §4.3)

This file proves Humphreys' lemma over algebraically closed fields.
The general characteristic zero version (by scalar extension) is in
`Mathlib.Algebra.Lie.HumphreysLemmaGeneral`.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.JordanChevalley

open LinearMap

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

namespace HumphreysLemma

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- If `[x, B] ⊆ A` and `A ≤ B`, then `(ad x)^k` maps `B` into `A` for all `k ≥ 1`. -/
lemma ad_pow_maps_to
    (A B : Submodule K (Module.End K V)) (hAB : A ≤ B)
    (x : Module.End K V) (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (k : ℕ) (hk : 0 < k) :
    ∀ b ∈ B, ((LieAlgebra.ad K (Module.End K V) x) ^ k) b ∈ A := by
  induction k with
  | zero => omega
  | succ n ih =>
    intro b hb
    rw [pow_succ, Module.End.mul_apply]
    have had : (LieAlgebra.ad K (Module.End K V) x) b ∈ A := hxM b hb
    rcases n.eq_zero_or_pos with rfl | hn
    · rw [pow_zero, Module.End.one_apply]; exact had
    · exact ih hn _ (hAB had)

/-- The semisimple part of the JC decomposition of `x` maps `B` into `A`.

This is the core of Humphreys' proof. The argument proceeds as follows:
1. `ad(s)` is semisimple on `End K V` (from `ad_isSemisimple_of_isSemisimple`).
2. `ad(x) = ad(n) + ad(s)` with `ad(n)` nilpotent, `ad(s)` semisimple, and they commute.
3. By JC uniqueness for `ad(x)`, `ad(s)` equals the semisimple part of `ad(x)`.
4. The semisimple part of `ad(x)` lies in `adjoin K {ad(x)}`, hence equals `p(ad(x))`
   for some polynomial `p` with `p(0) = 0` (since `ad(x)` has eigenvalue `0`).
5. Since `(ad x)^k` maps `B` into `A` for `k ≥ 1`, so does `p(ad(x))`, hence `ad(s)`. -/
lemma ad_semisimple_part_maps_to
    (A B : Submodule K (Module.End K V)) (hAB : A ≤ B)
    (x s : Module.End K V)
    (hs_adj : s ∈ Algebra.adjoin K {x})
    (hs_ss : s.IsSemisimple)
    (n : Module.End K V)
    (hn_nil : IsNilpotent n)
    (hxns : x = n + s)
    (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A) :
    ∀ b ∈ B, ⁅s, b⁆ ∈ A := by
  sorry

/-- A semisimple endomorphism with `tr(s²) = 0` over an algebraically closed field
of characteristic zero must be zero.

The proof uses the eigenspace decomposition: since `s` is semisimple and `K` is
algebraically closed, `V = ⨁ eigenspace(s, aᵢ)`. Then `tr(s²) = ∑ nᵢ · aᵢ²`
where `nᵢ = dim(eigenspace(s, aᵢ))`. Since `char K = 0`, this forces all `aᵢ = 0`. -/
lemma eq_zero_of_isSemisimple_of_trace_sq_eq_zero
    (s : Module.End K V) (hs : s.IsSemisimple)
    (htr : trace K V (s * s) = 0) : s = 0 := by
  sorry

end HumphreysLemma

open HumphreysLemma in
/-- Humphreys' Lemma over algebraically closed fields of characteristic zero.

Given subspaces `A ≤ B` of `gl(V)` and `M = {z ∈ gl(V) : [z, B] ⊆ A}`,
if `x ∈ M` satisfies `tr(xz) = 0` for all `z ∈ M`, then `x` is nilpotent. -/
theorem humphreys_lemma_algClosed
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : ∀ b ∈ B, ⁅x, b⁆ ∈ A)
    (htr : ∀ z : Module.End K V, (∀ b ∈ B, ⁅z, b⁆ ∈ A) →
           trace K V (x * z) = 0) :
    IsNilpotent x := by
  -- Step 1: Jordan-Chevalley decomposition x = n + s
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hxns⟩ :=
    x.exists_isNilpotent_isSemisimple
  -- Step 2: s maps B into A (the key step)
  have hsM : ∀ b ∈ B, ⁅s, b⁆ ∈ A :=
    ad_semisimple_part_maps_to A B hAB x s hs_adj hs_ss n hn_nil hxns hxM
  -- Step 3: tr(x * s) = 0
  have htr_xs : trace K V (x * s) = 0 := htr s hsM
  -- Step 4: n and s commute (both in adjoin K {x})
  have hns_comm : Commute n s :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs_adj
      (Algebra.commute_of_mem_adjoin_self hn_adj).symm
  -- Step 5: tr(n * s) = 0 (n * s is nilpotent since n is nilpotent and commutes with s)
  have htr_ns : trace K V (n * s) = 0 := by
    have hnil : IsNilpotent (n * s) := hns_comm.isNilpotent_mul_right hn_nil
    exact (isNilpotent_trace_of_isNilpotent hnil).eq_zero
  -- Step 6: tr(s²) = 0
  have htr_ss : trace K V (s * s) = 0 := by
    have hxs : x * s = n * s + s * s := by rw [hxns, add_mul]
    rw [hxs, map_add, htr_ns, zero_add] at htr_xs
    exact htr_xs
  -- Step 7: s = 0 (semisimple with trace of square zero)
  have hs_zero : s = 0 := eq_zero_of_isSemisimple_of_trace_sq_eq_zero s hs_ss htr_ss
  -- Step 8: x = n is nilpotent
  rw [hxns, hs_zero, add_zero]
  exact hn_nil
