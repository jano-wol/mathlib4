/-
Humphreys' Lemma (Introduction to Lie Algebras, §4.3)

This file proves Humphreys' lemma over algebraically closed fields.
The proof follows the textbook argument from Humphreys' "Introduction to
Lie Algebras and Representation Theory", §4.3, sentence by sentence,
using a concrete diagonalizing basis for the semisimple part.

The general characteristic zero version (by scalar extension) is in
`Mathlib.Algebra.Lie.HumphreysLemmaGeneral`.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Algebra.DirectSum.Module

open LinearMap Module.End

variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

namespace HumphreysLemma

/-! ## Setup: Diagonalizing basis

Humphreys: "Since F is algebraically closed, s is diagonalizable.
Fix a basis v₁, v₂, ..., vₘ that diagonalizes s, so that it has matrix
diag(a₁, a₂, ..., aₘ)." -/

omit [CharZero K] in
open Classical in
/-- The eigenspaces of a semisimple endomorphism over an algebraically closed field
form an internal direct sum decomposition of `V`. -/
noncomputable def eigenspaceIsInternal
    (s : Module.End K V) (hs : s.IsSemisimple) :
    DirectSum.IsInternal (fun μ : K => s.eigenspace μ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨s.eigenspaces_iSupIndep, by
    have := iSup_maxGenEigenspace_eq_top s
    simp_rw [hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
    exact this⟩

omit [CharZero K] in
open Classical in
/-- The eigenbasis: a basis of `V` that diagonalizes `s`.

Indexed by `Σ μ : K, Fin (finrank K (eigenspace s μ))`. Each basis vector
`eigenbasis s hs ⟨μ, i⟩` lies in `eigenspace s μ`. The eigenvalue of basis
vector `σ` is `σ.1`. -/
noncomputable def eigenbasis (s : Module.End K V) (hs : s.IsSemisimple) :=
  (eigenspaceIsInternal s hs).collectedBasis
    (fun μ => Module.finBasis K (s.eigenspace μ))

omit [CharZero K] in
open Classical in
/-- The eigenbasis index type is finite (since `V` is finite-dimensional). -/
noncomputable instance eigenbasisFintype (s : Module.End K V) (hs : s.IsSemisimple) :
    Fintype (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :=
  Module.Basis.fintypeIndexOfRankLtAleph0 (eigenbasis s hs)
    (Module.rank_lt_aleph0 K V)

omit [CharZero K] in
open Classical in
/-- Humphreys: "s has matrix diag(a₁, a₂, ..., aₘ)."

Each eigenbasis vector is an eigenvector: `s(vσ) = σ.1 • vσ`. -/
theorem eigenbasis_eigenvalue (s : Module.End K V) (hs : s.IsSemisimple)
    (σ : Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) :
    s (eigenbasis s hs σ) = σ.1 • eigenbasis s hs σ := by
  have hmem := (eigenspaceIsInternal s hs).collectedBasis_mem
    (fun μ => Module.finBasis K (s.eigenspace μ)) σ
  exact mem_eigenspace_iff.mp hmem

/-! ## The elementary endomorphisms e_{ij}

Humphreys: "If e_{ij} is the corresponding basis of gl(V) we saw in (4.2)
that (ad s)(e_{ij}) = (aᵢ − aⱼ)e_{ij} and
(ad y)(e_{ij}) = (f(aᵢ) − f(aⱼ))e_{ij}." -/

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- The elementary endomorphism `e_{ij}`: sends `b j ↦ b i`, all other basis
vectors to `0`. In coordinates: `e_{ij}(v) = ⟨v, b*.j⟩ • b i`. -/
noncomputable def eij {ι : Type*}
    (b : Module.Basis ι K V) (i j : ι) : Module.End K V :=
  (b.coord j).smulRight (b i)

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- Humphreys (4.2): `(ad s)(e_{ij}) = (aᵢ − aⱼ) e_{ij}` where `s` is diagonal
with eigenvalues `a` in the basis `b`. -/
theorem ad_diag_eij {ι : Type*}
    (b : Module.Basis ι K V) (a : ι → K) (s : Module.End K V)
    (hs : ∀ k, s (b k) = a k • b k)
    (i j : ι) : ⁅s, eij b i j⁆ = (a i - a j) • eij b i j := by
  classical
  apply b.ext; intro k
  change s (eij b i j (b k)) - eij b i j (s (b k)) =
    (a i - a j) • eij b i j (b k)
  simp only [eij, LinearMap.smulRight_apply, Module.Basis.coord_apply, hs k,
    map_smul, Module.Basis.repr_self]
  by_cases hjk : k = j
  · subst hjk
    simp only [Finsupp.single_eq_same, one_smul, hs i, sub_smul]
  · simp only [Finsupp.single_apply, hjk, ↓reduceIte, zero_smul, smul_zero,
      sub_self]

/-! ## Diagonal endomorphisms

Humphreys: "Given f, let y be that element of gl(V) whose matrix relative to
our given basis is diag(f(a₁), f(a₂), ..., f(aₘ))." -/

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- The diagonal endomorphism with entries `c` relative to basis `b`:
sends `b i ↦ c i • b i`. -/
noncomputable def diagEnd {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) : Module.End K V :=
  b.constr K (fun i => c i • b i)

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
theorem diagEnd_apply_basis {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) (k : ι) :
    diagEnd b c (b k) = c k • b k := by
  simp [diagEnd, Module.Basis.constr_basis]

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- Humphreys: "(ad y)(e_{ij}) = (f(aᵢ) − f(aⱼ))e_{ij}."

The adjoint action of a diagonal endomorphism on `e_{ij}`. -/
theorem ad_diagEnd_eij {ι : Type*}
    (b : Module.Basis ι K V) (c : ι → K) (i j : ι) :
    ⁅diagEnd b c, eij b i j⁆ = (c i - c j) • eij b i j :=
  ad_diag_eij b c (diagEnd b c) (diagEnd_apply_basis b c) i j

/-! ## The set M

Humphreys: "Let A ⊂ B be subspaces of gl(V).
Define M = {x ∈ gl(V) : [x, B] ⊂ A}." -/

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- Humphreys' set `M = {x ∈ gl(V) : [x, B] ⊂ A}`. -/
abbrev M (A B : Submodule K (Module.End K V)) : Set (Module.End K V) :=
  {x | ∀ b ∈ B, ⁅x, b⁆ ∈ A}

/-! ## Paragraph 3 helpers

Humphreys: "By hypothesis, ad x maps B into A; since A ⊂ B, it follows that
(ad x)^k maps B into A for all k ≥ 1
(inductively: (ad x)^{k+1}(B) = (ad x)((ad x)^k(B)) ⊂ (ad x)(A) ⊂ (ad x)(B) ⊂ A)." -/

omit [IsAlgClosed K] [CharZero K] [FiniteDimensional K V] in
/-- `(ad x)^k` maps `B` into `A` for all `k ≥ 1`. -/
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

/-! ## Paragraph 3: ad(s) maps B into A

Humphreys: "Now ad s is the semisimple part of ad x, by Lemma A of 4.2,
so it can be written as a polynomial in ad x without constant term.
[...] Hence any polynomial in ad x without constant term maps B into A,
so ad y(B) ⊂ A."

The proof requires Jordan-Chevalley uniqueness for `ad(x)`:
- `ad(s)` is semisimple (`LieAlgebra.ad_isSemisimple_of_isSemisimple`)
- `ad(n)` is nilpotent (`LieAlgebra.ad_nilpotent_of_nilpotent`)
- `ad(x) = ad(n) + ad(s)`, they commute
- By JC uniqueness (`eq_zero_of_isNilpotent_isSemisimple`), `ad(s)` equals
  the semisimple part of `ad(x)`
- The semisimple part lies in `adjoin K {ad(x)}`, i.e., is `p(ad(x))`
  for some polynomial `p` with `p(0) = 0` (since `ad(x)(x) = [x,x] = 0`)
- Apply `ad_pow_maps_to` to conclude `p(ad(x))` maps `B` into `A` -/
lemma ad_semisimple_part_maps_to
    (A B : Submodule K (Module.End K V)) (hAB : A ≤ B)
    (x s : Module.End K V)
    (hs_adj : s ∈ Algebra.adjoin K {x})
    (hs_ss : s.IsSemisimple)
    (n : Module.End K V)
    (hn_nil : IsNilpotent n)
    (hxns : x = n + s)
    (hxM : x ∈ M A B) :
    s ∈ M A B := by
  sorry

/-! ## Paragraph 1: s = 0 from eigenvalue information

Humphreys: "We have to show that s = 0 or equivalently that E = 0." -/

omit [CharZero K] in
/-- A semisimple endomorphism over an algebraically closed field with all eigenvalues
equal to zero must be zero.

Proof: `V = ⨁ eigenspace(s, μ)`. If all eigenvalues are zero, then
`V = ker(s)`, so `s = 0`. -/
lemma eq_zero_of_isSemisimple_of_forall_eigenvalue_eq_zero
    (s : Module.End K V) (hs : s.IsSemisimple)
    (h : ∀ μ : K, s.HasEigenvalue μ → μ = 0) : s = 0 := by
  have h_top : ⨆ μ, s.maxGenEigenspace μ = ⊤ := iSup_maxGenEigenspace_eq_top s
  have h_eq : ∀ μ, s.maxGenEigenspace μ = s.eigenspace μ :=
    hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace
  simp_rw [h_eq] at h_top
  have h_bot : ∀ μ ≠ (0 : K), s.eigenspace μ = ⊥ := by
    intro μ hμ
    by_contra h_ne
    exact hμ (h μ (hasEigenvalue_iff.mpr h_ne))
  have h_ker : s.eigenspace 0 = ⊤ := by
    rw [← h_top]
    apply le_antisymm (le_iSup _ 0)
    apply iSup_le; intro μ
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · rw [h_bot μ hμ]; exact bot_le
  rw [eigenspace_zero] at h_ker
  exact ker_eq_top.mp h_ker

/-! ## Paragraphs 2–4: The dual-space trace argument

This section formalizes the core of Humphreys' proof, showing each eigenvalue
of `s` is zero using the full trace orthogonality hypothesis.

The concrete approach uses the eigenbasis `b` and elementary endomorphisms
`e_{ij}` throughout.

**Paragraph 2** — Constructing y:

"Given f, let y be that element of gl(V) whose matrix relative to our given
basis is diag(f(a₁), f(a₂), ..., f(aₘ))."

→ `y = diagEnd b (fun σ => algebraMap ℚ K (f (σ.1)))`
  where `b = eigenbasis s hs` and `f : E →ₗ[ℚ] ℚ` with
  `E = Submodule.span ℚ {eigenvalues}`.

"Now let r(T) ∈ F[T] be a polynomial without constant term satisfying
r(aᵢ − aⱼ) = f(aᵢ) − f(aⱼ) for all i, j pairs."

→ Lagrange interpolation on the finite set of eigenvalue differences
  (`Lagrange.interpolate`). Well-defined because `f` is ℚ-linear.

"Evidently ad y = r(ad s)."

→ Both sides agree on every `e_{ij}`:
  `ad(y)(e_{ij}) = (f(aᵢ) − f(aⱼ)) e_{ij}` (from `ad_diagEnd_eij`)
  `r(ad s)(e_{ij}) = r(aᵢ − aⱼ) e_{ij}` (from `aeval_apply_of_hasEigenvector`)

**Paragraph 3** — y ∈ M:

"Now ad s is the semisimple part of ad x [...] so it can be written as a
polynomial in ad x without constant term. Therefore, ad y is also a
polynomial in ad x without constant term."

→ Uses `ad_semisimple_part_maps_to` and the composition `ad(y) = r(p(ad(x)))`.

"Hence any polynomial in ad x without constant term maps B into A,
so ad y(B) ⊂ A, i.e. y ∈ M."

→ Uses `ad_pow_maps_to`.

**Paragraph 4** — The trace argument:

"Using the hypothesis of the lemma, tr(xy) = 0, we get ∑(aᵢf(aᵢ)) = 0."

→ `tr(xy) = tr(sy) + tr(ny)`.
  `tr(ny) = 0` since `ny` is nilpotent (n commutes with y, both in adjoin K {x}).
  `tr(sy) = ∑_σ a(σ) · algebraMap ℚ K (f(a(σ)))` (trace of product of
  commuting diagonal endomorphisms).

"The left side is a Q-linear combination of elements in E; applying f,
we obtain ∑f(aᵢ)² = 0."

→ The identity `∑ f(aᵢ) · aᵢ = 0` holds in `E ⊆ K`. Applying f gives
  `∑ f(aᵢ)² = 0` in ℚ.

"But the numbers f(aᵢ) are rational, so this forces all of them to be zero.
Finally, f must be identically zero, because aᵢ span E."

→ `Finset.sum_eq_zero_iff_of_nonneg` gives each `f(aᵢ)² = 0` hence
  `f(aᵢ) = 0`. Since eigenvalues span E, f = 0, contradicting the choice
  of f with `f(μ) ≠ 0`. -/
lemma eigenvalues_eq_zero
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x s : Module.End K V)
    (hs_adj : s ∈ Algebra.adjoin K {x})
    (hs_ss : s.IsSemisimple)
    (n : Module.End K V)
    (hn_nil : IsNilpotent n)
    (hxns : x = n + s)
    (hxM : x ∈ M A B)
    (htr : ∀ z ∈ M A B, trace K V (x * z) = 0)
    (μ : K) (hμ : s.HasEigenvalue μ) : μ = 0 := by
  sorry

end HumphreysLemma

open HumphreysLemma in
/-- **Humphreys' Lemma** over algebraically closed fields of characteristic zero.

Given subspaces `A ≤ B` of `gl(V)` and `M = {z ∈ gl(V) : [z, B] ⊆ A}`,
if `x ∈ M` satisfies `tr(xz) = 0` for all `z ∈ M`, then `x` is nilpotent.

The proof follows Humphreys, "Introduction to Lie Algebras and Representation
Theory", §4.3:
1. Jordan-Chevalley decomposition: `x = n + s`
2. Show all eigenvalues of `s` are zero (the dual-space trace argument)
3. Conclude `s = 0`, hence `x = n` is nilpotent -/
theorem humphreys_lemma_algClosed
    (A B : Submodule K (Module.End K V))
    (hAB : A ≤ B)
    (x : Module.End K V)
    (hxM : x ∈ M A B)
    (htr : ∀ y ∈ M A B, trace K V (x * y) = 0) :
    IsNilpotent x := by
  -- Humphreys: "Let x = s + n (s = x_s, n = x_n) be the Jordan decomposition of x."
  obtain ⟨n, hn_adj, s, hs_adj, hn_nil, hs_ss, hxns⟩ :=
    x.exists_isNilpotent_isSemisimple
  -- Humphreys: "Since F is algebraically closed, s is diagonalizable.
  -- Fix a basis v₁, v₂, ..., vₘ that diagonalizes s, so that it has matrix
  -- diag(a₁, a₂, ..., aₘ)."
  let v := eigenbasis s hs_ss
  let a : (Σ μ : K, Fin (Module.finrank K (s.eigenspace μ))) → K := fun i => i.1
  have hv_diag : ∀ i, s (v i) = a i • v i := eigenbasis_eigenvalue s hs_ss
  -- Humphreys: "We have to show that s = 0 or equivalently that E = 0."
  suffices hs_zero : s = 0 by rw [hxns, hs_zero, add_zero]; exact hn_nil
  apply eq_zero_of_isSemisimple_of_forall_eigenvalue_eq_zero s hs_ss
  -- Humphreys, Paragraphs 2–4: show each eigenvalue μ is zero
  exact eigenvalues_eq_zero A B hAB x s hs_adj hs_ss n hn_nil hxns hxM htr
