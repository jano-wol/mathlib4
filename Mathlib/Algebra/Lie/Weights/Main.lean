import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

namespace LieAlgebra.IsKilling

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
open LieAlgebra LieModule Module
variable {H : LieSubalgebra K L} [H.IsCartanSubalgebra]
variable [IsKilling K L] [IsTriangularizable K H L]

lemma cartan_sup_iSup_rootSpace_eq_top :
    H.toLieSubmodule ⊔ ⨆ α : Weight K H L, ⨆ (_ : α.IsNonZero), rootSpace H α = ⊤ := by
  admit

lemma exists_rootSet_lieIdeal_eq (I : LieIdeal K L) :
    ∃ Φ : Set H.root, I.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔
      ⨆ α ∈ Φ, (rootSpace H α.1).toSubmodule := by
  admit

theorem isCompl_killingCompl (I : LieIdeal K L) :
    IsCompl I I.killingCompl := by
  admit

theorem compl_eq_killingCompl (I : LieIdeal K L) :
    Iᶜ = I.killingCompl := by
  admit

lemma cartan_is_abelian : IsLieAbelian H := by
  constructor ; aesop

lemma cartan_eq_sup_inf_ideal (I : LieIdeal K L) (hI : IsCompl I I.killingCompl) :
    H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (I.killingCompl.toSubmodule ⊓ H.toSubmodule) := by
  -- Since $I$ and $J$ are complementary ideals, we have $H \subseteq (H \cap I) + (H \cap J)$.
  have h_le : H.toSubmodule ≤ (I : Submodule K L) ⊓ H.toSubmodule ⊔ (LieIdeal.killingCompl K L I : Submodule K L) ⊓ H.toSubmodule := by
    intro x hx;
    -- Since $I$ and $J$ are complementary, $x$ can be written as $x = i + j$ with $i \in I$ and $j \in J$.
    obtain ⟨i, j, hi, hj, hx_eq⟩ : ∃ i j : L, i ∈ I ∧ j ∈ LieIdeal.killingCompl K L I ∧ x = i + j := by
      have := hI.sup_eq_top;
      replace this := Submodule.mem_sup.mp ( this.symm ▸ Submodule.mem_top : x ∈ I ⊔ LieIdeal.killingCompl K L I ) ; aesop;
    -- Since $H$ is abelian, we have $[i, x] = 0$ and $[j, x] = 0$ for all $x \in H$.
    have h_comm : ∀ x ∈ H, ⁅i, x⁆ = 0 ∧ ⁅j, x⁆ = 0 := by
      intro x hx
      have h_comm_i : ⁅i, x⁆ ∈ I := by
        exact?
      have h_comm_j : ⁅j, x⁆ ∈ LieIdeal.killingCompl K L I := by
        exact?
      have h_comm_zero : ⁅i, x⁆ + ⁅j, x⁆ = 0 := by
        have h_comm_zero : ⁅x, i + j⁆ = 0 := by
          have h_comm_zero : ∀ x ∈ H, ∀ y ∈ H, ⁅x, y⁆ = 0 := by
            have h_comm_zero : IsLieAbelian H := by
              exact?;
            intro x hx y hy; exact (by
            have := h_comm_zero.1 ⟨ x, hx ⟩ ⟨ y, hy ⟩;
            exact Subtype.ext_iff.mp this);
          aesop;
        rw [ ← neg_eq_zero, ← lie_skew, ← lie_skew ];
        simp_all +decide [ lie_add, add_comm ];
      have h_comm_zero : ⁅i, x⁆ ∈ I ⊓ LieIdeal.killingCompl K L I := by
        simp_all +decide [ add_eq_zero_iff_eq_neg ];
        intro y hy; specialize h_comm_j y hy; simp_all +decide [ killingForm, lie_skew ] ;
        simp_all +decide [ LieModule.traceForm, lie_skew ];
        simp_all +decide [ LieRing.of_associative_ring_bracket, mul_assoc ];
        simp_all +decide [ mul_sub, sub_mul, mul_assoc ];
        rw [ sub_eq_zero ] at * ; aesop;
      have := hI.disjoint.le_bot h_comm_zero; aesop;
    -- Since $i$ and $j$ are in the centralizer of $H$, they are in $H$.
    have h_i_j_in_H : i ∈ H ∧ j ∈ H := by
      have h_i_j_in_H : ∀ x : L, (∀ y ∈ H, ⁅x, y⁆ = 0) → x ∈ H := by
        intro x hx_comm
        have h_normalizer : x ∈ LieSubalgebra.normalizer H := by
          simp +decide [ LieSubalgebra.mem_normalizer_iff, hx_comm ];
          exact fun y hy => by rw [ hx_comm y hy ] ; exact H.zero_mem;
        have h_self_normalizing : H.normalizer = H := by
          exact?;
        exact h_self_normalizing ▸ h_normalizer;
      exact ⟨ h_i_j_in_H i fun y hy => h_comm y hy |>.1, h_i_j_in_H j fun y hy => h_comm y hy |>.2 ⟩;
    exact Submodule.mem_sup.mpr ⟨ i, ⟨ hi, h_i_j_in_H.1 ⟩, j, ⟨ hj, h_i_j_in_H.2 ⟩, by simp +decide [ hx_eq ] ⟩;
  exact le_antisymm h_le ( sup_le ( inf_le_right ) ( inf_le_right ) )

lemma h_H_le_C_1 (β : Weight K H L) (hβ : β.IsNonZero) :
    H.toSubmodule ≤ ⨆ j ≠ β, (rootSpace H j).toSubmodule := by
  intro x hx;
  have h_sum : x ∈ LieAlgebra.rootSpace H 0 := by
    simp_all +decide [ LieAlgebra.rootSpace, LieSubalgebra.mem_toSubmodule ];
  refine' Submodule.mem_iSup_of_mem _ ( Submodule.mem_iSup_of_mem _ _ );
  exact ⟨ 0, by
    intro h;
    rw [ LieSubmodule.eq_bot_iff ] at h;
    contrapose! hβ;
    ext x; specialize h x; aesop; ⟩
  all_goals generalize_proofs at *;
  · exact fun h => hβ <| h ▸ rfl;
  · exact h_sum

theorem isSimple_of_isIrreducible (hIrr : (rootSystem H).IsIrreducible) : IsSimple K L := by
  by_contra h_not_simple
  obtain ⟨I, hI_ne_bot, hI_ne_top⟩ : ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
    have h_not_simple_def : ¬LieAlgebra.IsSimple K L → ∃ I : LieIdeal K L, I ≠ ⊥ ∧ I ≠ ⊤ := by
      intro h_not_simple_def
      simp [LieAlgebra.IsSimple] at h_not_simple_def;
      contrapose! h_not_simple_def;
      constructor;
      · exact fun I => Classical.or_iff_not_imp_left.2 fun h => h_not_simple_def I h;
      · cases subsingleton_or_nontrivial L <;> simp_all +decide [ LieAlgebra.IsKilling ];
        · have := hIrr.1; simp_all +decide [ LieAlgebra.IsKilling.rootSystem ] ;
          exact False.elim ( this.exists_pair_ne.elim fun x hx => hx.elim fun y hy => hy <| Subsingleton.elim _ _ );
        · intro h_abelian
          have h_center : LieAlgebra.center K L = ⊤ := by
            exact?
          have h_center_eq_bot : LieAlgebra.center K L = ⊥ := by
            exact?
          exact absurd h_center_eq_bot (by
          simp +decide [ h_center ];
          exact absurd ( h_center_eq_bot ▸ h_center ) ( by simp +decide [ LieSubmodule.eq_bot_iff ] ));
    exact h_not_simple_def h_not_simple
  let J := I.killingCompl
  obtain ⟨Φ₁, hΦ₁⟩ := exists_rootSet_lieIdeal_eq (H := H) I
  obtain ⟨Φ₂, hΦ₂⟩ := exists_rootSet_lieIdeal_eq (H := H) J

  have s1 : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
    have h_cartan_decomp : H.toSubmodule = (I.toSubmodule ⊓ H.toSubmodule) ⊔ (J.toSubmodule ⊓ H.toSubmodule) := by
      have h_compl : IsCompl I J := by
        exact?
      exact?;
    exact h_cartan_decomp

  have sup_1 : I.toSubmodule ⊔ J.toSubmodule = ⊤ := by
    have := LieAlgebra.IsKilling.isCompl_killingCompl I;
    -- Since $I$ and $J$ are complementary ideals, their sum as submodules is the entire space.
    have h_sup : (I : Submodule K L) ⊔ (J : Submodule K L) = ⊤ := by
      have := this.sup_eq_top
      convert congr_arg ( fun x : LieIdeal K L => x.toLieSubalgebra.toSubmodule ) this using 1;
    convert h_sup using 1

  have hJ_ne_bot : J ≠ ⊥ := by
    by_contra J_bot
    rw [J_bot] at sup_1
    simp at sup_1
    exact Ne.elim hI_ne_top sup_1

  have bot_1 : I.toSubmodule ⊓ J.toSubmodule = ⊥  := by
    -- Since $I$ and $J$ are complementary, their intersection is trivial.
    have h_compl : I ⊓ J = ⊥ := by
      have h_compl : IsCompl I J := by
        -- By definition of the Killing form, we know that $I$ and $J$ are complementary as ideals.
        apply isCompl_killingCompl
      exact h_compl.inf_eq_bot;
    -- Since $I$ and $J$ are Lie ideals, their intersection as submodules is the same as their intersection as Lie ideals.
    convert h_compl using 1;
    simp +decide [ SetLike.ext_iff, LieSubmodule.mem_inf ]

  have s2 : Φ₁ ∩ Φ₂ = ∅ := by
    ext α
    simp [bot_1];
    intro hα₁ hα₂
    have h_contra : (rootSpace H α.val).toSubmodule ≤ (I : Submodule K L) ⊓ (J : Submodule K L) := by
      simp +zetaDelta at *;
      exact ⟨ hΦ₁.symm ▸ le_sup_of_le_right ( le_iSup₂_of_le α hα₁ le_rfl ), hΦ₂.symm ▸ le_sup_of_le_right ( le_iSup₂_of_le α hα₂ le_rfl ) ⟩;
    have h_contra : (rootSpace H α.val) ≠ ⊥ := by
      have := α.val.genWeightSpace_ne_bot
      simp at this
      simp
      dsimp [rootSpace]
      exact this
    exact h_contra ( by simpa [ bot_1 ] using ‹ ( LieAlgebra.rootSpace H ( α.val ) : Submodule K L ) ≤ ( I : Submodule K L ) ⊓ ( J : Submodule K L ) › )

  have s3 : Φ₁ ∪ Φ₂ = Set.univ := by
    by_contra h_not_univ
    rw [← ne_eq, Set.ne_univ_iff_exists_notMem] at h_not_univ
    obtain ⟨β, hβ⟩ := h_not_univ
    rw [Set.mem_union, not_or] at hβ
    obtain ⟨hβ_not_Φ₁, hβ_not_Φ₂⟩ := hβ

    -- Step 1: β is a nonzero weight (since β ∈ H.root = {α | α.IsNonZero})
    have hβ_nonzero : (β : Weight K H L).IsNonZero := by
      -- Extract IsNonZero from membership in LieSubalgebra.root
      have := β.2
      simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this

    -- Step 2: Independence of weight spaces (rootSpace = genWeightSpace)
    -- Key lemma: iSupIndep_genWeightSpace' gives independence over all weights
    -- rootSpace H χ = genWeightSpace L χ by definition
    have h_indep : iSupIndep fun (χ : Weight K H L) => (rootSpace H χ).toSubmodule :=
      LieSubmodule.iSupIndep_toSubmodule.mpr (iSupIndep_genWeightSpace' K H L)

    let C := ⨆ j ≠ (β : Weight K H L), (rootSpace H j).toSubmodule

    -- Step 3: (rootSpace H β) ⊓ C = ⊥ (directly from h_indep)
    -- h_indep gives Disjoint, convert to ⊓ = ⊥ using disjoint_iff
    have h_inf_C : (rootSpace H β).toSubmodule ⊓ C = ⊥ := disjoint_iff.mp (h_indep (β : Weight K H L))

    have h_H_le_C : H.toSubmodule ≤ C := by
      apply h_H_le_C_1 β.val hβ_nonzero

    -- (2) For any α ≠ β, rootSpace H α ≤ C
    have h_rootSpace_le_C : ∀ α : Weight K H L, α ≠ β → (rootSpace H α).toSubmodule ≤ C :=
      fun α hα => le_iSup₂_of_le α hα (le_refl _)

    -- I ≤ C: From hΦ₁, I = (I ⊓ H) ⊔ ⨆ α ∈ Φ₁, rootSpace H α
    -- (I ⊓ H) ≤ H ≤ C and each rootSpace in Φ₁ ≤ C (since β ∉ Φ₁)
    have h_I_le_C : I.toSubmodule ≤ C := by
      refine' le_trans ( hΦ₁.le ) _;
      -- Since $H \subseteq C$, we have $I \cap H \subseteq C$.
      have hIH_subset_C : (I : Submodule K L) ⊓ H.toSubmodule ≤ ⨆ j ≠ β.val, (rootSpace H j).toSubmodule := by
        refine' le_trans _ ( h_H_le_C);
        exact inf_le_right;
      refine' sup_le hIH_subset_C _;
      simp +decide [ iSup_le_iff ];
      exact fun a ha ha' => le_iSup₂_of_le a ( by rintro rfl; exact hβ_not_Φ₁ ha' ) le_rfl

    have h_J_le_C : J.toSubmodule ≤ C := by
      refine' le_trans ( hΦ₂.le ) _;
      -- Since $H \subseteq C$, we have $I \cap H \subseteq C$.
      have hJH_subset_C : (J : Submodule K L) ⊓ H.toSubmodule ≤ ⨆ j ≠ β.val, (rootSpace H j).toSubmodule := by
        refine' le_trans _ ( h_H_le_C);
        exact inf_le_right;
      refine' sup_le hJH_subset_C _;
      simp +decide [ iSup_le_iff ];
      exact fun a ha ha' => le_iSup₂_of_le a ( by rintro rfl; exact hβ_not_Φ₂ ha' ) le_rfl

    have h_leq : I.toSubmodule ⊔ J.toSubmodule ≤ C := by
      exact sup_le h_I_le_C h_J_le_C

    -- Now h_inf_I follows from h_I_le_C and h_inf_C via eq_bot_iff.
    have h_inf_I : (rootSpace H β).toSubmodule ⊓ (I.toSubmodule ⊔ J.toSubmodule) = ⊥ :=
      eq_bot_iff.mpr fun x hx => h_inf_C.le ⟨hx.1, h_leq hx.2⟩
    rw [sup_1] at h_inf_I
    have h_rootSpace_nonzero : (rootSpace H β : Submodule K L) ≠ ⊥ := by
      have := β.val.genWeightSpace_ne_bot
      simp at this
      simp
      dsimp [rootSpace]
      exact this
    exact h_rootSpace_nonzero ( by simpa using h_inf_I )

  have s4 : Φ₁ ≠ ∅ := by
    by_contra Φ_empty
    rw [Φ_empty] at hΦ₁
    simp at hΦ₁
    have ttt := cartan_is_abelian (K := K) (H := H) (L := L)
    have rrr : IsLieAbelian I := by
      have hI_abelian : IsLieAbelian (↥I) := by
        have h_submodule : I.toSubmodule ≤ H.toSubmodule := hΦ₁
        constructor;
        have h_abelian : ∀ x m : L, x ∈ I.toSubmodule → m ∈ I.toSubmodule → ⁅x, m⁆ = 0 := by
          intro x m hx hm;
          have := ttt.1 ⟨ x, h_submodule hx ⟩ ⟨ m, h_submodule hm ⟩;
          exact congr_arg Subtype.val this;
        exact fun x m => Subtype.ext <| h_abelian x m x.2 m.2;
      exact hI_abelian
    haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
    exact hI_ne_bot ( by
      exact HasTrivialRadical.eq_bot_of_isSolvable I )

  have s5 : Φ₂ ≠ ∅ := by
    by_contra Φ_empty
    rw [Φ_empty] at hΦ₂
    simp at hΦ₂
    have ttt := cartan_is_abelian (K := K) (H := H) (L := L)
    have rrr : IsLieAbelian J := by
      have hI_abelian : IsLieAbelian (↥J) := by
        have h_submodule : J.toSubmodule ≤ H.toSubmodule := hΦ₂
        constructor;
        have h_abelian : ∀ x m : L, x ∈ J.toSubmodule → m ∈ J.toSubmodule → ⁅x, m⁆ = 0 := by
          intro x m hx hm;
          have := ttt.1 ⟨ x, h_submodule hx ⟩ ⟨ m, h_submodule hm ⟩;
          exact congr_arg Subtype.val this;
        exact fun x m => Subtype.ext <| h_abelian x m x.2 m.2;
      exact hI_abelian
    haveI : LieAlgebra.IsSemisimple K L := LieAlgebra.IsKilling.instSemisimple K L
    exact hJ_ne_bot ( by
      exact HasTrivialRadical.eq_bot_of_isSolvable J )
  admit

end LieAlgebra.IsKilling
