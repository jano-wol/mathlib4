/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 421560a8-3b03-4018-b713-437eac817f7c

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

At Harmonic, we use a modified version of the `generalize_proofs` tactic.
For compatibility, we include this tactic at the start of the file.
If you add the comment "-- Harmonic `generalize_proofs` tactic" to your file, we will not do this.
-/

import Mathlib.Algebra.Lie.Weights.IsSimple
import Mathlib.Algebra.Lie.Weights.RootSystem
import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas


import Mathlib.Tactic.GeneralizeProofs

namespace Harmonic.GeneralizeProofs
-- Harmonic `generalize_proofs` tactic

open Lean Meta Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
def mkLambdaFVarsUsedOnly' (fvars : Array Expr) (e : Expr) : MetaM (Array Expr × Expr) := do
  let mut e := e
  let mut fvars' : List Expr := []
  for i' in [0:fvars.size] do
    let fvar := fvars[fvars.size - i' - 1]!
    e ← mkLambdaFVars #[fvar] e (usedOnly := false) (usedLetOnly := false)
    match e with
    | .letE _ _ v b _ => e := b.instantiate1 v
    | .lam _ _ _b _ => fvars' := fvar :: fvars'
    | _ => unreachable!
  return (fvars'.toArray, e)

partial def abstractProofs' (e : Expr) (ty? : Option Expr) : MAbs Expr := do
  if (← read).depth ≤ (← read).config.maxDepth then MAbs.withRecurse <| visit (← instantiateMVars e) ty?
  else return e
where
  visit (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    if (← read).config.debug then
      if let some ty := ty? then
        unless ← isDefEq (← inferType e) ty do
          throwError "visit: type of{indentD e}\nis not{indentD ty}"
    if e.isAtomic then
      return e
    else
      checkCache (e, ty?) fun _ ↦ do
        if ← isProof e then
          visitProof e ty?
        else
          match e with
          | .forallE n t b i =>
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              mkForallFVars #[x] (← visit (b.instantiate1 x) none) (usedOnly := false) (usedLetOnly := false)
          | .lam n t b i => do
            withLocalDecl n i (← visit t none) fun x ↦ MAbs.withLocal x do
              let ty'? ←
                if let some ty := ty? then
                  let .forallE _ _ tyB _ ← pure ty
                    | throwError "Expecting forall in abstractProofs .lam"
                  pure <| some <| tyB.instantiate1 x
                else
                  pure none
              mkLambdaFVars #[x] (← visit (b.instantiate1 x) ty'?) (usedOnly := false) (usedLetOnly := false)
          | .letE n t v b _ =>
            let t' ← visit t none
            withLetDecl n t' (← visit v t') fun x ↦ MAbs.withLocal x do
              mkLetFVars #[x] (← visit (b.instantiate1 x) ty?) (usedLetOnly := false)
          | .app .. =>
            e.withApp fun f args ↦ do
              let f' ← visit f none
              let argTys ← appArgExpectedTypes f' args ty?
              let mut args' := #[]
              for arg in args, argTy in argTys do
                args' := args'.push <| ← visit arg argTy
              return mkAppN f' args'
          | .mdata _ b  => return e.updateMData! (← visit b ty?)
          | .proj _ _ b => return e.updateProj! (← visit b none)
          | _           => unreachable!
  visitProof (e : Expr) (ty? : Option Expr) : MAbs Expr := do
    let eOrig := e
    let fvars := (← read).fvars
    let e := e.withApp' fun f args => f.beta args
    if e.withApp' fun f args => f.isAtomic && args.all fvars.contains then return e
    let e ←
      if let some ty := ty? then
        if (← read).config.debug then
          unless ← isDefEq ty (← inferType e) do
            throwError m!"visitProof: incorrectly propagated type{indentD ty}\nfor{indentD e}"
        mkExpectedTypeHint e ty
      else pure e
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← getLCtx) e do
        throwError m!"visitProof: proof{indentD e}\nis not well-formed in the current context\n\
          fvars: {fvars}"
    let (fvars', pf) ← mkLambdaFVarsUsedOnly' fvars e
    if !(← read).config.abstract && !fvars'.isEmpty then
      return eOrig
    if (← read).config.debug then
      unless ← Lean.MetavarContext.isWellFormed (← read).initLCtx pf do
        throwError m!"visitProof: proof{indentD pf}\nis not well-formed in the initial context\n\
          fvars: {fvars}\n{(← mkFreshExprMVar none).mvarId!}"
    let pfTy ← instantiateMVars (← inferType pf)
    let pfTy ← abstractProofs' pfTy none
    if let some pf' ← MAbs.findProof? pfTy then
      return mkAppN pf' fvars'
    MAbs.insertProof pfTy pf
    return mkAppN pf fvars'
partial def withGeneralizedProofs' {α : Type} [Inhabited α] (e : Expr) (ty? : Option Expr)
    (k : Array Expr → Array Expr → Expr → MGen α) :
    MGen α := do
  let propToFVar := (← get).propToFVar
  let (e, generalizations) ← MGen.runMAbs <| abstractProofs' e ty?
  let rec
    go [Inhabited α] (i : Nat) (fvars pfs : Array Expr)
        (proofToFVar propToFVar : ExprMap Expr) : MGen α := do
      if h : i < generalizations.size then
        let (ty, pf) := generalizations[i]
        let ty := (← instantiateMVars (ty.replace proofToFVar.get?)).cleanupAnnotations
        withLocalDeclD (← mkFreshUserName `pf) ty fun fvar => do
          go (i + 1) (fvars := fvars.push fvar) (pfs := pfs.push pf)
            (proofToFVar := proofToFVar.insert pf fvar)
            (propToFVar := propToFVar.insert ty fvar)
      else
        withNewLocalInstances fvars 0 do
          let e' := e.replace proofToFVar.get?
          modify fun s => { s with propToFVar }
          k fvars pfs e'
  go 0 #[] #[] (proofToFVar := {}) (propToFVar := propToFVar)

partial def generalizeProofsCore'
    (g : MVarId) (fvars rfvars : Array FVarId) (target : Bool) :
    MGen (Array Expr × MVarId) := go g 0 #[]
where
  go (g : MVarId) (i : Nat) (hs : Array Expr) : MGen (Array Expr × MVarId) := g.withContext do
    let tag ← g.getTag
    if h : i < rfvars.size then
      let fvar := rfvars[i]
      if fvars.contains fvar then
        let tgt ← instantiateMVars <| ← g.getType
        let ty := (if tgt.isLet then tgt.letType! else tgt.bindingDomain!).cleanupAnnotations
        if ← pure tgt.isLet <&&> Meta.isProp ty then
          let tgt' := Expr.forallE tgt.letName! ty tgt.letBody! .default
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .app g' tgt.letValue!
          return ← go g'.mvarId! i hs
        if let some pf := (← get).propToFVar.get? ty then
          let tgt' := tgt.bindingBody!.instantiate1 pf
          let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
          g.assign <| .lam tgt.bindingName! tgt.bindingDomain! g' tgt.bindingInfo!
          return ← go g'.mvarId! (i + 1) hs
        match tgt with
        | .forallE n t b bi =>
          let prop ← Meta.isProp t
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            let t' := t'.cleanupAnnotations
            let tgt' := Expr.forallE n t' b bi
            let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
            g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
            let (fvar', g') ← g'.mvarId!.intro1P
            g'.withContext do Elab.pushInfoLeaf <|
              .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
            if prop then
              MGen.insertFVar t' (.fvar fvar')
            go g' (i + 1) (hs ++ hs')
        | .letE n t v b _ =>
          withGeneralizedProofs' t none fun hs' pfs' t' => do
            withGeneralizedProofs' v t' fun hs'' pfs'' v' => do
              let tgt' := Expr.letE n t' v' b false
              let g' ← mkFreshExprSyntheticOpaqueMVar tgt' tag
              g.assign <| mkAppN (← mkLambdaFVars (hs' ++ hs'') g' (usedOnly := false) (usedLetOnly := false)) (pfs' ++ pfs'')
              let (fvar', g') ← g'.mvarId!.intro1P
              g'.withContext do Elab.pushInfoLeaf <|
                .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
              go g' (i + 1) (hs ++ hs' ++ hs'')
        | _ => unreachable!
      else
        let (fvar', g') ← g.intro1P
        g'.withContext do Elab.pushInfoLeaf <|
          .ofFVarAliasInfo { id := fvar', baseId := fvar, userName := ← fvar'.getUserName }
        go g' (i + 1) hs
    else if target then
      withGeneralizedProofs' (← g.getType) none fun hs' pfs' ty' => do
        let g' ← mkFreshExprSyntheticOpaqueMVar ty' tag
        g.assign <| mkAppN (← mkLambdaFVars hs' g' (usedOnly := false) (usedLetOnly := false)) pfs'
        return (hs ++ hs', g'.mvarId!)
    else
      return (hs, g)

end GeneralizeProofs

open Lean Elab Parser.Tactic Elab.Tactic Mathlib.Tactic.GeneralizeProofs
partial def generalizeProofs'
    (g : MVarId) (fvars : Array FVarId) (target : Bool) (config : Config := {}) :
    MetaM (Array Expr × MVarId) := do
  let (rfvars, g) ← g.revert fvars (clearAuxDeclsInsteadOfRevert := true)
  g.withContext do
    let s := { propToFVar := ← initialPropToFVar }
    GeneralizeProofs.generalizeProofsCore' g fvars rfvars target |>.run config |>.run' s

elab (name := generalizeProofsElab'') "generalize_proofs" config?:(Parser.Tactic.config)?
    hs:(ppSpace colGt binderIdent)* loc?:(location)? : tactic => withMainContext do
  let config ← elabConfig (mkOptionalNode config?)
  let (fvars, target) ←
    match expandOptLocation (Lean.mkOptionalNode loc?) with
    | .wildcard => pure ((← getLCtx).getFVarIds, true)
    | .targets t target => pure (← getFVarIds t, target)
  liftMetaTactic1 fun g => do
    let (pfs, g) ← generalizeProofs' g fvars target config
    g.withContext do
      let mut lctx ← getLCtx
      for h in hs, fvar in pfs do
        if let `(binderIdent| $s:ident) := h then
          lctx := lctx.setUserName fvar.fvarId! s.getId
        Expr.addLocalVarInfoForBinderIdent fvar h
      Meta.withLCtx lctx (← Meta.getLocalInstances) do
        let g' ← Meta.mkFreshExprSyntheticOpaqueMVar (← g.getType) (← g.getTag)
        g.assign g'
        return g'.mvarId!

end Harmonic

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

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

`grind` failed
case grind.1
K : Type u_1
L : Type u_2
inst : Field K
inst_1 : CharZero K
inst_2 : LieRing L
inst_3 : LieAlgebra K L
inst_4 : Module.Finite K L
H : LieSubalgebra K L
inst_5 : H.IsCartanSubalgebra
inst_6 : LieAlgebra.IsKilling K L
inst_7 : LieModule.IsTriangularizable K (↥H) L
hIrr : (LieAlgebra.IsKilling.rootSystem H).IsIrreducible
h_not_simple : ¬LieAlgebra.IsSimple K L
I : LieSubmodule K L L
hI_ne_bot : ¬I = ⊥
hI_ne_top : ¬I = ⊤
Φ₁ : Set { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }
hΦ₁ :
  (↑I : Submodule K L) =
    (↑I : Submodule K L) ⊓ H.toSubmodule ⊔
      ⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
Φ₂ : Set { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }
hΦ₂ :
  (↑(LieIdeal.killingCompl K L I) : Submodule K L) =
    (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule ⊔
      ⨆ α ∈ Φ₂, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
s1 :
  H.toSubmodule =
    (↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule
sup_1 : (↑I : Submodule K L) ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) = ⊤
hJ_ne_bot : ¬LieIdeal.killingCompl K L I = ⊥
bot_1 : (↑I : Submodule K L) ⊓ (↑(LieIdeal.killingCompl K L I) : Submodule K L) = ⊥
s2 : Φ₁ ∩ Φ₂ = ∅
s3 : Φ₁ ∪ Φ₂ = Set.univ
s4 : ¬Φ₁ = ∅
s5 : ¬Φ₂ = ∅
xxx :
  ∀ (i : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₁ })
    (j : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₂ }),
    (LieAlgebra.IsKilling.rootSystem H).pairing
        (↑i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} })
        (↑j : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =
      0
nontrivial : Nontrivial (↥H →ₗ[K] K)
h₁ : Nontrivial ↥H
h₃ :
  ∀ (q : Submodule K ↥H),
    ¬q = ⊥ →
      (∃ (i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          q ∉ Module.End.invtSubmodule (↑((LieAlgebra.IsKilling.rootSystem H).coreflection i) : ↥H →ₗ[K] ↥H)) ∨
        q = ⊤
val : LieModule.Weight K (↥H) L
property : val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
hx : ⟨val, ⋯⟩ ∈ Φ₁
h :
  ∀ (a : ↥H →ₗ[K] K) (a_1 : LieModule.Weight K (↥H) L) (a_2 : ¬a_1.IsZero),
    ⟨a_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L a_1 = a → a = 0
h_1 :
  (fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
      ⨆ (_ : α ∈ Φ₂), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) =
    fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
    ⨆ (_ : α ∈ Φ₁), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
val_1 : LieModule.Weight K (↥H) L
property_1 : val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
h_2 : (⟨val_1, ⋯⟩ ∈ Φ₁) = (⟨val_1, ⋯⟩ ∉ ∅)
val_2 : LieModule.Weight K (↥H) L
property_2 : val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
h_3 : (⟨val_2, ⋯⟩ ∈ Φ₂) = (⟨val_2, ⋯⟩ ∉ ∅)
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] CharZero K
    [prop] Module.Finite K L
    [prop] H.IsCartanSubalgebra
    [prop] LieAlgebra.IsKilling K L
    [prop] LieModule.IsTriangularizable K (↥H) L
    [prop] (LieAlgebra.IsKilling.rootSystem H).IsIrreducible
    [prop] ¬LieAlgebra.IsSimple K L
    [prop] ¬I = ⊥
    [prop] ¬I = ⊤
    [prop] (↑I : Submodule K L) =
          (↑I : Submodule K L) ⊓ H.toSubmodule ⊔
            ⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
    [prop] (↑(LieIdeal.killingCompl K L I) : Submodule K L) =
          (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule ⊔
            ⨆ α ∈ Φ₂, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
    [prop] H.toSubmodule =
          (↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule
    [prop] (↑I : Submodule K L) ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) = ⊤
    [prop] ¬LieIdeal.killingCompl K L I = ⊥
    [prop] (↑I : Submodule K L) ⊓ (↑(LieIdeal.killingCompl K L I) : Submodule K L) = ⊥
    [prop] Φ₁ ∩ Φ₂ = ∅
    [prop] Φ₁ ∪ Φ₂ = Set.univ
    [prop] ¬Φ₁ = ∅
    [prop] ¬Φ₂ = ∅
    [prop] ∀
          (i : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₁ })
          (j : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₂ }),
          (LieAlgebra.IsKilling.rootSystem H).pairing
              (↑i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} })
              (↑j : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =
            0
    [prop] Nontrivial (↥H →ₗ[K] K)
    [prop] Nontrivial ↥H
    [prop] ∀ (q : Submodule K ↥H),
          ¬q = ⊥ →
            (∃ (i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
                q ∉ Module.End.invtSubmodule (↑((LieAlgebra.IsKilling.rootSystem H).coreflection i) : ↥H →ₗ[K] ↥H)) ∨
              q = ⊤
    [prop] val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] ⟨val, ⋯⟩ ∈ Φ₁
    [prop] ∀ (a : ↥H →ₗ[K] K) (a_1 : LieModule.Weight K (↥H) L) (a_2 : ¬a_1.IsZero),
          ⟨a_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L a_1 = a → a = 0
    [prop] ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₁) = (x ∉ ∅)
    [prop] ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₂) = (x ∉ ∅)
    [prop] ∀ (a : LieModule.Weight K (↥H) L) (a_1 : ¬a.IsZero), ⟨a, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L a = 0
    [prop] (val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val ∈ Finset.univ ∧ ¬val.IsZero)
    [prop] ∀ (a : ¬val.IsZero), ⟨val, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val = 0
    [prop] val ∈ Finset.univ
    [prop] (fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
            ⨆ (_ : α ∈ Φ₂),
              (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) =
          fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
          ⨆ (_ : α ∈ Φ₁), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
    [prop] val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] (⟨val_1, ⋯⟩ ∈ Φ₁) = (⟨val_1, ⋯⟩ ∉ ∅)
    [prop] (val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val_1 ∈ Finset.univ ∧ ¬val_1.IsZero)
    [prop] (⟨val_1, ⋯⟩ ∈ Φ₁ ∩ Φ₂) = (⟨val_1, ⋯⟩ ∈ Φ₁ ∧ ⟨val_1, ⋯⟩ ∈ Φ₂)
    [prop] ⟨val_1, ⋯⟩ ∉ ∅
    [prop] ∀ (a : ¬val_1.IsZero), ⟨val_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_1 = 0
    [prop] val_1 ∈ Finset.univ
    [prop] val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] (⟨val_2, ⋯⟩ ∈ Φ₂) = (⟨val_2, ⋯⟩ ∉ ∅)
    [prop] (val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val_2 ∈ Finset.univ ∧ ¬val_2.IsZero)
    [prop] (⟨val_2, ⋯⟩ ∈ Φ₁ ∩ Φ₂) = (⟨val_2, ⋯⟩ ∈ Φ₁ ∧ ⟨val_2, ⋯⟩ ∈ Φ₂)
    [prop] ⟨val_2, ⋯⟩ ∉ ∅
    [prop] ∀ (a : ¬val_2.IsZero), ⟨val_2, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_2 = 0
    [prop] val_2 ∈ Finset.univ
  [eqc] True propositions
    [prop] Nontrivial ↥H
    [prop] Nontrivial (↥H →ₗ[K] K)
    [prop] CharZero K
    [prop] (fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
            ⨆ (_ : α ∈ Φ₂),
              (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) =
          fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
          ⨆ (_ : α ∈ Φ₁), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
    [prop] IsNoetherian K L
    [prop] LieAlgebra.IsKilling K L
    [prop] LieModule.IsNilpotent ↥H ↥H
    [prop] ⟨val, ⋯⟩ ∈ Φ₁
    [prop] val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] Module.Finite K L
    [prop] NoZeroSMulDivisors K L
    [prop] SMulCommClass K K K
    [prop] IsScalarTower K K L
    [prop] H.IsCartanSubalgebra
    [prop] LieModule K (↥H) L
    [prop] LieModule.IsTriangularizable K (↥H) L
    [prop] (LieAlgebra.IsKilling.rootSystem H).IsIrreducible
    [prop] LieModule.LinearWeights K (↥H) L
    [prop] ∀
          (i : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₁ })
          (j : { x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} } // x ∈ Φ₂ }),
          (LieAlgebra.IsKilling.rootSystem H).pairing
              (↑i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} })
              (↑j : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =
            0
    [prop] ∀ (q : Submodule K ↥H),
          ¬q = ⊥ →
            (∃ (i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
                q ∉ Module.End.invtSubmodule (↑((LieAlgebra.IsKilling.rootSystem H).coreflection i) : ↥H →ₗ[K] ↥H)) ∨
              q = ⊤
    [prop] ∀ (a : LieModule.Weight K (↥H) L) (a_1 : ¬a.IsZero), ⟨a, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L a = 0
    [prop] ∀ (a : ↥H →ₗ[K] K) (a_1 : LieModule.Weight K (↥H) L) (a_2 : ¬a_1.IsZero),
          ⟨a_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L a_1 = a → a = 0
    [prop] ⟨val_1, ⋯⟩ ∉ ∅
    [prop] ⟨val_2, ⋯⟩ ∉ ∅
    [prop] ¬val.IsZero
    [prop] val ∈ Finset.univ ∧ ¬val.IsZero
    [prop] ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₁) = (x ∉ ∅)
    [prop] ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₂) = (x ∉ ∅)
    [prop] (⟨val_1, ⋯⟩ ∈ Φ₁) = (⟨val_1, ⋯⟩ ∉ ∅)
    [prop] (⟨val_2, ⋯⟩ ∈ Φ₂) = (⟨val_2, ⋯⟩ ∉ ∅)
    [prop] (val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val ∈ Finset.univ ∧ ¬val.IsZero)
    [prop] LieModule.Weight.toLinear K (↥H) L val = 0
    [prop] ⟨val_1, ⋯⟩ ∈ Φ₁
    [prop] ⟨val_2, ⋯⟩ ∈ Φ₂
    [prop] val ∈ Finset.univ
    [prop] val ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] ∀ (a : ¬val.IsZero), ⟨val, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val = 0
    [prop] ⟨val, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val = 0
    [prop] ¬val_1.IsZero
    [prop] ¬val_2.IsZero
    [prop] val_1 ∈ Finset.univ ∧ ¬val_1.IsZero
    [prop] val_2 ∈ Finset.univ ∧ ¬val_2.IsZero
    [prop] (⟨val_1, ⋯⟩ ∈ Φ₁ ∩ Φ₂) = (⟨val_1, ⋯⟩ ∈ Φ₁ ∧ ⟨val_1, ⋯⟩ ∈ Φ₂)
    [prop] (⟨val_2, ⋯⟩ ∈ Φ₁ ∩ Φ₂) = (⟨val_2, ⋯⟩ ∈ Φ₁ ∧ ⟨val_2, ⋯⟩ ∈ Φ₂)
    [prop] (val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val_1 ∈ Finset.univ ∧ ¬val_1.IsZero)
    [prop] (val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}) = (val_2 ∈ Finset.univ ∧ ¬val_2.IsZero)
    [prop] LieModule.Weight.toLinear K (↥H) L val_1 = 0
    [prop] val ∈ Finset.univ
    [prop] val_1 ∈ Finset.univ
    [prop] val_2 ∈ Finset.univ
    [prop] val_1 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] val_2 ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}
    [prop] ∀ (a : ¬val_1.IsZero), ⟨val_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_1 = 0
    [prop] ∀ (a : ¬val_2.IsZero), ⟨val_2, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_2 = 0
    [prop] ⟨val_1, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_1 = 0
    [prop] ⟨val_2, ⋯⟩ ∈ Φ₁ → LieModule.Weight.toLinear K (↥H) L val_2 = 0
    [prop] val_1 ∈ Finset.univ
    [prop] val_2 ∈ Finset.univ
  [eqc] False propositions
    [prop] I = ⊥
    [prop] I = ⊤
    [prop] LieIdeal.killingCompl K L I = ⊥
    [prop] Φ₁ = ∅
    [prop] Φ₂ = ∅
    [prop] LieAlgebra.IsSimple K L
    [prop] ⟨val_1, ⋯⟩ ∈ ∅
    [prop] ⟨val_2, ⋯⟩ ∈ ∅
    [prop] val.IsZero
    [prop] ⟨val_1, ⋯⟩ ∈ Φ₁ ∧ ⟨val_1, ⋯⟩ ∈ Φ₂
    [prop] ⟨val_2, ⋯⟩ ∈ Φ₁ ∧ ⟨val_2, ⋯⟩ ∈ Φ₂
    [prop] ⟨val_2, ⋯⟩ ∈ Φ₁
    [prop] ⟨val_1, ⋯⟩ ∈ Φ₂
    [prop] ⟨val_1, ⋯⟩ ∈ Φ₁ ∩ Φ₂
    [prop] ⟨val_2, ⋯⟩ ∈ Φ₁ ∩ Φ₂
    [prop] val_1.IsZero
    [prop] val_2.IsZero
  [eqc] Equivalence classes
    [eqc] {Set.univ, Φ₁ ∪ Φ₂}
    [eqc] {⊥, (↑I : Submodule K L) ⊓ (↑(LieIdeal.killingCompl K L I) : Submodule K L)}
    [eqc] {∅, Φ₁ ∩ Φ₂}
    [eqc] {Finset.univ, Finset.univ}
    [eqc] {⊤, (↑I : Submodule K L) ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L)}
    [eqc] {{α : LieModule.Weight K (↥H) L | ¬α.IsZero}, {α : LieModule.Weight K (↥H) L | ¬α.IsZero}}
    [eqc] {(↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule,
        H.toSubmodule}
    [eqc] {(↑I : Submodule K L) ⊓ H.toSubmodule ⊔
          ⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L),
        (↑I : Submodule K L)}
    [eqc] {(↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule ⊔
          ⨆ α ∈ Φ₂, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L),
        (↑(LieIdeal.killingCompl K L I) : Submodule K L)}
    [eqc] {Membership.mem H, fun (x : L) => x ∈ H}
    [eqc] {Membership.mem Φ₁,
        fun (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) => x ∈ Φ₁}
    [eqc] {Membership.mem Φ₂,
        fun (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) => x ∈ Φ₂}
    [eqc] {Membership.mem {α : LieModule.Weight K (↥H) L | ¬α.IsZero},
        fun (x : LieModule.Weight K (↥H) L) => x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}}
    [eqc] {⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L),
        ⨆ α ∈ Φ₂, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)}
    [eqc] {LieModule.Weight K (↥H) L, LieModule.Weight K (↥H) L}
    [eqc] {fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
          ⨆ (_ : α ∈ Φ₁), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L),
        fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
          ⨆ (_ : α ∈ Φ₂), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)}
    [eqc] {0, LieModule.Weight.toLinear K (↥H) L val, LieModule.Weight.toLinear K (↥H) L val_1}
  [cases] Case analyses
    [cases] [1/2]: (fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
            ⨆ (_ : α ∈ Φ₂),
              (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) =
          fun (α : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
          ⨆ (_ : α ∈ Φ₁), (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
      [cases] source: Initial goal
    [cases] [1/1]: ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₁) = (x ∉ ∅)
      [cases] source: Extensionality Set.ext
    [cases] [1/1]: ∃ (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
          (x ∈ Φ₂) = (x ∉ ∅)
      [cases] source: Extensionality Set.ext
  [ematch] E-matching patterns
    [thm] Finset.mem_filter: [@Membership.mem #4 (Finset _) _ (@Finset.filter _ #3 #2 #1) #0]
    [thm] Finset.mem_univ: [@Membership.mem #2 (Finset _) _ (@Finset.univ _ #1) #0]
    [thm] Finset.bot_eq_empty: [@Bot.bot (Finset #0) _]
    [thm] Finset.sup_eq_union: [@Max.max (Finset #3) _ #1 #0]
    [thm] max_def: [@Max.max #3 _ #1 #0]
    [thm] Int.max_def: [@Max.max `[ℤ] `[Int.instMax] #1 #0]
    [thm] Nat.max_def: [@Max.max `[ℕ] `[Nat.instMax] #1 #0]
    [thm] Finset.inf_eq_inter: [@Min.min (Finset #3) _ #1 #0]
    [thm] min_def: [@Min.min #3 _ #1 #0]
    [thm] Int.min_def: [@Min.min `[ℤ] `[Int.instMin] #1 #0]
    [thm] Nat.min_def: [@Min.min `[ℕ] `[instMinNat] #1 #0]
    [thm] Finset.mem_inter: [@Membership.mem #4 (Finset _) _ (@Inter.inter (Finset _) _ #1 #0) #2]
    [thm] Set.mem_inter_iff: [@Membership.mem #3 _ _ (@Inter.inter _ _ #1 #0) #2]
    [thm] Finset.notMem_empty: [@Membership.mem #1 (Finset _) _ (@EmptyCollection.emptyCollection (Finset _) _) #0]
    [thm] Set.mem_empty_iff_false: [@Membership.mem #1 _ _ (@EmptyCollection.emptyCollection _ _) #0]
    [thm] Finset.mem_union: [@Membership.mem #4 (Finset _) _ (@Union.union (Finset _) _ #2 #1) #0]
    [thm] Set.mem_union: [@Membership.mem #3 _ _ (@Union.union _ _ #1 #0) #2]
    [thm] Set.mem_univ: [@Membership.mem #1 _ _ (@Set.univ _) #0]
    [thm] xxx: [@RootPairing.pairing `[{ x : LieModule.Weight K (↥H) L //
           x ∈
             {α : LieModule.Weight K (↥H) L |
               ¬α.IsZero} }] `[K] `[↥H →ₗ[K]
           K] `[↥H] `[Field.toEuclideanDomain.toCommRing] `[LinearMap.addCommGroup] `[LinearMap.module] `[(LieSubalgebra.lieRing
             K L
             H).toAddCommGroup] `[LieSubalgebra.instModuleSubtypeMemOfIsScalarTower K L
           H] `[(LieAlgebra.IsKilling.rootSystem
             H).toRootPairing] (@Subtype.val `[{ x : LieModule.Weight K (↥H) L //
            x ∈
              {α : LieModule.Weight K (↥H) L |
                ¬α.IsZero} }] `[fun
              (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
            x ∈
              Φ₁] #1) (@Subtype.val `[{ x : LieModule.Weight K (↥H) L //
            x ∈
              {α : LieModule.Weight K (↥H) L |
                ¬α.IsZero} }] `[fun
              (x : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }) =>
            x ∈ Φ₂] #0)]
    [thm] local_0: [@LieModule.Weight.IsZero `[K] `[↥H] `[L] `[Field.toEuclideanDomain.toCommRing] `[LieSubalgebra.lieRing
           K L
           H] `[LieSubalgebra.lieAlgebra K L
           H] `[inst_2.toAddCommGroup] `[inst_3.toModule] `[H.lieRingModule] `[‹LieModule K (↥H)
             L›] `[‹LieModule.IsNilpotent ↥H ↥H›] #2]
    [thm] local_0: [@Membership.mem `[{ x : LieModule.Weight K (↥H) L //
           x ∈
             {α : LieModule.Weight K (↥H) L |
               ¬α.IsZero} }] `[Set
           { x : LieModule.Weight K (↥H) L //
             x ∈
               {α : LieModule.Weight K (↥H) L |
                 ¬α.IsZero} }] `[Set.instMembership] `[Φ₁] (@Subtype.mk `[LieModule.Weight K (↥H)
            L] `[fun (x : LieModule.Weight K (↥H) L) => x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}] #2 _)]
    [thm] local_0: [@Subtype.mk `[LieModule.Weight K (↥H)
           L] `[fun (x : LieModule.Weight K (↥H) L) => x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero}] #2 _]
    [thm] local_0: [LieModule.Weight.toLinear `[K] `[↥H] `[L] `[Field.toEuclideanDomain.toCommRing] `[LieSubalgebra.lieRing
           K L
           H] `[LieSubalgebra.lieAlgebra K L
           H] `[inst_2.toAddCommGroup] `[inst_3.toModule] `[H.lieRingModule] `[‹LieModule K (↥H)
             L›] `[‹LieModule.IsNilpotent ↥H ↥H›] `[‹LieModule.LinearWeights K (↥H) L›] #2]
    [thm] Multiset.notMem_zero: [@Membership.mem #1 _ _ (@OfNat.ofNat _ `[0] _) #0]
    [thm] Ideal.one_eq_top: [@OfNat.ofNat (Submodule #1 _ #0 _ _) `[1] _]
  [linarith] Linarith assignment for `↥H →ₗ[K] K`
    [assign] LieModule.Weight.toLinear K (↥H) L val := 0
    [assign] LieModule.Weight.toLinear K (↥H) L val_1 := 0
    [assign] LieModule.Weight.toLinear K (↥H) L val_2 := 2
  [assoc] Operators
    [assoc] Operator `Max.max`
      [basis] Basis
        [_] ⨆ α ∈ Φ₂, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L) =
              ⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)
        [_] (↑I : Submodule K L) ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L) =
              (↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L)
        [_] (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule ⊔ (↑I : Submodule K L) =
              (↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑(LieIdeal.killingCompl K L I) : Submodule K L)
        [_] (⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) ⊔
                (↑(LieIdeal.killingCompl K L I) : Submodule K L) =
              (↑(LieIdeal.killingCompl K L I) : Submodule K L)
        [_] (⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) ⊔
                (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule =
              (↑(LieIdeal.killingCompl K L I) : Submodule K L)
        [_] (↑(LieIdeal.killingCompl K L I) : Submodule K L) ⊓ H.toSubmodule ⊔
                (↑(LieIdeal.killingCompl K L I) : Submodule K L) =
              (↑(LieIdeal.killingCompl K L I) : Submodule K L)
        [_] (⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L)) ⊔
                (↑I : Submodule K L) =
              (↑I : Submodule K L)
        [_] (↑I : Submodule K L) ⊓ H.toSubmodule ⊔ (↑I : Submodule K L) = (↑I : Submodule K L)
        [_] (↑I : Submodule K L) ⊓ H.toSubmodule ⊔
                ⨆ α ∈ Φ₁, (↑(LieModule.genWeightSpace L (⇑(↑α : LieModule.Weight K (↥H) L) : ↥H → K)) : Submodule K L) =
              (↑I : Submodule K L)
      [properties] Properties
        [_] commutative
        [_] idempotent
    [assoc] Operator `Inter.inter`
      [diseqs] Disequalities
        [_] Φ₁ ≠ Φ₁ ∩ Φ₂
        [_] Φ₂ ≠ Φ₁ ∩ Φ₂
      [properties] Properties
        [_] commutative
[grind] Issues
  [issue] failed to create E-match local theorem for
        ∀ (q : Submodule K ↥H),
          ¬q = ⊥ →
            (∃ (i : { x : LieModule.Weight K (↥H) L // x ∈ {α : LieModule.Weight K (↥H) L | ¬α.IsZero} }),
                q ∉ Module.End.invtSubmodule (↑((LieAlgebra.IsKilling.rootSystem H).coreflection i) : ↥H →ₗ[K] ↥H)) ∨
              q = ⊤
  [issue] failed to synthesize instance when instantiating max_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating max_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating max_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating max_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating min_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating min_def
        LinearOrder (Submodule K L)
  [issue] failed to synthesize instance when instantiating min_def
        LinearOrder (Submodule K L)
[grind] Diagnostics
  [thm] E-Matching instances
    [thm] Finset.mem_filter ↦ 3
    [thm] Finset.mem_univ ↦ 3
    [thm] Set.mem_empty_iff_false ↦ 2
    [thm] Set.mem_inter_iff ↦ 2
  [cases] Cases instances
    [cases] Subtype ↦ 3-/
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
  let S := rootSystem H
  have xxx (i : Φ₁) (j : Φ₂) : S.pairing i j = 0 := by
    -- S.pairing i j = i(h_j) where h_j = coroot j
    rw [rootSystem_pairing_apply]
    -- Get nonzero e_i ∈ rootSpace H i
    have hi_nonzero : i.val.val.IsNonZero := by
      have := i.val.property
      simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hj_nonzero : j.val.val.IsNonZero := by
      have := j.val.property
      simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    obtain ⟨e_i, he_i, he_i_ne⟩ := Weight.exists_ne_zero (R := K) (L := H) (M := L) i.val.val
    -- e_i ∈ I (since i ∈ Φ₁)
    have he_i_in_I : e_i ∈ I := by
      have : (rootSpace H i.val.val).toSubmodule ≤ I.toSubmodule := by
        rw [hΦ₁]; exact le_sup_of_le_right (le_iSup₂_of_le i.val i.property le_rfl)
      exact this he_i
    -- coroot j ∈ J (since j ∈ Φ₂ and J contains corootSpace via sl2 structure)
    -- Key: coroot is generated by [e_j, f_j] where e_j ∈ rootSpace j and f_j ∈ rootSpace (-j)
    -- Both are in J, hence [e_j, f_j] ∈ J since J is an ideal
    have h_neg_j_root : -j.val.val ∈ LieSubalgebra.root := by
      simp only [LieSubalgebra.root, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Weight.IsNonZero.neg hj_nonzero
    have h_neg_j_in_Φ₂ : ⟨-j.val.val, h_neg_j_root⟩ ∈ Φ₂ := by
      -- If -j ∈ Φ₁, then corootSpace j ⊆ I ∩ J = ⊥, contradicting j being a nonzero root
      by_contra h_neg_not_in_Φ₂
      have h_neg_in_Φ₁ : ⟨-j.val.val, h_neg_j_root⟩ ∈ Φ₁ := by
        have := s3.symm.subset (Set.mem_univ ⟨-j.val.val, h_neg_j_root⟩)
        simp only [Set.mem_union] at this
        exact this.resolve_right h_neg_not_in_Φ₂
      sorry -- corootSpace contradiction argument
    have h_coroot_in_J : (coroot j.val.val : L) ∈ J := by
      -- coroot j ∈ span{[e,f] : e ∈ rootSpace j, f ∈ rootSpace (-j)}
      -- Both rootSpace j ⊆ J and rootSpace (-j) ⊆ J (since j, -j ∈ Φ₂)
      -- Since J is a Lie ideal, [e,f] ∈ J, hence coroot j ∈ J
      sorry
    -- [h_j, e_i] = i(h_j) • e_i
    have h_lie_smul : ⁅(coroot j.val.val : L), e_i⁆ = i.val.val (coroot j.val.val) • e_i := by
      exact lie_eq_smul_of_mem_rootSpace he_i (coroot j.val.val)
    -- [h_j, e_i] ∈ I ∩ J = ⊥
    have h_in_I : ⁅(coroot j.val.val : L), e_i⁆ ∈ I := I.lie_mem he_i_in_I
    have h_in_J : ⁅(coroot j.val.val : L), e_i⁆ ∈ J := by
      rw [← lie_skew]
      exact J.neg_mem (J.lie_mem h_coroot_in_J)
    have h_zero : ⁅(coroot j.val.val : L), e_i⁆ = 0 := by
      have h_inf : ⁅(coroot j.val.val : L), e_i⁆ ∈ I.toSubmodule ⊓ J.toSubmodule := ⟨h_in_I, h_in_J⟩
      simp only [bot_1] at h_inf
      exact h_inf
    -- Since e_i ≠ 0, we get i(h_j) = 0
    rw [h_lie_smul] at h_zero
    exact (smul_eq_zero.mp h_zero).resolve_right he_i_ne
  have := hIrr;
  cases this;
  rename_i h₁ h₂ h₃;
  contrapose! h₂;
  refine' ⟨ Submodule.span K ( Set.image ( fun i : Φ₁ => ( LieAlgebra.IsKilling.rootSystem H ).root i ) Set.univ ), _, _, _ ⟩;
  · intro i;
    simp +decide [ Module.End.mem_invtSubmodule ];
    rw [ Submodule.span_le ];
    rintro _ ⟨ a, rfl ⟩;
    simp +decide [ RootPairing.reflection_apply, xxx ];
    refine' Submodule.sub_mem _ _ _;
    · exact Submodule.subset_span ⟨ a, rfl ⟩;
    · by_cases hi : i ∈ Φ₁;
      · exact Submodule.smul_mem _ _ ( Submodule.subset_span ⟨ ⟨ i, hi ⟩, rfl ⟩ );
      · -- Since $i \notin \Phi_1$, we have $i \in \Phi_2$.
        have hi₂ : i ∈ Φ₂ := by
          exact Or.resolve_left ( s3.symm.subset ( Set.mem_univ i ) ) hi;
        specialize xxx a ⟨ i, hi₂ ⟩;
        simp +zetaDelta at *;
        simp +decide [ xxx ];
  · simp +decide [ Submodule.ne_bot_iff ];
    obtain ⟨ x, hx ⟩ := Set.nonempty_iff_ne_empty.2 s4;
    -- Since $x$ is in $\Phi_1$, we can take $x$ as the element in $\Phi_1$.

    grind;
  · -- Since Φ₁ is a proper subset of the roots, the span of the roots in Φ₁ cannot be the entire space.
    have h_span_proper : Submodule.span K (Set.image (fun i : Φ₁ => S.root i) Set.univ) ≠ ⊤ := by
      have h_nonzero : ∃ j : { x : LieModule.Weight K (↥H) L // x ∈ LieSubalgebra.root }, j ∈ Φ₂ := by
        exact Set.nonempty_iff_ne_empty.2 s5
      obtain ⟨ j, hj ⟩ := h_nonzero;
      intro h;
      rw [ Submodule.eq_top_iff' ] at h;
      specialize h ( S.root j );
      rw [ Finsupp.mem_span_image_iff_linearCombination ] at h;
      obtain ⟨ l, hl₁, hl₂ ⟩ := h;
      replace hl₂ := congr_arg ( fun f => f ( S.coroot j ) ) hl₂ ; simp +decide [ Finsupp.linearCombination_apply, Finsupp.sum ] at hl₂;
      simp +zetaDelta at *;
      -- Since each term in the sum is zero, the entire sum must be zero.
      have h_sum_zero : ∑ x ∈ l.support, (l x) * ((x.val : LieModule.Weight K (↥H) L) : ↥H → K) (LieAlgebra.IsKilling.coroot (j.val)) = 0 := by
        -- Since each term in the sum is zero, the entire sum must be zero. We can apply the hypothesis `xxx` to each term in the sum.
        have h_term_zero : ∀ x ∈ l.support, (l x) * ((x.val : LieModule.Weight K (↥H) L) : ↥H → K) (LieAlgebra.IsKilling.coroot (j.val)) = 0 := by
          grind;
        exact Finset.sum_eq_zero h_term_zero;
      simp +decide [ h_sum_zero ] at hl₂;
      -- Since $j$ is a root, we have $j(coroot j) = 2$.
      have h_root_coroot : (j.val : ↥H → K) (LieAlgebra.IsKilling.coroot (j.val)) = 2 := by
        -- By definition of the coroot, we have that the root applied to the coroot is 2.
        apply LieAlgebra.IsKilling.root_apply_coroot;
        grind;
      norm_num [ h_root_coroot ] at hl₂;
    exact h_span_proper

end LieAlgebra.IsKilling