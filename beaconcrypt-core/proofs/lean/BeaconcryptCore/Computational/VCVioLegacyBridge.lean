import BeaconcryptCore.Computational.VCVioForwardEvalDist
import BeaconcryptCore.Computational.VCVioForwardOracleComp

/-!
# Transitional bridge between the deprecated and the forward probability vocabulary (VCVio pin 98dc1089)

This is the only project module allowed to contain the deprecated VCVio probability syntax (`Pr[= x | mx]`, `Pr[p | mx]`, `𝒮[mx]`), each use under an explicit `set_option linter.deprecated false in`. It relates the deprecated forms to the forward vocabulary of `VCVioForwardEvalDist`:

* `Pr[= x | mx] = Pr{let y ← mx}[y = x]` and `Pr[p | mx] = Pr{let x ← mx}[p x]`, with no measurable-space hypothesis on the output type;
* `𝒮[mx] = 𝒮[my] ↔ mx =ᵈ my`;
* the measure forms `Pr[= x | mx] = 𝒟[mx] {x}` (measurable singletons) and `Pr[p | mx] = 𝒟[mx] {x | p x}` (discrete outputs).

The primary bridges are stated for `ProbComp`, so that the pin's `DiscreteEvalDistCompatible` link, which upstream removes, stays inside the bridge's proofs; versions for any monad with that link (suffix `_of_compatible`) and for oracle computations over a variable uniform specification (prefix `oracleComp_`) cover the remaining cases. The tactic `vcvio_legacy` rewrites a deprecated-form goal or hypothesis into the forward form. The commands `vcvio_legacy_twin` and `vcvio_legacy_certificate` implement the transitional twins and the statement certificates of the migration plan. Migrated proofs use these lemmas where a statement outside the current migration stage, or a VCVio lemma, is still stated in the deprecated form; every such use names `VCVioLegacy` or `vcvio_legacy`, so the remaining uses are greppable and counted. The module is transitional: it is deleted at the VCVio upgrade, after which no deprecated form exists. Nothing here is assumed: every bridge is proved from the pinned VCVio.
-/

open MeasureTheory
open scoped ENNReal

set_option autoImplicit false

universe v v'

namespace BeaconcryptCore.VCVioLegacy

open Lean.Parser.Tactic

/-! ## Bridges for an arbitrary monad with the pin's discrete compatibility

These are stated for every monad with the pinned semantic classes and the pin's `DiscreteEvalDistCompatible` link, which upstream removes. A proof that uses them carries that instance in its term, so migrated proofs use the `ProbComp` and oracle forms below, which keep the link inside the bridge. -/

set_option linter.deprecated false in
/-- The deprecated output probability is the singleton mass of the output measure, for outputs with measurable singletons (any compatible monad). -/
theorem probOutput_eq_evalDist_singleton_of_compatible {m : Type → Type v} [MonadLiftT m SPMF]
    [EvalDistSemantics m] [DiscreteEvalDistCompatible m] {α : Type} [MeasurableSpace α]
    [MeasurableSingletonClass α] (mx : m α) (x : α) : Pr[= x | mx] = 𝒟[mx] {x} :=
  (evalDist_apply_singleton mx x).symm

set_option linter.deprecated false in
/-- The deprecated event probability is the mass of the event under the output measure, for discrete outputs (any compatible monad). -/
theorem probEvent_eq_evalDist_setOf_of_compatible {m : Type → Type v} [MonadLiftT m SPMF]
    [EvalDistSemantics m] [DiscreteEvalDistCompatible m] {α : Type} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] (mx : m α) (p : α → Prop) : Pr[p | mx] = 𝒟[mx] {x | p x} :=
  (evalDist_apply_setOf mx p).symm

set_option linter.deprecated false in
/-- The deprecated output probability is the forward singleton event (any compatible monad); no measurable space on the output is needed. -/
theorem probOutput_eq_prEvent_of_compatible {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [DiscreteEvalDistCompatible m] {α : Type} (mx : m α) (x : α) :
    Pr[= x | mx] = Pr{let y ← mx}[y = x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_singleton mx x, probOutput_eq_evalDist_singleton_of_compatible]

set_option linter.deprecated false in
/-- The deprecated event probability is the forward event (any compatible monad); no measurable space on the output is needed. -/
theorem probEvent_eq_prEvent_of_compatible {m : Type → Type v} [Monad m] [LawfulMonad m]
    [MonadLiftT m SPMF] [EvalDistSemantics m] [LawfulEvalDistSemantics m]
    [DiscreteEvalDistCompatible m] {α : Type} (mx : m α) (p : α → Prop) :
    Pr[p | mx] = Pr{let x ← mx}[p x] := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_eq_evalDist_of_discrete mx p, probEvent_eq_evalDist_setOf_of_compatible]

set_option linter.deprecated false in
/-- Equal deprecated output distributions are equality in distribution (any two compatible monads); no measurable space on the output is needed. -/
theorem evalSPMF_eq_iff_evalDistEq_of_compatible {m : Type → Type v} {m' : Type → Type v'}
    [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m'] [MonadLiftT m SPMF]
    [MonadLiftT m' SPMF] [EvalDistSemantics m] [EvalDistSemantics m'] [LawfulEvalDistSemantics m]
    [LawfulEvalDistSemantics m'] [DiscreteEvalDistCompatible m] [DiscreteEvalDistCompatible m']
    {α : Type} (mx : m α) (my : m' α) : 𝒮[mx] = 𝒮[my] ↔ mx =ᵈ my := by
  constructor
  · intro h p
    rw [← probEvent_eq_prEvent_of_compatible, ← probEvent_eq_prEvent_of_compatible]
    unfold probEvent
    rw [h]
  · intro h
    refine evalSPMF_ext fun x ↦ ?_
    rw [probOutput_eq_prEvent_of_compatible, probOutput_eq_prEvent_of_compatible]
    exact h (· = x)

/-! ## Bridges for `ProbComp`

The primary bridges. Their statements use `ProbComp`'s own instances, so they rewrite the terms of project statements directly, and the compatibility link stays inside their proofs. -/

set_option linter.deprecated false in
/-- The deprecated output probability of a probabilistic computation is the forward singleton event. -/
theorem probOutput_eq_prEvent {α : Type} (mx : ProbComp α) (x : α) :
    Pr[= x | mx] = Pr{let y ← mx}[y = x] :=
  probOutput_eq_prEvent_of_compatible mx x

set_option linter.deprecated false in
/-- The deprecated event probability of a probabilistic computation is the forward event. -/
theorem probEvent_eq_prEvent {α : Type} (mx : ProbComp α) (p : α → Prop) :
    Pr[p | mx] = Pr{let x ← mx}[p x] :=
  probEvent_eq_prEvent_of_compatible mx p

set_option linter.deprecated false in
/-- Equal deprecated output distributions of probabilistic computations are equality in distribution. -/
theorem evalSPMF_eq_iff_evalDistEq {α : Type} (mx my : ProbComp α) : 𝒮[mx] = 𝒮[my] ↔ mx =ᵈ my :=
  evalSPMF_eq_iff_evalDistEq_of_compatible mx my

set_option linter.deprecated false in
/-- The deprecated output probability of a probabilistic computation is the singleton mass of its output measure. -/
theorem probOutput_eq_evalDist_singleton {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : ProbComp α) (x : α) : Pr[= x | mx] = 𝒟[mx] {x} :=
  probOutput_eq_evalDist_singleton_of_compatible mx x

set_option linter.deprecated false in
/-- The singleton mass of a probabilistic computation's output measure is the deprecated output probability (the reverse bridge, for proofs whose statement is still deprecated). -/
theorem evalDist_singleton_eq_probOutput {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : ProbComp α) (x : α) : 𝒟[mx] {x} = Pr[= x | mx] :=
  (probOutput_eq_evalDist_singleton_of_compatible mx x).symm

set_option linter.deprecated false in
/-- The deprecated event probability of a probabilistic computation is the mass of the event, for discrete outputs. -/
theorem probEvent_eq_evalDist_setOf {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) (p : α → Prop) : Pr[p | mx] = 𝒟[mx] {x | p x} :=
  probEvent_eq_evalDist_setOf_of_compatible mx p

/-! ## Bridges for oracle computations with uniform answers

For oracle computations over a specification with uniform answers that is a variable with an `[IsUniformSpec spec]` hypothesis. Their statements use the semantics available in that context, the pin's `SPMF` adapter; for a concrete specification with measurable answer types, whose computations use VCVio's native free-monad semantics, use the bridges for any compatible monad instead. Not used by `vcvio_legacy`. -/

set_option linter.deprecated false in
/-- The deprecated output probability of an oracle computation with uniform answers is the forward singleton event. -/
theorem oracleComp_probOutput_eq_prEvent {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx : OracleComp spec α) (x : α) : Pr[= x | mx] = Pr{let y ← mx}[y = x] :=
  probOutput_eq_prEvent_of_compatible mx x

set_option linter.deprecated false in
/-- The deprecated event probability of an oracle computation with uniform answers is the forward event. -/
theorem oracleComp_probEvent_eq_prEvent {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx : OracleComp spec α) (p : α → Prop) : Pr[p | mx] = Pr{let x ← mx}[p x] :=
  probEvent_eq_prEvent_of_compatible mx p

set_option linter.deprecated false in
/-- Equal deprecated output distributions of oracle computations with uniform answers are equality in distribution. -/
theorem oracleComp_evalSPMF_eq_iff_evalDistEq {ι : Type} {spec : OracleSpec ι} [spec.IsUniformSpec]
    {α : Type} (mx my : OracleComp spec α) : 𝒮[mx] = 𝒮[my] ↔ mx =ᵈ my :=
  evalSPMF_eq_iff_evalDistEq_of_compatible mx my

/-- Rewrite the deprecated probability forms `Pr[= x | mx]`, `Pr[p | mx]` and `𝒮[mx] = 𝒮[my]`, in the goal or in the given hypotheses, into the forward forms `Pr{let y ← mx}[y = x]`, `Pr{let x ← mx}[p x]` and `mx =ᵈ my`: first with the `ProbComp` bridges, then, for the forms that remain, with the bridges for any compatible monad, whose semantics instance is the one found in context. -/
macro "vcvio_legacy" loc:(location)? : tactic =>
  match loc with
  | some l => `(tactic| first
      | (simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq] $l:location
         try simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible] $l:location)
      | simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible] $l:location)
  | none => `(tactic| first
      | (simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq]
         try simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible])
      | simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible])

/-! ## Certificates and transitional twins (plan section 5.2)

`vcvio_legacy_twin T` and `vcvio_legacy_certificate T against S from "dump.jsonl"` compute the deprecated-vocabulary statement of a restated declaration `T` by inverting the vocabulary map, so the old type is built programmatically and contains no deprecated syntax. The certificate compares it with the pre-stage declaration dump (type hash and single-line `pp.all` text) and proves `T ↔ old statement` (or, for a wrapper definition, `T = old body`) through the bridge lemmas; the twin adds `T_vcvioLegacy : old statement` for later-stage consumers. -/

section tooling

open Lean Meta Elab Command Term

/-- `{True}` as a set of propositions. -/
private def isSingletonTrue (e : Expr) : Bool :=
  e.isAppOfArity ``Singleton.singleton 4 && e.appArg!.isConstOf ``True

/-- One step of the inverse vocabulary map: the forward forms `Pr{let y ← mx}[y = x]`, `Pr{let x ← mx}[p x]` (the pin
expansion `𝒟[mx >>= fun y => pure (…)] {True}`) and `mx =ᵈ my` become `probOutput mx x`, `probEvent mx p` and
`evalSPMF mx = evalSPMF my`, with their instance arguments synthesized in the current context. A singleton event
`y = x` is ambiguous: it is the forward form of both `Pr[= x | mx]` and `Pr[fun y => y = x | mx]`; so is an event
`f y` whose predicate is eta-reducible: it is the forward form of both `Pr[fun y => f y | mx]` and `Pr[f | mx]`.
Ambiguous nodes are numbered in traversal order; when bit `i` of `mask` is set, node `i` takes the second reading
(`probEvent` with the singleton predicate, resp. the eta-reduced predicate), otherwise the first. -/
def legacyNode? (mask : Nat) (counter : IO.Ref Nat) (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOfArity ``DFunLike.coe 6 then
    let args := e.getAppArgs
    let meas := args[4]!
    if meas.isAppOfArity ``evalDist 5 && isSingletonTrue args[5]! then
      let margs := meas.getAppArgs
      let m := margs[0]!
      let comp := margs[4]!
      if comp.isAppOfArity ``Bind.bind 6 then
        let bargs := comp.getAppArgs
        let α := bargs[2]!
        let mx := bargs[4]!
        if let .lam n ty body bi := bargs[5]! then
          if body.isAppOfArity ``Pure.pure 4 then
            let ev := body.appArg!
            if ev.isAppOfArity ``Eq 3 && ev.appFn!.appArg! == .bvar 0 && !ev.appArg!.hasLooseBVars then
              let i ← counter.modifyGet fun i => (i, i + 1)
              if mask.testBit i then
                return some (← mkAppOptM ``probEvent #[m, α, none, mx, Expr.lam n ty ev bi])
              return some (← mkAppOptM ``probOutput #[m, α, none, mx, ev.appArg!])
            let lamP := Expr.lam n ty ev bi
            let etaP := lamP.eta
            if etaP != lamP then
              let i ← counter.modifyGet fun i => (i, i + 1)
              if mask.testBit i then
                return some (← mkAppOptM ``probEvent #[m, α, none, mx, etaP])
            return some (← mkAppOptM ``probEvent #[m, α, none, mx, lamP])
    return none
  if e.isAppOfArity ``EvalDistEq 9 then
    let args := e.getAppArgs
    let a ← mkAppOptM ``evalSPMF #[args[0]!, none, args[6]!, args[7]!]
    let b ← mkAppOptM ``evalSPMF #[args[1]!, none, args[6]!, args[8]!]
    return some (← mkEq a b)
  return none

/-- The inverse vocabulary map on a whole expression (statement or definition body), with the event mask of
`legacyNode?`; also returns the number of ambiguous singleton-event nodes. -/
def legacyExpr (e : Expr) (mask : Nat := 0) : MetaM (Expr × Nat) := do
  let counter ← IO.mkRef 0
  let r ← Meta.transform e (post := fun e => do
    match ← legacyNode? mask counter e with
    | some e' => return .done e'
    | none => return .continue)
  return (r, ← counter.get)

/-- The single-line `pp.all` text used by the pre-stage dump and the certificate checker. -/
def legacyPp (e : Expr) : MetaM String :=
  withOptions (fun o => o.setBool `pp.all true) do
    return (← ppExpr e).pretty 1000000

/-- Prove `newType ↔ oldType` by rewriting the deprecated forms of `oldType` into the forward forms with `vcvio_legacy`, or else with the bridges for oracle computations over a variable uniform specification. -/
def legacyIff (newType oldType : Expr) : TermElabM Expr := do
  let goal := mkApp2 (mkConst ``Iff) newType oldType
  let stx ← `(term| by
    first
    | (vcvio_legacy; done)
    | (simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq,
        BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq]; done))
  let pf ← elabTermEnsuringType stx goal
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars pf

/-- `vcvio_legacy_twin T` adds `T_vcvioLegacy`, the statement of `T` in the deprecated vocabulary, proved from `T`
through the bridge lemmas. It is used only for transitional twins of restated declarations consumed by later stages. -/
syntax (name := vcvioLegacyTwin) "vcvio_legacy_twin " ident (" event_mask " num)? : command

@[command_elab vcvioLegacyTwin]
def elabVcvioLegacyTwin : CommandElab := fun stx => do
  let id := stx[1]
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  let mask := if stx[2].isNone then 0 else stx[2][1].isNatLit?.getD 0
  let ci ← getConstInfo n
  unless ci.isTheorem do throwError "vcvio_legacy_twin: {n} is not a theorem"
  liftTermElabM do
    let (oldType, _) ← legacyExpr ci.type mask
    if oldType == ci.type then throwError "vcvio_legacy_twin: {n} has no forward probability form to invert"
    let iff ← legacyIff ci.type oldType
    let lvls := ci.levelParams.map mkLevelParam
    let value := mkApp3 (mkConst ``Iff.mp) ci.type oldType iff |>.app (mkConst n lvls)
    let twin := n.appendAfter "_vcvioLegacy"
    addDecl <| .thmDecl { name := twin, levelParams := ci.levelParams, type := oldType, value }
    logInfo m!"twin {twin} added"

/-- Expected values of one pre-stage dump entry. -/
structure DumpEntry where
  name : String
  kind : String
  typeHash : Nat
  typePp : String
  valueHash : Option Nat := none
  valuePp : Option String := none
  deriving FromJson

/-- `vcvio_legacy_certificate T against S from "dump.jsonl"` checks that the inverse vocabulary map reproduces the
pre-stage declaration `S` (default `T`) exactly from the restated `T`: for a theorem, the generated old statement has
the type hash and `pp.all` text of `S` in the dump, and `T ↔ old statement` is proved through the bridge lemmas; for a
definition (a wrapper), its type is unchanged and the generated old body has the value hash and text of `S`, and
`T = old body` is proved through the bridge lemmas. -/
syntax (name := vcvioLegacyCertificate)
  "vcvio_legacy_certificate " ident (" against " ident)? " from " str : command

@[command_elab vcvioLegacyCertificate]
def elabVcvioLegacyCertificate : CommandElab := fun stx => do
  let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[1])
  let base : Name ← if stx[2].isNone then pure n else
    liftCoreM (realizeGlobalConstNoOverloadWithInfo stx[2][1])
  let path := stx[4].isStrLit?.getD ""
  let lines := (← IO.FS.lines path).toList.filter (· ≠ "")
  let mut entry? : Option DumpEntry := none
  for l in lines do
    let j ← IO.ofExcept (Json.parse l)
    let e : DumpEntry ← IO.ofExcept (fromJson? j)
    if e.name == base.toString then entry? := some e
  let some entry := entry? | throwError "certificate: {base} is not in {path}"
  let ci ← getConstInfo n
  liftTermElabM do
    if ci.isTheorem then
      let (_, k) ← legacyExpr ci.type 0
      unless k ≤ 12 do throwError "certificate: {n} has {k} ambiguous nodes (limit 12)"
      let mut found : Option (Nat × Expr × String) := none
      for mask in List.range (2 ^ k) do
        let (oldType, _) ← legacyExpr ci.type mask
        let pp ← legacyPp oldType
        if oldType.hash.toNat == entry.typeHash && pp == entry.typePp then
          found := some (mask, oldType, pp)
          break
      match found with
      | some (mask, oldType, _) =>
        let _ ← legacyIff ci.type oldType
        logInfo m!"certificate PASS {n} against {base}: event mask {mask} of {k} ambiguous nodes; old statement hash {oldType.hash} and pp.all text equal; {n} ↔ old statement proved"
      | none =>
        let (oldType, _) ← legacyExpr ci.type 0
        let pp ← legacyPp oldType
        throwError "certificate FAIL {n} against {base}: no event mask of {k} ambiguous nodes reproduces the dump; mask 0 gives hash {oldType.hash} vs {entry.typeHash}\nold: {pp}\nexpected: {entry.typePp}"
    else if ci.isDefinition then
      let some v := ci.value? | throwError "certificate: {n} has no value"
      unless ci.type.hash.toNat == entry.typeHash do
        throwError "certificate FAIL {n}: type hash changed ({ci.type.hash} vs {entry.typeHash})"
      let some vh := entry.valueHash | throwError "certificate: no value hash for {base}"
      let (_, k) ← legacyExpr v 0
      unless k ≤ 12 do throwError "certificate: {n} has {k} ambiguous nodes (limit 12)"
      let mut found : Option (Nat × Expr) := none
      for mask in List.range (2 ^ k) do
        let (oldValue, _) ← legacyExpr v mask
        let pp ← legacyPp oldValue
        if oldValue.hash.toNat == vh && some pp == entry.valuePp then
          found := some (mask, oldValue)
          break
      match found with
      | some (mask, oldValue) =>
        let lvls := ci.levelParams.map mkLevelParam
        let goal ← mkEq (mkConst n lvls) oldValue
        let stx ← `(term| by
          delta $(mkIdent n):ident
          first
          | (vcvio_legacy; done)
          | (simp only [BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq,
        BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent,
        BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq]; done))
        let _ ← elabTermEnsuringType stx goal
        synthesizeSyntheticMVarsNoPostponing
        logInfo m!"certificate PASS {n} against {base}: type unchanged; event mask {mask} of {k}; old body hash {oldValue.hash} and pp.all text equal; {n} = old body proved"
      | none =>
        let (oldValue, _) ← legacyExpr v 0
        let pp ← legacyPp oldValue
        throwError "certificate FAIL {n} against {base}: no event mask reproduces the old body; mask 0 gives hash {oldValue.hash} vs {vh}\nold: {pp}\nexpected: {entry.valuePp}"
    else
      throwError "certificate: {n} is neither a theorem nor a definition"

end tooling

end BeaconcryptCore.VCVioLegacy

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq_of_compatible

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalSPMF_eq_iff_evalDistEq

/--
info: 'BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probOutput_eq_evalDist_singleton

/--
info: 'BeaconcryptCore.VCVioLegacy.evalDist_singleton_eq_probOutput' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.evalDist_singleton_eq_probOutput

/--
info: 'BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.probEvent_eq_evalDist_setOf

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_probOutput_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_probEvent_eq_prEvent

/--
info: 'BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.VCVioLegacy.oracleComp_evalSPMF_eq_iff_evalDistEq
