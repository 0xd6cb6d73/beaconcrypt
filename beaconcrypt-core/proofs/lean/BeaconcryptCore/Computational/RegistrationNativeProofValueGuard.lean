-- SPDX-License-Identifier: 0BSD
import Lean.Elab.Command
import Lean.Meta.InferType
import Lean.Util.FoldConsts
/-! Source-dependency checks inspect proof/computation values after beta/zeta reduction. Declaration types, binder/let annotations and type-valued arguments do not establish a source dependency. These syntactic guards complement kernel checking and source-fidelity controls. -/
open Lean Elab Command
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards
private def declarationValue? : ConstantInfo → Option Expr
  | .defnInfo declaration => some declaration.value
  | .thmInfo declaration => some declaration.value
  | .opaqueInfo declaration => some declaration.value
  | _ => none

/-- A proof value cannot be a type. Checking that first avoids reducing a dependent proposition's concrete controller execution merely to recognize a value position. Other expressions still use the full type predicate. -/
private def isTypeValue (expression : Expr) : MetaM Bool := do
  if ← Meta.isProof expression then return false
  Meta.isType expression

private partial def valueHead (expression : Expr) : Expr :=
  match expression with
  | .mdata _ body => valueHead body
  | .letE _ _ value body _ => valueHead (body.instantiate1 value)
  | _ => expression.headBeta

private abbrev FormalLivenessCache := Std.HashMap Expr Bool

/-- Binder liveness excludes annotations and discarded local computations before inspecting application arguments. -/
private partial def usesValueVariable (memo : IO.Ref FormalLivenessCache) (expression : Expr) (variableId : FVarId) : MetaM Bool := do
  if !expression.containsFVar variableId then return false
  let expression := Expr.betaRev expression.getAppFn expression.getAppRevArgs true
  match expression with
  | .lam binderName type body info =>
    Meta.withLocalDeclNoLocalInstanceUpdate binderName info type fun boundValue =>
      usesValueVariable memo (body.instantiate1 boundValue) variableId
  | .letE _ _ value body _ => usesValueVariable memo (body.instantiate1 value) variableId
  | .mdata _ body => usesValueVariable memo body variableId
  | .forallE .. | .sort .. => return false
  | _ =>
    if ← isTypeValue expression then return false
    match expression with
    | .fvar actual => return actual == variableId
    | .app .. =>
      let function := expression.getAppFn
      if ← usesValueVariable memo function variableId then return true
      let environment ← getEnv
      let mut shape := match function with
        | .const declName _ => (environment.find? declName).bind declarationValue?
        | _ => none
      for argument in expression.getAppArgs do
        match shape.map valueHead with
        | some (.lam binderName type body info) =>
          if argument.containsFVar variableId then
            if !(← isTypeValue argument) then
              let formal := Expr.lam binderName type body info
              let live ← match (← memo.get)[formal]? with
                | some live => pure live
                | none => do
                  -- A recursive-only cycle cannot establish a real use. The provisional false is conservative.
                  memo.modify fun values => values.insert formal false
                  let live ← Meta.withLocalDeclNoLocalInstanceUpdate binderName info type fun boundValue =>
                    usesValueVariable memo (body.instantiate1 boundValue) boundValue.fvarId!
                  memo.modify fun values => values.insert formal live
                  pure live
              if live then
                if ← usesValueVariable memo argument variableId then return true
          shape := some (body.instantiate1 argument)
        | _ =>
          if ← usesValueVariable memo argument variableId then return true
          shape := none
      return false
    | .proj _ _ body => usesValueVariable memo body variableId
    | _ => return false

/-- Raw value references include type positions and are used only as a conservative search prefilter. Each declaration is scanned at most once per command. -/
private abbrev RawGraph := Std.HashMap Name (Array Name)

private partial def rawValueGraph (environment : Environment) (pending : List Name)
    (visited : Std.HashSet Name) (graph : RawGraph) : RawGraph :=
  match pending with
  | [] => graph
  | currentName :: remaining =>
    if visited.contains currentName then rawValueGraph environment remaining visited graph else
    let visited := visited.insert currentName
    let dependencies := match (environment.find? currentName).bind declarationValue? with
      | none => #[]
      | some value => value.getUsedConstants
    rawValueGraph environment (dependencies.toList ++ remaining) visited (graph.insert currentName dependencies)

private partial def reverseReachable (parents : Std.HashMap Name (List Name)) (pending : List Name)
    (visited : Std.HashSet Name) : Std.HashSet Name :=
  match pending with
  | [] => visited
  | currentName :: remaining =>
    if visited.contains currentName then reverseReachable parents remaining visited else
    reverseReachable parents ((parents[currentName]?.getD []) ++ remaining) (visited.insert currentName)

/-- Membership here can only request a type-aware visit; it never establishes a successful dependency check. The reverse closure caches the possible targets for every raw-reachable declaration. -/
private def rawCandidates (graph : RawGraph) (targets : List Name) : Std.HashSet Name :=
  let parents := graph.toList.foldl (fun parents entry =>
    entry.2.foldl (fun parents dependency =>
      parents.insert dependency (entry.1 :: (parents[dependency]?.getD []))) parents)
    ({} : Std.HashMap Name (List Name))
  reverseReachable parents targets {}

/-- A fresh visited set bounds each pure scan on shared expression DAGs. Expr equality preserves the supported value syntax even when binder names/annotations are ignored. No Meta/type classification establishes a candidate here. -/
private partial def valueCandidateWork (possible : Std.HashSet Name) (pending : List Expr)
    (seen : Std.HashSet Expr) : Bool :=
  match pending with
  | [] => false
  | expression :: remaining =>
    if seen.contains expression then valueCandidateWork possible remaining seen else
    let seen := seen.insert expression
    match expression with
    | .const name _ => if possible.contains name then true else valueCandidateWork possible remaining seen
    | .app function argument => valueCandidateWork possible (function :: argument :: remaining) seen
    | .proj _ _ body | .mdata _ body | .lam _ _ body _ =>
      valueCandidateWork possible (body :: remaining) seen
    | .letE _ _ value body _ => valueCandidateWork possible (value :: body :: remaining) seen
    | .forallE .. | .sort .. | .bvar .. | .fvar .. | .mvar .. | .lit .. =>
      valueCandidateWork possible remaining seen

/-- A conservative value-syntax prefilter: annotations/type syntax cannot establish value dependencies; dead let values and type-valued arguments may overinclude. A positive result only requests the unchanged type-aware walker. -/
private def hasValueCandidate (possible : Std.HashSet Name) (expression : Expr) : Bool :=
  valueCandidateWork possible [expression] {}

private partial def valueConstants (memo : IO.Ref FormalLivenessCache) (possible : Std.HashSet Name) (expression : Expr)
    (found : Std.HashSet Name) : MetaM (Std.HashSet Name) := do
  if !(hasValueCandidate possible expression) then return found
  let expression := Expr.betaRev expression.getAppFn expression.getAppRevArgs true
  match expression with
  | .letE _ _ value body _ => valueConstants memo possible (body.instantiate1 value) found
  | .mdata _ body => valueConstants memo possible body found
  | .lam binderName type body info =>
    Meta.withLocalDeclNoLocalInstanceUpdate binderName info type fun boundValue => valueConstants memo possible (body.instantiate1 boundValue) found
  | .forallE .. | .sort .. => return found
  | _ =>
    if ← isTypeValue expression then return found
    match expression with
    | .const name _ => return found.insert name
    | .app .. =>
      let function := expression.getAppFn
      let mut found ← valueConstants memo possible function found
      let environment ← getEnv
      let mut shape := match function with
        | .const name _ => (environment.find? name).bind declarationValue?
        | _ => none
      for argument in expression.getAppArgs do
        match shape.map valueHead with
        | some (.lam name type body info) =>
          if hasValueCandidate possible argument then
            if !(← isTypeValue argument) then
              let formal := Expr.lam name type body info
              let live ← match (← memo.get)[formal]? with
                | some live => pure live
                | none => do
                  -- A recursive-only cycle cannot establish a real use. The provisional false is conservative.
                  memo.modify fun values => values.insert formal false
                  let live ← Meta.withLocalDeclNoLocalInstanceUpdate name info type fun boundValue =>
                    usesValueVariable memo (body.instantiate1 boundValue) boundValue.fvarId!
                  memo.modify fun values => values.insert formal live
                  pure live
              if live then found ← valueConstants memo possible argument found
          shape := some (body.instantiate1 argument)
        | _ =>
          found ← valueConstants memo possible argument found
          shape := none
      return found
    | .proj _ _ body => valueConstants memo possible body found
    | _ => return found

private partial def valueClosure (memo : IO.Ref FormalLivenessCache) (environment : Environment) (possible required : Std.HashSet Name)
    (pending : List Name) (visited : Std.HashSet Name) : MetaM (Std.HashSet Name) := do
  if required.toList.all visited.contains then return visited
  match pending with
  | [] => return visited
  | currentName :: remaining =>
    if visited.contains currentName || !possible.contains currentName then
      return ← valueClosure memo environment possible required remaining visited
    let visited := visited.insert currentName
    match environment.find? currentName with
    | none => valueClosure memo environment possible required remaining visited
    | some declaration => match declarationValue? declaration with
      | none => valueClosure memo environment possible required remaining visited
      | some value =>
        let constants ← try valueConstants memo possible value {} catch error =>
          throwError "source value traversal of {currentName}: {error.toMessageData}"
        valueClosure memo environment possible required (constants.toList ++ remaining) visited

elab "#guard_source_value_dependencies " root:ident " includes " "[" required:ident,* "]" : command => do
  let rootName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo root)
  let environment ← getEnv
  let some rootDeclaration := environment.find? rootName | throwErrorAt root "source endpoint declaration is unavailable"
  let some _ := declarationValue? rootDeclaration | throwErrorAt root "source endpoint has no declaration value"
  let requiredNames ← required.getElems.mapM fun requiredSyntax => do
    let requiredName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo requiredSyntax)
    let some (.thmInfo _) := environment.find? requiredName | throwErrorAt requiredSyntax "required source dependency must be a proved theorem"
    pure requiredName
  let graph := rawValueGraph environment [rootName] {} {}
  let possible := rawCandidates graph requiredNames.toList
  let requested := requiredNames.foldl (fun names name => names.insert name) ({} : Std.HashSet Name)
  let memo ← IO.mkRef ({} : FormalLivenessCache)
  let closure ← liftTermElabM (valueClosure memo environment possible requested [rootName] {})
  for requiredSyntax in required.getElems do
    let requiredName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo requiredSyntax)
    unless closure.contains requiredName do
      throwErrorAt root "source endpoint {rootName} does not reach source proof {requiredName} through declaration values"

namespace Controls
theorem anchor : True := True.intro
theorem actual : True := anchor
theorem usedLet : True := let receipt := anchor; receipt
theorem identity (receipt : True) : True := receipt
theorem actualApplication : True := identity anchor
theorem discard (_receipt : True) : True := True.intro
theorem ignoredApplication : True := discard anchor
theorem binderTypeOnly (_receipt : anchor = anchor) : True := True.intro
theorem unusedLet : True := let _receipt := anchor; True.intro
theorem betaOnly : True := (fun _ : True => True.intro) anchor
theorem typeArgument (_type : Prop) : True := True.intro
theorem typeArgumentOnly : True := typeArgument (anchor = anchor)
theorem typeBinderOnly (receipt : True) : True := typeArgument (receipt = receipt)
theorem nestedTypeArgumentOnly : True := typeBinderOnly anchor
theorem letTypeOnly : True := let _receipt : anchor = anchor := rfl; True.intro
theorem wrapper (receipt : True) : True := discard receipt
theorem wrappedIgnored : True := wrapper anchor
theorem forward (receipt : True) : True := identity receipt
theorem forwardedActual : True := forward anchor
#guard_source_value_dependencies actual includes [anchor]
#guard_source_value_dependencies usedLet includes [anchor]
#guard_source_value_dependencies actualApplication includes [anchor]
#guard_source_value_dependencies forwardedActual includes [anchor]

/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.ignoredApplication does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies ignoredApplication includes [anchor]

/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.binderTypeOnly does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies binderTypeOnly includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.unusedLet does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies unusedLet includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.betaOnly does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies betaOnly includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeArgumentOnly does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies typeArgumentOnly includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.nestedTypeArgumentOnly does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies nestedTypeArgumentOnly includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.letTypeOnly does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies letTypeOnly includes [anchor]
/-- error: source endpoint BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.wrappedIgnored does not reach source proof BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor through declaration values -/
#guard_msgs in
#guard_source_value_dependencies wrappedIgnored includes [anchor]
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.anchor

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.actual' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.actual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.usedLet' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.usedLet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.identity' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.actualApplication' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.actualApplication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.discard' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.discard

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.ignoredApplication' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.ignoredApplication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.binderTypeOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.binderTypeOnly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.unusedLet' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.unusedLet

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.betaOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.betaOnly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeArgument' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeArgument

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeArgumentOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeArgumentOnly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.letTypeOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.letTypeOnly

end Controls
end BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeBinderOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.typeBinderOnly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.nestedTypeArgumentOnly' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.nestedTypeArgumentOnly

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.wrapper' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.wrapper

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.wrappedIgnored' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.wrappedIgnored

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.forward' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.forward

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.forwardedActual' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSourceExecutionDependencyGuards.Controls.forwardedActual
