-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptivePostselection
import BeaconcryptCore.Computational.RegistrationNativeIdentityCensorPublicSource

/-! The executable before-accept packet visitor is coupled to its actual private source interpretation. It retains every original adaptive reply, true counter, cache, journal and allocator state until the fixed public stop; the postselection comparison discharges actual callback semantics. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhEd25519EufCma (Ed25519Signature)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityCensorEdOutgoingSource (Full interpret)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {mlSource : RegistrationNativeMldsa.Source}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
variable (keys : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (reserve : Usize → StateT Platform ProbComp (core.result.Result Unit E))
variable (selected position : Nat) (placeholder : Ed25519Signature)
local notation "actual" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper (RegistrationNativePlatformConcreteSource.writer reserve)
local notation "FullState" => Full (n := n) (KemSK := KemSK) (Platform := Platform) (mlSource := mlSource)
local notation "MainState" => RegistrationNativeIdentityMain.State n KemSK mlSource × Platform
local notation "view" => RegistrationNativeIdentityCensorOutgoingView.view placeholder

local notation "current" => RegistrationNativeIdentityCensorAdaptivePostselection.normalized setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve placeholder
noncomputable def sourceBackend (joint : PqxdhJointIdentity.Primitives) (selected : Nat) (placeholder : Ed25519Signature)
    (masked : Bool) : QueryImpl RegistrationNativeIdentityCensorOperational.Spec (StateT RegistrationNativeIdentityCensorSource.State ProbComp) :=
  if masked then RegistrationNativeIdentityCensorSource.censored joint selected placeholder
  else RegistrationNativeIdentityCensorSource.implementation joint selected
local notation "backend(" masked ")" => sourceBackend setup.joint selected placeholder masked
local notation "called(" masked "," query "," before ")" => RegistrationNativeIdentityCensorAdaptivePostselection.call setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder masked query before

private theorem callback_run (masked : Bool) (query : TypedSpec.Domain) (before : FullState) :
    (simulateQ (backend(masked))
      ((RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current query).run before.1)).run before.2 =
      (fun result : TypedSpec.Range query × FullState => ((result.1, result.2.1), result.2.2)) <$> called(masked, query, before) := by
  have actualRun := RegistrationNativeIdentityCensorPublicSource.current setup.joint selected position placeholder masked current query before
  have inverse := congrArg (fun distribution =>
    (fun result : TypedSpec.Range query × FullState => ((result.1, result.2.1), result.2.2)) <$> distribution) actualRun
  simp only [RegistrationNativeIdentityCensorPublicSource.callback, RegistrationNativeIdentityCensorPublicSource.runState,
    StateT.run, Functor.map_map, Prod.eta] at inverse
  have identity_function :
      (fun result : (TypedSpec.Range query × (MainState × RegistrationNativeIdentityCensorCompiler.Mode)) × RegistrationNativeIdentityCensorSource.State => result) = id := rfl
  rw [identity_function, id_map] at inverse
  exact inverse


private theorem step_run (masked : Bool) (query : TypedSpec.Domain) (before : FullState) (counter : Nat) :
    (simulateQ (backend(masked))
      ((RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current query).run (before.1, counter))).run before.2 =
      (fun result : TypedSpec.Range query × FullState =>
        ((result.1, (result.2.1, counter + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)), result.2.2)) <$>
          called(masked, query, before) := by
  change (simulateQ (backend(masked))
    ((fun result : TypedSpec.Range query × (MainState × RegistrationNativeIdentityCensorCompiler.Mode) =>
      (result.1, (result.2, counter + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0))) <$>
        (RegistrationNativeIdentityCensorPublicClient.callback selected position placeholder current query).run before.1)).run before.2 = _
  rw [simulateQ_map, StateT.run_map, callback_run, Functor.map_map]

private theorem not_attempted (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (before : FullState) (counter : Nat)
    (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query counter = none) :
    (RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current defaults query).run (before.1, counter) =
      (RegistrationNativeIdentityCensorPublicClient.step selected position placeholder current query).run (before.1, counter) := by
  rcases query with query | command
  · rfl
  · cases command <;> try rfl
    rename_i packet
    have different : counter ≠ accept := by
      intro same
      simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt, same, ite_true, reduceCtorEq] at skipped
    simp only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, different, ite_false]

omit primitive in
private theorem observe_not_attempted (accept : Nat) (query : TypedSpec.Domain) (before after : FullState)
    (counter nextCounter : Nat) (reply : TypedSpec.Range query)
    (skipped : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query counter = none) :
    RegistrationNativeIdentityCensorPublicClient.observe (S := MainState) accept query (before.1, counter) reply (after.1, nextCounter) =
      if RegistrationNativeIdentityCensorAdaptivePostselection.published query reply after then
        some RegistrationNativeIdentityCensorPublicClient.Stop.published else none := by
  rcases query with query | command
  · rfl
  · cases command <;> try rfl
    case bundle index =>
      cases active : after.1.2.active <;> cases returned : (RegistrationNativeRawAdapter.resultOption reply).isSome <;>
        simp only [RegistrationNativeIdentityCensorPublicClient.observe, RegistrationNativeIdentityCensorAdaptivePostselection.published,
          active, returned, Bool.and_false, Bool.and_true, Bool.false_eq_true, Bool.and_self,
          false_and, true_and, ite_true, ite_false]
    case accept packet =>
      have different : counter ≠ accept := by
        intro same
        simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt, same, ite_true, reduceCtorEq] at skipped
      simp only [RegistrationNativeIdentityCensorPublicClient.observe, different, ite_false,
        RegistrationNativeIdentityCensorAdaptivePostselection.published, Bool.false_eq_true]

omit primitive in
private theorem pure_apply {State Value : Type} {m : Type → Type} [Monad m] (value : Value) (before : State) :
    (pure value : StateT State m Value) before = pure (value, before) := rfl

omit primitive in
private theorem interpreted_bind {X Y : Type} (masked : Bool)
    (work : OracleComp RegistrationNativeIdentityCensorOperational.Spec X)
    (next : X → OracleComp RegistrationNativeIdentityCensorOperational.Spec Y)
    (before : RegistrationNativeIdentityCensorSource.State) :
    (simulateQ (backend(masked)) (work >>= next)).run' before =
      (do let result ← (simulateQ (backend(masked)) work).run before
          (simulateQ (backend(masked)) (next result.1)).run' result.2) := by
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]

local notation "visitor" => RegistrationNativeIdentityCensorPacketClient.visit selected position
local notation "privateVisit" => RegistrationNativeIdentityCensorAdaptivePostselection.visit setup checks wire route representation created credential keys failure allocation
  reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder

private theorem visit_query (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (query : TypedSpec.Domain) (next : TypedSpec.Range query → OracleComp TypedSpec A)
    (before : (MainState × RegistrationNativeIdentityCensorCompiler.Mode) × Nat) :
    visitor accept placeholder current defaults (TypedSpec.query query >>= next) before = (do
      let result ← (RegistrationNativeIdentityCensorBeforeAccept.step selected position accept placeholder current defaults query).run before
      match RegistrationNativeIdentityCensorPublicClient.observe accept query before result.1 result.2 with
      | none => visitor accept placeholder current defaults (next result.1) result.2
      | some reason => pure (RegistrationNativeIdentityCensorPacketClient.finish result.2.1.2.target reason)) := rfl

private theorem private_visit_query (masked : Bool) (accept : Nat) (query : TypedSpec.Domain)
    (next : TypedSpec.Range query → OracleComp TypedSpec A) (before : FullState × Nat) :
    privateVisit masked accept (TypedSpec.query query >>= next) before =
      (match RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query before.2 with
      | some packet => pure (before.1.1.2.target.map fun message => (message, packet))
      | none => do
          let selectedCut ← RegistrationNativeIdentityCensorAdaptivePostselection.cut query <$> called(masked, query, before.1)
          match selectedCut with
          | none => pure none
          | some kept => privateVisit masked accept (next kept.1) (kept.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)) := rfl

/-- The executable packet-only visitor has exactly its actual private source value interpretation, with no local selected-row or success condition. -/
theorem source (masked : Bool) (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : FullState × Nat) :
    (simulateQ (backend(masked))
      (visitor accept placeholder current defaults work (before.1.1, before.2))).run' before.1.2 =
        privateVisit masked accept work before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => rfl
  | query_bind query next ih =>
    rw [visit_query, private_visit_query]
    cases attempted : RegistrationNativeIdentityCensorAdaptivePostselection.attempt accept query before.2 with
    | some packet =>
      rcases query with query | command
      · cases attempted
      · cases command <;> try cases attempted
        rename_i submitted
        by_cases chosen : before.2 = accept
        · have same : submitted = packet := by
            simpa only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt, chosen, ite_true, Option.some.injEq] using attempted
          subst packet
          simp only [RegistrationNativeIdentityCensorBeforeAccept.step, StateT.run, chosen, ite_true, pure_bind,
            RegistrationNativeIdentityCensorPublicClient.observe, RegistrationNativeIdentityCensorPacketClient.finish,
            simulateQ_pure, StateT.run'_eq, StateT.run, pure_apply, map_pure]
        · simp only [RegistrationNativeIdentityCensorAdaptivePostselection.attempt, chosen, ite_false, reduceCtorEq] at attempted
    | none =>
      dsimp only
      rw [not_attempted setup checks wire route representation created credential keys failure allocation reserveRegistration reservePeer
        reserveFrame erased helper reserve selected position placeholder accept defaults query before.1 before.2 attempted,
        interpreted_bind, step_run]
      simp only [bind_map_left]
      apply bind_congr
      intro result
      rw [observe_not_attempted accept query before.1 result.2 before.2
        (before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0) result.1 attempted]
      unfold RegistrationNativeIdentityCensorAdaptivePostselection.cut
      cases published : RegistrationNativeIdentityCensorAdaptivePostselection.published query result.1 result.2 with
      | true =>
        simp only [ite_true, RegistrationNativeIdentityCensorPacketClient.finish, simulateQ_pure, StateT.run'_eq, StateT.run, pure_apply, map_pure]
      | false =>
        simp only [Bool.false_eq_true, ite_false]
        exact ih result.1 (result.2, before.2 + if RegistrationNativeIdentityCensorPublicClient.IsAccept query then 1 else 0)

/-- The original stopped client, observed only through its submitted packet, has this same exact source marginal. -/
theorem stopped (masked : Bool) (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (before : FullState × Nat) :
    (simulateQ (backend(masked))
      (RegistrationNativeIdentityCensorPacketClient.observed <$>
        (simulateQ (RegistrationNativeIdentityCensorBeforeAccept.freeze selected position accept placeholder current defaults) work).run
          ((before.1.1, before.2), none))).run' before.1.2 =
        privateVisit masked accept work before := by
  rw [RegistrationNativeIdentityCensorPacketClient.source, source]

/-- After a genuine target has been selected, the actual executable visitor has identical canonical and private-censored source observations up to the before-accept stop. -/
theorem paired (accept : Nat) (defaults : (query : TypedSpec.Domain) → TypedSpec.Range query)
    (work : OracleComp TypedSpec A) (target : Pqxdh.Bytes)
    (targetRole : RegistrationNativeIdentitySigningRole.oneTime target = true) (seed : PqxdhJointIdentity.IdentitySeed)
    (before : FullState × Nat) (prior : RegistrationNativeIdentityCensorAdaptivePostselection.Selected selected target seed before.1) :
    (simulateQ (backend(false))
      (visitor accept placeholder current defaults work (before.1.1, before.2))).run' before.1.2 =
    (simulateQ (backend(true))
      (visitor accept placeholder current defaults work (before.1.1, before.2))).run' before.1.2 := by
  rw [source, source]
  exact RegistrationNativeIdentityCensorAdaptivePostselection.paired setup checks wire route representation created credential keys failure allocation
    reserveRegistration reservePeer reserveFrame erased helper reserve selected position placeholder accept work target targetRole seed before prior

end BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.stopped

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.paired' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityCensorAdaptiveSource.paired
