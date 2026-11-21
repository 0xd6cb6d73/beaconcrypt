-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformOpenSessionShape
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
/-! The complete adaptive public state and its Server callback share the same private World, pool, root memo and external platform state. This is a state-layout equation derived from the concrete interpreter, before any security-event projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePlatformPublicSourceExecution (State execute)
open RegistrationNativePublicSourceEffects (Extra Private toPrivate fromPrivate close)
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

def layout (before : State n KemSK Platform source) : RegistrationNativePlatformServerOpenControl.State n KemSK Extra × Platform :=
  ((before.1.1.server, (before.1.1.environment, toPrivate before.2)), before.1.2)

def rebuild (before : RegistrationNativePublicFrontend.State source)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment)
    (state : Private n KemSK) (platform : Platform) : State n KemSK Platform source :=
  (({ before with server := front, environment := env }, platform), fromPrivate state)

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : A → B) (work : StateT S m A) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

/-- The new adaptive frontend executes any Server body in exactly its local indexed source state and the same platform state. -/
theorem server (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) Value)
    (before : State n KemSK Platform source) :
    (execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen work))).run before =
      (fun result => (result.1.1.1.1, rebuild before.1.1 result.1.1.1.2 result.1.1.2 result.1.2 result.2)) <$>
        (((RegistrationNativePlatformPublicSourceLocal.interpret setup wire route sign seed scalar
          ((work.run before.1.1.server).run before.1.1.environment)).run (toPrivate before.2)).run before.1.2) := by
  simp only [execute, RegistrationNativePlatformPublicFrontend.executeLocal,
    RegistrationNativePlatformPublicFrontend.serverOpen, RegistrationNativePlatformPublicSourceLocal.interpret,
    close, StateT.run, simulateQ_map, map_apply, Functor.map_map,
    rebuild, toPrivate, fromPrivate, Prod.map_def, id_eq]


private theorem nested_support {Index A S P : Type} {spec : OracleSpec Index}
    (implementation : QueryImpl spec (StateT S (StateT P ProbComp))) (work : OracleComp spec A)
    (value : A) (before after : S) (previous next : P)
    (supported : ((value, after), next) ∈ support (((simulateQ implementation work).run before).run previous)) :
    value ∈ support work := by
  have packed : (value, (after, next)) ∈ support
      ((simulateQ (fun query => RegistrationNativePlatformPackedState.pack (implementation query)) work).run (before, previous)) := by
    rw [← RegistrationNativePlatformPackedState.simulate_pack]
    change (value, (after, next)) ∈ support ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((simulateQ implementation work).run before).run previous))
    rw [support_map]
    exact ⟨((value, after), next), supported, rfl⟩
  apply support_simulateQ_run'_subset (fun query => RegistrationNativePlatformPackedState.pack (implementation query)) work (before, previous)
  rw [StateT.run'_eq, support_map]
  exact ⟨(value, (after, next)), packed, rfl⟩

/- The concrete corrected open-accept program now selects the Server pin purely (no fingerprint hash query), so elaboration-time `whnf` of its support types would evaluate the whole program; keep it opaque to the elaborator here. Proof terms are unchanged. -/
attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept

private theorem component_shape (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (front after : RegistrationServerMaterialFrontend.State)
    (env nextEnv : RegistrationServerReferenceCompiler.Environment) (before next : Private n KemSK)
    (previous nextPlatform : Platform) (reply : RustM (Option Nat))
    (supported : ((((reply, after), nextEnv), next), nextPlatform) ∈ support
      (((RegistrationNativePlatformPublicSourceLocal.interpret setup wire route sign seed scalar
        (((RegistrationNativePlatformServerOpenControl.accept
          (RegistrationNativePlatformPublicFrontend.localHandler selected)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet).run front).run env)).run before).run previous)) :
    RegistrationServerOpenReferenceSessionShape.Shape front.sessions reply after.sessions := by
  rw [RegistrationNativePlatformPublicSourceAccept.accept] at supported
  have free := congrArg (fun work => ((work.run front).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source
      (RegistrationNativePlatformPublicSourceAccept.syntaxActual (n := n) setup wire route sign seed scalar reserve)
      setup checks verify packet)
  change simulateQ (RegistrationNativePlatformPublicSourceAccept.syntaxActual setup wire route sign seed scalar reserve)
    (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run front).run env) =
      (((RegistrationNativePlatformServerOpenControl.accept
        (RegistrationNativePlatformPublicSourceAccept.actual setup wire route sign seed scalar)
        (StateT.lift reserve) setup checks verify packet).run front).run env) at free
  rw [← free] at supported
  have possible := nested_support _ _ ((reply, after), nextEnv) before next previous nextPlatform supported
  exact RegistrationNativePlatformOpenSessionShape.accept setup checks verify packet front after env nextEnv reply possible

/-- Every complete corrected public Server accept has the actual unchanged-or-one-returned-token shape under the private source interpreter. -/
theorem accept_shape (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : State n KemSK Platform source)
    (result : RustM (Option Nat) × State n KemSK Platform source)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
        (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before)) :
    RegistrationServerOpenReferenceSessionShape.Shape before.1.1.server.sessions result.1 result.2.1.1.server.sessions := by
  rw [server, support_map] at supported
  obtain ⟨⟨⟨⟨⟨reply, front⟩, env⟩, current⟩, platform⟩, reached, rfl⟩ := supported
  exact component_shape setup wire checks route sign seed scalar selected reserve verify packet
    before.1.1.server front before.1.1.environment env (toPrivate before.2) current before.1.2 platform reply reached


/-- Every returned capability in the whole corrected adaptive public Server callback is backed by its source root in the same final private memo. -/
theorem accept_receipt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : State n KemSK Platform source)
    (result : RustM (Option Nat) × State n KemSK Platform source) (handle : Nat)
    (success : result.1 = .ok (some handle))
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
        (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before)) :
    ∃ ready root, result.2.1.1.server.sessions[handle]? = some (some ready) ∧
      result.2.2.roots ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [server, support_map] at supported
  obtain ⟨⟨⟨⟨⟨reply, front⟩, env⟩, current⟩, platform⟩, reached, rfl⟩ := supported
  dsimp only at success
  cases success
  exact RegistrationNativePlatformPublicSourceAccept.receipt setup wire checks route sign seed scalar selected reserve verify packet
    before.1.1.server front before.1.1.environment env (toPrivate before.2) current before.1.2 platform handle reached

/-- The full corrected accept preserves internal live-root backing and source memo correctness for every outcome. -/
theorem accept_live (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : PqxdhServerAuthExperiment.Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (selected : Bool) (reserve : StateT Platform ProbComp Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : State n KemSK Platform source)
    (result : RustM (Option Nat) × State n KemSK Platform source)
    (live : RegistrationNativePublicSourceState.Live before.1.1 before.2)
    (correct : RegistrationNativePublicSourceState.MemoCorrect setup seed scalar before.2.roots)
    (supported : result ∈ support ((execute setup wire route sign seed scalar
      (RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.serverOpen
        (RegistrationNativePlatformServerOpenControl.accept (RegistrationNativePlatformPublicFrontend.localHandler selected)
          (RegistrationNativePlatformPublicFrontend.platform reserve) setup checks verify packet)))).run before)) :
    RegistrationNativePublicSourceState.Live result.2.1.1 result.2.2 ∧
      RegistrationNativePublicSourceState.MemoCorrect setup seed scalar result.2.2.roots := by
  have kept := RegistrationNativePlatformPublicSourceExecution.roots setup wire route sign seed scalar _ before result correct supported
  have shape := accept_shape setup wire checks route sign seed scalar selected reserve verify packet before result supported
  refine ⟨?_, kept.1⟩
  intro ready member
  rcases shape with unchanged | ⟨appended, returned, sessions⟩
  · rw [unchanged] at member
    obtain ⟨root, stored⟩ := live ready member
    exact ⟨root, kept.2 ready.reference root stored⟩
  · simp only [sessions, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with previous | same
    · obtain ⟨root, stored⟩ := live ready previous
      exact ⟨root, kept.2 ready.reference root stored⟩
    · cases same
      obtain ⟨actual, root, stored, prepared, _computed⟩ := accept_receipt setup wire checks route sign seed scalar
        selected reserve verify packet before result before.1.1.server.sessions.length returned supported
      have last : result.2.1.1.server.sessions[before.1.1.server.sessions.length]? = some (some ready) := by
        rw [sessions]
        simp only [List.getElem?_append, Nat.lt_irrefl, ite_false, Nat.sub_self, List.getElem?_cons_zero]
      rw [last] at stored
      cases stored
      exact ⟨root, prepared⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_shape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceServer.accept_live
