-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! Genuine startup is sampled inside the executable ordinary reduction. Moving this independent sampler before the reserved identity family preserves the complete conditional prefix experiment, including its fallback on startup failure. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup
open RegistrationNativeIdentityTemplateProtocol (PublicSpec)
variable {Value : Type}
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I}
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (CoreModels.core.result.Result Unit E)) (erased : beaconcrypt_core.commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

variable (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Aeneas.Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (previous : Platform)

noncomputable def fieldPrefix (initial : RegistrationNativeExperiment.Initial n KemSK source) (accept : Nat) (tag : Fin 3) :
    OracleComp PublicSpec (Option PqxdhJointIdentity.Forgery) :=
  (fun observed => RegistrationNativeIdentityUnissuedPacketClient.field tag observed.1) <$>
    (simulateQ RegistrationNativeIdentityUnissuedSource.reify
      (RegistrationNativeIdentityUnissuedPacketClient.visit accept
        (RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation initial.created initial.credential
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
        (RegistrationNativeFullCompiler.compile setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
          initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
        (RegistrationNativeIdentityMainProfile.fromInitial initial,previous) 0)).run
      (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])

noncomputable def conditional (initialized : Option (RegistrationNativeExperiment.Initial n KemSK source)) (accept : Nat) (tag : Fin 3) :
    OracleComp PublicSpec (Option PqxdhJointIdentity.Forgery) :=
  match initialized with
  | none => pure none
  | some initial => fieldPrefix setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initial accept tag

noncomputable def completeGame {count : Nat} (target : Fin (count+1)) (accept : Nat) (tag : Fin 3)
    (fallback : PqxdhJointIdentity.Forgery) : ProbComp Bool := do
  let initialized ← RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId
  RegistrationNativeIdentityUnissuedChosenGame.familyGame setup.joint target
    (fun _ => conditional setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source bounds mode adversary previous initialized accept tag) fallback

omit primitive in
private theorem coins_run {A : Type} {count : Nat} (joint : PqxdhJointIdentity.Primitives)
    (seeds : Fin (count+1) → PqxdhJointIdentity.IdentitySeed) (work : ProbComp A)
    (before : PqxdhDynamicIdentityRouting.PublicState × PqxdhJointIdentityFreshness.GlobalState (count+1)) :
    (simulateQ (RegistrationNativeIdentityTemplateChosenSource.reserved joint seeds)
      (simulateQ RegistrationNativeIdentityTemplateProtocol.coins work)).run before =
        (fun value => (value,before)) <$> work := by
  apply QueryImpl.Stateful.simulateQ_liftComp_run_of_query
  intro coin current
  change (do let answer ← unifSpec.query coin; pure (answer,current) : ProbComp _) = _
  simp only [bind_pure_comp]

/-- Independent genuine startup can be moved before the full reserved family without conditioning or discarding failure fallback wins. -/
theorem game_source {count : Nat} (target : Fin (count+1)) (accept : Nat) (tag : Fin 3)
    (fallback : PqxdhJointIdentity.Forgery) :
    completeGame (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback =ᵈ
      RegistrationNativeIdentityUnissuedChosenGame.familyGame setup.joint target
        (RegistrationNativeIdentityUnissuedNativeClient.client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous accept tag) fallback := by
  unfold completeGame RegistrationNativeIdentityUnissuedChosenGame.familyGame
  simp only [RegistrationNativeIdentityUnissuedNativeClient.client,simulateQ_bind,StateT.run_bind,coins_run,
    bind_map_left,map_bind,bind_pure_comp]
  exact OracleComp.EvalDistEq.bind_bind_swap
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
    (PqxdhJointIdentityFamily.sampleFamily (count+1)) _

/-- Each startup-averaged fixed public cut is one executable ordinary weak-EUF reduction, including all independent startup inside that reduction. -/
theorem probability_eq {count : Nat} (target : Fin (count+1)) (accept : Nat) (tag : Fin 3)
    (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let result ← (completeGame (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback)}[result=true] =
      PqxdhJointIdentity.advantage setup.joint
        (RegistrationNativeIdentityUnissuedNativeClient.reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback) :=
  ((game_source setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback).prEvent_eq (· = true)).trans
      (RegistrationNativeIdentityUnissuedNativeClient.probability_eq setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback)

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup.game_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup.game_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup.probability_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedStartup.probability_eq
