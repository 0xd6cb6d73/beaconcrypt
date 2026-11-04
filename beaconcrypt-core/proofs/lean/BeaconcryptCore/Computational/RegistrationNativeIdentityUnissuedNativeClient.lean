-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedSource
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedAcceptCut
import BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedChosenGame
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxInitial
/-! The unissued-field ordinary reduction samples the actual independent Server/ML/KEM startup internally, runs the unchanged raw source compiler to one public parsed-accept position, and submits an original attached field. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient
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
local notation "params" => RegistrationNativePlatformIdentityCtxTyped.handler (n := n) setup checks wire route representation

noncomputable def client {count : Nat} (accept : Nat) (tag : Fin 3)
    (_keys : Fin (count+1) → PqxdhJointIdentity.PublicIdentity) : OracleComp PublicSpec (Option PqxdhJointIdentity.Forgery) := do
  let initialized ← simulateQ RegistrationNativeIdentityTemplateProtocol.coins
    (RegistrationNativeExperiment.start (n := n) setup source ensureInit identityIndex serverKeyId)
  match initialized with
  | none => pure none
  | some initial =>
      (fun observed => RegistrationNativeIdentityUnissuedPacketClient.field tag observed.1) <$>
        (simulateQ RegistrationNativeIdentityUnissuedSource.reify
          (RegistrationNativeIdentityUnissuedPacketClient.visit accept
            (params initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
            (RegistrationNativeFullCompiler.compile setup.source.crypto
              (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) initial.created.server.server.metadata.sender bounds mode (adversary initial.public))
            (RegistrationNativeIdentityMainProfile.fromInitial initial,previous) 0)).run
          (RegistrationNativeWorldCache.cache initial.state,[PqxdhRefinement.absBytes initial.credential.publicKey])

omit primitive in
private theorem coin_scope {A : Type} (sampler : ProbComp A) :
    (simulateQ RegistrationNativeIdentityTemplateProtocol.coins sampler).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.Allowed := by
  induction sampler using OracleComp.inductionOn with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativeIdentityTemplateProtocol.coins]
      exact (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨trivial,ih⟩

/-- The actual independent startup and full raw source dictionary derive the executable reduction's no-reveal syntax internally. -/
theorem client_safe {count : Nat} (accept : Nat) (tag : Fin 3)
    (keys : Fin (count+1) → PqxdhJointIdentity.PublicIdentity) :
    (client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous accept tag keys).AllQueriesSatisfy RegistrationNativeIdentityTemplateChosenSource.Allowed := by
  unfold client
  apply allQueriesSatisfy_bind (coin_scope _)
  intro initialized
  cases initialized with
  | none => exact allQueriesSatisfy_pure _ _
  | some initial =>
      apply RegistrationNativeIdentityMainNoRevealCore.mapped
      exact RegistrationNativeIdentityUnissuedSource.program_safe _
        (RegistrationNativeIdentityUnissuedPacketClient.native_scope setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          accept 0 _ (RegistrationNativeIdentityMainProfile.fromInitial initial,previous)) _

noncomputable def reduction {count : Nat} (target : Fin (count+1)) (accept : Nat) (tag : Fin 3)
    (fallback : PqxdhJointIdentity.Forgery) : PqxdhJointIdentity.PublicIdentity → OracleComp PqxdhJointIdentity.AdversarySpec PqxdhJointIdentity.Forgery :=
  RegistrationNativeIdentityUnissuedChosenGame.reduction setup.joint target
    (client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous accept tag) fallback

/-- This literal native prefix experiment is exactly the ordinary joint weak-EUF advantage of E with all independent startup and other-identity sampling inside its execution. -/
theorem probability_eq {count : Nat} (target : Fin (count+1)) (accept : Nat) (tag : Fin 3)
    (fallback : PqxdhJointIdentity.Forgery) :
    Pr{let accepted ← (RegistrationNativeIdentityUnissuedChosenGame.familyGame setup.joint target
      (client (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        source ensureInit identityIndex serverKeyId bounds mode adversary previous accept tag) fallback)}[accepted = true] =
      PqxdhJointIdentity.advantage setup.joint
        (reduction (n := n) setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
          source ensureInit identityIndex serverKeyId bounds mode adversary previous target accept tag fallback) :=
  RegistrationNativeIdentityUnissuedChosenGame.probability_eq setup.joint target _
    (client_safe setup checks wire route representation view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      source ensureInit identityIndex serverKeyId bounds mode adversary previous accept tag) fallback

end BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient.client_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient.client_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient.probability_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityUnissuedNativeClient.probability_eq
