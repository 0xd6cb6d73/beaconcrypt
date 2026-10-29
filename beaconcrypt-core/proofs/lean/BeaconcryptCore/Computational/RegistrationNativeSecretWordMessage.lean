-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWord
import BeaconcryptCore.Computational.RegistrationNativePublicFrontend

/-! The symbolic frontend changes only the KEM word carried by a private root reference. Its public agreement, actual owner lifecycle, local environment and parsed-attempt counter remain the existing native data. Evaluating the opaque atom restores the exact native192-byte root input, including all optional DH failures. These representation laws do not assert that the actual candidate-provider execution is independent of the candidate; that source relation and the explicit off-protected suffix-key PRF hop are separate obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
open RegistrationNativeSecretWord (Word Key)
open PqxdhJointIdentity (Primitives IdentitySeed PeerEncoding DhOutput)
open PqxdhJointGapDh (DhInterface ScalarBytes)
open PqxdhKemIndCca (MlKemSharedSecret)
variable {joint : Primitives}

structure Message where
  staticPeer : PeerEncoding
  third : RegistrationNativeRelatedFamily.Third
  second : DhOutput
  fourth : DhOutput
  kem : Word
  deriving DecidableEq

def eval (candidate : MlKemSharedSecret) (message : Message) : RegistrationNativeRelatedFamily.Message :=
  ⟨message.staticPeer, message.third, message.second, message.fourth, message.kem.eval candidate⟩

def literal (message : RegistrationNativeRelatedFamily.Message) : Message :=
  ⟨message.staticPeer, message.third, message.second, message.fourth, .literal message.kem⟩

def zero : MlKemSharedSecret := List.Vector.replicate 32 0

def head (first second third fourth : DhOutput) : List.Vector UInt8 160 :=
  ⟨List.replicate 32 255 ++ first.toList ++ second.toList ++ third.toList ++ fourth.toList,
    by simp⟩

def input (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (message : Message) : Option Key := do
  let first ← RegistrationNativeRelatedFamily.firstValue joint dh seed scalar (eval zero message)
  let third ← RegistrationNativeRelatedFamily.thirdValue joint dh scalar message.third
  pure ⟨head first message.second third message.fourth, message.kem⟩

/-- Every ordinary native reference enters the symbolic language without changing any evaluated field. -/
theorem eval_literal (candidate : MlKemSharedSecret) (message : RegistrationNativeRelatedFamily.Message) :
    eval candidate (literal message) = message := by cases message; rfl

/-- KEM substitution changes only the final32-byte field; all optional first/third DH computations retain their actual order and outcome. -/
theorem input_eval (joint : Primitives) (dh : DhInterface joint) (seed : IdentitySeed) (scalar : ScalarBytes)
    (candidate : MlKemSharedSecret) (message : Message) :
    (input joint dh seed scalar message).map (RegistrationNativeSecretWord.eval candidate) =
      RegistrationNativeRelatedFamily.input joint dh seed scalar (eval candidate message) := by
  have first : RegistrationNativeRelatedFamily.firstValue joint dh seed scalar (eval zero message) =
      RegistrationNativeRelatedFamily.firstValue joint dh seed scalar (eval candidate message) := by
    cases message.third <;> rfl
  simp only [input, first, RegistrationNativeRelatedFamily.input, Option.bind_eq_bind, Option.pure_def, Option.map_bind]
  congr 1
  funext first
  simp only [Function.comp_apply, Option.map_bind]
  congr 1

abbrev PrepareSpec := Message →ₒ Option Message

structure ServerReady where
  agreement : RegistrationBoundGate.PublicAgreement
  reference : Message

structure BeaconReady where
  descriptor : RegistrationBeaconBoundSource.PublicAgreement
  reference : Message

def ServerReady.eval (candidate : MlKemSharedSecret) (ready : ServerReady) : RegistrationServerReferenceRoot.Ready :=
  ⟨ready.agreement, RegistrationNativeSecretWordMessage.eval candidate ready.reference⟩

def BeaconReady.eval (candidate : MlKemSharedSecret) (ready : BeaconReady) : RegistrationBeaconReferenceRoot.Ready :=
  ⟨ready.descriptor, RegistrationNativeSecretWordMessage.eval candidate ready.reference⟩

structure ServerState where
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option ServerReady)

def ServerState.eval (candidate : MlKemSharedSecret) (before : ServerState) : RegistrationServerMaterialFrontend.State :=
  ⟨before.control, before.pin, before.consumed, before.sessions.map (Option.map (ServerReady.eval candidate))⟩

structure State (source : RegistrationNativeMldsa.Source) where
  server : ServerState
  beacons : RegistrationNativePublicOwners.State source
  environment : RegistrationServerReferenceCompiler.Environment
  parsedAccepts : Nat

def State.eval {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret) (before : State source) :
    RegistrationNativePublicFrontend.State source :=
  ⟨before.server.eval candidate, before.beacons, before.environment, before.parsedAccepts⟩

/-- The symbolic whole-frontend state erases no owner, local environment, signing history or parsed-attempt field. -/
theorem state_fields {source : RegistrationNativeMldsa.Source} (candidate : MlKemSharedSecret) (before : State source) :
    (before.eval candidate).beacons = before.beacons ∧ (before.eval candidate).environment = before.environment ∧
      (before.eval candidate).parsedAccepts = before.parsedAccepts ∧
      (before.eval candidate).server.control = before.server.control ∧
      (before.eval candidate).server.pin = before.server.pin ∧
      (before.eval candidate).server.consumed = before.server.consumed := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.eval_literal' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.eval_literal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.input_eval' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.input_eval
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.state_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordMessage.state_fields
