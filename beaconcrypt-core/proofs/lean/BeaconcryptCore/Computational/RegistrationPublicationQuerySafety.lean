-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformQuerySafety
/-! Stateful actual publication preserves any query predicate for an arbitrary shared oracle language. The complete returned owner and platform states survive source writer failures. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationPublicationQuerySafety
variable {I Platform State Value Next : Type} {queries : OracleSpec I}
variable (predicate : I → Prop)

def Safe (work : StateT State (StateT Platform (OracleComp queries)) Value) : Prop :=
  ∀ before previous, ((work.run before).run previous).AllQueriesSatisfy predicate

theorem pure_safe (value : Value) : Safe predicate (pure value : StateT State (StateT Platform (OracleComp queries)) Value) :=
  fun _ _ => allQueriesSatisfy_pure _ _

theorem bind_safe (work : StateT State (StateT Platform (OracleComp queries)) Value)
    (next : Value → StateT State (StateT Platform (OracleComp queries)) Next)
    (first : Safe predicate work) (rest : ∀ value, Safe predicate (next value)) :
    Safe predicate (work >>= next) := by
  intro before previous
  simp only [StateT.run_bind]
  exact allQueriesSatisfy_bind (first before previous)
    (fun result => rest result.1.1 result.1.2 result.2)

attribute [local irreducible] registration.BeaconInitHash.resume registration.BeaconFingerprint.resume
  registration.BeaconMldsaSigning.resume registration.BeaconEd25519Signing.resume registration.begin_beacon_init

namespace Beacon
open RegistrationNativePlatformBeaconPublication
open RegistrationBeaconInitExecutor (Spec Result edRank ed_rank)
variable {Encoded : Type}

private theorem continue_safe {Input : Type} (action : RustM Input)
    (next : Input → StateT State ((StateT Platform (OracleComp queries))) (RustM (Result Encoded)))
    (allowed : ∀ value, Safe predicate (next value)) :
    Safe predicate (continueWith action next) := by
  cases action with
  | ok value => exact allowed value
  | fail error | div => exact pure_safe predicate _

theorem ready (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (allowed : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconInitReady) :
    Safe predicate (RegistrationNativePlatformBeaconPublication.ready encode pending) := by
  unfold RegistrationNativePlatformBeaconPublication.ready
  apply continue_safe
  intro view
  exact bind_safe predicate _ _ (allowed view) (fun _ => pure_safe predicate _)

theorem signing (implementation : QueryImpl Spec (StateT State ((StateT Platform (OracleComp queries)))))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view))
    (payload : MldsaTranscriptAuth.Payload) (digest : CtxRomAuth.CtxDigest)
    (pending : registration.BeaconMldsaSigning) :
    Safe predicate (fromSigning implementation encode payload digest pending) := by
  unfold fromSigning
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.sign request payload digest)))
  intro reply
  apply continue_safe
  intro effect
  cases effect with
  | Ready selected => exact ready predicate encode encoded selected
  | _ => exact pure_safe predicate _

theorem hashing (implementation : QueryImpl Spec (StateT State ((StateT Platform (OracleComp queries)))))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconInitHash) :
    Safe predicate (fromHash implementation encode pending) := by
  unfold fromHash
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.hash request)))
  intro digest
  apply continue_safe
  intro effect
  cases effect with
  | MldsaSigningRequested selected => exact signing predicate implementation allowed encode encoded _ digest selected
  | _ => exact pure_safe predicate _

theorem fingerprint (implementation : QueryImpl Spec (StateT State ((StateT Platform (OracleComp queries)))))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconFingerprint) :
    Safe predicate (fromFingerprint implementation encode pending) := by
  unfold fromFingerprint
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inl (.hash request)))
  intro digest
  apply continue_safe
  intro effect
  cases effect with
  | HashRequested selected => exact hashing predicate implementation allowed encode encoded selected
  | _ => exact pure_safe predicate _

theorem ed (implementation : QueryImpl Spec (StateT State ((StateT Platform (OracleComp queries)))))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (pending : registration.BeaconEd25519Signing) :
    Safe predicate (fromEd implementation encode pending) := by
  rw [fromEd.eq_def]
  apply continue_safe
  intro request
  apply bind_safe predicate _ _ (allowed (.inr request))
  intro reply
  cases actual : pending.resume reply with
  | fail error | div => exact pure_safe predicate _
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed implementation allowed encode encoded next
    | FingerprintRequested selected => exact fingerprint predicate implementation allowed encode encoded selected
    | _ => exact pure_safe predicate _
termination_by edRank pending
decreasing_by exact ed_rank pending reply next actual

theorem begin (implementation : QueryImpl Spec (StateT State ((StateT Platform (OracleComp queries)))))
    (allowed : ∀ query, Safe predicate (implementation query))
    (encode : registration.SignedInitView → StateT State ((StateT Platform (OracleComp queries))) (RustM (core.option.Option Encoded)))
    (encoded : ∀ view, Safe predicate (encode view)) (control : pqxdh.BeaconFresh)
    (inputs : pqxdh.BeaconStartInputs) (coins : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (publicKey : Std.Array U8 1952#usize) :
    Safe predicate (RegistrationNativePlatformBeaconPublication.begin implementation encode control inputs coins pin publicKey) := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  apply continue_safe
  intro effect
  cases effect with
  | Ed25519SigningRequested selected => exact ed predicate implementation allowed encode encoded selected
  | _ => exact pure_safe predicate _
end Beacon

end BeaconcryptCore.Computational.RegistrationPublicationQuerySafety

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.pure_safe' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.pure_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.bind_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.bind_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.ready

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.signing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.signing

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.hashing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.hashing

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.fingerprint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.fingerprint

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.ed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.ed

/-- info: 'BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.begin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationPublicationQuerySafety.Beacon.begin
