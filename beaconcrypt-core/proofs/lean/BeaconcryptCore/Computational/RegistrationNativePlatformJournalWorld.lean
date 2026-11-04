-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalPublication
import BeaconcryptCore.Computational.RegistrationNativePlatformJournalErasure
/-! The complete actual stateful Beacon Init and Server response publication programs erase only the private chronological hash journal to the full native World execution. Actual dynamic encoders and Ed capabilities retain the same shared base-monad poststates on all failures. The proof derives sign metadata from source continuations and uses no codec law or source-wrapper security premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld
open RegistrationNativePlatformSigningJournal (State source forward)
open RegistrationNativePlatformJournalErasure (liftWorld)
open RegistrationNativePlatformJournalPublication (extended)
variable {n : Nat} {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable (coins : QueryImpl unifSpec m) (primitive : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)

abbrev BeaconSideSpec (Encoded : Type) := RegistrationBeaconInitExecutor.EdSpec +
  (registration.SignedInitView →ₒ RustM (core.option.Option Encoded))

private def beaconSide
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded))) :
    QueryImpl (BeaconSideSpec Encoded) (StateT (RegistrationWorldSigning.State n) m)
  | .inl request => ed request
  | .inr view => encode view

noncomputable def beaconOutgoing
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (RegistrationWorldSigning.State n) m)
  | .inl query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive query)
  | .inr request => ed request

private def beaconFree : QueryImpl RegistrationBeaconInitExecutor.Spec
    (OracleComp (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)))
  | .inl query => (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inl query)
  | .inr request => (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inl request))

private def encodeFree (view : registration.SignedInitView) :
    OracleComp (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)) (RustM (core.option.Option Encoded)) :=
  (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inr view))

private theorem beacon_forward
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) (before : State n) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (forward coins primitive) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing coins primitive ed) encode control inputs scalar pin mldsa).run before.1 := by
  have erased := RegistrationNativePlatformJournalErasure.program coins primitive (beaconSide ed encode)
    (RegistrationNativePlatformBeaconPublication.begin beaconFree encodeFree control inputs scalar pin mldsa) before
  rw [RegistrationNativePlatformBeaconPublication.begin_interpret,
    RegistrationNativePlatformBeaconPublication.begin_interpret] at erased
  have leftCallbacks : (fun query => simulateQ (RegistrationNativePlatformJournalErasure.handler coins primitive (beaconSide ed encode))
      (beaconFree (Encoded := Encoded) query)) =
      extended (forward coins primitive) (fun request => liftWorld (ed request)) := by
    funext query
    cases query <;> simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformJournalErasure.handler, beaconSide, extended]
  have rightCallbacks : (fun query => simulateQ (RegistrationNativePlatformJournalErasure.native coins primitive (beaconSide ed encode))
      (beaconFree (Encoded := Encoded) query)) = beaconOutgoing coins primitive ed := by
    funext query
    cases query <;> simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformJournalErasure.native, beaconSide, beaconOutgoing]
  rw [leftCallbacks, rightCallbacks] at erased
  simpa only [encodeFree, simulateQ_spec_query, RegistrationNativePlatformJournalErasure.handler,
    RegistrationNativePlatformJournalErasure.native, beaconSide] using erased

/-- Source request-only signing and effectful source writing retain the complete native World after erasing only the private chronological cut. -/
theorem beacon
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.SignedInitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (mldsa : Std.Array U8 1952#usize) (before : State n) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (source coins primitive) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin mldsa).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing coins primitive ed) encode control inputs scalar pin mldsa).run before.1 := by
  rw [RegistrationNativePlatformJournalPublication.beacon_begin]
  exact beacon_forward coins primitive ed encode control inputs scalar pin mldsa before

theorem server
    (encode : registration.SignedResponseView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : State n) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformServerPublication.program (source coins primitive) (fun view => liftWorld (encode view)) pending).run before =
      (RegistrationNativePlatformServerPublication.program
        (fun query => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive query)) encode pending).run before.1 := by
  rw [RegistrationNativePlatformJournalPublication.server]
  let spec := RegistrationNativePlatformJournalErasure.Spec (registration.SignedResponseView →ₒ RustM (core.option.Option Encoded))
  have erased := RegistrationNativePlatformJournalErasure.program coins primitive encode
    (RegistrationNativePlatformServerPublication.program (fun query => spec.query (.inl query))
      (fun view => spec.query (.inr view)) pending) before
  rw [RegistrationNativePlatformServerPublication.program_interpret,
    RegistrationNativePlatformServerPublication.program_interpret] at erased
  simpa only [spec, simulateQ_spec_query, RegistrationNativePlatformJournalErasure.handler,
    RegistrationNativePlatformJournalErasure.native] using erased
end BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformJournalWorld.server
