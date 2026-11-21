-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCutJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformCutErasure
/-! The complete actual stateful Beacon Init and Server response publication programs erase only the private chronological hash journal to the full native interpreter execution. Actual dynamic encoders and Ed capabilities retain the same shared base-monad poststates on all failures. The proof derives sign metadata from source continuations and uses no codec law or source-wrapper security premise. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld
open RegistrationNativePlatformCutJournal (State source forward)
open RegistrationNativePlatformCutErasure (liftWorld)
open RegistrationNativePlatformCutJournal (extended)
variable {S : Type} {Encoded : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
variable (impl : QueryImpl RegistrationSigningShared.Spec (StateT S m))
variable (fallback : registration.MldsaSigningRequest → StateT S m RegistrationSigningShared.SignReply)

abbrev BeaconSideSpec (Encoded : Type) := RegistrationBeaconInitExecutor.EdSpec +
  (registration.InitView →ₒ RustM (core.option.Option Encoded))

private def beaconSide
    (ed : registration.Ed25519SigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT S m (RustM (core.option.Option Encoded))) :
    QueryImpl (BeaconSideSpec Encoded) (StateT S m)
  | .inl request => ed request
  | .inr view => encode view

noncomputable def beaconOutgoing
    (ed : registration.Ed25519SigningRequest → StateT S m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT S m)
  | .inl (.hash request) => impl (.hash request)
  | .inl (.sign _ _ _) => pure .None
  | .inr request => ed request

private def beaconFree : QueryImpl RegistrationBeaconInitExecutor.Spec
    (OracleComp (RegistrationNativePlatformCutErasure.Spec (BeaconSideSpec Encoded)))
  | .inl (.hash request) => (RegistrationNativePlatformCutErasure.Spec (BeaconSideSpec Encoded)).query (.inl (.hash request))
  | .inl (.sign _ _ _) => pure .None
  | .inr request => (RegistrationNativePlatformCutErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inl request))

private def encodeFree (view : registration.InitView) :
    OracleComp (RegistrationNativePlatformCutErasure.Spec (BeaconSideSpec Encoded)) (RustM (core.option.Option Encoded)) :=
  (RegistrationNativePlatformCutErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inr view))

private theorem beacon_forward
    (ed : registration.Ed25519SigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT S m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (forward impl) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing impl ed) encode control inputs scalar pin).run before.1 := by
  have erased := RegistrationNativePlatformCutErasure.program impl (beaconSide ed encode)
    (RegistrationNativePlatformBeaconPublication.begin beaconFree encodeFree control inputs scalar pin) before
  rw [RegistrationNativePlatformBeaconPublication.begin_interpret,
    RegistrationNativePlatformBeaconPublication.begin_interpret] at erased
  have leftCallbacks : (fun query => simulateQ (RegistrationNativePlatformCutErasure.handler impl (beaconSide ed encode))
      (beaconFree (Encoded := Encoded) query)) =
      extended (forward impl) (fun request => liftWorld (ed request)) := by
    funext query
    cases query with
    | inl query => cases query <;> simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformCutErasure.handler, extended, simulateQ_pure]
    | inr query => simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformCutErasure.handler, beaconSide, extended]
  have rightCallbacks : (fun query => simulateQ (RegistrationNativePlatformCutErasure.native impl (beaconSide ed encode))
      (beaconFree (Encoded := Encoded) query)) = beaconOutgoing impl ed := by
    funext query
    cases query with
    | inl query => cases query <;> simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformCutErasure.native, beaconOutgoing, simulateQ_pure]
    | inr query => simp only [beaconFree, simulateQ_spec_query, RegistrationNativePlatformCutErasure.native, beaconSide, beaconOutgoing]
  rw [leftCallbacks, rightCallbacks] at erased
  simpa only [encodeFree, simulateQ_spec_query, RegistrationNativePlatformCutErasure.handler,
    RegistrationNativePlatformCutErasure.native, beaconSide] using erased

/-- Source request-only signing and effectful source writing retain the complete native interpreter poststate after erasing only the private chronological cut. -/
theorem beacon
    (ed : registration.Ed25519SigningRequest → StateT S m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT S m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (source impl fallback) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing impl ed) encode control inputs scalar pin).run before.1 := by
  rw [RegistrationNativePlatformCutJournal.beacon_begin]
  exact beacon_forward impl ed encode control inputs scalar pin before

theorem server
    (encode : registration.SignedResponseView → StateT S m (RustM (core.option.Option Encoded)))
    (pending : registration.ServerResponseHash) (before : State S) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformServerPublication.program (source impl fallback) (fun view => liftWorld (encode view)) pending).run before =
      (RegistrationNativePlatformServerPublication.program
        (fun query => impl query) encode pending).run before.1 := by
  rw [RegistrationNativePlatformCutJournal.server]
  let spec := RegistrationNativePlatformCutErasure.Spec (registration.SignedResponseView →ₒ RustM (core.option.Option Encoded))
  have erased := RegistrationNativePlatformCutErasure.program impl encode
    (RegistrationNativePlatformServerPublication.program (fun query => spec.query (.inl query))
      (fun view => spec.query (.inr view)) pending) before
  rw [RegistrationNativePlatformServerPublication.program_interpret,
    RegistrationNativePlatformServerPublication.program_interpret] at erased
  simpa only [spec, simulateQ_spec_query, RegistrationNativePlatformCutErasure.handler,
    RegistrationNativePlatformCutErasure.native] using erased
end BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCutWorld.server
