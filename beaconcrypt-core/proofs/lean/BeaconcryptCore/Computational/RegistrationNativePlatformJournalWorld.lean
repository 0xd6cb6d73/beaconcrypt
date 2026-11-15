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
  (registration.InitView →ₒ RustM (core.option.Option Encoded))

private def beaconSide
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded))) :
    QueryImpl (BeaconSideSpec Encoded) (StateT (RegistrationWorldSigning.State n) m)
  | .inl request => ed request
  | .inr view => encode view

noncomputable def beaconOutgoing
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply) :
    QueryImpl RegistrationBeaconInitExecutor.Spec (StateT (RegistrationWorldSigning.State n) m)
  | .inl (.hash request) => RegistrationNativePlatformInterpret.state coins (RegistrationWorldSigning.outgoing primitive (.hash request))
  | .inl (.sign _ _ _) => pure .None
  | .inr request => ed request

private def beaconFree : QueryImpl RegistrationBeaconInitExecutor.Spec
    (OracleComp (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)))
  | .inl (.hash request) => (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inl (.hash request))
  | .inl (.sign _ _ _) => pure .None
  | .inr request => (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inl request))

private def encodeFree (view : registration.InitView) :
    OracleComp (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)) (RustM (core.option.Option Encoded)) :=
  (RegistrationNativePlatformJournalErasure.Spec (BeaconSideSpec Encoded)).query (.inr (.inr view))

omit [LawfulMonad m] in
private theorem hash_congr
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (same : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (pending : registration.BeaconInitHash) :
    RegistrationNativePlatformBeaconPublication.fromHash left encode pending =
      RegistrationNativePlatformBeaconPublication.fromHash right encode pending := by
  unfold RegistrationNativePlatformBeaconPublication.fromHash
  apply congrArg (RegistrationNativePlatformBeaconPublication.continueWith pending.request)
  funext request
  rw [same]

omit [LawfulMonad m] in
private theorem ed_congr
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (hashSame : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (edSame : ∀ request, left (.inr request) = right (.inr request))
    (pending : registration.BeaconEd25519Signing) :
    RegistrationNativePlatformBeaconPublication.fromEd left encode pending =
      RegistrationNativePlatformBeaconPublication.fromEd right encode pending := by
  rw [RegistrationNativePlatformBeaconPublication.fromEd.eq_def,
    RegistrationNativePlatformBeaconPublication.fromEd.eq_def]
  apply congrArg (RegistrationNativePlatformBeaconPublication.continueWith pending.request)
  funext request
  rw [edSame]
  apply congrArg (Bind.bind (right (.inr request)))
  funext reply
  cases resumed : pending.resume reply with
  | fail error | div => rfl
  | ok effect => cases effect with
    | Ed25519SigningRequested next => exact ed_congr left right encode hashSame edSame next
    | HashRequested next => exact hash_congr left right encode hashSame next
    | _ => rfl
termination_by RegistrationBeaconInitExecutor.edRank pending
decreasing_by exact RegistrationBeaconInitExecutor.ed_rank pending reply next resumed

omit [LawfulMonad m] in
private theorem begin_congr
    (left right : QueryImpl RegistrationBeaconInitExecutor.Spec m)
    (encode : registration.InitView → m (RustM (core.option.Option Encoded)))
    (hashSame : ∀ request, left (.inl (.hash request)) = right (.inl (.hash request)))
    (edSame : ∀ request, left (.inr request) = right (.inr request))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) :
    RegistrationNativePlatformBeaconPublication.begin left encode control inputs scalar pin =
      RegistrationNativePlatformBeaconPublication.begin right encode control inputs scalar pin := by
  unfold RegistrationNativePlatformBeaconPublication.begin
  apply congrArg (RegistrationNativePlatformBeaconPublication.continueWith
    (registration.begin_beacon_init control inputs scalar pin))
  funext effect
  cases effect with
  | Ed25519SigningRequested next => exact ed_congr left right encode hashSame edSame next
  | _ => rfl

private theorem beacon_forward
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : State n) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (forward coins primitive) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing coins primitive ed) encode control inputs scalar pin).run before.1 := by
  have erased := RegistrationNativePlatformJournalErasure.program coins primitive (beaconSide ed encode)
    (RegistrationNativePlatformBeaconPublication.begin beaconFree encodeFree control inputs scalar pin) before
  rw [RegistrationNativePlatformBeaconPublication.begin_interpret,
    RegistrationNativePlatformBeaconPublication.begin_interpret] at erased
  have rightCallbacks : (fun query => simulateQ (RegistrationNativePlatformJournalErasure.native coins primitive (beaconSide ed encode))
      (beaconFree (Encoded := Encoded) query)) = beaconOutgoing coins primitive ed := by
    funext query
    cases query with
    | inl request => cases request <;> simp only [beaconFree, simulateQ_spec_query,
        simulateQ_pure, RegistrationNativePlatformJournalErasure.native, beaconOutgoing]
    | inr request => simp only [beaconFree, simulateQ_spec_query,
        RegistrationNativePlatformJournalErasure.native, beaconSide, beaconOutgoing]
  rw [rightCallbacks] at erased
  simp only [encodeFree, simulateQ_spec_query, RegistrationNativePlatformJournalErasure.handler,
    RegistrationNativePlatformJournalErasure.native, beaconSide] at erased
  rw [begin_congr _ (extended (forward coins primitive) (fun request => liftWorld (ed request)))
    _ (by intro request; simp only [beaconFree, simulateQ_spec_query,
      RegistrationNativePlatformJournalErasure.handler, extended])
    (by intro request; simp only [beaconFree, simulateQ_spec_query,
      RegistrationNativePlatformJournalErasure.handler, beaconSide, extended])] at erased
  exact erased

/-- Source request-only signing and effectful source writing retain the complete native World after erasing only the private chronological cut. -/
theorem beacon
    (ed : registration.Ed25519SigningRequest → StateT (RegistrationWorldSigning.State n) m RegistrationSigningShared.SignReply)
    (encode : registration.InitView → StateT (RegistrationWorldSigning.State n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.BeaconFresh) (inputs : pqxdh.BeaconStartInputs) (scalar : pqxdh.BeaconCoins)
    (pin : session.ServerAuthenticationPin) (before : State n) :
    Prod.map id Prod.fst <$>
      (RegistrationNativePlatformBeaconPublication.begin (extended (source coins primitive) (fun request => liftWorld (ed request)))
        (fun view => liftWorld (encode view)) control inputs scalar pin).run before =
      (RegistrationNativePlatformBeaconPublication.begin (beaconOutgoing coins primitive ed) encode control inputs scalar pin).run before.1 := by
  rw [RegistrationNativePlatformJournalPublication.beacon_begin]
  exact beacon_forward coins primitive ed encode control inputs scalar pin before

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
