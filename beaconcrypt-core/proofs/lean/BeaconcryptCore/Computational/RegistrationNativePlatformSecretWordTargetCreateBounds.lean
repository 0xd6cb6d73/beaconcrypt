-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAliasCreate
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateFrontend
import BeaconcryptCore.Computational.RegistrationNativeKemFullFootprint
/-! Original public create budgets count every genuine private KEM birth of the actual corrected Word frontend, including rows created before a later constructor refusal. Other current dynamic callbacks have zero private births. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordTargetPoolFrame (IsCreate)
open RegistrationNativePlatformSecretWordOrdinary (State)
variable {n : Nat} {I KemSK Platform E A : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

private theorem compiler_bound (work : OracleComp (RegistrationNativeBeaconFrontend.Trusted n KemSK) A) (cap : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativeKemBeaconFootprint.counted (n := n) (KemSK := KemSK) .create) cap) :
    (simulateQ RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler work).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) cap := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work cap bounded
  intro query
  rcases query with effect | other | pool | key
  all_goals try cases pool
  all_goals simp [RegistrationNativeSecretWordTargetAlignmentCreateQuery.compiler, QueryImpl.compose,
    RegistrationBeaconReferenceCompiler.trustedLift, RegistrationBeaconReferenceCompiler.effect, RegistrationBeaconReferenceCompiler.indexed,
    RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.common,
    RegistrationNativeSecretWordInterface.localKem, RegistrationNativeSecretWordInterface.liftLocal,
    RegistrationNativeSecretWordInterface.route, RegistrationNativeSecretWordInterface.routedKem,
    IsCreate, RegistrationNativeKemBeaconFootprint.counted, isQueryBoundP_query_iff, isQueryBoundP_map_iff]

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The actual common-platform creation body has at most one genuine private KEM birth, regardless of its eventual result. -/
theorem create_bound (setup : Setup base KemSK) (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State source Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) (KemSK := KemSK) setup source selectedOwner publicPrekey reserveFrame writer
      (.inr (.create edPin mlPin keyId))).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) 1 := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler, RegistrationNativePlatformSecretWordOrdinary.beacon,
    RegistrationNativePlatformPublicOwners.create, RegistrationNativePlatformPublicOwners.executeLocal,
    RegistrationNativePlatformGenericBundle.liftLegacy, StateT.run, map_apply, simulateQ_map, isQueryBoundP_map_iff]
  change (simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base RegistrationNativeSecretWordMessage.zero)
    ((simulateQ RegistrationNativePlatformPublicFrontend.trusted
      (((RegistrationNativeBeaconFrontend.create (n := n) (Auxiliary := RegistrationServerRoleBackend.State)
        setup source edPin mlPin keyId).run (before.1.beacons.map RegistrationNativePublicOwners.restore)).run before.1.environment)).run before.2)).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) 1
  rw [RegistrationNativePlatformSecretWordAliasCreate.native_program, isQueryBoundP_map_iff]
  exact compiler_bound _ 1 (RegistrationNativeKemBeaconFootprint.create_bound setup .create edPin mlPin keyId _ _)

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "handler" => RegistrationNativePlatformSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
  view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer

/-- Only the literal current public create call can spend a private birth allowance. -/
theorem handler_bound (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform) :
    ((handler query).run before).IsQueryBoundP (IsCreate (KemSK := KemSK))
      (if RegistrationNativeRawAdapter.kind query = 1 then 1 else 0) := by
  by_cases creates : RegistrationNativeRawAdapter.kind query = 1
  · cases query with
    | inl coin => cases creates
    | inr command =>
      cases command with
      | create edPin mlPin keyId => exact create_bound setup selectedOwner publicPrekey reserveFrame writer edPin mlPin keyId before
      | _ => cases creates
  · simpa only [ite_eq_right creates] using
      RegistrationNativePlatformSecretWordNoCreateFrontend.handler_free setup checks wire source sign selectedOwner selectedAccept publicPrekey
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query creates before

/-- Arbitrary adaptive typed source work retains its original create allowance. -/
theorem program_bound (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (cap : Nat)
    (bounded : work.IsQueryBoundP (fun query => RegistrationNativeRawAdapter.kind query = 1) cap) (before : State source Platform) :
    ((simulateQ handler work).run before).IsQueryBoundP (IsCreate (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted current
    simpa only [ite_eq_left counted] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current
  · intro query free current
    simpa only [ite_eq_right free] using handler_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query current

/-- The actual complete raw compiler supplies the public create budget internally, with every mode and original ledger retained. -/
theorem run_bound (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (budget : PqxdhDeploymentInterface.Budget)
    (bounded : RegistrationNativeInterface.Respects budget work) (before : State source Platform) :
    (RegistrationNativePlatformSecretWordFrontend.run (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before).IsQueryBoundP
      (IsCreate (KemSK := KemSK)) budget.create :=
  program_bound setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source sign selectedOwner selectedAccept publicPrekey
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer _ budget.create
    (RegistrationNativeKemFullFootprint.compile_creates setup.source.crypto (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire)
      serverKeyId bounds mode work budget bounded) before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.create_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.create_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.handler_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.handler_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.run_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetCreateBounds.run_bound
