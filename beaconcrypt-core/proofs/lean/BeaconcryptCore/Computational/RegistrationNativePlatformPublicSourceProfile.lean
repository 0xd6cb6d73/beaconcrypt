-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceFull
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinarySeedProfile
/-! Literal generated runtime initialization and the corrected root-oracle client retain the original full-ledger decision and persistent platform state. Selected seed and scalar remain private source parameters. This intermediate client receives public challenge data and roots returned by RootSpec.derive, retains an oracle-derived root memo, and computes full material from those replies. It is not the separate restricted material44/opaque-slot environment. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {I KemSK Platform E Value : Type} {base : OracleSpec I}
variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (selectedOwner selectedAccept : Nat)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (decision : Value × RegistrationNativeLedger.State → Bool)

/-- The executable initialized client receives only the selected public challenge and retains literal dynamic source writers. -/
noncomputable def client (publicValue : PqxdhJointGapDh.PublicChallenge) (previous : Platform) :
    OracleComp RegistrationNativeRelatedRoot.RootSpec (Bool × Platform) := do
  let initialized ← (RegistrationNativePublicStartup.start (n := n) setup source ensureInit identityIndex serverKeyId publicValue.identity).run
    RegistrationNativePublicInterpreter.initial
  match initialized.1 with
  | none => pure (false, previous)
  | some started => do
    let observed ← RegistrationNativePlatformPublicSourceFull.run setup checks wire route started.credential selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer publicValue.prekey serverKeyId bounds mode
      (adversary ⟨publicValue.identity, started.credential.publicKey, serverKeyId⟩) started.frontend initialized.2 previous
    pure (decision observed.1.1, observed.1.2.2)

/-- Successful literal startup derives every internal source condition before the actual full-ledger/native/P run comparison. -/
theorem fixed_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) (previous : Platform) :
    simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
      (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
        (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) previous) = (do
      let initialized ← RegistrationNativeSeedStart.start (n := n) setup source ensureInit identityIndex serverKeyId seed
      match initialized with
      | none => pure (false, previous)
      | some initial =>
        (fun (result : ((Value × RegistrationNativeLedger.State) × RegistrationNativeExperiment.State n KemSK source) × Platform) => (decision result.1.1, result.2)) <$>
          (RegistrationNativePlatformOrdinaryScalarEager.run setup checks wire route representation initial.created source initial.credential view failure allocation
            reserveRegistration reservePeer reserveFrame erased helper writer selectedOwner scalar bounds mode (adversary initial.public) initial.state).run previous) := by
  rw [← RegistrationNativePublicSourceStartup.start_source setup source ensureInit identityIndex serverKeyId seed scalar]
  simp only [client, simulateQ_bind, bind_map_left]
  apply bind_congr_of_forall_mem_support
  rintro ⟨initialized, after⟩ supported
  cases initialized with
  | none => rfl
  | some started =>
    have good := RegistrationNativePlatformPublicSourceGood.start setup source seed scalar ensureInit identityIndex serverKeyId selectedOwner started after previous supported
    let created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize) :=
      PqxdhLiveServerConstruction.initialized setup.joint identityIndex serverKeyId .generated seed
    have actual := RegistrationNativePlatformPublicSourceFull.ledger_source setup checks wire route started.credential selectedOwner selectedAccept scalar view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer representation correct created bounds mode
      (adversary ⟨setup.joint.publicKeys seed, started.credential.publicKey, serverKeyId⟩) started.frontend after previous good decision
    simpa only [RegistrationNativePublicSourceStartupWorld.observe, Option.map_some,
      simulateQ_bind, simulateQ_pure, simulateQ_map, bind_pure_comp, RegistrationNativeExperiment.Initial.public,
      PqxdhJointGapDh.challenge, created, PqxdhLiveServerConstruction.initialized] using actual

/-- The joint source game keeps the actual persistent platform poststate beside the decision. -/
noncomputable def jointGame (previous : Platform) : ProbComp (Bool × Platform) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let scalar ← PqxdhJointGapDh.sampleScalar
  simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed scalar)
    (client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision
      (PqxdhJointGapDh.challenge setup.joint setup.dh seed scalar) previous)

/-- The source joint game is the literal initialized seed/scalar runtime profile, including every failure and exact P. -/
theorem seeded_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) (previous : Platform) :
    jointGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous =
      (RegistrationNativePlatformOrdinarySeedProfile.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId selectedOwner
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
        (fun result => decision (result.1, result.2.1))).run previous := by
  simp only [jointGame, fixed_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct,
    RegistrationNativePlatformOrdinarySeedProfile.profile, StateT.run_bind, StateT.run_lift,
    bind_pure_comp]
  simp only [bind_map_left]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  apply bind_congr
  intro initialized
  cases initialized with
  | none => rfl
  | some initial => simp only [StateT.run_map]

/-- The original corrected generated runtime has this actual public-client source-game law, retaining the complete P marginal. -/
theorem profile_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) (previous : Platform) :
    (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1))).run previous =ᵈ
      jointGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous := by
  rw [seeded_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct]
  exact RegistrationNativePlatformOrdinarySeedProfile.source_law (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId selectedOwner
    view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary _ previous

/-- The joint decision marginal is exactly the established primitive related-root source game of this concrete public client. -/
theorem source_game (previous : Platform) :
    Prod.fst <$> jointGame (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous =
    RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
      (fun publicValue => Prod.fst <$> client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous) := by
  simp only [jointGame, RegistrationNativeRelatedRoot.sourceGame, StateT.run'_eq, map_bind]
  apply bind_congr
  intro seed
  apply bind_congr
  intro scalar
  rw [RegistrationNativeSourceRoot.program_value, simulateQ_map]

/-- Every original full-ledger decision has the same initialized concrete source game, without a source-profile correspondence premise. -/
theorem decision_source (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac) (previous : Platform) :
    Prod.fst <$> (RegistrationNativePlatformOrdinaryExperiment.profile (n := n) setup checks wire route representation source ensureInit identityIndex serverKeyId
      view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary
      (fun result => decision (result.1, result.2.1))).run previous =ᵈ
    RegistrationNativeRelatedRoot.sourceGame setup.source setup.hmac setup.joint setup.dh
      (fun publicValue => Prod.fst <$> client (n := n) setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept
        view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision publicValue previous) := by
  rw [← source_game setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision previous]
  exact (profile_source setup checks wire route source ensureInit identityIndex serverKeyId selectedOwner selectedAccept view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer bounds mode adversary decision representation correct previous).map Prod.fst

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.fixed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.fixed_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.seeded_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.seeded_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.profile_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.profile_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.source_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.source_game

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.decision_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicSourceProfile.decision_source
