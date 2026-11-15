-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeInitializerAgreement
import BeaconcryptCore.Computational.RegistrationNativeInitializedRootAgreement

/-! Original initialized protected native finish determines complementary computations at both actually reached source initializers. The root is proved by the same-run primitive/source argument; the actual pending initializers and concrete fixed-source replies give complementary chains and all logical message-key streams under a common step interpretation. Later consumed record kernels and application equality are separate content obligations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open BeaconcryptCore.Refinement.PqxdhConcreteSession (ConcreteSession)
variable {n : Nat} {ι KemSK AD PT CT : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

/-- The exact reached pending role initializers resumed with concrete fixed-source replies have one complementary pair of origin streams. -/
def Initializers (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (serverCapability : agreement.ServerAgreement) (beaconCapability : agreement.BeaconAgreement)
    (serverInitial : registration.ServerInitialKdf) (beaconInitial : registration.BeaconInitialKdf) : Prop :=
  ∃ beaconOrigin serverOrigin beaconKernel serverKernel,
    pqxdh.concrete.resume_initial_ratchet_kdf beaconInitial.pending
      (RawCtxSourceHkdf.initialResponse source.crypto ⟨beaconCapability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩) = .ok beaconKernel ∧
    pqxdh.concrete.resume_initial_ratchet_kdf serverInitial.pending
      (RawCtxSourceHkdf.initialResponse source.crypto ⟨serverCapability.root.bytes, ratchet.INITIAL_RATCHET_INFO⟩) = .ok serverKernel ∧
    ConcreteSession crypto beaconOrigin serverOrigin beaconKernel serverKernel ∧
    beaconKernel.refined.send_chain = serverKernel.refined.receive_chain ∧
    beaconKernel.refined.receive_chain = serverKernel.refined.send_chain ∧
    ∀ position, Ratchet.msgKeyAt crypto beaconKernel.refined.send_chain position = Ratchet.msgKeyAt crypto serverKernel.refined.receive_chain position ∧
      Ratchet.msgKeyAt crypto serverKernel.refined.send_chain position = Ratchet.msgKeyAt crypto beaconKernel.refined.receive_chain position

/-- The same native successful completion receipt retains both source initializer computations alongside the actual consumed Beacon record kernel. -/
def Outcome (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (token : peer.ConsumedRegistration)
    (serverInitial : registration.ServerInitialKdf) (pending : registration.BeaconPending) (application : Pqxdh.Bytes) : Prop :=
    ∃ (capability : agreement.BeaconAgreement) (established : registration.CompletedBeacon)
      (initial : registration.BeaconInitialKdf) (aead : registration.BeaconRecordAead) (plaintext : Slice U8)
      (adDigest : CtxRomAuth.CtxDigest),
      Initializers crypto source token.agreement capability serverInitial initial ∧
      token.agreement.root.bytes = capability.root.bytes ∧
      capability.binding = RegistrationResponseExecutor.completedBinding pending adDigest ∧
      established.binding = BeaconcryptCore.Refinement.RegistrationPublication.completedBinding (RegistrationResponseExecutor.completedBinding pending adDigest) capability.candidate.assigned_key_id ∧
      registration.begin_beacon_completion capability = .ok initial ∧ initial.agreement = capability ∧
      BeaconcryptCore.Refinement.RegistrationReachability.BeaconRecordReachable initial (.AeadRequested aead) ∧
      aead.agreement = capability ∧
      aead.pending.finish (.Some plaintext) = .ok (established.kernel,
        .Some (⟨plaintext, capability.candidate.server_binding.identity_key_id, 1#u64⟩ : record.OpenedRecord (Slice U8))) ∧
      established.application = plaintext.drop 8#usize ∧ application = TranscriptAuthParts.absSlice established.application

/-- Every original initialized protected finish has earlier same-run root-bearing Server and Beacon initializers with complementary concrete source computations. -/
theorem path_initializers (crypto : Ratchet.Crypto ratchet.RatchetChain ratchet.RatchetMaterial AD PT CT) (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKid : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKid))
    (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native)) (final : Native)
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (pending : registration.BeaconPending) (packet : registration.ResponsePacket)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (beforeFinish afterFinish : Native) (application : Pqxdh.Bytes)
    (member : (⟨.inr (.finish index (some packet)), beforeFinish, .ok (some application), afterFinish⟩ : Call RegistrationNativeRawAdapter.TypedSpec Native) ∈ calls)
    (found : beforeFinish.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime)
    (good : ¬ RegistrationNativeMldsaOriginJournal.BadCalls initial.credential calls)
    (keyProtected : pending.binding.server_pin.public_key = initial.credential.publicKey)
    (collisionFree : ¬ CacheHasCollision (RegistrationNativeWorldCache.cache beforeFinish))
    (correct : RegistrationNativePairedCoordinates.RecipientCorrect setup) :
    ∃ serverCall ∈ calls, ∃ handle token current plaintext availability serverInitial hashed,
      serverCall.query = .inr (.build handle (some plaintext)) ∧
      RegistrationServerSdkSource.take handle serverCall.before.server = (some token, current) ∧
      BeaconcryptCore.Refinement.RegistrationAd.ServerAdmission current.control current.pin availability token.agreement plaintext serverInitial ∧
      RegistrationServerRecordExecutor.Path serverInitial hashed ∧ Outcome crypto setup.source token serverInitial pending application := by
  obtain ⟨serverCall, memberServer, handle, token, current, plaintext, availability, serverInitial, hashed,
      query, taken, admitted, path, rootOutcome⟩ := RegistrationNativeInitializedRootAgreement.path_root
    setup checks wire route representation ensureInit identityIndex serverKid initial startup calls final actual
    index pending packet owner oneTime beforeFinish afterFinish application member found phase good keyProtected collisionFree correct
  obtain ⟨capability, established, beaconInitial, aead, opened, adDigest, rootEq, binding, metadata, started,
      sameAgreement, reached, aeadAgreement, kernel, message, returned⟩ := rootOutcome
  have paired : Initializers crypto setup.source token.agreement capability serverInitial beaconInitial :=
    RegistrationNativeInitializerAgreement.kernels crypto setup.source current.control current.pin availability token.agreement
      capability plaintext serverInitial beaconInitial admitted started rootEq
  exact ⟨serverCall, memberServer, handle, token, current, plaintext, availability, serverInitial, hashed,
    query, taken, admitted, path, capability, established, beaconInitial, aead, opened, adDigest, paired, rootEq, binding, metadata,
    started, sameAgreement, reached, aeadAgreement, kernel, message, returned⟩

end BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers.path_initializers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitializedInitializers.path_initializers
