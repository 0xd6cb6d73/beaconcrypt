-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeFinishLifetime
import BeaconcryptCore.Refinement.AdapterPublicFinishSourceJournal
import BeaconcryptCore.Refinement.AdapterPublicFinishEndpoint
/-! The literal complete extracted active SDK finish and the actual corrected native finish are projections of the same trusted cryptographic run. Concrete decoding, source loops and individual primitive contracts are dependencies. Every reached result has derived normality, exact returned bytes and selected owner, and the complete private-material, binding, assigned-identifier, kernel and World-slot relation; the native finalizer accounts explicitly for metadata and the terminal administrative effect. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Refinement.AdapterPublicFinishLifetime
open BeaconcryptCore.Computational
open RegistrationNativeBeaconFrontend (M Owner Trusted)
variable {n : Nat} {I KemSK : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

noncomputable def packet (input : Slice U8) : Option registration.ResponsePacket :=
  RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input)

theorem packet_roundtrip (input : Slice U8) :
    ((match packet input with | none => core.option.Option.None | some value => core.option.Option.Some value) : core.option.Option registration.ResponsePacket) =
      (RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input) : core.option.Option registration.ResponsePacket) := by
  unfold packet
  cases RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input) <;> rfl

variable [material : PublicWrapperPlatform.Material] [ed : AdapterInitEdPrimitive.Operations]
variable [platform : PublicWrapperPlatform.Platform] [PublicWrapperPlatform.CryptoOperations]
variable [localOps : AdapterPublicWrapperRequestMonad.LocalOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State))]
variable {E : Type}
theorem same_execution (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire)
    (erased : commitment.CommitmentTranscript)
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (M n KemSK source RegistrationServerRoleBackend.State))
    (initial : ∀ request, (localOps.ratchet_initial_ratchet_hkdf request).run =
      pure (.ok (RawCtxSourceHkdf.initialResponse setup.source.crypto request).bytes))
    (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (model : AdapterPublicAgreementCommonModel.Model (m := M n KemSK source RegistrationServerRoleBackend.State) setup view)
    (parseEd : Slice U8 → M n KemSK source RegistrationServerRoleBackend.State (RustM (core.result.Result ed.PublicKey ed.Error)))
    (verifyEd : Slice U8 → ed.PublicKey → M n KemSK source RegistrationServerRoleBackend.State (RustM (core.option.Option (alloc.vec.Vec U8))))
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state = .InitSent pending prekey oneTime kem) (input : Slice U8) (owner : Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (keys : AdapterPublicAgreementBeaconFrontend.PrivateKeys view
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar)
    (decap : AdapterPublicAgreementBeaconFrontend.Decapsulation model
      (AdapterPublicAgreementBeaconMaterial.registrationKeys
        {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} prekey oneTime kem) owner scalar keys)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar) :
    letI : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
      (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
      (AdapterPublicFinishRecordDictionary.recording setup erased) writer
    letI : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
    ((RegistrationNativeExperiment.beacon setup checks representation created
      ((beaconcrypt_public_request.beacon.Beacon.Insts.BeaconcryptBeaconProviderBeacon.finish_registration
      (m := AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) self input).run)).run before =
        (fun result => (AdapterPublicFinishNormalized.output {self with state := .Aborted (BeaconcryptCore.Refinement.RegistrationResponse.abortedState pending)} result.1.1, result.2)) <$>
          RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before) ∧
    ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformBeaconFinish.finish setup source wire index (packet input))).run before =
      (fun result => (RegistrationNativeFinishTerminalTree.bytes result.1.1,
        RegistrationNativeFinishTerminalTree.after index owner (RegistrationResponse.abortedState pending) result.1.1
          (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2))) <$>
            RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before) := by
  let : AdapterPublicWrapperRequestMonad.ChildOperations (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicWrapperChildren.children
    (AdapterPublicWrapperChildNative.authentication (RegistrationNativeBeaconFrontend.authentication setup source) parseEd verifyEd)
    (AdapterPublicFinishRecordDictionary.recording setup erased) writer
  let : AdapterPublicWrapperRequestMonad.Codecs (AdapterPublicWrapperRustT.RustT (M n KemSK source RegistrationServerRoleBackend.State)) := AdapterPublicConcreteCodecs.codecs
  constructor
  · rw [AdapterPublicFinishSourceJournal.source_joint setup checks representation created wire erased writer initial view model parseEd verifyEd self pending prekey oneTime kem stored input owner scalar keys decap (RegistrationWorldAgreementCompiler.erase before.server.world) before]
    unfold RegistrationNativeFinishLifetime.tree
    unfold packet
    cases RegistrationNativeConcreteCodec.wire.decodeResponse (TranscriptAuthParts.absSlice input) <;> rfl
  · exact RegistrationNativeFinishLifetime.source_ready view setup checks representation created wire index self owner pending prekey oneTime kem scalar stored (packet input) before related selected phase

omit material ed platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem accepted_normal (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (reply : RustM (Option registration.CompletedBeacon))
    (reached : reply ∈ support (RegistrationNativeFinishLowerErasure.accepted (n := n) setup wire owner scalar authenticated)) :
    ∃ optional, reply = .ok optional := by
  simp only [RegistrationNativeFinishLowerErasure.accepted, mem_support_bind_iff] at reached
  obtain ⟨agreed, called, continued⟩ := reached
  have actual := AdapterPublicFinishNormalized.simulation_support (RegistrationNativeAgreementJournal.core setup owner scalar) (RegistrationAgreementExecutor.beacon authenticated) called
  obtain ⟨phase, normal⟩ := RegistrationAgreementNormal.beacon_normal authenticated agreed actual
  rw [normal] at continued
  cases phase with
  | BeaconComplete candidate =>
      simp only [RegistrationNativeFinishLowerErasure.afterAgreement, support_map] at continued
      obtain ⟨opened, called, returned⟩ := continued
      have actual := AdapterPublicFinishNormalized.simulation_support (RegistrationNativeRecordJournal.core setup wire) (RegistrationBeaconRecordExecutor.begin candidate) called
      obtain ⟨result, normal⟩ := RegistrationBeaconRecordNormal.begin_normal candidate opened actual
      cases returned
      rw [normal]
      cases result <;> exact ⟨_, rfl⟩
  | _ =>
      simp only [RegistrationNativeFinishLowerErasure.afterAgreement, support_pure, Set.mem_singleton_iff] at continued
      exact ⟨none, continued⟩

omit material ed platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem body_normal (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (reply : RustM (Option registration.CompletedBeacon))
    (reached : reply ∈ support (RegistrationNativeFinishLowerErasure.body (n := n) setup wire pending packet owner scalar)) :
    ∃ optional, reply = .ok optional := by
  simp only [RegistrationNativeFinishLowerErasure.body, mem_support_bind_iff] at reached
  obtain ⟨authenticated, called, continued⟩ := reached
  have actual := AdapterPublicFinishNormalized.simulation_support (AdapterPublicFinishFreeTree.authentication (source := source) setup) (RegistrationResponseExecutor.begin pending packet) called
  obtain ⟨result, normal⟩ := RegistrationResponseNormal.normal pending packet authenticated actual
  rw [normal] at continued
  cases result with
  | Err rejected =>
      simp only [RegistrationNativeFinishLowerErasure.afterAuthentication, support_pure, Set.mem_singleton_iff] at continued
      exact ⟨none, continued⟩
  | Ok accepted => exact accepted_normal setup wire owner scalar accepted reply continued


omit material ed platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem interpreted_normal {Auxiliary : Type} (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (pending : registration.BeaconPending) (packet : core.option.Option registration.ResponsePacket)
    (owner : Owner source) (scalar : PqxdhJointGapDh.ScalarBytes) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (result : (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState Auxiliary) × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      ((RegistrationNativeFinishFactor.body setup wire pending packet owner scalar).run env)).run before)) :
    ∃ optional, result.1.1 = .ok optional := by
  have raw : result.1 ∈ support ((RegistrationNativeFinishFactor.body (n := n) setup wire pending packet owner scalar).run env) := by
    apply OracleComp.support_simulateQ_run'_subset (RegistrationNativeExperiment.trusted setup checks representation created source) _ before
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst reached
  have projected : result.1.1 ∈ support (RegistrationNativeFinishLowerErasure.body (n := n) setup wire pending packet owner scalar) := by
    rw [← RegistrationNativeFinishLowerErasure.body_erasure (n := n) setup wire pending packet owner scalar env]
    rw [support_map]
    exact Set.mem_image_of_mem Prod.fst raw
  exact body_normal (n := n) setup wire pending packet owner scalar result.1.1 projected


def ownerAfter (owner : Owner source) (control : pqxdh.BeaconAborted) (reply : RustM (Option registration.CompletedBeacon)) : Owner source :=
  match reply with
  | .ok (some completed) => {owner with phase := .established ⟨completed.control, completed.binding, completed.application⟩}
  | _ => {owner with phase := .aborted control}

def ReturnedMaterial (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source) (control : pqxdh.BeaconAborted)
    (index : Nat) (before : RegistrationNativeExperiment.State n KemSK source) (reply : RustM (Option registration.CompletedBeacon)) : Prop :=
  match AdapterPublicFinishNormalized.output {self with state := .Aborted control} reply with
  | .ok (_, returned) => AdapterPublicWrapperState.Beacon view joint
      (RegistrationNativeFinishTerminalTree.after index owner control reply before).pool returned (ownerAfter owner control reply)
      (RegistrationNativeFinishTerminalTree.after index owner control reply before).server.world.world.1.owners[owner.worldOwner]?
  | _ => True

omit platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem returned_material (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (originalPool : PqxdhLiveKemBirth.Pool KemSK) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (world : Option PqxdhRecordLiftBeacon.Phase) (related : AdapterPublicWrapperState.Beacon view joint originalPool self owner world)
    (pending : registration.BeaconPending) (scalar : PqxdhJointGapDh.ScalarBytes) (phase : owner.phase = .initSent pending scalar)
    (index : Nat) (before : RegistrationNativeExperiment.State n KemSK source)
    (ready : PqxdhRecordLiftWorld.BeaconReady before.server.world.world.1 owner.worldOwner)
    (reply : RustM (Option registration.CompletedBeacon)) :
    ReturnedMaterial view joint self owner (RegistrationResponse.abortedState pending) index before reply := by
  cases reply with
  | fail error | div => trivial
  | ok optional => cases optional with
    | none =>
        exact AdapterPublicFinishEndpoint.aborted_material view joint originalPool self owner world related index
          (RegistrationResponse.abortedState pending) before pending scalar phase ready
    | some completed => exact AdapterPublicFinishEndpoint.installed_material view joint originalPool self owner world related index completed before ready

omit material ed platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem selected_owner (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted)
    (reply : RustM (Option registration.CompletedBeacon)) (before : RegistrationNativeExperiment.State n KemSK source)
    (selected : before.beacons[index]? = some owner) :
    (RegistrationNativeFinishTerminalTree.after index owner control reply before).beacons[index]? = some (ownerAfter owner control reply) := by
  cases reply with
  | fail error | div => exact RegistrationNativeFinishTerminal.aborted_owner index owner control before selected
  | ok optional => cases optional with
    | none => exact RegistrationNativeFinishTerminal.aborted_owner index owner control before selected
    | some completed => exact RegistrationNativeFinishTerminal.installed_owner index owner completed before selected


def finalState (index : Nat) (owner : Owner source) (control : pqxdh.BeaconAborted) (owners : List (Owner source))
    (result : (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source) :
    RegistrationNativeExperiment.State n KemSK source :=
  RegistrationNativeFinishTerminalTree.after index owner control result.1.1
    (RegistrationNativeFinishTerminalTree.assemble owners result.1.2 result.2)

omit platform [PublicWrapperPlatform.CryptoOperations] localOps crypto in
theorem reached_material (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (index : Nat) (self : beaconcrypt_public_wrapper.beacon.Beacon) (owner : Owner source)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state = .InitSent pending prekey oneTime kem)
    (before : RegistrationNativeExperiment.State n KemSK source)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]? = some owner) (phase : owner.phase = .initSent pending scalar)
    (decoded : core.option.Option registration.ResponsePacket)
    (result : (RustM (Option registration.CompletedBeacon) × RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State) × RegistrationNativeExperiment.State n KemSK source)
    (reached : result ∈ support ((simulateQ (RegistrationNativeExperiment.trusted setup checks representation created source)
      ((RegistrationNativeFinishFactor.body setup wire pending decoded owner scalar).run (RegistrationWorldAgreementCompiler.erase before.server.world))).run before)) :
    ∃ returned : AdapterPublicFinishBody.Result,
      AdapterPublicFinishNormalized.output {self with state := .Aborted (RegistrationResponse.abortedState pending)} result.1.1 = .ok returned ∧
      AdapterPublicFinishEndpoint.bytes (.ok returned) = RegistrationNativeFinishTerminalTree.bytes result.1.1 ∧
      (finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).beacons[index]? =
        some (ownerAfter owner (RegistrationResponse.abortedState pending) result.1.1) ∧
      AdapterPublicWrapperState.Beacon view setup.joint (finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).pool
        returned.2 (ownerAfter owner (RegistrationResponse.abortedState pending) result.1.1)
        (finalState index owner (RegistrationResponse.abortedState pending) before.beacons result).server.world.world.1.owners[owner.worldOwner]? := by
  have stayed := RegistrationNativeFinishBodySafety.raw_owners setup checks representation created wire pending decoded owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) before result reached
  have ready : PqxdhRecordLiftWorld.BeaconReady (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2).server.world.world.1 owner.worldOwner := by
    change result.2.server.world.world.1.owners[owner.worldOwner]? = some (.inactive .initSent)
    rw [stayed]
    exact AdapterPublicFinishWorld.initSent_ready view setup.joint before.pool self owner before.server.world.world.1 related pending prekey oneTime kem scalar stored phase
  have material := returned_material view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]? related pending scalar phase index
    (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2) ready result.1.1
  have lookup := selected_owner index owner (RegistrationResponse.abortedState pending) result.1.1
    (RegistrationNativeFinishTerminalTree.assemble before.beacons result.1.2 result.2) selected
  obtain ⟨optional, normal⟩ := interpreted_normal setup checks representation created wire pending decoded owner scalar
    (RegistrationWorldAgreementCompiler.erase before.server.world) before result reached
  unfold finalState
  rw [normal] at material lookup ⊢
  cases optional with
  | none => exact ⟨(.None, {self with state := .Aborted (RegistrationResponse.abortedState pending)}), rfl, rfl, lookup, material⟩
  | some completed => exact ⟨(.Some completed.application, AdapterPublicFinishEndpoint.completedSelf {self with state := .Aborted (RegistrationResponse.abortedState pending)} completed), rfl, rfl, lookup, material⟩


end BeaconcryptCore.Refinement.AdapterPublicFinishLifetime

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.packet_roundtrip' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.packet_roundtrip

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.same_execution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.same_execution

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.accepted_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.accepted_normal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.body_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.body_normal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.interpreted_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.interpreted_normal

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.returned_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.returned_material

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.selected_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.selected_owner

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.reached_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicFinishLifetime.reached_material
