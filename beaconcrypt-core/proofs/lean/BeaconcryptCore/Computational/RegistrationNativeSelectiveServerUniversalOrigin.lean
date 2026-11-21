-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialExecution
import BeaconcryptCore.Computational.RegistrationNativeSelectiveMaterialUniversal

/-! The original native one-use Server controller reaches a hidden installed peer on every selected successful build. Lookup, preflight, occupancy, reservation and all failure paths are consumed from that same actual controller. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationNativeSelectiveMaterialService (Local)
open RegistrationNativeSelectiveMaterialExecution (Result execute pure_source bind_source)
open RegistrationServerMaterialFrontend (State)
open RegistrationServerReferenceRoot (Ready)
variable {n : Nat} {ι KemSK ProviderState Auxiliary Reader Response Secret : Type} {base : OracleSpec ι}
variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
  (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Secret ProbComp)) (codec : Codec Reader Response)
local notation "run" => execute setup wire route sign seed scalar candidate provider service codec

private theorem finish (published : RustM (RegistrationNativePairedServerService.Result Pqxdh.Bytes))
    (before : State) (localState : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n Auxiliary KemSK ProviderState Secret (RegistrationServerMaterialFrontend.Result × State))
    (supported : result ∈ support (run ((RegistrationServerMaterialFrontend.finish published).run before) localState shell world secret))
    (keyId : U64) (bytes : Pqxdh.Bytes) (successful : result.1.1.1.1.1 = .ok (some (keyId, bytes))) :
    ∃ peer, published = .ok (.Ok peer) ∧ peer.key_id = keyId ∧ result.1.2 = world := by
  cases published with
  | fail error | div =>
      simp only [RegistrationServerMaterialFrontend.finish, StateT.run, pure_source, mem_support_pure_iff] at supported
      subst result
      cases successful
  | ok published => cases published with
    | Err previous =>
        simp only [RegistrationServerMaterialFrontend.finish, StateT.run, pure_source, mem_support_pure_iff] at supported
        subst result
        cases successful
    | Ok peer =>
        simp only [RegistrationServerMaterialFrontend.finish, StateT.run, pure_source, mem_support_pure_iff] at supported
        subst result
        simp only [RustM.ok.injEq, Option.some.injEq, Prod.mk.injEq] at successful
        exact ⟨peer, rfl, successful.1, rfl⟩

attribute [local irreducible] peer.begin_completion_lookup RegistrationServerSdkSource.preflight

/-- The actual complete controller installs a hidden origin whenever its same retained reference is selected and publication succeeds. -/
theorem complete (reservePeer : Bool) (ready : Ready) (application : Slice U8) (before : State)
    (localState : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n Auxiliary KemSK ProviderState Secret (RegistrationServerMaterialFrontend.Result × State))
    (supported : result ∈ support (run ((RegistrationServerMaterialFrontend.complete wire reservePeer ready application).run before)
      localState shell world secret)) (keyId : U64) (bytes : Pqxdh.Bytes)
    (successful : result.1.1.1.1.1 = .ok (some (keyId, bytes)))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer keyId) = some slot := by
  unfold RegistrationServerMaterialFrontend.complete at supported
  simp only [StateT.run] at supported
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    cases successful }
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    cases successful }
  split at supported <;> try {
    rw [pure_source, mem_support_pure_iff] at supported
    subst result
    cases successful }
  rw [bind_source, mem_support_bind_iff] at supported
  obtain ⟨occupied, _asked, continued⟩ := supported
  split at continued <;> try {
    rw [pure_source, mem_support_pure_iff] at continued
    subst result
    cases successful }
  rw [bind_source, mem_support_bind_iff] at continued
  obtain ⟨hashed, _hashedSupport, continued⟩ := continued
  cases hashResult : hashed.1.1.1.1 with
  | fail error | div =>
      simp only [hashResult, pure_source, mem_support_pure_iff] at continued
      subst result
      cases successful
  | ok reply => cases reply with
    | Err previous =>
      simp only [hashResult, pure_source, mem_support_pure_iff] at continued
      subst result
      cases successful
    | Ok initial =>
      simp only [hashResult] at continued
      split at continued <;> try {
        rw [pure_source, mem_support_pure_iff] at continued
        subst result
        cases successful }
      rw [bind_source, mem_support_bind_iff] at continued
      obtain ⟨published, admitted, completed⟩ := continued
      obtain ⟨peer, same, key, control⟩ := finish setup wire route sign seed scalar candidate provider service codec
        published.1.1.1.1 before published.1.1.1.2 published.1.1.2 published.1.2 published.2 result completed keyId bytes successful
      have installed := RegistrationNativeSelectiveMaterialUniversal.server setup wire route sign seed scalar candidate provider service codec
        ready.reference selected wire.encodeResponse before.control _ peer
        hashed.1.1.1.2 hashed.1.1.2 hashed.1.2 hashed.2 published admitted same
      rw [control, ← key]
      exact installed

/-- The actual selected one-use build uses its same stored Ready and returns a hidden record origin. -/
theorem build (reservePeer : Bool) (handle : Nat) (application : Option (Slice U8)) (before : State) (ready : Ready)
    (stored : before.sessions[handle]? = some (some ready))
    (localState : Local n Auxiliary KemSK ProviderState) (shell : CborRecordWorldClient.Shell)
    (world : PqxdhRecordLiftProtocol.Control n) (secret : Secret)
    (result : Result n Auxiliary KemSK ProviderState Secret (RegistrationServerMaterialFrontend.Result × State))
    (supported : result ∈ support (run ((RegistrationServerMaterialFrontend.build wire reservePeer handle application).run before)
      localState shell world secret)) (keyId : U64) (bytes : Pqxdh.Bytes)
    (successful : result.1.1.1.1.1 = .ok (some (keyId, bytes)))
    (selected : ∀ realizedBytes, RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar ready.reference = some realizedBytes →
      RegistrationNativeSelectiveHiddenService.selected
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate realizedBytes = true) :
    ∃ slot, PqxdhRecordLiftIdeal.handleSlot result.1.2 (.peer keyId) = some slot := by
  simp only [RegistrationServerMaterialFrontend.build, StateT.run, RegistrationServerMaterialFrontend.take, stored] at supported
  cases application with
  | none =>
      rw [pure_source, mem_support_pure_iff] at supported
      subst result
      cases successful
  | some application =>
      exact complete setup wire route sign seed scalar candidate provider service codec reservePeer ready application
        { before with sessions := before.sessions.set handle none } localState shell world secret result supported keyId bytes successful selected

end BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin.complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin.complete
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveServerUniversalOrigin.build
