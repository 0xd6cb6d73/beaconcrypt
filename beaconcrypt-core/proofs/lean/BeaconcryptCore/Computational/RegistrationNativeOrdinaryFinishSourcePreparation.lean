-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceCallbacks
import BeaconcryptCore.Computational.RegistrationNativePublicOwners
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativePreparation

/-! An ordinary owner's native preparation supplies its two prekey-DH coordinates to the private literal source. The reference returned by that source is the translated message itself, and the memo stores the root under that returned name. Reconstruction therefore follows the actual later material demand without identifying two differently keyed memos. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointIdentity (IdentitySeed PeerEncoding)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativePublicSourceEffects (Private)
open RegistrationNativePublicSourceCallbacks (implementation)
open RegistrationBeaconReferenceNativePreparation (restored)
variable {ι KemSK : Type} {base : OracleSpec ι} {n : Nat}

/-- Materialization preserves the literal optional native root, including either failed DH coordinate. -/
theorem materialize_value (setup : Setup base KemSK) (seed : IdentitySeed)
    (localScalar selectedScalar : ScalarBytes) (message : Message) (peer : PeerEncoding)
    (pinned : message.third = .pinned peer) :
    (RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar message).bind
      (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed selectedScalar) =
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed localScalar message := by
  simp only [RegistrationNativeLocalMessage.materialize, pinned,
    RegistrationNativeSourceRoot.value, RegistrationNativeRelatedFamily.input,
    RegistrationNativeRelatedFamily.firstValue, RegistrationNativeRelatedFamily.thirdValue]
  cases first : setup.dh.dh localScalar message.staticPeer <;>
    cases third : setup.dh.dh localScalar peer <;>
    simp [RegistrationNativeRelatedFamily.address]

/-- Preparation retains every private coordinate and records its root under the actual translated return value. -/
theorem prepare_run (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes) (message : Message)
    (before : Private n KemSK) :
    (simulateQ (implementation setup wire route sign seed selectedScalar)
      (RegistrationNativePublicOwners.ordinary setup localScalar (.inl message))).run before =
      match RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar message with
      | none => pure (none, before)
      | some translated =>
          let root := RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed selectedScalar translated
          pure (root.map (fun _ => translated),
            { before with extra := (Function.update before.extra.1 translated root, before.extra.2) }) := by
  cases translated : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar message <;>
    simp only [RegistrationNativePublicOwners.ordinary, translated, simulateQ_pure,
      simulateQ_spec_query, implementation,
      RegistrationNativeKemReferenceEffects.implementation, RegistrationNativeKemReferenceWorld.handler,
      RegistrationServerOpenReferenceSourceStage.callbacks,
      RegistrationServerOpenReferenceSourceStage.prepare, RegistrationNativePublicSourceCallbacks.remember,
      StateT.run]
  rfl

/-- The actual Beacon root client reconstructs its ordinary scalar's native effect from the freshly returned translated reference. -/
theorem client_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before : Private n KemSK) :
    (fun result => (restored result.2.extra.1 authenticated result.1,
      (result.2.world, result.2.pool, result.2.extra.2))) <$>
      (simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
          (simulateQ RegistrationBeaconReferenceCompiler.prepare
            (RegistrationBeaconReferenceRoot.client authenticated pending)))).run before =
      (fun result => (result, (before.world, before.pool, before.extra.2))) <$>
        simulateQ (RegistrationNativeSourceRoot.handler setup.source setup.hmac setup.joint setup.dh seed localScalar)
          (RegistrationNativeBeaconRootSource.client authenticated pending) := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare, StateT.run_map]
  rw [prepare_run]
  have value := materialize_value setup seed localScalar selectedScalar
    (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) _ rfl
  cases translatedEq : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar
      (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) with
  | none =>
      simp only [translatedEq, Option.bind_none] at value
      simp only [RegistrationNativeBeaconRootSource.client, RegistrationNativeBeaconRootSource.root,
        simulateQ_map, simulateQ_spec_query, RegistrationNativeSourceRoot.handler, ← value,
        map_pure, Functor.map_map, restored]
      rfl
  | some translated =>
      simp only [translatedEq, Option.bind_some] at value
      simp only [RegistrationNativeBeaconRootSource.client, RegistrationNativeBeaconRootSource.root,
        simulateQ_map, simulateQ_spec_query, RegistrationNativeSourceRoot.handler, ← value,
        Functor.map_map]
      cases rootEq : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed selectedScalar translated <;>
        simp only [map_pure, Option.map_none, Option.map_some, restored, Function.update_self]
      all_goals rfl

/-- A successful returned capability names exactly a root stored by this preparation, independently of the old memo. -/
theorem client_prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : IdentitySeed) (selectedScalar localScalar : ScalarBytes)
    (authenticated : registration.AuthenticatedResponse)
    (pending : PqxdhPhase2DhMetadata.Prepared registration.AuthenticatedResponse)
    (before after : Private n KemSK) (ready : RegistrationBeaconReferenceRoot.Ready)
    (supported : (.ok (some ready), after) ∈ support
      ((simulateQ (implementation setup wire route sign seed selectedScalar)
        (simulateQ (RegistrationNativePublicOwners.ordinary setup localScalar)
          (simulateQ RegistrationBeaconReferenceCompiler.prepare
            (RegistrationBeaconReferenceRoot.client authenticated pending)))).run before)) :
    ∃ root, after.extra.1 ready.reference = some root := by
  simp only [RegistrationBeaconReferenceRoot.client, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, RegistrationBeaconReferenceCompiler.prepare, StateT.run_map] at supported
  rw [prepare_run] at supported
  cases translatedEq : RegistrationNativeLocalMessage.materialize setup.joint setup.dh localScalar
      (RegistrationNativeRelatedRoot.pinnedBeaconMessage pending.collected) with
  | none => simp only [translatedEq, map_pure, mem_support_pure_iff] at supported; cases supported
  | some translated =>
      simp only [translatedEq, map_pure, mem_support_pure_iff] at supported
      cases rootEq : RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed selectedScalar translated with
      | none => simp only [rootEq, Option.map_none] at supported; cases supported
      | some root =>
          simp only [rootEq, Option.map_some] at supported
          cases supported
          exact ⟨root, Function.update_self _ _ _⟩

end BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.materialize_value' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.materialize_value
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.prepare_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.prepare_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.client_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.client_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.client_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeOrdinaryFinishSourcePreparation.client_prepared
