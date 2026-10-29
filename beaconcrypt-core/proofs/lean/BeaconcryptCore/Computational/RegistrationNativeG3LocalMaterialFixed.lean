-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion

/-! Fixed-table callback equations retain the current selective key metadata and semantic World. Ordinary callbacks run verbatim; preparation and material demand use the current key state and update only that reached state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3LocalKeys (State)
open RegistrationNativeG3LocalMaterialCompletion (fixed openHandler onKeys)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}

private theorem coins_fixed (table : Slot n → Material) (work : ProbComp Value) :
    simulateQ (RegistrationNativeG3CellEager.fixed table)
      (simulateQ RegistrationNativeG3LocalMaterialService.coins work) = work := by
  rw [← QueryImpl.simulateQ_compose]
  have same : RegistrationNativeG3CellEager.fixed table ∘ₛ RegistrationNativeG3LocalMaterialService.coins = QueryImpl.id' unifSpec := by
    funext query
    simp only [QueryImpl.compose, RegistrationNativeG3LocalMaterialService.coins, simulateQ_spec_query,
      RegistrationNativeG3CellEager.fixed, QueryImpl.id', QueryImpl.liftTarget_apply, QueryImpl.id_apply]
  rw [same, simulateQ_id']

/-- Every ordinary fixed-table callback is exactly the original actual callback on the same full current state. -/
theorem fixed_ordinary (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : (RegistrationNativePublicFrontend.Spec n KemSK).Domain)
    (ordinary : RegistrationNativeG3LocalMaterialFrame.Ordinary (KemSK := KemSK) query) :
    fixed table setup codec route wire sign seed scalar candidate provider query =
      RegistrationNativeG3LocalKeys.actual setup codec route wire sign seed scalar candidate provider query := by
  apply StateT.ext
  intro before
  rcases query with (message | (message | common) | kem) | record
  · exact ordinary.elim
  · exact ordinary.elim
  all_goals
    simp only [fixed, QueryImpl.mapStateTBase, openHandler, StateT.run]
    change simulateQ (RegistrationNativeG3CellEager.fixed table)
      (simulateQ RegistrationNativeG3LocalMaterialService.coins _) = _
    exact coins_fixed table _

/-- Preparation runs on the current key metadata while retaining the complete current World and private frame. -/
theorem fixed_prepare (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n KemSK ProviderState) :
    (fixed table setup codec route wire sign seed scalar candidate provider (.inl (.inl message))).run before =
      (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$>
        simulateQ (RegistrationNativeG3CellEager.fixed table)
          ((RegistrationNativeG3LocalMaterialService.prepare
            (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar) message).run
              (RegistrationNativeG3LocalKeys.getKeys before.1)) := by
  simp only [fixed, QueryImpl.mapStateTBase, openHandler, onKeys, StateT.run, simulateQ_map]
  rfl

/-- Material demand uses the fixed slot oracle with the same current allocator, known108 cache and full reached private state. -/
theorem fixed_demand (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (message : RegistrationNativeRelatedFamily.Message) (before : State n KemSK ProviderState) :
    (fixed table setup codec route wire sign seed scalar candidate provider (.inl (.inr (.inl (.inl message))))).run before =
      (fun result => (result.1, (RegistrationNativeG3LocalKeys.putKeys before.1 result.2, before.2))) <$>
        simulateQ (RegistrationNativeG3CellEager.fixed table)
          ((RegistrationNativeG3LocalMaterialService.demand setup.source
            (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
            (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate message).run
              (RegistrationNativeG3LocalKeys.getKeys before.1)) := by
  simp only [fixed, QueryImpl.mapStateTBase, openHandler, onKeys, StateT.run, simulateQ_map]
  rfl

end BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_demand' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialFixed.fixed_demand
