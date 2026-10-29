-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedState
import BeaconcryptCore.Computational.RegistrationNativeG3LocalMaterialCompletion

/-! These concrete callback interpretations retain the actual fixed-material selective handler. The known interpretation reconstructs demanded hidden108 outputs; the thin materialized interpretation replaces only hidden installation references by their fixed canonical kernels. Preparation, ordinary publication, routed KEM and actual guarded records keep the same executable callbacks and full private state. The complete typed source comparison is a separate composition theorem. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativePublicFrontend (Spec)
open RegistrationNativeG3MaterializedState (Core View view restore getKeys putKeys)
variable {n : Nat} {ι KemSK ProviderState Reader Response : Type} {base : OracleSpec ι}

noncomputable def translate (full : Bool) (seeds : Seeds n) : QueryImpl (Spec n KemSK) (OracleComp (Spec n KemSK))
  | .inl (.inr (.inl (.inl message))) => if full then
      Option.map (RegistrationNativeG3MaterializedFrontend.materialize seeds) <$>
        (Spec n KemSK).query (.inl (.inr (.inl (.inl message))))
    else (Spec n KemSK).query (.inl (.inr (.inl (.inl message))))
  | .inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot))))))) => if full then
      (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding (.hidden slot))))))))
    else (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr (.inr (.installServer keyId binding
      (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot))))))))))
  | .inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot))))))) => if full then
      (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell (.hidden slot))))))))
    else (Spec n KemSK).query (.inl (.inr (.inl (.inr (.inr (.inr (.installBeacon owner shell
      (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot))))))))))
  | query => (Spec n KemSK).query query

noncomputable def handler (full : Bool) (table : Slot n → Material) (seeds : Seeds n)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :=
  RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider ∘ₛ
    translate full seeds

noncomputable def service (table : Slot n → Material)
    (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    QueryImpl (RegistrationNativeG3MaterializedFrontend.ServiceSpec n) (StateT (Core n KemSK ProviderState) ProbComp) := fun message before =>
  (fun result => (result.1, putKeys before result.2)) <$>
    simulateQ (RegistrationNativeG3CellEager.fixed table)
      ((RegistrationNativeG3LocalMaterialService.demand setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar)))
        candidate message).run (getKeys before))

noncomputable def fallback (table : Slot n → Material)
    (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT (View n KemSK ProviderState) ProbComp) := fun query before =>
  Prod.map id view <$>
    (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
      (RegistrationNativePublicFrontend.liftLocal false query)).run (restore before)

/-- Actual root preparation is identical in the two concrete materialized interpretations. -/
theorem prepare (full : Bool) (seeds : Seeds n) (message : RegistrationNativeRelatedFamily.Message) :
    translate (KemSK := KemSK) full seeds (.inl (.inl message)) =
      (Spec n KemSK).query (.inl (.inl message)) := rfl

/-- Every actual ongoing record request retains its literal guarded callback. -/
theorem record (full : Bool) (seeds : Seeds n) (query : PqxdhRecordLiftInterface.RecordQuery) :
    translate (KemSK := KemSK) full seeds (.inr query) = (Spec n KemSK).query (.inr query) := rfl

/-- Every routed KEM operation retains its complete actual callback, including its private provider state. -/
theorem routed (full : Bool) (seeds : Seeds n) (query : (RegistrationNativePublicFrontend.RoutedKem KemSK).Domain) :
    translate (KemSK := KemSK) full seeds (.inl (.inr (.inr query))) = (Spec n KemSK).query (.inl (.inr (.inr query))) := rfl
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.prepare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.prepare
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.record
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocal.routed
