-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedLocalSource

/-! The exact finite Common source diagram extends through every adaptive publication/environment program. Fixed seed materialization is a literal query translation on that same Common interface, preserving both private receipts and the full semantic World. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
open RegistrationNativeG3AuditedWorld (Seeds)
open RegistrationNativeG3MaterializedState (Core View view restore)
open RegistrationNativeG3MaterializedLocalCommon (project)
open RegistrationNativePairedServerService (Common)
variable {n : Nat} {ι KemSK ProviderState Reader Response Value : Type} {base : OracleSpec ι}
variable (table : Slot n → Material) (setup : Setup base KemSK) (codec : Codec Reader Response)
  (route : RawCtxServerRouting.SenderDecoder) (wire : RegistrationNativeWire.Wire)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

def liftCommon : QueryImpl (Common n) (OracleComp (RegistrationNativePublicFrontend.Spec n KemSK)) := fun query =>
  (RegistrationNativePublicFrontend.Spec n KemSK).query (.inl (.inr (.inl (.inr query))))

noncomputable def actual : QueryImpl (Common n) (StateT (View n KemSK ProviderState) ProbComp) := fun query before =>
  Prod.map id view <$>
    (simulateQ (RegistrationNativeG3LocalMaterialCompletion.fixed table setup codec route wire sign seed scalar candidate provider)
      (liftCommon query)).run (restore before)

noncomputable def translate (full : Bool) (seeds : Seeds n) : QueryImpl (Common n) (OracleComp (Common n))
  | .inr (.inr (.installServer keyId binding (.hidden slot))) => if full then
      (Common n).query (.inr (.inr (.installServer keyId binding (.hidden slot))))
    else (Common n).query (.inr (.inr (.installServer keyId binding (.known (PqxdhRecordLiftWorld.kernel .server (seeds slot))))))
  | .inr (.inr (.installBeacon owner shell (.hidden slot))) => if full then
      (Common n).query (.inr (.inr (.installBeacon owner shell (.hidden slot))))
    else (Common n).query (.inr (.inr (.installBeacon owner shell (.known (PqxdhRecordLiftWorld.kernel .beacon (seeds slot))))))
  | query => (Common n).query query

/-- Each actual Common callback has the literal finite source diagram after the same bilateral accounting view. -/
theorem query_source (query : (Common n).Domain) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (RegistrationNativeG3MaterializedFrontend.common (RegistrationNativeG3Common.handler setup.source wire.frameWrite sign) query).run before =
      (actual table setup codec route wire sign seed scalar candidate provider query).run (project before) := by
  cases query with
  | inl publication =>
      simpa only [actual, liftCommon, simulateQ_spec_query, StateT.run] using
        RegistrationNativeG3MaterializedLocalCommon.publication table setup codec route wire sign seed scalar candidate provider publication before
  | inr effect =>
      simpa only [actual, liftCommon, simulateQ_spec_query, StateT.run] using
        RegistrationNativeG3MaterializedLocalCommon.effect table setup codec route wire sign seed scalar candidate provider effect before

/-- The concrete source diagram retains every adaptive Common continuation and the full reached receipt/World state. -/
theorem program_source (work : OracleComp (Common n) Value) (before : View n KemSK ProviderState) :
    Prod.map id project <$>
      (simulateQ (RegistrationNativeG3MaterializedFrontend.common
        (RegistrationNativeG3Common.handler setup.source wire.frameWrite sign)) work).run before =
      (simulateQ (actual table setup codec route wire sign seed scalar candidate provider) work).run (project before) :=
  OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ project
    (query_source table setup codec route wire sign seed scalar candidate provider) work before

/-- The materialized Common translation is exactly the restriction of the concrete global callback translation. -/
theorem translation_lift (full : Bool) (seeds : Seeds n) :
    RegistrationNativeG3MaterializedLocal.translate (KemSK := KemSK) full seeds ∘ₛ liftCommon =
      liftCommon ∘ₛ translate full seeds := by
  funext query
  rcases query with publication | effect
  · rfl
  · rcases effect with coin | capability
    · rfl
    · cases capability <;> try rfl
      case installServer keyId binding tag => cases tag <;> cases full <;> rfl
      case installBeacon owner shell tag => cases tag <;> cases full <;> rfl
end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.translation_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedCommonDiagram.translation_lift
