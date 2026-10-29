-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeIdentityMainState

/-! Whole opaque-identity record operations recover actual original native owner lookup and full record admission. The private identity table affects only source owner realization; routing continues to use the literal public World owner handle. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeIdentityMainRecord
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeWire (Wire ledgerCodec)
open RegistrationNativeIdentityMain (State)
open RegistrationNativeIdentityMainSource (interpret project)
open PqxdhDynamicIdentityPool (SourceState)
variable {n : Nat} {ι KemSK : Type} {base : OracleSpec ι}
variable {mlSource : RegistrationNativeMldsa.Source}

/-- Every actual record command keeps full native lookup, refusal, consumed-kernel and final-state behavior. -/
theorem record_source (setup : Setup base KemSK) (wire : Wire) (route : RawCtxServerRouting.SenderDecoder)
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State n KemSK mlSource × SourceState) :
    Prod.map id project <$>
      (interpret setup.joint (RegistrationNativeIdentityMain.record setup wire route query)).run before =
      (RegistrationNativeExperiment.record setup wire route query mlSource).run (project before) := by
  cases query with
  | inl query =>
      exact RegistrationNativeIdentityMainState.world_source setup.joint _ before
  | inr query =>
      rcases query with ⟨index, query⟩
      cases query with
      | inl plaintext =>
          unfold RegistrationNativeIdentityMain.record
          rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
            RegistrationNativeIdentityMainState.get_source, pure_bind]
          cases found : before.1.beacons[index]? with
          | none =>
              have law := RegistrationNativeIdentityMainState.pure_source setup.joint
                (none : (PqxdhRecordLiftInterface.RecordSpec .O).Range (.inr (index, .inl plaintext))) before
              simpa only [RegistrationNativeExperiment.record, StateT.run, project,
                RegistrationNativeIdentityRealization.owners, List.getElem?_map, found, Option.map_none] using law
          | some selected =>
              have law := RegistrationNativeIdentityMainState.world_source setup.joint
                (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
                  (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before
              simpa only [RegistrationNativeExperiment.record, StateT.run, project,
                RegistrationNativeIdentityRealization.owners, List.getElem?_map, found, Option.map_some,
                RegistrationNativeIdentityRealization.owner, RegistrationNativeIdentityFrontend.restore] using law
      | inr raw =>
          unfold RegistrationNativeIdentityMain.record
          rw [RegistrationNativeIdentityMainOrdinary.interpret_bind, StateT.run_bind,
            RegistrationNativeIdentityMainState.get_source, pure_bind]
          cases found : before.1.beacons[index]? with
          | none =>
              have law := RegistrationNativeIdentityMainState.pure_source setup.joint
                (core.option.Option.None : (PqxdhRecordLiftInterface.RecordSpec .O).Range (.inr (index, .inr raw))) before
              simpa only [RegistrationNativeExperiment.record, StateT.run, project,
                RegistrationNativeIdentityRealization.owners, List.getElem?_map, found, Option.map_none] using law
          | some selected =>
              have law := RegistrationNativeIdentityMainState.world_source setup.joint
                (CborRecordWorldSimulation.guarded setup (ledgerCodec wire) route
                  (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before
              simpa only [RegistrationNativeExperiment.record, StateT.run, project,
                RegistrationNativeIdentityRealization.owners, List.getElem?_map, found, Option.map_some,
                RegistrationNativeIdentityRealization.owner, RegistrationNativeIdentityFrontend.restore] using law

end BeaconcryptCore.Computational.RegistrationNativeIdentityMainRecord

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeIdentityMainRecord.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeIdentityMainRecord.record_source
