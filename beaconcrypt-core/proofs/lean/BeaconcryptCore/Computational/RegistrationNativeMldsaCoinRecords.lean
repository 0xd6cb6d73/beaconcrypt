-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaCoinPrimitives
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldBudget

/-! Actual real record callbacks draw randomness only on shared commitment misses. Fixed HKDF, AEAD and writer work remain their original source bodies and draw no randomness. The syntactic per-record hash cap therefore gives a64-draw ordinary uniform bound for every original raw/send callback, before any source accounting projection. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface (RecordQuery)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}

/-- Actual counted primitive execution retains the original shared-miss draw allowance. -/
theorem primitive (setup : Setup base KemSK) (codec : Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (before : PqxdhRecordLiftWorld.Primitive) :
    ((PqxdhRecordLiftWorld.primitives setup codec query).run before).IsTotalQueryBound
      (64 * if RawCtxMixedOwner.callKind query = .hash then 1 else 0) := by
  simpa only [PqxdhRecordLiftWorld.primitives, StateT.run, bind_pure_comp,
    IsTotalQueryBound, isQueryBound_map_iff] using
    RegistrationNativeMldsaCoinPrimitives.counted _ _
      (PqxdhRecordLiftWorldBudget.primitive_uniform_bound setup codec query before.2) before.1.uniform

/-- The literal record primitive program's hash-class cap controls its whole actual uniform-query tree. -/
theorem program (setup : Setup base KemSK) (codec : Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Value) (qHash : Nat)
    (bounded : work.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) qHash)
    (before : PqxdhRecordLiftWorld.Primitive) :
    ((simulateQ (PqxdhRecordLiftWorld.primitives setup codec) work).run before).IsTotalQueryBound (64 * qHash) := by
  induction work using OracleComp.inductionOn generalizing qHash before with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      apply (isTotalQueryBound_bind (primitive setup codec query before)
        (fun result => ih result.1 _ (bounded.2 result.1) result.2)).mono
      by_cases active : RawCtxMixedOwner.callKind query = .hash
      · have positive := bounded.1.resolve_left (not_not.mpr active)
        simp only [active, ite_true, Nat.mul_one]
        omega
      · simp only [active, ite_false, Nat.mul_zero, Nat.zero_add]
        exact le_rfl

/-- Every actual Server record attempt has at most one shared commitment miss, including absent peers and malformed input. -/
theorem server (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RawCtxServerMixed.SourceSpec.Domain)
    (before : PqxdhRecordLiftWorld.State n) :
    ((PqxdhRecordLiftWorld.serverStep setup codec route query).run before).IsTotalQueryBound 64 := by
  cases present : before.server with
  | none => cases query <;> simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, present,
      IsTotalQueryBound, isQueryBound_pure]
  | some current =>
    simp only [PqxdhRecordLiftWorld.serverStep, StateT.run, present, bind_pure_comp,
      IsTotalQueryBound, isQueryBound_map_iff]
    cases query with
    | inl send =>
      exact program setup codec
        (PqxdhDeploymentNative.logged (MldsaServerRouting.send PqxdhRefinement.absBytes
          (fun _ => current.sender) send.1 send.2 current.records)) 1
        (PqxdhDeploymentCompileBudget.logged_bound _ _ _ []
          (MldsaServerRouting.send_bound PqxdhRefinement.absBytes (fun _ => current.sender)
            send.1 send.2 current.records .hash)) before.primitive
    | inr raw =>
      exact program setup codec
        (PqxdhDeploymentNative.logged (MldsaServerRouting.receive PqxdhRefinement.absBytes
          route codec.frameRead raw current.records)) 1
        (PqxdhDeploymentCompileBudget.logged_bound _ _ _ []
          (MldsaServerRouting.raw_bound PqxdhRefinement.absBytes route codec.frameRead raw current.records .hash)) before.primitive

/-- Actual Beacon record dispatch has the same one-miss cap for every active, inactive and absent owner. -/
theorem beacon (setup : Setup base KemSK) (codec : Codec Reader Response)
    (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain) (before : PqxdhRecordLiftWorld.State n) :
    ((PqxdhRecordLiftWorld.beaconStep setup codec owner query).run before).IsTotalQueryBound 64 := by
  cases found : before.owners[owner]? with
  | none => simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, IsTotalQueryBound, isQueryBound_pure]
  | some phase =>
      simp only [PqxdhRecordLiftWorld.beaconStep, StateT.run, found, bind_pure_comp,
        IsTotalQueryBound, isQueryBound_map_iff]
      apply program setup codec _ 1
      cases query <;> exact PqxdhDeploymentCompileBudget.logged_bound _ _ _ []
        (PqxdhRecordLiftBeacon.handler_bound codec.frameRead _ _ .hash)

/-- The actual public size/cursor filter adds no random query before record execution. -/
theorem guarded (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery) (before : PqxdhRecordLiftWorld.State n) :
    ((CborRecordWorldSimulation.guarded setup codec route (.inr (.inr query))).run before).IsTotalQueryBound 64 := by
  cases refused : CborRecordWorldClient.refusal (n := n) (.inr (.inr query)) (CborRecordWorldCursor.worldShell before) with
  | some reply => simp only [CborRecordWorldSimulation.guarded, StateT.run, refused, IsTotalQueryBound, isQueryBound_pure]
  | none =>
      simp only [CborRecordWorldSimulation.guarded, StateT.run, refused]
      cases query with
      | inl query => cases query <;> exact server setup codec route _ before
      | inr query =>
          rcases query with ⟨owner, query⟩
          cases query <;> exact beacon setup codec owner _ before

/-- The original source owner lookup and native-state lens preserve the full64-draw per-record cap. -/
theorem record {source : RegistrationNativeMldsa.Source} (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : RecordQuery)
    (before : RegistrationNativeExperiment.State n KemSK source) :
    ((RegistrationNativeExperiment.record setup wire route query source).run before).IsTotalQueryBound 64 := by
  cases query with
  | inl query =>
      simpa only [RegistrationNativeExperiment.record, RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
        StateT.run, IsTotalQueryBound, isQueryBound_map_iff] using
        guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inl query) before.server.world.world.1
  | inr query =>
      rcases query with ⟨owner, query⟩
      cases query with
      | inl plaintext =>
        cases found : before.beacons[owner]? with
        | none => simp only [RegistrationNativeExperiment.record, StateT.run, found, IsTotalQueryBound, isQueryBound_pure]
        | some selected =>
          simpa only [RegistrationNativeExperiment.record, StateT.run, found, RegistrationNativeExperiment.world,
            RegistrationNativeExperiment.server, IsTotalQueryBound, isQueryBound_map_iff] using
            guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (selected.worldOwner, .inl plaintext)) before.server.world.world.1
      | inr raw =>
        cases found : before.beacons[owner]? with
        | none => simp only [RegistrationNativeExperiment.record, StateT.run, found, IsTotalQueryBound, isQueryBound_pure]
        | some selected =>
          simpa only [RegistrationNativeExperiment.record, StateT.run, found, RegistrationNativeExperiment.world,
            RegistrationNativeExperiment.server, IsTotalQueryBound, isQueryBound_map_iff] using
            guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (selected.worldOwner, .inr raw)) before.server.world.world.1
end BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.primitive

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.program

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.server

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.beacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.guarded' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.guarded

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCoinRecords.record
