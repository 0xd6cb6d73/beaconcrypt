-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginSourceProbability
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginNative
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerOwner
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerLocation

/-! The literal native interface with the selected replay marker retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt clientImpl handler_known support_keep_oracle support_run_fst)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec)
open PqxdhRecordFactsOriginHandles
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Complete source native state with one analysis-only sticky flag. -/
abbrev State (n : Nat) (E : Type) := (E × PqxdhRecordLiftProtocol.Control n) × (CtxPrivate n × Bool)

/-- Literal selected-source interpreter; every service reply and private field remain present. -/
noncomputable abbrev service (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :=
  PqxdhRecordFactsOriginMuteAdaptive.marked target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)

/-- Actual compiled native commands over the same service program with only its marker added. -/
noncomputable def nativeImpl (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) : QueryImpl Spec (StateT (State n E) ProbComp) :=
  ((service target modes replace setup codec).mapStateTBase (clientImpl env codec route)).flattenStateT

/-- Exact unflattened source execution, including all native environment and control state. -/
theorem native_run (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (state : State n E) :
    (nativeImpl target modes replace setup codec route env query).run state =
      (fun z => (z.1.1.1, ((z.1.1.2, z.1.2), z.2))) <$> (simulateQ (service target modes replace setup codec)
        ((simulateQ (PqxdhRecordLiftProtocol.handler codec.frameRead route) ((native env query).run state.1.1)).run
          state.1.2)).run state.2 := by
  simp only [nativeImpl, clientImpl, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    simulateQ_map, StateT.run_map, Functor.map_map]

/-- Any complete adaptive service continuation retains a flag that is already raised. -/
theorem service_sticky (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) X)
    (state : CtxPrivate n × Bool) (bad : state.2 = true)
    (result : X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec) client).run state)) :
    result.2.2 = true := by
  exact support_keep_oracle (service target modes replace setup codec) (fun current => current.2 = true)
    (PqxdhRecordFactsOriginMuteAdaptive.marked_sticky target (RawCtxUniversalDecoder.decoder codec.frameRead)
      (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)) client state bad result supported

/-- Complete native execution preserves an already raised source marker. -/
theorem native_sticky (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (bad : before.2.2 = true)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    result.2.2.2 = true := by
  rw [native_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact service_sticky target modes replace setup codec _ before.2 bad inner reached

/-- The marker leaves the actual native source safety and forward control transition intact. -/
theorem native_step (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (safe : Safe before.1.2)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    Step before.1.2 result.2.1.2 := by
  rw [native_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftProtocolHistory.interpreted_schedule (service target modes replace setup codec)
    codec.frameRead route ((native env query).run before.1.1) before.1.2 safe before.2 inner reached

/-- Caller-known handles remain known through the complete marked native source interface. -/
theorem native_known (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (handle : Handle) (query : Spec.Domain) (before : State n E)
    (known : KnownAt before.1.2 handle) (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    KnownAt result.2.1.2 handle := by
  rw [native_run, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact support_keep_oracle (PqxdhRecordLiftProtocol.handler codec.frameRead route) (fun control => KnownAt control handle)
    (handler_known codec.frameRead route handle) _ before.1.2 known inner.1 (support_run_fst _ _ _ inner reached)

/-- Actual successful Server raw delivery raises the selected marker at its before-command hidden slot and returned sequence. -/
theorem serverRaw_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (before : State n E) (safe : Safe before.1.2)
    (slot : handleSlot before.1.2 (.peer keyId) = some target.slot)
    (direction : target.direction = !handleDirection (.peer keyId))
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2.2 = true := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerOwner.serverReceive_flag target modes replace setup codec route
    before.1.2 safe raw keyId routed slot direction before.2 inner reached opened returned position

/-- Actual successful Beacon raw delivery raises the selected marker at its before-command hidden slot and returned sequence. -/
theorem beaconRaw_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (index : Nat) (raw : Pqxdh.Bytes) (before : State n E) (safe : Safe before.1.2)
    (slot : handleSlot before.1.2 (.owner index) = some target.slot)
    (direction : target.direction = !handleDirection (.owner index))
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.beaconRaw index raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened)
    (position : target.position + 1 = opened.sequence.val) : result.2.2.2 = true := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerOwner.beaconReceive_flag target modes replace setup codec
    before.1.2 safe index raw slot direction before.2 inner reached opened returned position

/-- Actual successful Server native receives use an already installed physical handle. -/
theorem serverRaw_location (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (raw : Pqxdh.Bytes) (keyId : Std.U64) (routed : route raw = some keyId)
    (before : State n E) (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.serverRaw raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt before.1.2 (.peer keyId) ∨ ∃ slot, handleSlot before.1.2 (.peer keyId) = some slot := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_serverRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerLocation.server_location codec.frameRead route before.1.2 raw keyId routed
    inner.1 (support_run_fst _ _ _ inner reached) opened returned

/-- Actual successful Beacon native receives use an already established physical owner. -/
theorem beaconRaw_location (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (index : Nat) (raw : Pqxdh.Bytes) (before : State n E)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env (.inr (.beaconRaw index raw))).run before))
    (opened : RawCtxWholeOwner.Decrypted) (returned : result.1 = .Some opened) :
    KnownAt before.1.2 (.owner index) ∨ ∃ slot, handleSlot before.1.2 (.owner index) = some slot := by
  simp only [native_run, PqxdhRecordFactsOriginNative.native_beaconRaw_run, simulateQ_map, StateT.run_map,
    Functor.map_map, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordFactsOriginMarkerLocation.beacon_location codec.frameRead before.1.2 index raw
    inner.1 (support_run_fst _ _ _ inner reached) opened returned

/-- Every adaptive native continuation retains a marker already raised. -/
theorem program_sticky (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E) (bad : before.2.2 = true)
    (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    result.2.2.2 = true :=
  support_keep_oracle (nativeImpl target modes replace setup codec route env) (fun current => current.2.2 = true)
    (fun query state raised => native_sticky target modes replace setup codec route env query state raised)
    client before bad result supported

/-- Every adaptive native continuation preserves the actual control safety and forward provenance. -/
theorem program_step (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E) (safe : Safe before.1.2)
    (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    Step before.1.2 result.2.1.2 := by
  apply support_keep_oracle (nativeImpl target modes replace setup codec route env)
    (fun current => Step before.1.2 current.1.2) _ client before
    (PqxdhRecordLiftProtocolHistory.step_refl before.1.2 safe) result supported
  exact fun query state progress next reached => PqxdhRecordFactsOriginControl.step_trans _ _ _ progress
    (native_step target modes replace setup codec route env query state progress.1 next reached)

/-- Every adaptive native continuation preserves the caller-known classification separately from hidden-slot provenance. -/
theorem program_known (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (client : OracleComp Spec X) (before : State n E)
    (handle : Handle) (known : KnownAt before.1.2 handle) (result : X × State n E)
    (supported : result ∈ support ((simulateQ (nativeImpl target modes replace setup codec route env) client).run before)) :
    KnownAt result.2.1.2 handle :=
  support_keep_oracle (nativeImpl target modes replace setup codec route env) (fun current => KnownAt current.1.2 handle)
    (fun query state present => native_known target modes replace setup codec route env handle query state present)
    client before known result supported

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.service_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.service_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.native_known

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.serverRaw_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.serverRaw_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.beaconRaw_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.beaconRaw_flag

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.serverRaw_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.serverRaw_location

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.beaconRaw_location' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.beaconRaw_location

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_sticky' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_sticky

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative.program_known
