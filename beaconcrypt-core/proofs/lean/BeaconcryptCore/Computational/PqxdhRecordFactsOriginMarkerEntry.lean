-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerNative

/-! Exact accepted-entry source location and selected marker facts. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftFlat (KnownAt)
open PqxdhRecordLiftProtocolHistory (Safe Step)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle Spec Entry)
open PqxdhRecordFactsOriginHandles PqxdhRecordFactsOriginMarkerNative
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Each successful actual received entry has an installed handle, and a selected hidden match has raised the same execution's flag. -/
def EntryFact (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (flag : Bool) (entry : Entry) : Prop :=
  ∀ receiver raw opened handle, entry.received = some (receiver, raw, .Some opened) →
    receivingHandle route receiver raw = some handle →
    (KnownAt control handle ∨ ∃ slot, handleSlot control handle = some slot) ∧
    (handleSlot control handle = some target.slot → target.direction = !handleDirection handle →
      target.position + 1 = opened.sequence.val → flag = true)

/-- Source control growth transports exact received-entry facts by using prior installed-handle provenance and a sticky flag. -/
theorem entry_mono (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (before after : PqxdhRecordLiftProtocol.Control n) (first last : Bool)
    (progress : Step before after) (known : ∀ handle, KnownAt before handle → KnownAt after handle)
    (sticky : first = true → last = true) (entry : Entry) (good : EntryFact target route before first entry) :
    EntryFact target route after last entry := by
  intro receiver raw opened handle received routed
  obtain ⟨located, matched⟩ := good receiver raw opened handle received routed
  exact ⟨PqxdhRecordFactsOriginMarkerLocation.location_mono before after progress known handle located,
    fun slot direction position => sticky (matched
      (PqxdhRecordFactsOriginMarkerLocation.slot_before before after progress known handle located target.slot slot)
      direction position)⟩

/-- Every literal native reply satisfies the selected received-entry facts at its before-command control and complete final flag. -/
theorem native_before (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (safe : Safe before.1.2)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    EntryFact target route before.1.2 result.2.2.2 ⟨.inl query, result.1⟩ := by
  rcases query with coin | command
  · simp [EntryFact, Entry.received]
  · cases command <;> simp only [EntryFact, Entry.received, reduceCtorEq, false_implies, implies_true]
    case serverRaw raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed
      rcases routeValue : route raw with _ | keyId
      · simp only [receivingHandle, routeValue, Option.map_none, reduceCtorEq] at routed
      · simp only [receivingHandle, routeValue, Option.map_some, Option.some.injEq] at routed
        subst handle
        exact ⟨serverRaw_location target modes replace setup codec route env raw keyId routeValue before result supported opened returned,
          fun slot direction position => serverRaw_flag target modes replace setup codec route env raw keyId routeValue
            before safe slot direction result supported opened returned position⟩
    case beaconRaw index raw =>
      simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
      rintro _ _ opened handle rfl rfl returned routed
      simp only [receivingHandle, Option.some.injEq] at routed
      subst handle
      exact ⟨beaconRaw_location target modes replace setup codec route env index raw before result supported opened returned,
        fun slot direction position => beaconRaw_flag target modes replace setup codec route env index raw
          before safe slot direction result supported opened returned position⟩

/-- Every actual native reply supplies the exact received-entry marker fact at its complete final control and flag. -/
theorem native_final (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (query : Spec.Domain) (before : State n E) (safe : Safe before.1.2)
    (result : Spec.Range query × State n E)
    (supported : result ∈ support ((nativeImpl target modes replace setup codec route env query).run before)) :
    EntryFact target route result.2.1.2 result.2.2.2 ⟨.inl query, result.1⟩ :=
  entry_mono target route before.1.2 result.2.1.2 result.2.2.2 result.2.2.2
    (native_step target modes replace setup codec route env query before safe result supported)
    (fun handle known => native_known target modes replace setup codec route env handle query before known result supported)
    id _ (native_before target modes replace setup codec route env query before safe result supported)

/-- Experiment-generated send records contain no receive event and therefore require no selected receive flag. -/
theorem secrecy_entry (target : Label n) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (flag : Bool)
    (query : PqxdhDeploymentInterface.Secrecy) (reply : Option RawCtxSourceSend.Encrypted) :
    EntryFact target route control flag ⟨.inr query, reply⟩ := by
  cases query <;> simp [EntryFact, Entry.received]

end BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.entry_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.entry_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.native_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.native_before

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.native_final

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.secrecy_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordFactsOriginMarkerEntry.secrecy_entry
