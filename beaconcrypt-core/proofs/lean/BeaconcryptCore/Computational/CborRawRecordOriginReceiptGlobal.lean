-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginReceiptLedger
import BeaconcryptCore.Computational.CborRawRecordOriginStartup
import BeaconcryptCore.Computational.CborRawRecordOriginObservation

/-! Initialization discharges the selected-marker and exact-metadata invariants for the complete actual raw cursor ledger. The concrete source prefix, same private flag and full optional replies remain in this run. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal
open PqxdhRecordLiftInterface PqxdhRecordLiftIdeal
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Handle FreshBounds Mode ModeSpec asModeO)
open PqxdhRecordFactsOriginHandles
open PqxdhRecordFactsOriginMarkerNative (service)
open PqxdhRecordFactsOriginMetadataNative (Metadata EntryFact)
open CborRawRecordOriginReceipt (Receipt)
open CborRawRecordOriginReceiptLedger (full_program_invariant empty_invariant)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- The actual initialized raw program derives this same-execution receive receipt. -/
theorem program_entryFacts (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript,
      Receipt target codec.frameRead route result.1.2 result.2.2 entry := by
  rw [CborRawRecordOriginFlatten.program_flat, mem_support_bind_iff] at supported
  obtain ⟨born, bornSupported, continued⟩ := supported
  have bornSafe := CborRawRecordOriginStartup.startup_safe (service target modes replace setup codec) env codec route initial born bornSupported
  cases bornEq : born.1.1.1 with
  | none =>
      simp only [bornEq] at continued
      obtain rfl := (mem_support_pure_iff _ _).mp continued
      simp
  | some start =>
      rcases start with ⟨created, start⟩
      simp only [bornEq] at continued
      rw [mem_support_bind_iff] at continued
      obtain ⟨installed, installSupported, continued⟩ := continued
      have installedSafe := CborRawRecordOriginStartup.install_safe (service target modes replace setup codec) codec route created born.1.1.2 born.1.2 bornSafe born.2 installed installSupported
      rw [support_map] at continued
      obtain ⟨final, finalSupported, rfl⟩ := continued
      have complete := full_program_invariant target modes replace setup codec route env serverKid bounds
        (asModeO mode adversary) _ (empty_invariant target codec.frameRead route _ installedSafe) final finalSupported
      intro value member
      have equal := Option.some.inj member
      subst value
      exact complete.2


/-- The actual initialized raw program derives this same-execution receive receipt. -/
theorem program_received_flag (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n × Bool)
    (result : Client n E X × (CtxPrivate n × Bool))
    (supported : result ∈ support ((simulateQ (service target modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, ∀ receiver raw opened handle,
      entry.received = some (receiver, raw, .Some opened) → receivingHandle route receiver raw = some handle →
      handleSlot result.1.2 handle = some target.slot → target.direction = !handleDirection handle →
      target.position + 1 = opened.sequence.val → result.2.2 = true := by
  intro value present entry recorded receiver raw opened handle received routed slot direction position
  exact ((program_entryFacts target modes replace setup codec route env serverKid bounds mode adversary initial result supported
    value present entry recorded).1 receiver raw opened handle received routed).2 slot direction position


/-- The actual initialized raw program derives this same-execution receive receipt. -/
theorem erased_entryFacts (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, EntryFact codec.frameRead route result.1.2 entry := by
  rw [← PqxdhRecordFactsOriginMuteAdaptive.complete_erase target (RawCtxUniversalDecoder.decoder codec.frameRead)
    (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec) _ (initial, false), support_map] at supported
  obtain ⟨marked, reached, rfl⟩ := supported
  intro value member entry recorded
  exact (program_entryFacts target modes replace setup codec route env serverKid bounds mode adversary
    (initial, false) marked reached value member entry recorded).2


/-- The actual initialized raw program derives this same-execution receive receipt. -/
theorem erased_received_metadata (target : Label n) (modes : Label n → KeyMode)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) (initial : CtxPrivate n)
    (result : Client n E X × CtxPrivate n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordFactsPrivateCacheWorld.erased modes replace setup codec)
      (CborRawRecordOriginProgram.program env setup.source.crypto codec route serverKid bounds mode adversary)).run initial)) :
    ∀ value ∈ result.1.1, ∀ entry ∈ value.2.1.2.transcript, ∀ receiver raw opened handle slot,
      entry.received = some (receiver, raw, .Some opened) → receivingHandle route receiver raw = some handle →
      handleSlot result.1.2 handle = some slot → Metadata codec.frameRead raw opened := by
  intro value present entry recorded receiver raw opened handle slot received routed hidden
  rcases erased_entryFacts target modes replace setup codec route env serverKid bounds mode adversary initial result supported
    value present entry recorded receiver raw opened handle received routed with known | metadata
  · have absent := PqxdhRecordFactsOriginAccepted.known_no_slot result.1.2 handle known
    rw [absent] at hidden
    cases hidden
  · exact metadata


end BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.program_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.program_entryFacts
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.program_received_flag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.program_received_flag
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.erased_entryFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.erased_entryFacts
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.erased_received_metadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginReceiptGlobal.erased_received_metadata
