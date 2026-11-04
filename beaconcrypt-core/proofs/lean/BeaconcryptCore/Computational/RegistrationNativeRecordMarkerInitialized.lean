-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordServiceInitialized
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace

/-! The literal native initialized original ledger retains the selected receive marker jointly with decoded raw metadata. This uses the actual sticky-marker interpreter, rather than postulating an event simulation after dropping its flag. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftProtocol (Control)
open PqxdhDeploymentInterface (Entry FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordOriginReceipt (Receipt)
open PqxdhRecordFactsOriginMarkerNative (service)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}

/-- Native transcript restoration preserves the exact selected marker and decoded record-metadata receipts. -/
theorem strip_receipts (target : Label n) (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (control : Control n) (flag : Bool) (transcript : List Entry)
    (good : ∀ entry ∈ transcript, Receipt target read route control flag entry) :
    ∀ entry ∈ RegistrationNativeEntropyTrace.strip transcript, Receipt target read route control flag entry := by
  intro entry member
  have receives (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
      (returned : entry.received = some (receiver, raw, .Some opened)) :
      ∃ original ∈ transcript, original.received = some (receiver, raw, .Some opened) := by
    apply List.mem_filterMap.mp
    rw [← RegistrationNativeEntropyTrace.projection_strip Entry.received (fun _ _ _ => rfl) transcript]
    exact List.mem_filterMap.mpr ⟨entry, member, returned⟩
  constructor
  · intro receiver raw opened handle returned routed
    obtain ⟨original, originalMember, originalReturn⟩ := receives receiver raw opened returned
    exact (good original originalMember).1 receiver raw opened handle originalReturn routed
  · intro receiver raw opened handle returned routed
    obtain ⟨original, originalMember, originalReturn⟩ := receives receiver raw opened returned
    exact (good original originalMember).2 receiver raw opened handle originalReturn routed

/-- The actual initialized native ledger derives every selected-marker receipt from arbitrary reached cursor/control/cache and analysis-flag state. -/
theorem receipts (target : Label n) (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : RegistrationNativeEntropyInterface.Environment n E) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control) (secret : CtxPrivate n) (flag : Bool)
    (result : RegistrationNativeRecordServiceInitialized.Result n E (CtxPrivate n × Bool) Value)
    (supported : result ∈ support (RegistrationNativeRecordServiceInitialized.run (service target modes replace setup codec)
      env setup.source.crypto codec route serverKid bounds mode work created initial shell control (secret, flag))) :
    ∀ born ∈ result.1.1, ∀ entry ∈ born.2.1.2.ledger.transcript,
      Receipt target codec.frameRead route result.1.2 result.2.2 entry := by
  rw [← RegistrationNativeRecordServiceInitialized.run_transport, support_map] at supported
  obtain ⟨old, oldSupported, rfl⟩ := supported
  simp only [RegistrationNativeRecordServiceInitialized.oldRun, support_map] at oldSupported
  obtain ⟨final, finalSupported, rfl⟩ := oldSupported
  have complete := CborRawRecordOriginReceiptLedger.full_program_invariant target modes replace setup codec route
    (RegistrationNativeEntropyPort.environment env) serverKid bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)) _
    (CborRawRecordOriginReceiptLedger.empty_invariant target codec.frameRead route _ safe) final finalSupported
  intro born member
  have selected : born = (PqxdhRegistrationJointServerBirth.encode created,
      ((final.1, RegistrationNativeEntropyRestore.ledger final.2.1), final.2.2.1.1.1.2)) := by
    symm
    simpa only [RegistrationNativeRecordServiceInitialized.project, RegistrationNativeEntropyProgram.outcome,
      RegistrationNativeEntropyExecution.result, Prod.map, id_eq, Option.map_some, Option.mem_some_iff] using member
  subst born
  rw [RegistrationNativeEntropyRestore.ledger_transcript]
  exact strip_receipts target codec.frameRead route _ _ _ complete.2

end BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized.strip_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized.strip_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized.receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordMarkerInitialized.receipts
