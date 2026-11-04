-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordBindingLedger
import BeaconcryptCore.Computational.RegistrationNativeEntropyInitialized

/-! The actual native original ledger has record acceptance/publication evidence after arbitrary reached startup effects in the shared CTX cache. Entropy-port restoration removes only public ML creation metadata and HMAC tags, so both directions of record traffic keep their literal record observations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordLedger
open PqxdhRecordFactsBindingLedger (LedgerEvidence)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Entry FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}

private theorem records_strip (transcript : List Entry) :
    (RegistrationNativeEntropyTrace.strip transcript).filterMap Entry.received = transcript.filterMap Entry.received ∧
    (RegistrationNativeEntropyTrace.strip transcript).filterMap Entry.published = transcript.filterMap Entry.published :=
  ⟨RegistrationNativeEntropyTrace.projection_strip Entry.received (fun _ _ _ => rfl) transcript,
    RegistrationNativeEntropyTrace.projection_strip Entry.published (fun _ _ _ => rfl) transcript⟩

/-- Removing only native transport metadata preserves every exact record witness in both directions. -/
theorem strip_evidence (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (control : PqxdhRecordLiftProtocol.Control n) (secret : CtxPrivate n) (transcript : List Entry)
    (good : LedgerEvidence codec route control secret transcript) :
    LedgerEvidence codec route control secret (RegistrationNativeEntropyTrace.strip transcript) := by
  have receives (entry : Entry) (member : entry ∈ RegistrationNativeEntropyTrace.strip transcript)
      (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
      (returned : entry.received = some (receiver, raw, .Some opened)) :
      ∃ original ∈ transcript, original.received = some (receiver, raw, .Some opened) := by
    apply List.mem_filterMap.mp
    rw [← (records_strip transcript).1]
    exact List.mem_filterMap.mpr ⟨entry, member, returned⟩
  have publishes (entry : Entry) (member : entry ∈ RegistrationNativeEntropyTrace.strip transcript)
      (handle : PqxdhDeploymentInterface.Handle) (encrypted : RawCtxSourceSend.Encrypted)
      (returned : entry.published = some (handle, encrypted)) :
      ∃ original ∈ transcript, original.published = some (handle, encrypted) := by
    apply List.mem_filterMap.mp
    rw [← (records_strip transcript).2]
    exact List.mem_filterMap.mpr ⟨entry, member, returned⟩
  constructor
  · intro entry member receiver raw opened handle returned routed
    obtain ⟨original, originalMember, originalReturn⟩ := receives entry member receiver raw opened returned
    exact good.accepted original originalMember receiver raw opened handle originalReturn routed
  · intro entry member handle encrypted returned
    obtain ⟨original, originalMember, originalReturn⟩ := publishes entry member handle encrypted returned
    exact good.published original originalMember handle encrypted originalReturn
  · intro entry member receiver raw opened handle returned routed known
    obtain ⟨original, originalMember, originalReturn⟩ := receives entry member receiver raw opened returned
    exact good.knownReceived original originalMember receiver raw opened handle originalReturn routed known
  · intro entry member handle encrypted returned known
    obtain ⟨original, originalMember, originalReturn⟩ := publishes entry member handle encrypted returned
    exact good.knownPublished original originalMember handle encrypted originalReturn known

/-- The original native ledger derives its full same-execution record evidence at every supported initialized execution, retaining the reached cursor/control/cache. -/
theorem initialized (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : RegistrationNativeEntropyInterface.Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (secret : CtxPrivate n) (result : RegistrationNativeEntropyRun.Result n E Value)
    (supported : result ∈ support (RegistrationNativeEntropyInitialized.run modes replace setup codec route env serverKid bounds mode work
      created initial shell control secret)) :
    ∀ born ∈ result.1.1, LedgerEvidence codec route result.1.2 result.2 born.2.1.2.ledger.transcript := by
  rw [← RegistrationNativeEntropyInitialized.run_transport, support_map] at supported
  obtain ⟨old, oldSupported, rfl⟩ := supported
  simp only [CborRawRecordEntropyInitial.run, support_map] at oldSupported
  obtain ⟨final, finalSupported, rfl⟩ := oldSupported
  have complete := CborRawRecordBindingLedger.full_program modes ideal replace setup codec route readback
    (RegistrationNativeEntropyPort.environment env) serverKid bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)) _
    (CborRawRecordBindingLedger.empty_invariant codec route _ safe) final finalSupported
  intro born member
  have selected : born = (PqxdhRegistrationJointServerBirth.encode created,
      ((final.1, RegistrationNativeEntropyRestore.ledger final.2.1), final.2.2.1.1.1.2)) := by
    symm
    simpa only [RegistrationNativeEntropyRun.project, RegistrationNativeEntropyProgram.outcome,
      RegistrationNativeEntropyExecution.result, Prod.map, id_eq, Option.map_some, Option.mem_some_iff] using member
  subst born
  rw [RegistrationNativeEntropyRestore.ledger_transcript]
  exact strip_evidence codec route _ _ _ (CborRawRecordBindingLedger.evidence codec route _ complete)

end BeaconcryptCore.Computational.RegistrationNativeRecordLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordLedger.strip_evidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordLedger.strip_evidence

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordLedger.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordLedger.initialized
