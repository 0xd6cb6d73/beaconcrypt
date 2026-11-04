-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginService
import BeaconcryptCore.Computational.PqxdhRecordFactsBindingKnownLedger

/-! Actual cursor-filtered record replies retain the original accepted/published and shared-cache evidence. Oversized sends stutter with a missing-ciphertext reply before private sealing, and raw receives retain their literal original execution. All statements begin at an arbitrary reached shared cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.CborRawRecordBindingReceipt
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Spec Entry Handle)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginNative (EntryFacts)
open PqxdhRecordFactsBindingNative (KnownEntryFacts)
variable {n : Nat} {ι KemSK Reader Response E : Type} {base : OracleSpec ι}
variable (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
  (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK)
  (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec) (env : Environment n E)

/-- A successful cursor-filtered send has the literal original source path after dropping only its public cursor. -/
theorem send_supported (handle : Handle) (plaintext : Pqxdh.Bytes)
    (before : CborRawRecordFlat.NativeState n E)
    (result : Option RawCtxSourceSend.Encrypted × CborRawRecordFlat.NativeState n E)
    (supported : result ∈ support ((simulateQ (CborRawRecordFlat.nativeImpl modes replace setup codec route env)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (encrypted : RawCtxSourceSend.Encrypted) (returned : result.1 = some encrypted) :
    (result.1, CborRawRecordFlat.project result.2) ∈ support
      ((simulateQ (PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env)
        (PqxdhDeploymentSecrecy.send handle plaintext)).run (CborRawRecordFlat.project before)) := by
  have mapped : (result.1, CborRawRecordOriginService.project result.2) ∈ support
      (Prod.map id CborRawRecordOriginService.project <$>
        (simulateQ (CborRawRecordOriginService.native (PqxdhRecordLiftIdeal.ctxInterpreter modes replace setup codec) env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run before) := by
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [CborRawRecordOriginService.send_project] at mapped
  cases refused : CborRawRecordFlat.sendRefusal (n := n) handle plaintext before.1.1.2 with
  | none => simpa only [refused, CborRawRecordOriginService.original, CborRawRecordOriginService.project, CborRawRecordFlat.project, CborRawRecordFlat.clientProject, PqxdhRecordLiftFlat.nativeImpl] using mapped
  | some reply =>
      simp only [refused, mem_support_pure_iff, Prod.mk.injEq] at mapped
      have missing := CborRawRecordOriginService.refused_none handle plaintext before.1.1.2 reply refused
      rw [returned, missing] at mapped
      cases mapped.1

include ideal readback in
/-- Every actual native reply supplies both endpoint classification and known-key shared-cache evidence. -/
theorem native_final (query : Spec.Domain) (before : CborRawRecordFlat.NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × CborRawRecordFlat.NativeState n E)
    (supported : result ∈ support ((CborRawRecordFlat.nativeImpl modes replace setup codec route env query).run before)) :
    EntryFacts codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ ∧
      KnownEntryFacts codec route result.2.1.2 result.2.2 ⟨.inl query, result.1⟩ := by
  rcases result with ⟨reply, after⟩
  by_cases free : ¬PqxdhRecordLiftBudget.NativeRecord .send query
  · have projected : (reply, CborRawRecordFlat.project after) ∈ support
        ((PqxdhRecordLiftFlat.nativeImpl modes replace setup codec route env query).run (CborRawRecordFlat.project before)) := by
      rw [← CborRawRecordFlat.nativeImpl_project_nonrecord modes replace setup codec route env query before free, support_map]
      exact ⟨(reply, after), supported, rfl⟩
    exact ⟨PqxdhRecordFactsOriginNative.native_entryFacts modes ideal replace setup codec route readback env query
        (CborRawRecordFlat.project before) safe _ projected,
      PqxdhRecordFactsBindingNative.native_knownEntryFacts modes ideal replace setup codec route readback env query
        (CborRawRecordFlat.project before) safe _ projected⟩
  · have sent_case (handle : Handle) (plaintext : Pqxdh.Bytes)
        (reply : Option RawCtxSourceSend.Encrypted) (after : CborRawRecordFlat.NativeState n E)
        (reached : (reply, after) ∈ support ((simulateQ (CborRawRecordFlat.nativeImpl modes replace setup codec route env)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run before)) :
        (∀ encrypted, reply = some encrypted → PqxdhRecordFactsOriginPublished.Published codec after.1.2 after.2 handle encrypted) ∧
        (∀ encrypted, reply = some encrypted → PqxdhRecordLiftFlat.KnownAt after.1.2 handle →
          PqxdhRecordFactsBindingKnown.SharedRecord codec after.2 encrypted.ciphertext) := by
      constructor
      · intro encrypted returned
        exact PqxdhRecordFactsOriginNative.native_send_published modes ideal replace setup codec route readback env handle plaintext
          (CborRawRecordFlat.project before) safe (reply, CborRawRecordFlat.project after)
          (send_supported modes replace setup codec route env handle plaintext before (reply, after) reached encrypted returned) encrypted returned
      · intro encrypted returned known
        exact PqxdhRecordFactsBindingNative.native_send_shared modes ideal replace setup codec route readback env handle plaintext
          (CborRawRecordFlat.project before) safe (reply, CborRawRecordFlat.project after)
          (send_supported modes replace setup codec route env handle plaintext before (reply, after) reached encrypted returned) encrypted returned known
    rcases query with coin | command
    · exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))
    · cases command
      case serverSend keyId plaintext =>
        have facts := sent_case (.peer keyId) plaintext reply after (by simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using supported)
        cases returned : reply with
        | none => simp [EntryFacts, KnownEntryFacts, Entry.published, Entry.received]
        | some encrypted =>
          simpa [EntryFacts, KnownEntryFacts, Entry.published, Entry.received, returned] using
            And.intro (facts.1 encrypted returned) (facts.2 encrypted returned)
      case beaconSend owner plaintext =>
        have facts := sent_case (.owner owner) plaintext reply after (by simpa only [PqxdhDeploymentSecrecy.send, simulateQ_spec_query] using supported)
        cases returned : reply with
        | none => simp [EntryFacts, KnownEntryFacts, Entry.published, Entry.received]
        | some encrypted =>
          simpa [EntryFacts, KnownEntryFacts, Entry.published, Entry.received, returned] using
            And.intro (facts.1 encrypted returned) (facts.2 encrypted returned)
      all_goals exact False.elim (free (by simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]))

end BeaconcryptCore.Computational.CborRawRecordBindingReceipt
/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingReceipt.send_supported' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingReceipt.send_supported

/-- info: 'BeaconcryptCore.Computational.CborRawRecordBindingReceipt.native_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordBindingReceipt.native_final
