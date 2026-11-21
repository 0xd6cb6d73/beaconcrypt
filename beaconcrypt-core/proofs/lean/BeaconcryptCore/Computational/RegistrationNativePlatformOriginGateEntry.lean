-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage
import BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateSource
/-! Same-run attribution of every new hidden seal retains the genuine pre-gate send reply instead of pretending that a public reserve refusal was a failed codec. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry
open CtxRomAuth
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordLiftInterface (Environment)
open PqxdhDeploymentInterface (Spec Entry Handle)
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordFactsOriginPublicationNative (CreatedAt NonSending)
open CborRawRecordFlat (NativeState)
variable {n : Nat} {I KemSK Reader Response E Failure : Type} {base : OracleSpec I}
attribute [local irreducible] ctxInterpreter CborRawRecordOriginService.native RegistrationNativePlatformGatedRecordFlat.fold RegistrationNativePlatformGatedRecordFlat.native

def sendEntry (handle : Handle) (plaintext : Pqxdh.Bytes) (reply : Option RawCtxSourceSend.Encrypted) : Entry :=
  match handle with
  | .peer keyId => ⟨.inl (.inr (.serverSend keyId plaintext)),reply⟩
  | .owner owner => ⟨.inl (.inr (.beaconSend owner plaintext)),reply⟩

/-- An actual guarded send either creates no new hidden seal or has the original source writer's precise frame witness before any public capacity gate. -/
theorem send_entry (modes : Label n → KeyMode) (ideal : ∀ label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (handle : Handle) (plaintext : Pqxdh.Bytes) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Option RawCtxSourceSend.Encrypted × NativeState n E)
    (supported : result ∈ support ((simulateQ (CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route)
      (PqxdhDeploymentSecrecy.send handle plaintext)).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    entry ∈ (before.2.keys label).1.successfulSeals ∨ CreatedAt codec before.1.2 (sendEntry handle plaintext result.1) label entry := by
  have projected : (result.1,CborRawRecordOriginService.project result.2) ∈ support
      (Prod.map id CborRawRecordOriginService.project <$>
        (simulateQ (CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route)
          (PqxdhDeploymentSecrecy.send handle plaintext)).run before) := by
    rw [support_map]
    exact ⟨result,supported,rfl⟩
  rw [CborRawRecordOriginService.send_project] at projected
  cases refused : CborRawRecordFlat.sendRefusal (n := n) handle plaintext before.1.1.2 with
  | some reply =>
    rw [refused,mem_support_pure_iff] at projected
    have privateSame := congrArg (fun result => result.2.2) projected
    exact Or.inl (privateSame ▸ member)
  | none =>
    rw [refused] at projected
    cases handle with
    | peer keyId =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at projected
      exact PqxdhRecordFactsOriginPublicationNative.native_entry modes ideal replace setup codec route readback env
        (.inr (.serverSend keyId plaintext)) (CborRawRecordOriginService.project before) safe
        (result.1,CborRawRecordOriginService.project result.2) projected label entry member
    | owner owner =>
      simp only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] at projected
      exact PqxdhRecordFactsOriginPublicationNative.native_entry modes ideal replace setup codec route readback env
        (.inr (.beaconSend owner plaintext)) (CborRawRecordOriginService.project before) safe
        (result.1,CborRawRecordOriginService.project result.2) projected label entry member

private theorem nonsend_seals (modes : Label n → KeyMode) (ideal : ∀ label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E) (query : Spec.Domain) (nonsend : NonSending query)
    (before : NativeState n E) (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route query).run before)) :
    ∀label,(result.2.2.keys label).1.successfulSeals=(before.2.keys label).1.successfulSeals := by
  have projected : (result.1,CborRawRecordOriginService.project result.2) ∈ support
      ((CborRawRecordOriginService.original (ctxInterpreter modes replace setup codec) env codec route query).run
        (CborRawRecordOriginService.project before)) := by
    rw [← CborRawRecordOriginService.nonrecord_project _ env codec route query before ?_,support_map]
    · exact ⟨result,supported,rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [NonSending,PqxdhRecordLiftBudget.NativeRecord,PqxdhDeploymentCompileBudget.commandKind]
  exact PqxdhRecordFactsOriginPublicationNative.native_nonSend_seals modes ideal replace setup codec route env query nonsend
    (CborRawRecordOriginService.project before) (result.1,CborRawRecordOriginService.project result.2) projected

/-- The current cursor-filtered native callback attributes every new seal to the exact source writer outcome on that same call. -/
theorem native_entry (modes : Label n → KeyMode) (ideal : ∀ label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (query : Spec.Domain) (before : NativeState n E)
    (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    entry ∈ (before.2.keys label).1.successfulSeals ∨ CreatedAt codec before.1.2 ⟨.inl query,result.1⟩ label entry := by
  rcases query with coin | command
  · exact Or.inl ((nonsend_seals modes ideal replace setup codec route env _ (by trivial) before result supported label) ▸ member)
  · cases command
    case serverSend keyId plaintext =>
      exact send_entry modes ideal replace setup codec route readback env (.peer keyId) plaintext before safe result
        (by simpa only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] using supported) label entry member
    case beaconSend owner plaintext =>
      exact send_entry modes ideal replace setup codec route readback env (.owner owner) plaintext before safe result
        (by simpa only [PqxdhDeploymentSecrecy.send,simulateQ_spec_query] using supported) label entry member
    all_goals exact Or.inl ((nonsend_seals modes ideal replace setup codec route env _ (by trivial) before result supported label) ▸ member)

/-- Every actual terminal public reserve keeps the entire hidden-seal dictionary and produced/pending logs, including Err and absent-encoder branches. -/
theorem post_kept (modes : Label n → KeyMode) (replace : Pqxdh.Bytes → Pqxdh.Bytes)
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain) (reply : Spec.Range query)
    (before : NativeState n E) (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
      (RegistrationNativePlatformGatedRecordInterface.post reserve query reply)).run before)) :
    PqxdhRecordFactsOriginAmbient.Kept before.2 result.2.2 := by
  rcases query with coin | command
  · exact RegistrationNativePlatformOriginGateSource.closed_kept modes replace setup codec route (pure reply) before result supported
  · cases command
    case serverSend keyId plaintext =>
      exact RegistrationNativePlatformOriginGateSource.closed_kept modes replace setup codec route
        (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) reply) before result supported
    case beaconSend owner plaintext =>
      exact RegistrationNativePlatformOriginGateSource.closed_kept modes replace setup codec route
        (RegistrationNativePlatformOrdinaryGate.gate reserve (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) reply) before result supported
    all_goals exact RegistrationNativePlatformOriginGateSource.closed_kept modes replace setup codec route (pure reply) before result supported

/-- A new hidden seal in a gated callback carries its genuine earlier encoder reply and same-run reserve execution. A removed publication is never rewritten to a codec failure. -/
theorem gated_entry (modes : Label n → KeyMode) (ideal : ∀ label,modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (before : NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFlat.native (ctxInterpreter modes replace setup codec) env reserve codec route query).run before))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.2.keys label).1.successfulSeals) :
    entry ∈ (before.2.keys label).1.successfulSeals ∨ ∃ original,
      original ∈ support ((CborRawRecordOriginService.native (ctxInterpreter modes replace setup codec) env codec route query).run before) ∧
      result ∈ support ((RegistrationNativePlatformGatedRecordFlat.fold (ctxInterpreter modes replace setup codec) codec route
        (RegistrationNativePlatformGatedRecordInterface.post reserve query original.1)).run original.2) ∧
      CreatedAt codec before.1.2 ⟨.inl query,original.1⟩ label entry := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_split,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨original,called,gated⟩ := supported
  have kept := post_kept modes replace setup codec route reserve query original.1 original.2 result gated
  have originalMember : entry ∈ (original.2.2.keys label).1.successfulSeals := by
    simpa only [kept.keys] using member
  rcases native_entry modes ideal replace setup codec route readback env query before safe original called label entry originalMember with prior | newSeal
  · exact Or.inl prior
  · exact Or.inr ⟨original,called,gated,newSeal⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.send_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.send_entry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.native_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.native_entry
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.post_kept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.post_kept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.gated_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOriginGateEntry.gated_entry
