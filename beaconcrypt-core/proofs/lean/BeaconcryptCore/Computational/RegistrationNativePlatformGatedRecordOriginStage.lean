-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingLedger
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginPublicationNative
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage
open PqxdhRecordLiftInterface (Environment WorldSpec)
open PqxdhRecordLiftProtocol (ServiceSpec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode ctxInterpreter)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Spec Entry)
open PqxdhServerAuthExperiment (Setup Codec)
open CborRawRecordFlat (NativeState)
open RegistrationNativePlatformGatedRecordFlat (fold native)
open PqxdhRecordFactsOriginPublicationNative (NonSending)
variable {n : Nat} {I KemSK Reader Response E Failure S A : Type} {base : OracleSpec I}
attribute [local irreducible] ctxInterpreter CborRawRecordOriginService.native

private theorem fold_pure (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (value : A) :
    fold (E := E) service codec route (pure value) = pure value := by
  funext before
  unfold fold
  change RegistrationNativePlatformGatedRecordFlat.join <$>
    CborRawRecordOriginFlatten.interpret service codec route (pure (value, before.1.1.1)) before.1.1.2 before.1.2 before.2 =
      pure (value, before)
  rw [CborRawRecordOriginFlatten.interpret_pure, map_pure]
  rfl

/-- A non-send request has no terminal allocation gate, so its complete actual private and platform execution is unchanged. -/
theorem native_nonSend (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (env : Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (query : Spec.Domain)
    (nonsending : NonSending query) :
    native service env reserve codec route query = CborRawRecordOriginService.native service env codec route query := by
  rw [RegistrationNativePlatformGatedRecordFlat.native_split]
  have same : ∀ reply, RegistrationNativePlatformGatedRecordInterface.post (n := n) reserve query reply = pure reply := by
    rcases query with coin | command
    · intro reply; rfl
    · cases command
      case serverSend keyId plaintext => exact False.elim nonsending
      case beaconSend owner plaintext => exact False.elim nonsending
      all_goals intro reply; rfl
  simp only [same, fold_pure, bind_pure]

/-- Every successful actual receive already matches its installed opposite-direction seal dictionary before the callback; failed public sends need not have published those seals. -/
theorem received_before (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (query : Spec.Domain) (before : NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.1.2)
    (result : Spec.Range query × NativeState n E)
    (supported : result ∈ support ((native (ctxInterpreter modes replace setup codec) env reserve codec route query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨.inl query, result.1⟩ : Entry).received = some (receiver, raw, .Some opened)) :
    ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
      PqxdhRecordFactsOriginAccepted.Accepted codec before.1.2 before.2 handle raw opened := by
  have nonsending : NonSending query := by
    rcases query with coin | command
    · trivial
    · cases command <;> simp_all only [NonSending, Entry.received, reduceCtorEq]
  rw [native_nonSend _ codec route env reserve query nonsending] at supported
  have projected : (result.1, CborRawRecordOriginService.project result.2) ∈ support
      ((CborRawRecordOriginService.original (ctxInterpreter modes replace setup codec) env codec route query).run
        (CborRawRecordOriginService.project before)) := by
    rw [← CborRawRecordOriginService.nonrecord_project _ env codec route query before ?_, support_map]
    · exact ⟨result, supported, rfl⟩
    · rcases query with coin | command
      · simp [PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]
      · cases command <;> simp_all [NonSending, PqxdhRecordLiftBudget.NativeRecord, PqxdhDeploymentCompileBudget.commandKind]
  exact PqxdhRecordFactsOriginPublicationNative.native_received_before modes ideal replace setup codec route readback env query
    (CborRawRecordOriginService.project before) safe _ projected receiver raw opened received

/-- Every literal full-ledger receive consults the dictionary at its own actual pre-callback state, including when earlier sends were refused. -/
theorem full_received_before (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : Environment n E) (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure))
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (query : PqxdhDeploymentInterface.FullSpec.Domain)
    (before : PqxdhDeploymentSecrecy.Ledger × NativeState n E) (safe : PqxdhRecordLiftProtocolHistory.Safe before.2.1.2)
    (result : PqxdhDeploymentInterface.FullSpec.Range query × (PqxdhDeploymentSecrecy.Ledger × NativeState n E))
    (supported : result ∈ support ((RegistrationNativePlatformGatedRecordFreshCoupling.fullImpl modes replace setup codec route env reserve serverKid bounds query).run before))
    (receiver : PqxdhDeploymentInterface.Receiver) (raw : Pqxdh.Bytes) (opened : RawCtxWholeOwner.Decrypted)
    (received : (⟨query, result.1⟩ : Entry).received = some (receiver, raw, .Some opened)) :
    ∃ handle, PqxdhRecordLiftIdeal.receivingHandle route receiver raw = some handle ∧
      PqxdhRecordFactsOriginAccepted.Accepted codec before.2.1.2 before.2.2 handle raw opened := by
  rcases query with forwarded | secrecy
  · change result ∈ support ((fun inner => (inner.1.1, (inner.1.2, inner.2))) <$>
      (simulateQ (RegistrationNativePlatformGatedRecordFreshCoupling.nativeImpl modes replace setup codec route env reserve)
        ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto codec serverKid bounds (.inl forwarded)).run before.1)).run before.2) at supported
    rw [support_map] at supported
    obtain ⟨inner, called, rfl⟩ := supported
    rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query,
      StateT.run_map, support_map] at called
    obtain ⟨actual, reached, rfl⟩ := called
    exact received_before modes ideal replace setup codec route readback env reserve forwarded before.2 safe actual reached receiver raw opened received
  · cases secrecy <;> simp [Entry.received] at received

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.native_nonSend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.native_nonSend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.received_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.received_before

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.full_received_before' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordOriginStage.full_received_before
