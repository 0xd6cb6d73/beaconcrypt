-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetLedgerCounter
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath
import BeaconcryptCore.Computational.RegistrationNativeLedgerJournal
/-! A canonical original acceptance has its exact supported typed call on the same complete source path. The source state is arbitrary; its parsed-counter equation is a local callback fact, and current source callbacks discharge it internally. All original replies and the complete suffix are retained. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall
open RegistrationNativeSecretWordTargetCall (Call)
open RegistrationNativeSecretWordTargetPath (Path)
variable {S : Type} (crypto : Pqxdh.Crypto) (wire : RegistrationNativeWire.Wire)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT S ProbComp)) (counter : S → Nat)
    (step : ∀ (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : S)
      (result : RegistrationNativeRawAdapter.TypedSpec.Range query × S),
      result ∈ support ((typed query).run before) →
      counter result.2 = counter before + (RegistrationNativeSecretWordTargetCounter.isAccept query).toNat)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
local notation "full" => RegistrationNativeFullCompiler.handler crypto wire serverKeyId bounds typed

private theorem raw_success (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : S) (decoded : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some session,last) ∈ support ((RegistrationNativeRawAdapter.handler wire typed (.inr (.accept raw))).run first)) :
    (.ok (some session),last) ∈ support ((typed (.inr (.accept packet))).run first) := by
  simp only [RegistrationNativeRawAdapter.handler, QueryImpl.apply_compose,
    RegistrationNativeRawAdapter.adapter, decoded, simulateQ_map, simulateQ_spec_query,
    StateT.run_map, support_map] at supported
  obtain ⟨⟨reply,reachedState⟩,reached,equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual,RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
    simp only [actual,RegistrationNativeRawAdapter.resultOption,Prod.mk.injEq] at equal
    obtain ⟨rfl,rfl⟩ := equal
    simpa only [actual] using reached

include step in
/-- The original canonical accept supplies its same-run parsed call, original prefix and complete supported suffix. -/
theorem accepted_call (before : S) (initial : counter before = 0)
    (after : RegistrationNativeLedger.State × S)
    (actual : Path full (RegistrationNativeLedger.empty,before) after.1.transcript after)
    (session parsed : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire after.1.transcript session parsed) :
    ∃ call : Call S typed counter wire parsed after.1.transcript session,
      ∃ first last : RegistrationNativeLedger.State × S,
        call.first = first.2 ∧ call.last = last.2 ∧
        Path full (RegistrationNativeLedger.empty,before) call.pre first ∧
        (some session,last) ∈ support ((full (.inl (.inr (.accept call.raw)))).run first) ∧
        Path full last call.post after := by
  obtain ⟨pre,raw,packet,post,recorded,counted,decoded,canonical⟩ := accepted
  obtain ⟨first,last,prior,called,suffix⟩ := RegistrationNativeSecretWordTargetPath.split full actual pre _ post recorded
  have prefixTrace := RegistrationNativeSecretWordTargetPath.records full (fun current => current.1.transcript)
    (fun query current next reached => RegistrationNativeLedgerJournal.handler_records _ crypto
      (RegistrationNativeWire.ledgerCodec wire) serverKeyId bounds query current next reached) prior
  simp only [RegistrationNativeLedger.empty,List.nil_append] at prefixTrace
  have ordinal := RegistrationNativeSecretWordTargetPath.preserves full
    (fun current => counter current.2 = RegistrationNativeEvents.parsedAcceptCount wire current.1.transcript)
    (fun query current next valid reached => by
      simpa only [Nat.zero_add] using RegistrationNativeRegistrationTargetLedgerCounter.step_counter
        crypto wire typed counter step serverKeyId bounds query 0 current (by simpa only [Nat.zero_add] using valid) next reached)
    prior (by simpa only [RegistrationNativeLedger.empty,RegistrationNativeEvents.parsedAcceptCount,List.filter_nil,List.length_nil] using initial)
  have selected : counter first.2 = parsed := by rw [prefixTrace,counted] at ordinal; exact ordinal
  have typedCall : (.ok (some session),last.2) ∈ support ((typed (.inr (.accept packet))).run first.2) := by
    rw [RegistrationNativeRegistrationTargetLedgerCounter.core_run, support_map] at called
    obtain ⟨⟨reply,current⟩,reached,equal⟩ := called
    have success : reply = some session := congrArg Prod.fst equal
    have state : current = last.2 := congrArg (fun result => result.2.2) equal
    subst reply
    rw [state] at reached
    exact raw_success wire typed raw packet session first.2 last.2 decoded reached
  let call : Call S typed counter wire parsed after.1.transcript session :=
    ⟨pre,raw,packet,post,first.2,last.2,recorded,counted,decoded,selected,canonical,typedCall⟩
  exact ⟨call,first,last,rfl,rfl,prior,called,suffix⟩

end BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall.accepted_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRegistrationTargetAcceptedCall.accepted_call
