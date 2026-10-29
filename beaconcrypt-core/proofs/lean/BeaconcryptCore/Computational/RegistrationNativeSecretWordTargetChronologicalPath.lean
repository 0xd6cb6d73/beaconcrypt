-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPath

/-! Canonical original APP success supplies an actual selected accept call whose reached provider marker is absent. The historical fact is recorded during the complete original ledger execution and is not inferred from its counter alone. Earlier selected-owner challenge decapsulation remains permitted by the concrete early provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalPath
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeSecretWordTargetCall (Call)
open PqxdhKemIndCca
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler

private theorem raw_success (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (selectedOwner parsed : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : State n KemSK source) (decoded : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some session, last) ∈ support
      ((RegistrationNativeSecretWordTargetLedger.native setup checks wire route sign input inside provider outer
        selectedOwner parsed publicPrekey (.inr (.accept raw))).run first)) :
    (.ok (some session), last) ∈ support
      ((RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        selectedOwner parsed publicPrekey (.inr (.accept packet))).run first) := by
  simp only [RegistrationNativeSecretWordTargetLedger.native, RegistrationNativeRawAdapter.handler,
    QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, decoded, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, reachedState⟩, reached, equal⟩ := supported
  cases actual : reply with
  | fail error | div => simp [actual, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [actual, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      simpa only [actual] using reached

/-- Canonical APP success chooses its call on the supplied same-execution chronological path, retaining its genuinely absent reached getter marker. -/
theorem selected_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (pairs : List (MlKem768PublicKey × KemSK)) (publicKey : MlKem768PublicKey) (challenge : MlKem768Ciphertext)
    (outer : QueryImpl Combined ProbComp) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (before : State n KemSK source) (initialCounter : before.1.parsedAccepts = 0) (initialMarker : before.2.kem.2 = none)
    (observed : RegistrationNativeEvents.Observed Value (State n KemSK source))
    (_supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
        outer target.2.val target.1.val publicPrekey) mode work before))
    (actualPath : RegistrationNativeSecretWordTargetPath.Path
      (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
        (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
          outer target.2.val target.1.val publicPrekey))
      (RegistrationNativeLedger.empty, before) observed.2.1.transcript observed.2)
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire serverKeyId budget target claim observed) :
    ∃ index guess entry session,
      ∃ call : Call (State n KemSK source)
        (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
          (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
          outer target.2.val target.1.val publicPrekey) (fun current => current.1.parsedAccepts) wire target.1.val
        observed.2.1.transcript session.val,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess ∧ call.first.2.kem.2 = none ∧
      ∃ firstLedger lastLedger,
        RegistrationNativeSecretWordTargetPath.Path
          (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
              outer target.2.val target.1.val publicPrekey))
          (RegistrationNativeLedger.empty, before) call.pre (firstLedger, call.first) ∧
        (some session.val, (lastLedger, call.last)) ∈ support
          ((RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
              outer target.2.val target.1.val publicPrekey) (.inl (.inr (.accept call.raw)))).run (firstLedger, call.first)) ∧
        RegistrationNativeSecretWordTargetPath.Path
          (RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds
            (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
              (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
              outer target.2.val target.1.val publicPrekey))
          (lastLedger, call.last) call.post observed.2 := by
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  obtain ⟨pre, raw, packet, post, recorded, counted, decoded, canonical⟩ := accepted
  let typed := RegistrationNativeSecretWordTargetSource.typed (n := n) (source := source)
    setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
  let implementation := RegistrationNativeFullCompiler.handler setup.source.crypto wire serverKeyId bounds typed
  obtain ⟨first, last, priorPath, fullCall, suffix⟩ := RegistrationNativeSecretWordTargetPath.split implementation actualPath pre _ post recorded
  have prefixTrace := RegistrationNativeSecretWordTargetPath.records implementation (fun current => current.1.transcript)
    (fun query current result called => RegistrationNativeSecretWordTargetLedger.step_trace setup checks wire route sign input inside
      provider outer target.2.val target.1.val publicPrekey serverKeyId bounds query current result called) priorPath
  simp only [RegistrationNativeLedger.empty, List.nil_append] at prefixTrace
  have ordinal := RegistrationNativeSecretWordTargetPath.preserves implementation
    (fun current => current.2.1.parsedAccepts = before.1.parsedAccepts + RegistrationNativeEvents.parsedAcceptCount wire current.1.transcript)
    (fun query current result valid called => RegistrationNativeSecretWordTargetLedger.step_counter setup checks wire route sign input inside
      provider outer target.2.val target.1.val publicPrekey serverKeyId bounds query before.1.parsedAccepts current valid result called)
    priorPath (by simp only [RegistrationNativeLedger.empty, RegistrationNativeEvents.parsedAcceptCount, List.filter_nil, List.length_nil, Nat.add_zero])
  have phase := RegistrationNativeSecretWordTargetPath.preserves implementation
    (fun current => RegistrationNativeSecretWordTargetPhase.Holds target.1.val current.2)
    (fun query current result valid called => RegistrationNativeSecretWordTargetPhase.full_step_keeps setup checks wire route sign input inside
      target.2.val pairs publicKey challenge outer target.1.val publicPrekey serverKeyId bounds query current result valid called)
    priorPath (fun _ => initialMarker)
  have selected : first.2.1.parsedAccepts = target.1.val := by
    simpa only [initialCounter, Nat.zero_add, prefixTrace, counted] using ordinal
  have called : (.ok (some session.val), last.2) ∈ support ((typed (.inr (.accept packet))).run first.2) := by
    have rawCalled := fullCall
    rw [RegistrationNativeSecretWordTargetLedger.core_run, support_map] at rawCalled
    obtain ⟨⟨reply, reachedState⟩, reached, equal⟩ := rawCalled
    have success : reply = some session.val := congrArg Prod.fst equal
    have state : reachedState = last.2 := congrArg (fun result => result.2.2) equal
    subst reply
    rw [state] at reached
    exact raw_success setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
      raw packet session.val first.2 last.2 decoded reached
  let call : Call (State n KemSK source)
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey)
      (fun current => current.1.parsedAccepts) wire target.1.val observed.2.1.transcript session.val :=
    ⟨pre, raw, packet, post, first.2, last.2, recorded, counted, decoded, selected, canonical, called⟩
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, phase (by omega), first.1, last.1, priorPath, fullCall, suffix⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalPath
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalPath.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetChronologicalPath.selected_call
