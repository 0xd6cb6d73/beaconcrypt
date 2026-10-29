-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhase
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCertifiedReceipts
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall

/-! Canonical original APP success supplies an actual selected accept call whose reached provider marker is absent. The historical fact is recorded during the complete original ledger execution and is not inferred from its counter alone. Earlier selected-owner challenge decapsulation remains permitted by the concrete early provider. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCall
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

/-- Actual canonical APP success chooses a successful typed call at the same target and its genuinely absent reached getter marker. -/
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
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside
        (RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge)
        outer target.2.val target.1.val publicPrekey) mode work before))
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
      entry.message = guess ∧ call.first.2.kem.2 = none := by
  let provider := RegistrationNativeSecretWordKemEarly.early setup.baseImpl setup.kem target.2.val pairs publicKey challenge
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  obtain ⟨pre, raw, packet, post, recorded, counted, decoded, canonical⟩ := accepted
  have receipts := (RegistrationNativeSecretWordTargetCertifiedReceipts.run_receipts setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId (RegistrationNativeSecretWordTargetPhase.Holds target.1.val) bounds
    (fun query current reached valid called => RegistrationNativeSecretWordTargetPhase.full_step_keeps setup checks wire route sign input inside
      target.2.val pairs publicKey challenge outer target.1.val publicPrekey serverKeyId bounds query current reached valid called)
    mode work before (fun _ => initialMarker) observed supported).2.2
  obtain ⟨first, last, prior, ordinal, called⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session.val⟩ post recorded
  have selected : first.1.parsedAccepts = target.1.val := by simpa only [initialCounter, Nat.zero_add, counted] using ordinal
  have typed := raw_success setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
    raw packet session.val first last decoded called
  let call : Call (State n KemSK source)
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey)
      (fun current => current.1.parsedAccepts) wire target.1.val observed.2.1.transcript session.val :=
    ⟨pre, raw, packet, post, first, last, recorded, counted, decoded, selected, canonical, typed⟩
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, prior (by omega)⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCall
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCall.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCall.selected_call
