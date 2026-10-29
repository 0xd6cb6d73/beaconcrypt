-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetReceipts
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical

/-! A canonical original APP target in the concrete Word execution supplies its actual successful typed accept call and exact parsed preincrement ordinal. The original session, raw accepted bytes, full private source states, fresh entry and designation remain explicit. No real SDK collector, unchanged-bundle case, target mark or guessed key alignment is substituted. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
open RegistrationNativeSecretWordTargetSource (State)
open RegistrationNativeEvents (Observed)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

structure Call (NativeState : Type)
    (typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT NativeState ProbComp))
    (counter : NativeState → Nat) (wire : RegistrationNativeWire.Wire) (parsed : Nat)
    (transcript : List RegistrationNativeInterface.Entry) (session : Nat) where
  pre : List RegistrationNativeInterface.Entry
  raw : Pqxdh.Bytes
  packet : registration.InitPacket
  post : List RegistrationNativeInterface.Entry
  first : NativeState
  last : NativeState
  recorded : transcript = pre ++ ⟨.inl (.inr (.accept raw)), some session⟩ :: post
  counted : RegistrationNativeEvents.parsedAcceptCount wire pre = parsed
  decoded : RegistrationNativeWire.readInit wire raw = some packet
  selected : counter first = parsed
  canonical : PqxdhDeploymentTranscript.acceptOf (transcript.map RegistrationNativeInterface.Entry.erase) session = some raw
  reached : (.ok (some session), last) ∈ support ((typed (.inr (.accept packet))).run first)

attribute [local irreducible] RegistrationNativeSecretWordTargetSource.typed
  RegistrationNativeSecretWordTargetSource.implementation RegistrationNativeSecretWordInterpreter.handler

private theorem raw_success (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
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

/-- The literal canonical APP target has its actual successful Word source call at the same sole parsed-attempt coordinate. -/
theorem selected_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (before : State n KemSK source) (initialCounter : before.1.parsedAccepts = 0)
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
        target.2.val target.1.val publicPrekey) mode work before))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire serverKeyId budget target claim observed) :
    ∃ index guess entry session,
      ∃ _call : Call (State n KemSK source)
        (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
          target.2.val target.1.val publicPrekey) (fun current => current.1.parsedAccepts) wire target.1.val
        observed.2.1.transcript session.val,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        serverKeyId budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  obtain ⟨pre, raw, packet, post, recorded, counted, decoded, canonical⟩ := accepted
  have receipts := (RegistrationNativeSecretWordTargetReceipts.run_receipts setup checks wire route sign input inside provider outer
    target.2.val target.1.val publicPrekey serverKeyId bounds mode work before observed supported).2
  obtain ⟨first, last, ordinal, called⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session.val⟩ post recorded
  have selected : first.1.parsedAccepts = target.1.val := by simpa only [initialCounter, Nat.zero_add, counted] using ordinal
  have typed := raw_success setup checks wire route sign input inside provider outer target.2.val target.1.val publicPrekey
    raw packet session.val first last decoded called
  let call : Call (State n KemSK source)
        (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer
          target.2.val target.1.val publicPrekey) (fun current => current.1.parsedAccepts) wire target.1.val
        observed.2.1.transcript session.val :=
    ⟨pre, raw, packet, post, first, last, recorded, counted, decoded, selected, canonical, typed⟩
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed⟩

end BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall.selected_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetCall.selected_call
