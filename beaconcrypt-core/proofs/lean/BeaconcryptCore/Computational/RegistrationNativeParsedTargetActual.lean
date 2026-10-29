-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedCounterReceipts
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetEvents
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCut

/-! A broad native target obtained from actual generated startup has an actual successful SDK call at that parsed ordinal and a reached literal KEM getter-zero context. The original session remains existential, with its original verified-key designation. There is no exact-bundle, incoming ML membership, no-prior-finish or assumed source-simulation condition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeWire (Wire)
open RegistrationNativeInterface (Entry ModeSpec Respects)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Mode Budget FreshBounds)
open RegistrationNativeEvents (Observed)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {mlSource : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativeKemParsedRouting.source
  RegistrationNativeKemParsedRouting.handler

set_option maxRecDepth 2048 in
structure Call (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (transcript : List Entry) (parsed session : Nat) where
  before : List Entry
  raw : Pqxdh.Bytes
  packet : registration.InitPacket
  after : List Entry
  first : State n KemSK mlSource
  last : State n KemSK mlSource
  transcript_eq : transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after
  count : RegistrationNativeEvents.parsedAcceptCount wire before = parsed
  read : RegistrationNativeWire.readInit wire raw = some packet
  counter : first.parsedAccepts = parsed
  success : (.ok (some session), last) ∈ support
    ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential
      (.inr (.accept packet))).run first)
  pending : ∃ key next reached, (.pending key next, reached) ∈ support
    ((RegistrationNativeKemCut.scan (RegistrationNativeKemParsedRouting.source setup checks wire route representation created credential)
      (RegistrationNativeKemParsedRouting.handler setup checks wire parsed (.inr (.accept packet))) 0).run
        (RegistrationNativeKemAcceptCompiler.nativeProject first))

/-- Actual generated startup initializes the private parsed counter after every successful native constructor branch. -/
theorem start_counter (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.parsedAccepts = 0 := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _generated, continued⟩ := supported
  cases constructor : constructed.1.1 with
  | none => simp [constructor] at continued
  | some created =>
      simp only [constructor, mem_support_bind_iff] at continued
      obtain ⟨generated, _sampled, continued⟩ := continued
      cases generation : generated.1 with
      | none => simp [generation] at continued
      | some credential =>
          simp only [generation, mem_support_bind_iff] at continued
          obtain ⟨initialized, _native, returned⟩ := continued
          cases native : initialized.1 with
          | fail error | div => simp [native] at returned
          | ok reply => cases reply with
            | none => simp [native] at returned
            | some state =>
                simp only [native, support_pure, Set.mem_singleton_iff, Option.some.injEq] at returned
                cases returned
                rfl

private theorem raw_success (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : State n KemSK mlSource) (read : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some session, last) ∈ support
      ((RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential
        (.inr (.accept raw))).run first)) :
    (.ok (some session), last) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created mlSource credential
        (.inr (.accept packet))).run first) := by
  simp only [RegistrationNativeParsedCounterLedger.native, RegistrationNativeRawAdapter.handler,
    QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, read, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, state⟩, reached, equal⟩ := supported
  cases result : reply with
  | fail error | div => simp [result, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [result, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      simpa only [result] using reached

/-- Every witnessed original accept entry has a derived source prestate and reached selected getter, from the complete original ledger execution. -/
theorem call_of_accept (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : State n KemSK mlSource) (zero : before.parsedAccepts = 0)
    (observed : Observed Value (State n KemSK mlSource))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created
      mlSource credential bounds mode work before)) (parsed session : Nat)
    (accepted : RegistrationNativeParsedTarget.AcceptedAt wire observed.2.1.transcript session parsed) :
    Nonempty (Call (n := n) setup checks wire route representation created credential observed.2.1.transcript parsed session) := by
  obtain ⟨pre, raw, packet, post, trace, count, read⟩ := accepted
  have receipts := (RegistrationNativeParsedCounterReceipts.run_receipts setup checks wire route representation
    created credential bounds mode work before observed supported).2
  obtain ⟨first, last, counter, reached⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session⟩ post trace
  have selected : first.parsedAccepts = parsed := by simpa only [zero, Nat.zero_add, count] using counter
  have success := raw_success setup checks wire route representation created credential raw packet session first last read reached
  exact ⟨⟨pre, raw, packet, post, first, last, trace, count, read, selected, success,
    RegistrationNativeParsedTargetCut.selected_pending setup checks wire route representation created credential
      packet parsed session first last selected success⟩⟩

/-- The broad selected event at actual generated startup supplies its original designation and actual successful native getter-zero witness. -/
theorem initialized_selected (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created
      source initial.credential bounds mode work initial.state))
    (winning : RegistrationNativeParsedTargetEvents.CEAppAt setup.source.crypto wire
      initial.created.server.server.metadata.sender budget target claim observed) :
    ∃ index guess entry session, claim observed.1 = some (index, guess) ∧
      observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        initial.created.server.server.metadata.sender budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess ∧ Nonempty (Call (n := n) setup checks wire route representation initial.created initial.credential
        observed.2.1.transcript target.1.val session.val) := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  exact ⟨index, guess, entry, session, claimed, fresh, designated, guessed,
    call_of_accept setup checks wire route representation initial.created initial.credential bounds mode work initial.state
      (start_counter setup source ensureInit identityIndex serverKeyId initial started) observed supported
      target.1.val session.val accepted⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.start_counter' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.start_counter
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.call_of_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.call_of_accept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.initialized_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual.initialized_selected
