-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonical
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual
import BeaconcryptCore.Computational.RegistrationNativeKemTargetTrace
import BeaconcryptCore.Computational.RegistrationNativeKemRosterAlignmentRun

/-! The canonical original accepted bytes supply an actual successful SDK call and its reached getter-zero source context. Their source-verified PQ key is the genuinely generated pair at the same derived owner/KEM creation coordinate. No second capacity guess or same-session packet assumption enters this receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeWire (Wire)
open RegistrationNativeEvents (Observed)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeParsedTargetActual (Call)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativeKemParsedRouting.source
  RegistrationNativeKemParsedRouting.handler

private theorem raw_success (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : State n KemSK source) (read : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some session, last) ∈ support
      ((RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential
        (.inr (.accept raw))).run first)) :
    (.ok (some session), last) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential
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

/-- Actual generated startup and the original full ledger supply the canonical successful SDK call, retaining its original session and first accepted bytes. -/
theorem initialized_call (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire initial.created.server.server.metadata.sender budget target claim observed) :
    ∃ index guess entry session,
      ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript target.1.val session.val,
      claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        initial.created.server.server.metadata.sender budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess ∧ PqxdhDeploymentTranscript.acceptOf observed.2.1.ledger.transcript session.val = some call.raw := by
  obtain ⟨index, guess, entry, session, claimed, fresh, designated, accepted, guessed⟩ := winning
  obtain ⟨pre, raw, packet, post, trace, count, read, first⟩ := accepted
  have receipts := (RegistrationNativeParsedCounterReceipts.run_receipts setup checks wire route representation
    initial.created initial.credential bounds mode work initial.state observed supported).2
  obtain ⟨before, after, counter, reached⟩ := receipts pre ⟨.inl (.inr (.accept raw)), some session.val⟩ post trace
  have zero := RegistrationNativeParsedTargetActual.start_counter setup source ensureInit identityIndex serverKeyId initial started
  have selected : before.parsedAccepts = target.1.val := by simpa only [zero, Nat.zero_add, count] using counter
  have success := raw_success setup checks wire route representation initial.created initial.credential raw packet session.val before after read reached
  let call : Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript target.1.val session.val :=
    ⟨pre, raw, packet, post, before, after, trace, count, read, selected, success,
      RegistrationNativeParsedTargetCut.selected_pending setup checks wire route representation initial.created initial.credential
        packet target.1.val session.val before after selected success⟩
  have projected := RegistrationNativeFullCompiler.ledger_projection setup.source.crypto wire initial.created.server.server.metadata.sender bounds
    (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) mode work initial.state observed supported
  exact ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, by simpa only [projected] using first⟩

/-- Canonical broad native success has its actual SDK call and genuine generated KEM pair at the same single owner/creation target coordinate. -/
theorem initialized_born_call (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (budget : Budget)
    (target : Fin budget.accept × Fin budget.capacity) (claim : Value → Option (Nat × Pqxdh.Bytes))
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential bounds mode work initial.state))
    (winning : RegistrationNativeParsedTargetCanonical.CEAppAt setup.source.crypto wire initial.created.server.server.metadata.sender budget target claim observed) :
    ∃ index guess entry session,
      ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript target.1.val session.val,
      ∃ owner keys pair, claim observed.1 = some (index, guess) ∧ observed.2.1.ledger.fresh[index]? = some entry ∧
      PqxdhDeploymentTranscript.designateIn setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
        initial.created.server.server.metadata.sender budget observed.2.1.ledger.transcript entry.handle = some (session, target.2) ∧
      entry.message = guess ∧ observed.2.2.beacons[target.2.val]? = some owner ∧ owner.kemHandle = target.2.val ∧
      observed.2.2.pool.keys[target.2.val]? = some pair ∧
      pair ∈ support (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) ∧
      PqxdhDeploymentTranscript.acceptedKeys setup.source.crypto (RegistrationRootInput.candidate call.packet) = some keys ∧
      keys.2.pqKey = pair.1 := by
  obtain ⟨index, guess, entry, session, call, claimed, fresh, designated, guessed, first⟩ :=
    initialized_call setup checks wire route representation source ensureInit identityIndex serverKeyId initial started bounds mode work budget target claim observed supported winning
  obtain ⟨owner, raw, packet, keys, pair, found, privateAt, generated, _publicKey, accepted, parsed, verified, matched⟩ :=
    RegistrationNativeKemTargetTrace.designated_born setup checks wire route representation source ensureInit identityIndex serverKeyId
      initial started readback bounds mode work observed supported budget entry.handle (session, target.2) designated
  have rawEq := Option.some.inj (accepted.symm.trans first)
  subst raw
  have packetEq := Option.some.inj (parsed.symm.trans call.read)
  subst packet
  have aligned := RegistrationNativeKemRosterAlignmentRun.initialized_run setup checks wire route representation source ensureInit identityIndex
    serverKeyId initial started bounds mode work observed supported
  have handle := aligned.2 target.2.val owner found
  rw [handle] at privateAt
  exact ⟨index, guess, entry, session, call, owner, keys, pair, claimed, fresh, designated, guessed,
    found, handle, privateAt, generated, verified, matched⟩

end BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual.initialized_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual.initialized_call
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual.initialized_born_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeParsedTargetCanonicalActual.initialized_born_call
