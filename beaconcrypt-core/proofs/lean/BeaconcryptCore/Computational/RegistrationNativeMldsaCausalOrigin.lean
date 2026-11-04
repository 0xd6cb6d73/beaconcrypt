-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaPrefixReceipts
import BeaconcryptCore.Computational.RegistrationNativeMldsaTypedOrigin
import BeaconcryptCore.Computational.RegistrationNativeCanonicalReceipt
import BeaconcryptCore.Computational.RegistrationNativeParsedTargetActual

/-! The exact canonical public acceptance prefix supplies a same-run native source callback and its cached prior unsigned signing receipts. Protected-key staged origin is therefore judged at acceptance, before every later callback or signing attempt. This is causal unsigned issuance, not successful prior wire publication or completed partner installation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeInterface (Entry ModeSpec)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Mode FreshBounds)
open RegistrationNativeEvents (Observed)
open RegistrationNativeMldsaEuf (PublicKey)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

structure Call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (transcript : List Entry) (parsed session : Nat) where
  before : List Entry
  raw : Pqxdh.Bytes
  packet : registration.InitPacket
  after : List Entry
  first : State n KemSK source
  last : State n KemSK source
  transcript_eq : transcript = before ++ (Entry.mk (.inl (.inr (.accept raw))) (some session)) :: after
  count : RegistrationNativeEvents.parsedAcceptCount wire before = parsed
  read : RegistrationNativeWire.readInit wire raw = some packet
  canonical : PqxdhDeploymentTranscript.acceptOf (transcript.map Entry.erase) session = some raw
  counter : first.parsedAccepts = parsed
  cached_before : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject first)
  cached_after : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject last)
  success : (.ok (some session), last) ∈ support
    ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.accept packet))).run first)

private theorem raw_success (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (raw : Pqxdh.Bytes) (packet : registration.InitPacket) (session : Nat)
    (first last : State n KemSK source) (read : RegistrationNativeWire.readInit wire raw = some packet)
    (supported : (some session, last) ∈ support
      ((RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential (.inr (.accept raw))).run first)) :
    (.ok (some session), last) ∈ support
      ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential (.inr (.accept packet))).run first) := by
  simp only [RegistrationNativeParsedCounterLedger.native, RegistrationNativeRawAdapter.handler,
    QueryImpl.apply_compose, RegistrationNativeRawAdapter.adapter, read, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨⟨reply, state⟩, reached, equal⟩ := supported
  cases outcome : reply with
  | fail error | div => simp [outcome, RegistrationNativeRawAdapter.resultOption] at equal
  | ok reply =>
      simp only [outcome, RegistrationNativeRawAdapter.resultOption, Prod.mk.injEq] at equal
      obtain ⟨rfl, rfl⟩ := equal
      simpa only [outcome] using reached

/-- Every canonical successful public acceptance from actual startup has its original native cut and cached chronological history from that prefix. -/
theorem initialized_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created
      source initial.credential bounds mode work initial.state)) (parsed session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire observed.2.1.transcript session parsed) :
    Nonempty (Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript parsed session) := by
  obtain ⟨before, raw, packet, after, same, counted, decoded, canonical⟩ := accepted
  have receipts := (RegistrationNativeMldsaPrefixReceipts.run_receipts setup checks wire route representation initial.created
    initial.credential bounds mode work initial.state
    (RegistrationNativeMldsaInvariant.start setup ensureInit identityIndex serverKeyId initial startup) observed supported).2.2
  obtain ⟨first, last, counter, cachedFirst, cachedLast, reached⟩ := receipts before
    ⟨.inl (.inr (.accept raw)), some session⟩ after same
  have zero := RegistrationNativeParsedTargetActual.start_counter setup source ensureInit identityIndex serverKeyId initial startup
  have ordinal : first.parsedAccepts = parsed := by simpa only [zero, Nat.zero_add, counted] using counter
  exact ⟨⟨before, raw, packet, after, first, last, same, counted, decoded, canonical, ordinal, cachedFirst, cachedLast,
    raw_success setup checks wire route representation initial.created initial.credential raw packet session first last decoded reached⟩⟩

/-- The permitted public first-accept scanner selects exactly such a source cut; it never consults a private origin predicate. -/
theorem public_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (observed : Observed Value (State n KemSK source))
    (supported : observed ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created
      source initial.credential bounds mode work initial.state)) (parsed session : Nat) (raw : Pqxdh.Bytes)
    (found : RegistrationNativePublicObservation.firstAccept wire session
      (observed.2.1.transcript.map RegistrationNativeLedgerHiding.view) = some (parsed, raw))
    (decodable : (RegistrationNativeWire.readInit wire raw).isSome) :
    ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential observed.2.1.transcript parsed session,
      call.raw = raw := by
  obtain ⟨call⟩ := initialized_call setup checks wire route representation ensureInit identityIndex serverKeyId initial startup bounds mode work observed
    supported parsed session (RegistrationNativeCanonicalReceipt.first_receipt wire session parsed observed.2.1.transcript raw found decodable)
  have first := (RegistrationNativePublicObservation.first_acceptOf wire session observed.2.1.transcript).symm.trans
    (congrArg (Option.map Prod.snd) found)
  exact ⟨call, Option.some.inj (call.canonical.symm.trans first)⟩

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (transcript : List Entry) (parsed session : Nat)

/-- The successful native prefix gives its accepted protected-key trial, and either earlier unsigned issuance or an executable ordinary candidate/shared-cache collision at the same cut. -/
theorem staged (call : Call (n := n) setup checks wire route representation created credential transcript parsed session)
    (publicKey : PublicKey) (matching : call.packet.mldsa_public_key = publicKey) :
    MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash call.last.server.world.world.1.primitive.2) source.verify
      (RegistrationAuthenticationNative.trial true call.first.server.pin call.packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes call.packet.mldsa_public_key)
          (RegistrationNativeMldsaShared.nativeProject call.first))) ∧
    (MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true call.first.server.pin call.packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes call.packet.mldsa_public_key)
        (RegistrationNativeMldsaShared.nativeProject call.first))) ∨
      (∃ forgery, RegistrationNativeMldsaTrialObserver.observe source.verify publicKey (.inr (.accept call.packet))
        call.first (.ok (some session)) call.last = some forgery) ∨ CacheHasCollision call.last.server.world.world.1.primitive.2) := by
  refine ⟨RegistrationNativeInitFinal.typed_accepted setup checks wire route representation created credential call.packet
    call.first call.last session call.success true rfl, ?_⟩
  classical
  by_cases issued : MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true call.first.server.pin call.packet
      (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes call.packet.mldsa_public_key)
        (RegistrationNativeMldsaShared.nativeProject call.first)))
  · exact Or.inl issued
  · exact Or.inr (RegistrationNativeMldsaTypedOrigin.accept setup checks wire route representation created credential
      publicKey call.packet call.first call.last session call.success matching call.cached_before issued)

end BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.initialized_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.initialized_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.public_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.public_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.staged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin.staged
