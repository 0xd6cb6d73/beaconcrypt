-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStagedSnapshots
import BeaconcryptCore.Computational.RegistrationNativeMldsaCausalOrigin

/-! The finite same-run native snapshot map retains the exact cached signing prefix used by canonical public acceptance. Every selected accepted raw packet at every saved endpoint has its actual successful source cut and causal unsigned-issuance/candidate/collision decomposition. No future signing, final ratchet reconstruction or completed-partner premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin
open RegistrationNativeExperiment (State Initial)
open RegistrationNativeInterface (Entry FullSpec ModeSpec)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Mode FreshBounds)
open RegistrationNativeMldsaCausalOrigin (Call)
open RegistrationNativeMldsaEuf (PublicKey)
open RegistrationNativeStagedSnapshots (Endpoints Snapshots Native)
open PqxdhDeploymentSessionSnapshots (Journal)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.handler

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


private theorem prefix_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : Native (n := n) (KemSK := KemSK) (source := source))
    (valid : RegistrationNativeMldsaPrefixReceipts.Holds
      (RegistrationNativeParsedCounterLedger.native setup checks wire route representation created credential) wire 0 current)
    (parsed session : Nat)
    (accepted : RegistrationNativeParsedTargetCanonical.AcceptedAt wire current.1.transcript session parsed) :
    Nonempty (Call (n := n) setup checks wire route representation created credential current.1.transcript parsed session) := by
  obtain ⟨before, raw, packet, after, same, counted, decoded, canonical⟩ := accepted
  obtain ⟨first, last, counter, cachedFirst, cachedLast, reached⟩ := valid.2.2 before
    ⟨.inl (.inr (.accept raw)), some session⟩ after same
  have ordinal : first.parsedAccepts = parsed := by simpa only [Nat.zero_add, counted] using counter
  exact ⟨⟨before, raw, packet, after, first, last, same, counted, decoded, canonical, ordinal, cachedFirst, cachedLast,
    raw_success setup checks wire route representation created credential raw packet session first last decoded reached⟩⟩

/-- Every saved endpoint of the actual initialized simultaneous native run retains the literal source cut selected by its own public first-accept bytes. -/
theorem captured_call (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) {sessions owners : Nat}
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    (supported : result ∈ support (RegistrationNativeStagedSnapshots.run setup checks wire route representation initial.created
      initial.credential bounds mode work initial.state))
    (endpoint : Endpoints sessions owners) (snapshot : Journal FullSpec × Native (n := n) (KemSK := KemSK) (source := source))
    (saved : result.2.captured endpoint = some snapshot) (parsed session : Nat) (raw : Pqxdh.Bytes)
    (found : RegistrationNativePublicObservation.firstAccept wire session
      (snapshot.2.1.transcript.map RegistrationNativeLedgerHiding.view) = some (parsed, raw))
    (decodable : (RegistrationNativeWire.readInit wire raw).isSome) :
    ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential snapshot.2.1.transcript parsed session,
      call.raw = raw := by
  have histories := RegistrationNativeStagedSnapshots.initialized_histories setup checks wire route representation bounds
    ensureInit identityIndex serverKeyId initial startup mode work result supported
  have valid := histories.2 endpoint snapshot saved
  rw [RegistrationNativeParsedTargetActual.start_counter setup source ensureInit identityIndex serverKeyId initial startup] at valid
  obtain ⟨call⟩ := prefix_call setup checks wire route representation initial.created initial.credential snapshot.2 valid parsed session
    (RegistrationNativeCanonicalReceipt.first_receipt wire session parsed snapshot.2.1.transcript raw found decodable)
  have first := (RegistrationNativePublicObservation.first_acceptOf wire session snapshot.2.1.transcript).symm.trans
    (congrArg (Option.map Prod.snd) found)
  exact ⟨call, Option.some.inj (call.canonical.symm.trans first)⟩

/-- All saved endpoints from that one run use their own causal prior signing prefix for native staged origin. -/
theorem captured_staged (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value) {sessions owners : Nat}
    (result : Value × Snapshots (n := n) (KemSK := KemSK) (source := source) (Endpoints sessions owners))
    (supported : result ∈ support (RegistrationNativeStagedSnapshots.run setup checks wire route representation initial.created
      initial.credential bounds mode work initial.state))
    (endpoint : Endpoints sessions owners) (snapshot : Journal FullSpec × Native (n := n) (KemSK := KemSK) (source := source))
    (saved : result.2.captured endpoint = some snapshot) (parsed session : Nat) (raw : Pqxdh.Bytes)
    (found : RegistrationNativePublicObservation.firstAccept wire session
      (snapshot.2.1.transcript.map RegistrationNativeLedgerHiding.view) = some (parsed, raw))
    (decodable : (RegistrationNativeWire.readInit wire raw).isSome) :
    ∃ call : Call (n := n) setup checks wire route representation initial.created initial.credential snapshot.2.1.transcript parsed session,
      call.raw = raw ∧ ∀ publicKey : PublicKey, call.packet.mldsa_public_key = publicKey →
      MldsaTranscriptAuth.Accepted (MldsaSharedAuthentication.cacheHash call.last.server.world.world.1.primitive.2) source.verify
        (RegistrationAuthenticationNative.trial true call.first.server.pin call.packet
          (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes call.packet.mldsa_public_key)
            (RegistrationNativeMldsaShared.nativeProject call.first))) ∧
      (MldsaTranscriptAuth.Issued (RegistrationAuthenticationNative.trial true call.first.server.pin call.packet
        (RegistrationSigningShared.historyFor (PqxdhRefinement.absBytes call.packet.mldsa_public_key)
          (RegistrationNativeMldsaShared.nativeProject call.first))) ∨
        (∃ forgery, RegistrationNativeMldsaTrialObserver.observe source.verify publicKey (.inr (.accept call.packet))
          call.first (.ok (some session)) call.last = some forgery) ∨ CacheHasCollision call.last.server.world.world.1.primitive.2) := by
  obtain ⟨call, same⟩ := captured_call setup checks wire route representation ensureInit identityIndex serverKeyId initial startup
    bounds mode work result supported endpoint snapshot saved parsed session raw found decodable
  exact ⟨call, same, fun publicKey matching => RegistrationNativeMldsaCausalOrigin.staged setup checks wire route representation
    initial.created initial.credential snapshot.2.1.transcript parsed session call publicKey matching⟩

end BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin.captured_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin.captured_call

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin.captured_staged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeStagedSnapshotOrigin.captured_staged
