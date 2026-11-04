-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaNoSign
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerCached

/-! Validity of the actual native chronological ML signing history is an execution invariant. It starts at the real generated Server's empty receipt list and is preserved by every original typed callback, including all failures, arbitrary raw records and the complete original secrecy ledger. No history-validity or event-simulation premise is supplied for a native run from actual startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
attribute [local irreducible] RegistrationNativeExperiment.run
  RegistrationServerSdkSource.accept RegistrationServerSdkSource.build RegistrationNativeExperiment.start

def Valid (before : RegistrationNativeExperiment.State n KemSK source) : Prop :=
  RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before)

private theorem world (work : StateT (PqxdhRecordLiftWorld.State n) ProbComp Value)
    (persistent : ∀ before result, result ∈ support (work.run before) → before.primitive.2 ≤ result.2.primitive.2)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.world work).run before)) : Valid result.2 := by
  simp only [RegistrationNativeExperiment.world, RegistrationNativeExperiment.server,
    StateT.run, Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationSigningShared.cached_extend before.server.world.world.2 _ _
    (persistent before.server.world.world.1 inner possible) valid

private theorem server (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (keeps : ∀ before, RegistrationNativeMldsaServerCached.FrontValid before → ∀ result,
      result ∈ support (work.run before) → RegistrationNativeMldsaServerCached.FrontValid result.2)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.server work).run before)) : Valid result.2 := by
  simp only [RegistrationNativeExperiment.server, StateT.run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact keeps before.server valid inner possible

private theorem record (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (query : PqxdhRecordLiftInterface.RecordQuery)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : (PqxdhRecordLiftInterface.RecordSpec .O).Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.record setup wire route query source).run before)) : Valid result.2 := by
  cases query with
  | inl query => exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route (.inr (.inr (.inl query)))) before valid result supported
  | inr pair =>
      rcases pair with ⟨owner, command⟩
      cases command with
      | inl plaintext =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          cases found : before.beacons[owner]? with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact valid
          | some selected =>
              simp only [found] at supported
              exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inl plaintext))))) before valid result supported
      | inr raw =>
          simp only [RegistrationNativeExperiment.record, StateT.run] at supported
          cases found : before.beacons[owner]? with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              cases supported
              exact valid
          | some selected =>
              simp only [found] at supported
              exact world _ (RegistrationNativeWorldCache.guarded setup (RegistrationNativeWire.ledgerCodec wire) route
                (.inr (.inr (.inr (selected.worldOwner, .inr raw))))) before valid result supported

/-- Every actual original typed callback preserves validity of all prior and newly attempted ML signing receipts. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation created source credential query).run before)) :
    Valid result.2 := by
  cases query with
  | inl coin => exact world _ (RegistrationWorldCache.effects_cache (.inl coin)) before valid result supported
  | inr query => cases query with
    | create edPin mlPin keyId => exact RegistrationNativeMldsaNoSign.source_create_cached setup checks representation created edPin mlPin keyId before valid result supported
    | bundle owner => exact RegistrationNativeMldsaNoSign.source_bundle_cached setup checks wire representation created owner before valid result supported
    | build session application =>
        exact server _
          (RegistrationNativeMldsaServerCached.build setup (RegistrationNativeWire.ledgerCodec wire) checks
            (RegistrationNativeMldsa.owned source credential) wire.encodeResponse session application) before valid result supported
    | accept packet =>
        have law : (RegistrationNativeExperiment.handler setup checks wire route representation created source credential
            (.inr (.accept packet))).run before =
            (fun result => (result.1, { before with parsedAccepts := before.parsedAccepts + 1, server := result.2 })) <$>
              (RegistrationServerSdkSource.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
                representation created packet).run before.server := by
          simp only [RegistrationNativeExperiment.handler, StateT.run]
          rfl
        rw [law, support_map] at supported
        obtain ⟨inner, possible, same⟩ := supported
        cases same
        exact RegistrationNativeMldsaServerCached.accept setup (RegistrationNativeWire.ledgerCodec wire) checks route source.verify
          representation created packet before.server valid inner possible
    | finish owner packet => exact RegistrationNativeMldsaNoSign.source_finish_cached setup checks wire representation created owner packet before valid result supported
    | hmac key message =>
        simp only [RegistrationNativeExperiment.handler, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact valid
    | hash bytes => exact world _ (RegistrationWorldCache.effects_cache (.inr (.hash bytes))) before valid result supported
    | serverSend keyId plaintext => exact record setup wire route (.inl (.inl (plaintext, keyId))) before valid result supported
    | serverRaw raw => exact record setup wire route (.inl (.inr raw)) before valid result supported
    | beaconSend owner plaintext => exact record setup wire route (.inr (owner, .inl plaintext)) before valid result supported
    | beaconRaw owner raw => exact record setup wire route (.inr (owner, .inr raw)) before valid result supported

/-- Arbitrary adaptive original typed programs retain the real global signing-history invariant. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : Value × RegistrationNativeExperiment.State n KemSK source)
    (supported : result ∈ support ((simulateQ
      (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) work).run before)) :
    Valid result.2 :=
  simulateQ_run_preservesInv (RegistrationNativeExperiment.handler setup checks wire route representation created source credential)
    Valid (fun query current checked output possible => handler setup checks wire route representation created credential query current checked output possible)
    work before valid result supported

/-- The complete original raw execution, original bit/fresh sampling and every optional outcome preserve the same actual signing history. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK source) (valid : Valid before)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation created source credential bounds mode work before)) :
    Valid result.2.2 := by
  rw [RegistrationNativeExperiment.run, RegistrationNativeFullCompiler.compile_run, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program setup checks wire route representation created credential
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
    before valid inner possible

/-- Actual effectful native startup derives the signing-history invariant from the generated Server's empty receipt list. -/
theorem start (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    Valid initial.state := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructor, continued⟩ := supported
  cases born : constructed.1.1 with
  | none =>
      simp only [born, support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | some created =>
      simp only [born, mem_support_bind_iff] at continued
      obtain ⟨generated, _generation, continued⟩ := continued
      cases keyed : generated.1 with
      | none =>
          simp only [keyed, support_pure, Set.mem_singleton_iff] at continued
          cases continued
      | some credential =>
          simp only [keyed, mem_support_bind_iff] at continued
          obtain ⟨initialized, possible, returned⟩ := continued
          rcases initialized with ⟨reply, after⟩
          cases reply with
          | fail error | div =>
              simp only [support_pure, Set.mem_singleton_iff] at returned
              cases returned
          | ok option => cases option with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
            | some native =>
                simp only [support_pure, Set.mem_singleton_iff] at returned
                cases returned
                exact RegistrationNativeMldsaServerCached.start created credential.publicKey
                  RegistrationServerRoleBackend.empty generated.2 after native possible

/-- A complete native run from actual successful startup derives its global signing-history invariant without a history premise. -/
theorem initialized_run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (initialized : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source))
    (supported : result ∈ support (RegistrationNativeExperiment.run setup checks wire route representation initial.created
      source initial.credential bounds mode work initial.state)) : Valid result.2.2 :=
  run setup checks wire route representation initial.created initial.credential bounds mode work initial.state
    (start setup ensureInit identityIndex serverKeyId initial initialized) result supported

noncomputable def checked
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source)) : Bool := by
  classical
  exact event result && decide (Valid result.2.2)

/-- In the actual whole native profile, explicitly checking receipt validity changes no event distribution. It is an execution invariant, not a conditioning or eligibility restriction. -/
theorem profile (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : RegistrationNativeExperiment.Public → OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (event : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK source) → Bool) :
    RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
      bounds mode adversary (checked event) =ᵈ
      RegistrationNativeExperiment.profile setup checks wire route representation source ensureInit identityIndex serverKeyId
        bounds mode adversary event := by
  classical
  unfold RegistrationNativeExperiment.profile
  apply OracleComp.EvalDistEq.bind_congr_of_support
  intro initial supported
  cases initial with
  | none => exact _root_.EvalDistEq.rfl
  | some initial =>
      simp only [← bind_pure_comp]
      apply OracleComp.EvalDistEq.bind_congr_of_support
      intro observed reached
      have valid := initialized_run setup checks wire route representation ensureInit identityIndex serverKeyId
        initial supported bounds mode (adversary initial.public) observed reached
      simp only [checked, valid, decide_true, Bool.and_true]
      exact _root_.EvalDistEq.rfl

end BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.initialized_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.initialized_run
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.profile' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInvariant.profile
