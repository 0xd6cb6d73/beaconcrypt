-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableStart
import BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology

/-! Actual effectful startup creates no ML signing attempt before the adversary begins. The original constructor and real Server source generation retain their actual counts/cache, while full pin selection is pure; successful startup has empty private and native signing logs. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
open RegistrationNativeMldsaOpaque (Pool handleSource birth)
open RegistrationNativeMldsaTableProgram (evaluate runState)
open RegistrationNativeMldsaChronology (Aligned)
variable {Value : Type} {n : Nat} {Auxiliary ι KemSK : Type} {base : OracleSpec ι}

private theorem initializePin_receipts (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary)
    (result : RustM (core.option.Option session.ServerAuthenticationPin) × RegistrationWorldServerReplay.Global n Auxiliary)
    (supported : result ∈ support ((RegistrationWorldServerFrontend.initializePin binding publicKey).run before)) :
    result.2.2.world.2 = before.2.world.2 := by
  simp only [RegistrationWorldServerFrontend.initializePin, StateT.run,
    support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

/-- The actual Server initializer's pure full pin retains its source-created empty native signing history. -/
theorem world_start (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (publicKey : Std.Array U8 1952#usize)
    (auxiliary : Auxiliary) (before after : PqxdhRecordLiftWorld.State n)
    (native : RegistrationWorldServerFrontend.State n Auxiliary)
    (supported : (.ok (.Some native), after) ∈ support
      ((RegistrationWorldServerFrontend.start created publicKey auxiliary).run before)) :
    native.global.2.world.2 = [] := by
  simp only [RegistrationWorldServerFrontend.start, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨installed, _first, continued⟩ := supported
  obtain ⟨pinned, possible, returned⟩ := continued
  have empty := initializePin_receipts ⟨created.server.server.identity, created.server.server.metadata.sender⟩ publicKey
    (PqxdhJointDhExtractFamily.empty, ⟨auxiliary, [], [], (installed.2, [])⟩) pinned possible
  simp only [support_pure, Set.mem_singleton_iff] at returned
  rcases pinned with ⟨reply, current⟩
  cases reply with
  | fail error | div => cases returned
  | ok option => cases option with
    | none => cases returned
    | some pin => cases returned; exact empty

variable (source : RegistrationNativeMldsa.Source)
private theorem evaluate_bind {Value Next : Type}
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value)
    (next : Value → OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Next) (pool : Pool source) :
    evaluate source (work >>= next) pool = (do
      let middle ← evaluate source work pool
      evaluate source (next middle.1) middle.2) := by
  simp only [evaluate, simulateQ_bind, StateT.run_bind]

private theorem evaluate_pure {Value : Type} (value : Value) (pool : Pool source) :
    evaluate source (pure value) pool = pure (value, pool) := by
  simp only [evaluate, simulateQ_pure, StateT.run_pure]


/-- Every successful actual opaque startup has empty raw primitive signing attempts and empty native payload receipts, including the real initialization prefix. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64)
    (result : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ result.1) :
    result.2.signing = [] ∧ initial.state.server.world.world.2 = [] := by
  simp only [RegistrationNativeMldsaCreation.start, evaluate_bind,
    RegistrationNativeMldsaTableProgram.ordinary, mem_support_bind_iff] at supported
  obtain ⟨constructor, drawn, continued⟩ := supported
  rw [support_map] at drawn
  obtain ⟨constructed, _possible, same⟩ := drawn
  cases same
  cases selected : constructed.1.1 with
  | none =>
      simp only [selected, evaluate_pure, support_pure, Set.mem_singleton_iff] at continued
      cases continued
      cases member
  | some created =>
      simp only [selected] at continued
      rw [evaluate_bind] at continued
      change result ∈ support
        (runState source (RegistrationNativeMldsaProgram.call .native .generate) constructed.2 {} >>= _) at continued
      rw [RegistrationNativeMldsaTableProgram.generate_source, mem_support_bind_iff] at continued
      obtain ⟨generation, drawn, suffix⟩ := continued
      rw [support_map] at drawn
      obtain ⟨generated, _actual, same⟩ := drawn
      cases same
      rcases generated with ⟨generated, count⟩
      cases generated with
      | none =>
          simp only [birth, evaluate_pure, support_pure, Set.mem_singleton_iff] at suffix
          cases suffix
          cases member
      | some key =>
          simp only [birth] at suffix
          rw [evaluate_bind, RegistrationNativeMldsaTableProgram.ordinary, mem_support_bind_iff] at suffix
          obtain ⟨initialization, drawn, finished⟩ := suffix
          rw [support_map] at drawn
          obtain ⟨initialized, _actual, same⟩ := drawn
          cases same
          cases outcome : initialized.1 with
          | fail error | div =>
              simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
              cases finished
              cases member
          | ok option => cases option with
            | none =>
                simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
                cases finished
                cases member
            | some native =>
                simp only [outcome, evaluate_pure, support_pure, Set.mem_singleton_iff] at finished
                cases finished
                simp only [Option.mem_some_iff] at member
                cases member
                have actualSource := _actual
                rw [show initialized = (.ok (.Some native), initialized.2) from Prod.ext outcome rfl] at actualSource
                have empty := world_start created key.publicKey RegistrationServerRoleBackend.empty
                  _ _ native actualSource
                exact ⟨rfl, empty⟩

/-- The initial chronological relation is derived from the actual source startup, not supplied by an initialized-game premise. -/
theorem aligned (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64)
    (result : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ result.1) :
    Aligned result.2.signing initial.state.server.world.world.2 := by
  obtain ⟨privateEmpty, nativeEmpty⟩ := initialized source setup ensureInit identityIndex serverKeyId result supported initial member
  rw [privateEmpty, nativeEmpty]
  exact .nil

/-- Actual source startup followed by any adaptive original ledger run derives the complete chronological signing relation without an initial-history assumption. -/
theorem run (setup : Setup base KemSK) (checks : Checks)
    (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (ModeSpec mode) Value)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaProfile.run setup checks wire route representation initial.created initial.credential
        bounds mode work initial.state) started.2)) :
    Aligned result.2.signing result.1.2.2.server.world.world.2 := by
  exact RegistrationNativeMldsaRunChronology.run source setup checks wire route representation
    initial.created initial.credential bounds mode work initial.state started.2 result
    (aligned source setup ensureInit identityIndex serverKeyId started startup initial member) supported

end BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.world_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.world_start
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.initialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.aligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.aligned

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaInitializedChronology.run
