-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaBeaconChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaServerChronology
import BeaconcryptCore.Computational.RegistrationNativeMldsaReceiptPreservation
import BeaconcryptCore.Computational.RegistrationNativeMldsaProfile

/-! The positionwise real-primitive/native-payload chronology is invariant under actual named generation, complete original typed callbacks, arbitrary adaptive programs and the unchanged raw/secrecy compiler. No generated-key ownership or authentication conclusion is assumed for this structural log invariant. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology
open RegistrationNativeMldsaOpaque (Pool handleSource birth)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaTableProgram (runState evaluate)
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeInterface (ModeSpec)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
attribute [local irreducible] RegistrationNativeExperiment.handler

def receipts (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) := before.server.world.world.2
private def Keeps (work : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source))
    (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value) : Prop :=
  ∀ before pool result, Aligned pool.signing (receipts source before) →
    result ∈ support (runState source work before pool) → Aligned result.2.signing (receipts source result.1.2)
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before
private theorem pure_keeps (value : Value) : Keeps source
    (pure value : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) _ Value) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_pure] at supported
  simp only [support_pure, Set.mem_singleton_iff] at supported
  cases supported
  exact aligned
private theorem bind_keeps
    (work : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Value)
    (next : Value → StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) (OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source))) Next)
    (first : Keeps source work) (rest : ∀ value, Keeps source (next value)) : Keeps source (work >>= next) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, queried, continued⟩ := supported
  exact rest middle.1.1 middle.1.2 middle.2 result (first before pool middle aligned queried) continued
private theorem lift_keeps (work : StateT (RegistrationNativeExperiment.State n KemSK (handleSource source)) ProbComp Value)
    (law : ∀ before result, result ∈ support (work.run before) → receipts source result.2 = receipts source before) :
    Keeps source (RegistrationNativeMldsaProgram.liftState work) := by
  intro before pool result aligned supported
  rw [RegistrationNativeMldsaTableProgram.run_liftState, support_map] at supported
  obtain ⟨reached, possible, same⟩ := supported
  cases same
  rw [law before reached possible]
  exact aligned

/-- A real named generation advances the actual private table while retaining both complete earlier signing logs. -/
theorem generation (accounting : RegistrationNativeMldsaCapability.Accounting)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : (Option (RegistrationNativeMldsa.Credential (handleSource source)) ×
      RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing (receipts source before))
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.world (RegistrationNativeMldsaProgram.call accounting .generate)) before pool)) :
    Aligned result.2.signing (receipts source result.1.2) := by
  simp only [RegistrationNativeMldsaCreation.world, StateT.run, runState, evaluate,
    simulateQ_map, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  change inner ∈ support (runState source (RegistrationNativeMldsaProgram.call accounting .generate)
    before.server.world.world.1 pool) at possible
  rw [RegistrationNativeMldsaTableProgram.generate_source, support_map] at possible
  obtain ⟨generated, _actual, same⟩ := possible
  cases same
  rcases generated with ⟨generated, count⟩
  cases generated <;> exact aligned

/-- The complete actual creation callback preserves true-count signing chronology through every optional generation and constructor outcome. -/
theorem create (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : Std.U64)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : (RustM (Option Nat) × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing (receipts source before))
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaCreation.create setup checks representation created edPin mlPin keyId) before pool)) :
    Aligned result.2.signing (receipts source result.1.2) := by
  have law : Keeps source (RegistrationNativeMldsaCreation.create (n := n) (source := handleSource source)
      setup checks representation created edPin mlPin keyId) := by
    unfold RegistrationNativeMldsaCreation.create
    exact lift_keeps source _ (RegistrationNativeMldsaReceiptPreservation.source_create setup checks representation created
      edPin mlPin keyId)
  exact law before pool result aligned supported

private theorem server_build (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (credential : RegistrationNativeMldsa.Credential (handleSource source)) (index : Nat) (application : Option (Slice U8)) :
    Keeps source (RegistrationNativeMldsaProfile.server (n := n) (KemSK := KemSK)
      (RegistrationNativeMldsaServer.build (handleSource source) credential setup (RegistrationNativeWire.ledgerCodec wire)
        checks wire.encodeResponse index application)) := by
  intro before pool result aligned supported
  simp only [RegistrationNativeMldsaProfile.server, StateT.run, runState, evaluate,
    simulateQ_map, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact RegistrationNativeMldsaServerChronology.SDK.build source credential setup (RegistrationNativeWire.ledgerCodec wire)
    checks wire.encodeResponse index application before.server pool inner aligned possible

/-- Every complete original typed native callback preserves the actual complete signing histories, including all failed publication and authentication outcomes. -/
theorem handler (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : (RegistrationNativeRawAdapter.TypedSpec.Range query × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing (receipts source before))
    (supported : result ∈ support (runState source
      (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before pool)) :
    Aligned result.2.signing (receipts source result.1.2) := by
  have ordinary (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query) :
      Keeps (n := n) source (RegistrationNativeMldsaProgram.liftState
        (RegistrationNativeExperiment.handler setup checks wire route representation created (handleSource source) credential query)) :=
    lift_keeps (n := n) source _ (RegistrationNativeMldsaReceiptPreservation.handler (n := n) setup checks wire route representation created credential query allowed)
  cases query with
  | inl coin => exact ordinary trivial before pool result aligned supported
  | inr query => cases query with
    | create edPin mlPin keyId => exact create source setup checks representation created edPin mlPin keyId before pool result aligned supported
    | bundle index => exact RegistrationNativeMldsaBeaconChronology.sourceBundle source setup checks wire representation created index before pool result aligned supported
    | build index application =>
        simp only [RegistrationNativeMldsaProfile.handler] at supported
        exact server_build source setup checks wire credential index application before pool result aligned supported
    | _ => exact ordinary trivial before pool result aligned supported

/-- Arbitrary adaptive original typed programs retain every chronological real primitive attempt and its native unsigned receipt from the same run. -/
theorem program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : (Value × RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing (receipts source before))
    (supported : result ∈ support (runState source
      (simulateQ (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential) work) before pool)) :
    Aligned result.2.signing (receipts source result.1.2) := by
  induction work using OracleComp.inductionOn generalizing before pool with
  | pure value => exact pure_keeps source value before pool result aligned supported
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, RegistrationNativeMldsaTableProgram.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1.1 middle.1.2 middle.2
        (handler source setup checks wire route representation created credential query before pool middle aligned queried) continued

/-- The original complete raw/secrecy ledger run retains that same actual signing chronology in every observation mode. -/
theorem run (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (ModeSpec mode) Value)
    (before : RegistrationNativeExperiment.State n KemSK (handleSource source)) (pool : Pool source)
    (result : RegistrationNativeEvents.Observed Value (RegistrationNativeExperiment.State n KemSK (handleSource source)) × Pool source)
    (aligned : Aligned pool.signing (receipts source before))
    (supported : result ∈ support (evaluate source
      (RegistrationNativeMldsaProfile.run setup checks wire route representation created credential bounds mode work before) pool)) :
    Aligned result.2.signing (receipts source result.1.2.2) := by
  simp only [RegistrationNativeMldsaProfile.run, evaluate, simulateQ_map, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact program source setup checks wire route representation created credential _ before pool inner aligned possible

end BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.generation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.generation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.create
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.handler
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaRunChronology.run
