-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource
/-! Exact flattening for a Word callback tree with arbitrary common frontend state, including the corrected frontend's persistent platform state. The observer and private provider execute on the same query tree. Only the observer is dropped by its erasure equation; no callback, state-frame or security conclusion is a premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {I KemSK Front A : Type} {base : OracleSpec I}
abbrev Private (n : Nat) (KemSK : Type) := RegistrationNativeSecretWordInterpreter.State n KemSK
abbrev State (Front : Type) (n : Nat) (KemSK : Type) := Front × Private n KemSK
abbrev TracedState (Front : Type) (n : Nat) (KemSK : Type) := Front × (RegistrationNativeSecretWordFrontendTrace.State × Private n KemSK)
def drop (before : TracedState Front n KemSK) : State Front n KemSK := (before.1, before.2.2)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
    (controller : QueryImpl RegistrationNativeRawAdapter.TypedSpec
      (StateT Front (OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK))))
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n) setup wire route sign input inside provider outer
local notation "word" => RegistrationNativeSecretWordAtomTracedSource.word (n := n) setup wire route sign input inside provider outer

noncomputable def typed : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State Front n KemSK) ProbComp) :=
  (QueryImpl.mapStateTBase implementation controller).flattenStateT

noncomputable def traced : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (TracedState Front n KemSK) ProbComp) :=
  (QueryImpl.mapStateTBase word controller).flattenStateT

/-- The literal typed source retains its entire frontend/platform and private provider poststate. -/
theorem typed_run (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State Front n KemSK) :
    (typed setup wire route sign input inside provider outer controller query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ implementation ((controller query).run before.1)).run before.2 :=
  QueryImpl.flattenStateT_mapStateTBase_apply_run _ _ _ _ _

/-- Every interpreted typed outcome has the original free source outcome with the same full frontend/platform state. -/
theorem typed_support (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State Front n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State Front n KemSK)
    (supported : result ∈ support ((typed setup wire route sign input inside provider outer controller query).run before)) :
    (result.1, result.2.1) ∈ support ((controller query).run before.1) := by
  rw [typed_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  apply OracleComp.support_simulateQ_run'_subset implementation _ before.2
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem Prod.fst called

/-- Dropping only the actual observer restores the same typed source and complete private state. -/
theorem traced_source (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState Front n KemSK) :
    Prod.map id drop <$> (traced setup wire route sign input inside provider outer controller query).run before =
      (typed setup wire route sign input inside provider outer controller query).run (drop before) := by
  rw [traced, QueryImpl.flattenStateT_mapStateTBase_apply_run, typed_run]
  dsimp only [drop]
  rw [← RegistrationNativeSecretWordAtomTracedSource.word_source setup wire route sign input inside provider outer _ before.2.1 before.2.2]
  simp only [Functor.map_map]
  rfl

/-- The actual traced typed callback exposes its own pure chronology and full source frontend/platform result. -/
theorem traced_support (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : TracedState Front n KemSK)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × TracedState Front n KemSK)
    (supported : result ∈ support ((traced setup wire route sign input inside provider outer controller query).run before)) :
    ((result.1, result.2.1), result.2.2.1) ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((controller query).run before.1)).run before.2.1) := by
  rw [traced, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact RegistrationNativeSecretWordAtomTracedSource.word_support setup wire route sign input inside provider outer _ before.2 reached called

/-- Every adaptive continuation uses the same actual source tree, chronology and reached common/private state. -/
theorem program_trace (work : OracleComp RegistrationNativeRawAdapter.TypedSpec A) (before : TracedState Front n KemSK) :
    (fun result => (((result.1, result.2.1), result.2.2.1), result.2.2.2)) <$>
      (simulateQ (traced setup wire route sign input inside provider outer controller) work).run before =
      (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        ((simulateQ controller work).run before.1)).run before.2.1)).run before.2.2 := by
  rw [traced, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  rw [RegistrationNativeSecretWordAtomTracedSource.word_program]
  simp only [bind_pure_comp, Functor.map_map, id_map']

/-- Original raw compilation and its full ledger share that same chronology; no intermediate state or log is reset. -/
theorem run_trace (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) A) (before : TracedState Front n KemSK) :
    (fun result => ((((result.1, result.2.1), result.2.2.1), result.2.2.2.1), result.2.2.2.2)) <$>
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (traced setup wire route sign input inside provider outer controller) mode work before =
      (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        ((simulateQ controller (RegistrationNativeFullCompiler.compile setup.source.crypto wire serverKeyId bounds mode work)).run before.1)).run before.2.1)).run before.2.2 := by
  rw [RegistrationNativeFullCompiler.compile_run]
  simp only [Functor.map_map]
  exact program_trace setup wire route sign input inside provider outer controller _ before

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.typed_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.typed_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.typed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.typed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.traced_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.traced_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.traced_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.traced_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.program_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.program_trace

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordExecution.run_trace
