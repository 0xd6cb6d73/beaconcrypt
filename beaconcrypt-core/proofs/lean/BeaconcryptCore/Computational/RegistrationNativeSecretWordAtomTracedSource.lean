-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomInstallTrace
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetSource

/-! The chronological observer is placed over the same concrete Word callback source. Its product state retains the original frontend, the complete trace and the complete private interpreter. Dropping only the trace recovers the literal native typed and full-ledger execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordInterpreter (Provider)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

abbrev State (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  RegistrationNativeSecretWordMessage.State source ×
    (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK)

def drop (before : State n KemSK source) : RegistrationNativeSecretWordTargetSource.State n KemSK source :=
  (before.1, before.2.2)

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
  (provider : Provider KemSK) (outer : QueryImpl Combined ProbComp)
local notation "implementation" => RegistrationNativeSecretWordTargetSource.implementation (n := n)
  setup wire route sign input inside provider outer

noncomputable def word : QueryImpl (RegistrationNativeSecretWordInterface.Spec n KemSK)
    (StateT (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK) ProbComp) :=
  (QueryImpl.mapStateTBase implementation RegistrationNativeSecretWordFrontendTrace.handler).flattenStateT

/-- The concrete traced callback source executes the observer and the original private source once, retaining both final states. -/
theorem word_program (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (simulateQ (word setup wire route sign input inside provider outer) work).run (trace, before) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run trace)).run before := by
  rw [word, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  rw [bind_pure_comp]

/-- Forgetting only the observer leaves the exact original private execution of any actual Word callback program. -/
theorem word_source (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (trace : RegistrationNativeSecretWordFrontendTrace.State) (before : RegistrationNativeSecretWordInterpreter.State n KemSK) :
    (fun result => (result.1, result.2.2)) <$>
      (simulateQ (word setup wire route sign input inside provider outer) work).run (trace, before) =
      (simulateQ implementation work).run before := by
  rw [word_program, Functor.map_map]
  have same := congrArg (fun program => (simulateQ implementation program).run before)
    (RegistrationNativeSecretWordFrontendTrace.program_erase work trace)
  simpa only [simulateQ_map, StateT.run_map, Functor.map_map] using same

/-- Every supported concrete traced callback has its same chronological pure trace before the private interpretation. -/
theorem word_support (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK)
    (result : Value × (RegistrationNativeSecretWordFrontendTrace.State × RegistrationNativeSecretWordInterpreter.State n KemSK))
    (supported : result ∈ support ((simulateQ (word setup wire route sign input inside provider outer) work).run before)) :
    (result.1, result.2.1) ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run before.1) := by
  rw [word_program, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact OracleComp.support_simulateQ_run'_subset implementation _ before.2 (by
    rw [StateT.run'_eq, support_map]
    exact Set.mem_image_of_mem Prod.fst called)

noncomputable def typed (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) :
    QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT (State n KemSK source) ProbComp) :=
  ((word setup wire route sign input inside provider outer).mapStateTBase
    (RegistrationNativeSecretWordFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey)).flattenStateT

/-- Tracing a concrete typed callback preserves the same actual frontend and private result after dropping only the trace. -/
theorem typed_source (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) :
    Prod.map id drop <$> (typed setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey query).run before =
      (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey query).run (drop before) := by
  rw [typed, QueryImpl.flattenStateT_mapStateTBase_apply_run, RegistrationNativeSecretWordTargetSource.typed_run]
  dsimp only [drop]
  rw [← word_source setup wire route sign input inside provider outer _ before.2.1 before.2.2]
  simp only [Functor.map_map]
  rfl

/-- Actual typed support retains the same callback's full pure trace and frontend poststate. -/
theorem typed_support (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State n KemSK source) (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State n KemSK source)
    (supported : result ∈ support ((typed setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey query).run before)) :
    ((result.1, result.2.1), result.2.2.1) ∈ support ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
      ((RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey query).run before.1)).run before.2.1) := by
  rw [typed, QueryImpl.flattenStateT_mapStateTBase_apply_run, support_map] at supported
  obtain ⟨reached, called, equal⟩ := supported
  cases equal
  exact word_support setup wire route sign input inside provider outer _ before.2 reached called

/-- The exact actual source projection is valid through every adaptive typed continuation, with the original raw ledger compiled unchanged. -/
theorem program_source (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) :
    Prod.map id drop <$>
      (simulateQ (typed setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey) work).run before =
      (simulateQ (RegistrationNativeSecretWordTargetSource.typed setup checks wire route sign input inside provider outer selectedOwner selectedAccept publicPrekey) work).run (drop before) := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map, id_eq]
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind,
        simulateQ_bind, simulateQ_spec_query, StateT.run_bind, ← typed_source setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey query before]
      simp only [bind_map_left]
      apply bind_congr
      intro middle
      exact ih middle.1 middle.2

/-- The same complete chronological Word observer is executed by the flattened actual typed source; no new audit query or intermediate reset is introduced. -/
theorem program_trace (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State n KemSK source) :
    (fun result => (((result.1, result.2.1), result.2.2.1), result.2.2.2)) <$>
      (simulateQ (typed setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey) work).run before =
      (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        ((simulateQ (RegistrationNativeSecretWordFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey) work).run before.1)).run before.2.1)).run before.2.2 := by
  rw [typed, OracleComp.simulateQ_flattenStateT_run, ← QueryImpl.simulateQ_mapStateTBase_run]
  rw [word_program]
  simp only [bind_pure_comp, Functor.map_map, id_map']

/-- The source trace is exactly the observer used by the alias client over the original full raw secrecy ledger. -/
theorem run_trace (checks : Checks) (selectedOwner selectedAccept : Nat)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (serverKeyId : U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before : State n KemSK source) :
    (fun result => ((((result.1, result.2.1), result.2.2.1), result.2.2.2.1), result.2.2.2.2)) <$>
      RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
        (typed setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey) mode work before =
      (simulateQ implementation ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler
        (RegistrationNativeSecretWordFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey
          serverKeyId bounds mode work before.1)).run before.2.1)).run before.2.2 := by
  rw [RegistrationNativeFullCompiler.compile_run]
  simp only [Functor.map_map]
  exact program_trace setup wire route sign input inside provider outer checks selectedOwner selectedAccept publicPrekey
    _ before

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_program
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.typed_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.typed_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.program_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.word_support
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.typed_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.typed_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.program_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.program_trace
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTracedSource.run_trace
