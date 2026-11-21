-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemFullSource

/-! Actual generated startup connects the complete original native raw experiment to the genuine selected-first KEM family. Every native ledger and operational state field is retained through the proved compiler projection; only the independently bounded uniform accounting coordinate is masked. No supplied empty-pool, private-query-budget or whole-game simulation condition remains. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhDeploymentInterface (Budget FreshBounds Mode)
open RegistrationNativeExperiment (Initial State)
open RegistrationNativeWire (Wire)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}

def observe (outcome : Option (Value × RegistrationNativeLedger.State) ×
    (RegistrationNativeKemServerState.State n mlSource × PqxdhLiveKemBirth.Pool KemSK)) :=
  outcome.1.map fun result => (result.1, (result.2, outcome.2))

noncomputable def reserved (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential mlSource)
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (parsed : Nat) (selected : Fin (budget.create + 1))
    (localState : RegistrationNativeKemServerState.State n mlSource) :=
  observe <$> (do
    let chosen ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
    let others ← PqxdhLiveKemSelection.sampleFamily
      (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen) budget.create
    let pairs := List.ofFn (selected.insertNth chosen others)
    Prod.map id (RegistrationNativeKemPoolSource.project pairs) <$>
      (((simulateQ (RegistrationNativeKemGame.stopped setup.baseImpl setup.kem
        (RegistrationNativeKemParsedRouting.other setup checks wire route representation created credential)
        selected.val pairs)
        (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender bounds mode work parsed)).run).run
          (localState, PqxdhDynamicKemRouter.empty)))

/-- The actual native generated constructor starts the indexed private KEM service empty. -/
theorem start_pool (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.pool = PqxdhLiveKemBirth.empty := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _born, continued⟩ := supported
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

/-- The actual original initialized native run has the complete selected-first private KEM source distribution at its original public query caps. -/
theorem initialized_source (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (source : RegistrationNativeMldsa.Source) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : Initial n KemSK source)
    (started : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (bounds : FreshBounds) (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (budget : Budget) (bounded : RegistrationNativeInterface.Respects budget work)
    (parsed : Nat) (selected : Fin (budget.create + 1)) :
    EvalDistEq
      ((fun result => some (RegistrationNativeKemDispatcherCompiler.fullProject result)) <$>
        RegistrationNativeExperiment.run setup checks wire route representation initial.created source initial.credential
          bounds mode work initial.state)
      (reserved setup checks wire route representation initial.created initial.credential bounds mode work budget parsed selected
        (RegistrationNativeKemServerState.project initial.state)) := by
  have law := (RegistrationNativeKemFullSource.selected_source setup checks wire route representation initial.created
    initial.credential bounds mode work budget bounded parsed selected
    (RegistrationNativeKemServerState.project initial.state)).map observe
  have same := congrArg (fun run => some <$> run)
    (RegistrationNativeKemParsedRouting.full_source setup checks wire route representation initial.created initial.credential
      parsed bounds mode work initial.state)
  have empty := start_pool setup source ensureInit identityIndex serverKeyId initial started
  simp only [Functor.map_map, RegistrationNativeKemFullSource.program, observe, Option.map_some,
    RegistrationNativeKemAcceptCompiler.nativeProject, empty] at same law ⊢
  rw [same]
  exact law

end BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource.start_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource.start_pool
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource.initialized_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemInitializedSource.initialized_source
