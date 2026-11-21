-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawIdealKeymatchTrace

/-! The exact original secrecy ledger is retained above native raw admission. Its internal coins and sends preserve every old accept/bundle witness even when the send is refused; its returned public entry is appended only by the unchanged ledger implementation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawIdealKeymatchRun
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentInterface (Spec FullSpec Entry FreshBounds)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentIdealKeymatch (KeyTrace)
open CborRawPublicState (Public)
open CborRawMiddleSimulation (Native)
variable {ι KemSK Reader Response Result : Type} {baseSpec : OracleSpec ι}
section Run
variable (setup : Setup baseSpec KemSK) (wire : Codec Reader Response)
    (parse : Pqxdh.Bytes → Option CborProductionBoundary.NativeFrame) (checks : Checks) {count : Nat}
    (target : Target count) (parameters : Params KemSK count) (created : PqxdhLiveServerConstruction.Created Unit)

/-- Every adaptive native subprogram preserves the old transcript's complete key trace. -/
theorem keeps (work : OracleComp Spec Result) (transcript : List Entry) (state : Public × Native KemSK)
    (holds : KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript state.2.base
      state.2.backend.2.2) (result : Result × (Public × Native KemSK))
    (supported : result ∈ support ((simulateQ (CborRawNativePublic.native setup wire parse checks target parameters
      created) work).run state)) :
    KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript result.2.2.base
      result.2.2.backend.2.2 := by
  exact OracleComp.simulateQ_run_preserves_inv_of_query
    (CborRawNativePublic.native setup wire parse checks target parameters created)
    (fun current => KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters transcript
      current.2.base current.2.backend.2.2)
    (fun query current valid after member =>
      CborRawIdealKeymatchTrace.restrict setup (CborRawCompile.sourceCodec wire parse) checks target parameters
        transcript (transcript ++ [⟨.inl query, after.1⟩]) (fun entry found => List.mem_append_left _ found) _ _
        (CborRawIdealKeymatchTrace.handler_trace setup wire parse checks target parameters created query transcript
          current valid after member)) work state holds result supported

noncomputable def ledgerHandler (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (Ledger × (Public × Native KemSK)) ProbComp) :=
  ((CborRawNativePublic.native setup wire parse checks target parameters created).mapStateTBase
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds)).flattenStateT

/-- Every original full-interface command preserves the actual ledger trace, including refused fresh and test sends. -/
theorem query_trace (bounds : FreshBounds) (query : FullSpec.Domain) (state : Ledger × (Public × Native KemSK))
    (holds : KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters state.1.transcript
      state.2.2.base state.2.2.backend.2.2)
    (result : FullSpec.Range query × (Ledger × (Public × Native KemSK)))
    (member : result ∈ support ((ledgerHandler setup wire parse checks target parameters created bounds query).run state)) :
    KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters result.2.1.transcript
      result.2.2.2.base result.2.2.2.backend.2.2 := by
  rcases state with ⟨ledger, native⟩
  change result ∈ support ((fun value => (value.1.1, (value.1.2, value.2))) <$>
    (simulateQ (CborRawNativePublic.native setup wire parse checks target parameters created)
      ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds query).run ledger)).run native) at member
  rw [support_map] at member
  obtain ⟨reached, reachedMember, rfl⟩ := member
  rcases query with request | secrecy
  · rw [PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      support_map] at reachedMember
    obtain ⟨answer, answerMember, rfl⟩ := reachedMember
    exact CborRawIdealKeymatchTrace.handler_trace setup wire parse checks target parameters created request
      ledger.transcript native holds answer answerMember
  · have value : reached.1 ∈ support ((PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto
        (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds (.inr secrecy)).run ledger) := by
      apply OracleComp.support_simulateQ_run'_subset
        (CborRawNativePublic.native setup wire parse checks target parameters created) _ native
      rw [StateT.run'_eq, support_map]
      exact ⟨reached, reachedMember, rfl⟩
    have recorded := PqxdhDeploymentEligibility.ledger_secrecy setup.source.crypto
      (CborTaggedSimulation.boundaryWire wire parse) setup.serverKeyId bounds secrecy ledger reached.1 value
    have kept := keeps setup wire parse checks target parameters created _ ledger.transcript native holds reached reachedMember
    change KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters reached.1.2.transcript
      reached.2.2.base reached.2.2.backend.2.2
    rw [recorded]
    exact PqxdhDeploymentIdealKeymatch.keyTrace_quiet setup (CborRawCompile.sourceCodec wire parse) checks target
      parameters ledger.transcript _ _ _ _ kept (.inr secrecy) trivial _ rfl kept.owners rfl rfl

/-- Every initialized execution of the complete original secrecy wrapper has its actual raw key trace. -/
theorem run_trace (bounds : FreshBounds) (work : OracleComp FullSpec Result) (publicState : Public)
    (result : (Result × Ledger) × (Public × Native KemSK))
    (supported : result ∈ support ((simulateQ (CborRawNativePublic.native setup wire parse checks target parameters
      created) (PqxdhDeploymentSecrecy.wrap setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
        setup.serverKeyId bounds work)).run
          (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created)))) :
    KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters result.1.2.transcript result.2.2.base
      result.2.2.backend.2.2 := by
  have flattened := OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT
    (CborRawNativePublic.native setup wire parse checks target parameters created)
    (PqxdhDeploymentSecrecy.ledgerImpl setup.source.crypto (CborTaggedSimulation.boundaryWire wire parse)
      setup.serverKeyId bounds) work Ledger.empty
    (publicState, PqxdhDeploymentBackend.xinitial created (PqxdhDeploymentIdealSteps.idealInit created))
  simp only [PqxdhDeploymentSecrecy.wrap] at supported
  rw [flattened, support_map] at supported
  obtain ⟨flat, flatMember, rfl⟩ := supported
  exact OracleComp.simulateQ_run_preserves_inv_of_query (ledgerHandler setup wire parse checks target parameters created bounds)
    (fun current => KeyTrace setup (CborRawCompile.sourceCodec wire parse) checks target parameters current.1.transcript
      current.2.2.base current.2.2.backend.2.2)
    (fun query current valid after member => query_trace setup wire parse checks target parameters created bounds query
      current valid after member) work _
    (PqxdhDeploymentIdealKeymatch.keyTrace_initial setup (CborRawCompile.sourceCodec wire parse)
      checks target parameters created) flat flatMember

end Run
end BeaconcryptCore.Computational.CborRawIdealKeymatchRun

/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchRun.keeps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchRun.keeps
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchRun.query_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchRun.query_trace
/-- info: 'BeaconcryptCore.Computational.CborRawIdealKeymatchRun.run_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawIdealKeymatchRun.run_trace
