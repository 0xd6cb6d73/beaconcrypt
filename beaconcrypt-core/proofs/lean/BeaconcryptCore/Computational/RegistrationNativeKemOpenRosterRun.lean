-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRoster
import BeaconcryptCore.Computational.RegistrationNativeKemFullSource
import BeaconcryptCore.Computational.RegistrationNativeKemOpenRawCounter

/-! The actual original raw and hidden secrecy-ledger program preserves the derived candidate-source roster relation. Its initialized native owner roster and private prefix are both empty; no target honesty or whole-game simulation is supplied as an assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenRoster (Holds)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real

/-- Arbitrary adaptive typed native work retains the actual current owner-to-genuine-prefix relation under the candidate provider. -/
theorem typed_work_holds (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before after : State n mlSource KemSK) (prior : Holds pairs before) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ (provider ∘ₛ RegistrationNativeKemParsedRouting.handler setup checks wire parsed) work).run).run before)) :
    Holds pairs after := by
  induction work using OracleComp.inductionOn generalizing before after with
  | pure original =>
      simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq] at supported
      rw [supported.2]
      exact prior
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [Option.elim_none, StateT.run_pure, mem_support_pure_iff, Prod.mk.injEq,
            reduceCtorEq, false_and] at tail
      | some reply =>
          exact ih reply reached after
            (RegistrationNativeKemOpenRoster.parsed_holds setup checks wire route representation created credential
              selected pairs publicKey real parsed query before reached prior reply called) tail

/-- The literal complete original raw compiler derives the same owner/private-handle relation below its unchanged secrecy draws and transcript. -/
theorem program_holds (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (before after : State n mlSource KemSK) (prior : Holds pairs before) (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before)) : Holds pairs after := by
  apply typed_work_holds setup checks wire route representation created credential selected pairs publicKey real parsed
    (RegistrationNativeFullCompiler.compile setup.source.crypto wire created.server.server.metadata.sender bounds mode work)
    before after prior (value, ledger)
  simpa only [RegistrationNativeKemFullSource.program, QueryImpl.simulateQ_compose] using supported

/-- Arbitrary original raw callback programs retain the same roster relation through their actual bounded native adapter. -/
theorem raw_work_holds (work : OracleComp RegistrationNativeInterface.Spec Value)
    (before after : State n mlSource KemSK) (prior : Holds pairs before) (value : Value)
    (supported : (some value, after) ∈ support
      (((simulateQ (RegistrationNativeKemOpenRawCounter.native setup checks wire route representation created credential
        selected pairs publicKey real parsed) work).run).run before)) : Holds pairs after := by
  apply typed_work_holds setup checks wire route representation created credential selected pairs publicKey real parsed
    (RegistrationNativeRawAdapter.compile wire work) before after prior value
  simpa only [RegistrationNativeRawAdapter.compile, RegistrationNativeKemOpenRawCounter.native,
    QueryImpl.simulateQ_compose] using supported

/-- Empty actual native owner and private creation rosters establish the genuine-prefix relation for every reserved family. -/
theorem empty_holds (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (state : RegistrationNativeKemServerState.State n mlSource) (empty : state.beacons = [])
    (phase : RegistrationNativeKemSwitchSource.Phase) : Holds pairs ((state, PqxdhDynamicKemRouter.empty), phase) := by
  constructor
  · simp only [RegistrationNativeKemOpenBirth.borns, PqxdhDynamicKemRouter.empty, empty, List.length_nil]
  · intro index owner found
    simp only [empty, List.getElem?_nil, reduceCtorEq] at found

end BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.typed_work_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.typed_work_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.program_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.empty_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.empty_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.raw_work_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenRosterRun.raw_work_holds
