-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationTrace
import BeaconcryptCore.Computational.RegistrationNativeKemOpenReceipts

/-! The entire original adaptive native secrecy-ledger execution derives genuine candidate-source publication history. The original transcript projection is obtained from the literal ledger syntax; source initialization derives an empty local owner roster. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeWire (Wire)
open RegistrationNativeKemOpenProvider (State)
open RegistrationNativeKemOpenPublicationTrace (Holds)
open PqxdhDeploymentInterface (FreshBounds Mode)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat} {mlSource : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : Wire)
  (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
  (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential mlSource)
  (selected : Nat) (pairs : List (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
  (publicKey : PqxdhKemIndCca.MlKem768PublicKey) (real : Bool) (parsed : Nat)
local notation "provider" => RegistrationNativeKemOpenProvider.implementation (n := n) setup checks wire route representation created credential selected pairs publicKey real
local notation "run" => RegistrationNativeKemOpenReceipts.run (n := n) setup checks wire route representation created credential selected pairs publicKey real parsed

/-- All original adaptive public and hidden secrecy operations preserve the actual roster and genuine native publication history. -/
theorem run_holds (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds)
    (work : OracleComp RegistrationNativeInterface.FullSpec Value)
    (beforeLedger afterLedger : RegistrationNativeLedger.State) (before after : State n mlSource KemSK)
    (priorRoster : RegistrationNativeKemOpenRoster.Holds pairs before)
    (prior : Holds wire pairs before beforeLedger.transcript) (value : Value)
    (supported : (some (value, afterLedger), after) ∈ support (((run bounds work beforeLedger).run).run before)) :
    RegistrationNativeKemOpenRoster.Holds pairs after ∧ Holds wire pairs after afterLedger.transcript := by
  induction work using OracleComp.inductionOn generalizing beforeLedger afterLedger before after with
  | pure original =>
      simp only [RegistrationNativeKemOpenReceipts.run, simulateQ_pure, StateT.run_pure, OptionT.run_pure,
        mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
      obtain ⟨⟨_sameValue, rfl⟩, rfl⟩ := supported
      exact ⟨priorRoster, prior⟩
  | query_bind query next ih =>
      rw [RegistrationNativeKemOpenReceipts.run_query_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨reply, reached⟩, called, tail⟩ := supported
      cases reply with
      | none =>
          simp only [mem_support_pure_iff, Prod.mk.injEq, reduceCtorEq, false_and] at tail
      | some result =>
          obtain ⟨reply, reachedLedger⟩ := result
          obtain ⟨nextRoster, nextPublications⟩ := RegistrationNativeKemOpenPublicationTrace.step_holds setup checks wire route representation
            created credential selected pairs publicKey real parsed readback bounds query beforeLedger reachedLedger before reached priorRoster prior reply called
          exact ih reply reachedLedger afterLedger reached after nextRoster nextPublications tail

/-- The complete original raw compiler derives these publication receipts from its actual empty secrecy ledger under the candidate source. -/
theorem program_holds (readback : RegistrationNativeWire.InitReadBack wire) (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before after : State n mlSource KemSK)
    (priorRoster : RegistrationNativeKemOpenRoster.Holds pairs before) (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before)) :
    RegistrationNativeKemOpenRoster.Holds pairs after ∧ Holds wire pairs after ledger.transcript := by
  rw [RegistrationNativeKemOpenReceipts.program_run] at supported
  apply run_holds setup checks wire route representation created credential selected pairs publicKey real parsed readback bounds
    (RegistrationNativeInterface.asModeO mode work) RegistrationNativeLedger.empty ledger before after priorRoster _ value supported
  intro entry impossible
  cases impossible

/-- The candidate provider retains the exact original CE ledger transcript, dropping only the extra native create-pin field in its public projection. -/
theorem program_consistent (bounds : FreshBounds) (mode : Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (before after : State n mlSource KemSK)
    (value : Value) (ledger : RegistrationNativeLedger.State)
    (supported : (some (value, ledger), after) ∈ support
      (((simulateQ provider (RegistrationNativeKemFullSource.program setup checks wire created.server.server.metadata.sender
        bounds mode work parsed)).run).run before)) :
    ledger.ledger.transcript = ledger.transcript.map RegistrationNativeInterface.Entry.erase := by
  apply RegistrationNativeLedger.wrap_consistent setup.source.crypto (RegistrationNativeWire.ledgerCodec wire)
    created.server.server.metadata.sender bounds (RegistrationNativeInterface.asModeO mode work) (value, ledger)
  apply RegistrationNativeOptionalSupport.completed_support
    (RegistrationNativeKemOpenRawCounter.native setup checks wire route representation created credential
      selected pairs publicKey real parsed) _ (value, ledger) before after
  simpa only [RegistrationNativeKemOpenReceipts.program_run, RegistrationNativeKemOpenReceipts.run,
    RegistrationNativeLedger.wrap] using supported

/-- Actual generated native startup has no retained local Beacon owner, independently of its initialized World counters and cache. -/
theorem start_empty (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.beacons = [] := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _generated, continued⟩ := supported
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

end BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.run_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.run_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.program_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.program_consistent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.program_consistent
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeKemOpenPublicationRun.start_empty
