-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeRecordOriginTrace

/-! The actual initialized native ledger retains every ordinary raw receive's exact earlier publication prefix and failed-writer alternative. Initial dictionaries are structural empty-startup receipts, separately derived from the original effectful startup. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeRecordOriginInitialized
open PqxdhRecordFactsOriginPublicationPrefixes (Prefixes)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Codec)
variable {n : Nat} {ι KemSK Reader Response E Value : Type} {base : OracleSpec ι}

/-- The original native ledger derives its full same-execution record evidence at every supported initialized execution, retaining the reached cursor/control/cache. -/
theorem initialized_prefixes (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : RegistrationNativeEntropyInterface.Environment n E) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (secret : CtxPrivate n) (empty : ∀ label, (secret.keys label).1.successfulSeals = []) (result : RegistrationNativeEntropyRun.Result n E Value)
    (supported : result ∈ support (RegistrationNativeEntropyInitialized.run modes replace setup codec route env serverKid bounds mode work
      created initial shell control secret)) :
    ∀ born ∈ result.1.1, Prefixes codec route result.1.2 result.2 born.2.1.2.ledger.transcript := by
  rw [← RegistrationNativeEntropyInitialized.run_transport, support_map] at supported
  obtain ⟨old, oldSupported, rfl⟩ := supported
  simp only [CborRawRecordEntropyInitial.run, support_map] at oldSupported
  obtain ⟨final, finalSupported, rfl⟩ := oldSupported
  have history : PqxdhRecordFactsOriginPublicationHistory.History codec control secret [] := by
    intro label entry member
    rw [empty label] at member
    exact False.elim (List.not_mem_nil member)
  have complete := CborRawRecordOriginPrefixes.full_program_invariant modes ideal replace setup codec route readback
    (RegistrationNativeEntropyPort.environment env) serverKid bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)) _
    ⟨⟨safe, history⟩, by simp [Prefixes, PqxdhDeploymentSecrecy.Ledger.empty]⟩ final finalSupported
  intro born member
  have selected : born = (PqxdhRegistrationJointServerBirth.encode created,
      ((final.1, RegistrationNativeEntropyRestore.ledger final.2.1), final.2.2.1.1.1.2)) := by
    symm
    simpa only [RegistrationNativeEntropyRun.project, RegistrationNativeEntropyProgram.outcome,
      RegistrationNativeEntropyExecution.result, Prod.map, id_eq, Option.map_some, Option.mem_some_iff] using member
  subst born
  rw [RegistrationNativeEntropyRestore.ledger_transcript]
  exact RegistrationNativeRecordOriginTrace.strip_prefixes codec route _ _ _ complete.2

end BeaconcryptCore.Computational.RegistrationNativeRecordOriginInitialized
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeRecordOriginInitialized.initialized_prefixes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeRecordOriginInitialized.initialized_prefixes
