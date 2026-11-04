-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedRecordBindingLedger
import BeaconcryptCore.Computational.RegistrationNativeRecordLedger
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeEntropy

/-! The actual native original ledger has record acceptance/publication evidence after arbitrary reached startup effects in the shared CTX cache. Entropy-port restoration removes only public ML creation metadata and HMAC tags, so both directions of record traffic keep their literal record observations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordLedger
open PqxdhRecordFactsBindingLedger (LedgerEvidence)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (Entry FreshBounds Mode)
open PqxdhServerAuthExperiment (Setup Codec)
attribute [local irreducible] PqxdhRecordLiftIdeal.ctxInterpreter
variable {n : Nat} {ι KemSK Reader Response E Value Failure : Type} {base : OracleSpec ι}

/-- The original native ledger derives its full same-execution record evidence at every supported initialized execution, retaining the reached cursor/control/cache. -/
theorem initialized (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : RegistrationNativeEntropyInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : Std.U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (secret : CtxPrivate n) (result : RegistrationNativeEntropyRun.Result n E Value)
    (supported : result ∈ support (RegistrationNativePlatformGatedNativeEntropy.run modes replace setup codec route env reserve serverKid bounds mode work
      created initial shell control secret)) :
    ∀ born ∈ result.1.1, LedgerEvidence codec route result.1.2 result.2 born.2.1.2.ledger.transcript := by
  rw [← RegistrationNativePlatformGatedNativeEntropy.run_transport, support_map] at supported
  obtain ⟨old, oldSupported, rfl⟩ := supported
  simp only [RegistrationNativePlatformGatedEntropyInitial.run, support_map] at oldSupported
  obtain ⟨final, finalSupported, rfl⟩ := oldSupported
  have complete := RegistrationNativePlatformGatedRecordBindingLedger.full_program modes ideal replace setup codec route readback
    (RegistrationNativeEntropyPort.environment env) (RegistrationNativePlatformGatedNativeEntropy.reserveLift reserve) serverKid bounds
    (PqxdhDeploymentInterface.asModeO mode (RegistrationNativeEntropyCompile.compile mode work)) _
    (RegistrationNativePlatformGatedRecordBindingLedger.empty_invariant codec route _ safe) final finalSupported
  intro born member
  have selected : born = (PqxdhRegistrationJointServerBirth.encode created,
      ((final.1, RegistrationNativeEntropyRestore.ledger final.2.1), final.2.2.1.1.1.2)) := by
    symm
    simpa only [RegistrationNativeEntropyRun.project, RegistrationNativeEntropyProgram.outcome,
      RegistrationNativeEntropyExecution.result, Prod.map, id_eq, Option.map_some, Option.mem_some_iff] using member
  subst born
  rw [RegistrationNativeEntropyRestore.ledger_transcript]
  exact RegistrationNativeRecordLedger.strip_evidence codec route _ _ _ (RegistrationNativePlatformGatedRecordBindingLedger.evidence codec route _ complete)

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordLedger
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordLedger.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordLedger.initialized
