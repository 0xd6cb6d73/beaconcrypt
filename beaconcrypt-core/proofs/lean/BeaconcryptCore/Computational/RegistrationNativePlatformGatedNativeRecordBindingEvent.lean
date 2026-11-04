-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordLedger
import BeaconcryptCore.Computational.RegistrationNativeRecordBindingEvent
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhDeploymentInterface (FreshBounds Mode)
open RegistrationNativeRecordBindingEvent (view)
variable {n : Nat} {I KemSK Reader Response E Failure Value : Type} {base : OracleSpec I}
attribute [local irreducible] PqxdhRecordLiftIdeal.ctxInterpreter

/-- Actual cross-handle acceptance after any reached initialized cache forces a retained same-execution commitment conflict, including every terminal refusal. -/
theorem initialized_conflict (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (readback : PqxdhServerAuthNegativeControl.FrameReadBack codec)
    (env : RegistrationNativeEntropyInterface.Environment n E)
    (reserve : Nat → StateT E ProbComp (core.result.Result Unit Failure)) (serverKid : U64) (bounds : FreshBounds)
    (mode : Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value)
    (created : PqxdhLiveServerConstruction.Created Unit) (initial : E) (shell : CborRecordWorldClient.Shell)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : PqxdhRecordLiftProtocolHistory.Safe control)
    (secret : CtxPrivate n) (result : RegistrationNativeEntropyRun.Result n E Value)
    (supported : result ∈ support (RegistrationNativePlatformGatedNativeEntropy.run modes replace setup codec route env reserve serverKid bounds mode work
      created initial shell control secret))
    (crossed : PqxdhRecordLiftIdeal.CrossAccept codec route (view result)) :
    PqxdhRecordFactsBindingEvent.DigestConflict result.2 := by
  apply PqxdhRecordFactsBindingEvent.cross_accept_conflict codec route (view result) result.1.2 result.2 rfl _ crossed
  intro actual member
  change actual ∈ result.1.1.map _ at member
  rw [Option.mem_def, Option.map_eq_some_iff] at member
  obtain ⟨born, bornMember, rfl⟩ := member
  exact RegistrationNativePlatformGatedNativeRecordLedger.initialized modes ideal replace setup codec route readback env reserve serverKid bounds
    mode work created initial shell control safe secret result supported born bornMember

end BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent.initialized_conflict' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformGatedNativeRecordBindingEvent.initialized_conflict
