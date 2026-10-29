-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRawRecordOriginObservation
import BeaconcryptCore.Computational.PqxdhRecordFactsOriginInvariant

/-! Every exact hidden seal in the raw cursor world has an actual produced frame on its physical sender. The source invariant is instantiated with the entire arbitrary guarded World client, retaining the complete actual control and private histories. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRawRecordOriginProduced
open CtxRomAuth AdaptiveCtxReceive
open PqxdhRecordLiftInterface (Environment)
open PqxdhRecordLiftIdeal (CtxPrivate KeyMode Client)
open PqxdhRecordLiftWorldCompiler (Label)
open PqxdhRecordFactsOriginInvariant (Invariant schedule_invariant initial_invariant)
open CborRawRecordOriginObservation (ctxRun)
variable {n : Nat} {ι KemSK Reader Response E X : Type} {baseSpec : OracleSpec ι}

/-- Initialized raw guarded source scheduling derives the exact dictionary-origin invariant. -/
theorem ctxRun_invariant (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary)) :
    Invariant result.1.2 result.2 :=
  schedule_invariant modes ideal replace setup codec route
    (CborRawRecordLiftBounds.client env setup.source.crypto codec serverKid bounds mode adversary)
    PqxdhRecordLiftProtocol.initialControl CtxPrivate.initial initial_invariant result supported


/-- Every retained raw-world seal has its actual source-produced frame and installed counterpart. -/
theorem ctxRun_dictionary_origin (modes : Label n → KeyMode) (ideal : ∀ label, modes label ≠ .real)
    (replace : Pqxdh.Bytes → Pqxdh.Bytes) (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (result : PqxdhRecordLiftIdeal.Client n E X × CtxPrivate n)
    (supported : result ∈ support (ctxRun modes replace setup codec route env serverKid bounds mode adversary))
    (label : Label n) (entry : CtxSuccessfulSeal) (member : entry ∈ (result.2.keys label).1.successfulSeals) :
    ∃ handle frame, PqxdhRecordFactsOriginHandles.OwnsLabel result.1.2 label handle ∧
      (some handle, frame) ∈ result.2.base.produced ∧ PqxdhRecordFactsOriginReplay.Matches frame entry := by
  have invariant := ctxRun_invariant modes ideal replace setup codec route env serverKid bounds mode adversary result supported
  obtain ⟨tag, frame, ⟨handle, rfl, owned⟩, produced, matched⟩ := invariant.2.1 label entry member
  exact ⟨handle, frame, owned, produced, matched⟩


end BeaconcryptCore.Computational.CborRawRecordOriginProduced

/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProduced.ctxRun_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProduced.ctxRun_invariant
/-- info: 'BeaconcryptCore.Computational.CborRawRecordOriginProduced.ctxRun_dictionary_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRawRecordOriginProduced.ctxRun_dictionary_origin
