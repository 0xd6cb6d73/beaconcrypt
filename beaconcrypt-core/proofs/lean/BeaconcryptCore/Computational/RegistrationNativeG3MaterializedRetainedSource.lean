-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeG3RetainedFrontendRun
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectRun
import BeaconcryptCore.Computational.RegistrationNativeG3MaterializedDirectWorld

/-! The actual complete known108 materialized native frontend, with its original chronological observer and reached startup World/cache, is the original open retained compiler closed by the same actual provider and selective direct108-byte service. Original demand bounds discharge all finite service capacity internally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Slot)
open PqxdhDeploymentHiddenLayout (Material)
variable {n : Nat} {ι KemSK ProviderState Value : Type} {base : OracleSpec ι}

noncomputable def ordinary (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n) : RegistrationNativePublicInterpreter.State n KemSK :=
  ⟨RegistrationNativeReferenceInterpreter.initial, world, frame.1.pool, frame.1.receipts⟩

noncomputable def sourceFrame (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n) : RegistrationNativeG3RetainedFrontendSource.Frame n KemSK ProviderState :=
  ((ordinary frame world, frame.1.provider), (RegistrationNativeHiddenService.initial, frame.2))

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
  (route : RawCtxServerRouting.SenderDecoder)
  (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
  (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
  (candidate : PqxdhKemIndCca.MlKemSharedSecret)
  (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)

/-- The complete actual bounded frontend has the original retained compiler source, preserving every original client observation and the reached startup cache. -/
theorem program_source (materials : Slot n → Material) (seeds : RegistrationNativeG3AuditedWorld.Seeds n)
    (work : OracleComp (RegistrationNativePublicFrontend.Spec n KemSK) Value)
    (bounded : work.IsQueryBoundP (RegistrationNativePublicCaps.IsDemand (KemSK := KemSK)) n)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State n) :
    (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider) work).run'
      (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
        (RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider work
          (ordinary frame world, frame.1.provider))).run' (RegistrationNativeHiddenService.initial, frame.2) := by
  have material := congrArg (Functor.map Prod.fst)
    (RegistrationNativeG3MaterializedDirectRun.program_source materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds work n bounded
      (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) (by simp [RegistrationNativeG3AuditTraceRun.cold, RegistrationNativeHiddenService.initial]))
  have normalized := RegistrationNativeG3MaterializedDirectWorld.values_source materials setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider seeds work
    (RegistrationNativeG3AuditTraceRun.cold frame ∅, world)
  have retained := RegistrationNativeG3RetainedFrontendRun.values_source setup wire route sign seed scalar candidate provider materials seeds work (sourceFrame frame world)
  have result := material.trans (normalized.trans (by
    simpa only [sourceFrame, ordinary, RegistrationNativeG3RetainedFrontendSource.project,
      RegistrationNativeG3LocalKeys.project, RegistrationNativeG3AuditTraceRun.cold, RegistrationNativeHiddenService.initial] using retained))
  simpa only [StateT.run'_eq, ordinary, RegistrationNativeHiddenService.initial] using result

/-- The full original registration ledger and actual G2 chronology derive the complete retained-service source from original Respects alone. -/
theorem frontend_source (budget : PqxdhDeploymentInterface.Budget)
    (materials : Slot (budget.cap 4 + budget.cap 5) → Material)
    (seeds : RegistrationNativeG3AuditedWorld.Seeds (budget.cap 4 + budget.cap 5))
    (checks : Checks) (source : RegistrationNativeMldsa.Source)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (serverKeyId : U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) Value) (bounded : RegistrationNativeInterface.Respects budget work)
    (front : RegistrationNativePublicFrontend.State source)
    (frame : RegistrationNativeSelectiveHiddenInterpreter.State (budget.cap 4 + budget.cap 5) KemSK ProviderState)
    (world : PqxdhRecordLiftWorld.State (budget.cap 4 + budget.cap 5)) :
    (simulateQ (RegistrationNativeG3MaterializedLocal.handler true materials seeds setup (RegistrationNativeWire.ledgerCodec wire) route wire sign seed scalar candidate provider)
      (RegistrationNativeG2Trace.program
        (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))).run'
          (RegistrationNativeG3AuditTraceRun.cold frame ∅, world) =
      (simulateQ (RegistrationNativeG3RetainedCallbacks.keys setup.source
        (RegistrationNativeRelatedFamily.input setup.joint setup.dh seed scalar)
        (RegistrationNativeKeyFamilyPreparation.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))) candidate materials seeds)
        (RegistrationNativeG3RetainedFrontendRun.retainedClient setup wire route sign provider
          (RegistrationNativeG2Trace.program
            (RegistrationNativePublicFrontend.run setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work front))
          (ordinary frame world, frame.1.provider))).run' (RegistrationNativeHiddenService.initial, frame.2) := by
  apply program_source
  apply RegistrationNativeG2Trace.program_bound
  exact RegistrationNativePublicCaps.run_bound setup checks wire source sign selectedOwner selectedAccept publicPrekey serverKeyId bounds mode work budget bounded front

end BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource.program_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource.frontend_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeG3MaterializedRetainedSource.frontend_source
