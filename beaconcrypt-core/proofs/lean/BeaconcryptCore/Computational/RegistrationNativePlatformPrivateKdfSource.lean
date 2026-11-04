-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion
import BeaconcryptCore.Computational.RegistrationServerRecordWorldSource
/-! Actual private initial/ratchet KDF callbacks compute the fixed source replies without changing operational World or common platform state. Only the explicit existing instrumentation view is applied; native-call and chronological-kind costs remain in the original source execution for separate resource bills. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource
open PqxdhServerAuthExperiment (Setup Codec)
open RegistrationServerRecordWorldSource (project target)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem query (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : RegistrationRecordPrimitives.Spec.Domain) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$> ((RegistrationNativePlatformServerCompletion.records coins setup codec request).run before) =
      simulateQ coins ((target setup.source codec.frameWrite request).run (project before)) := by
  have same := congrArg (fun work => simulateQ coins work)
    (RegistrationServerRecordWorldSource.query setup codec request before)
  simpa only [RegistrationNativePlatformServerCompletion.records,
    RegistrationNativePlatformServerCompletion.liftNative, StateT.run, simulateQ_map] using same

/-- The actual initial64 callback retains its literal source request/reply and the complete common state after the stated private instrumentation view. -/
theorem initial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.SymmetricRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      ((RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), project before) := by
  rw [query]
  simp only [target, StateT.run, RegistrationServerRecordSourceProgram.initial_source,
    simulateQ_pure]
  rfl

/-- The actual ongoing76 callback likewise leaves the operational World and persistent platform state unchanged after its original source accounting is projected. -/
theorem ratchet (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.SymmetricRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      ((RegistrationNativePlatformServerCompletion.records coins setup codec (.ratchetKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.response setup.source.crypto request), project before) := by
  rw [query]
  simp only [target, StateT.run, RegistrationServerRecordSourceProgram.ratchet_source,
    simulateQ_pure]
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource.initial

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource.ratchet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPrivateKdfSource.ratchet
