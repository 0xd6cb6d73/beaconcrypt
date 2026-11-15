-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion
import BeaconcryptCore.Computational.RegistrationServerRecordWorldView
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
open RegistrationServerRecordWorldSource (project)
variable {n : Nat} {Auxiliary ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- The actual initial64 callback retains its literal source request/reply and the complete common state after the stated private instrumentation view. -/
theorem initial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.InitialRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      ((RegistrationNativePlatformServerCompletion.records coins setup codec (.initialKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request), project before) := by
  have actual : (RegistrationWorldRecords.handler setup codec (.initialKdf request)).run before =
      pure (.Some (RawCtxSourceHkdf.initialResponse setup.source.crypto request),
        { before with recordRequests := before.recordRequests ++
          [RegistrationWorldAgreement.recordCall (.initialKdf request)] }) := rfl
  change Prod.map id project <$> simulateQ coins
    ((RegistrationWorldRecords.handler setup codec (.initialKdf request)).run before) = _
  rw [actual, simulateQ_pure, map_pure]
  rfl

/-- The actual ongoing76 callback likewise leaves the operational World and persistent platform state unchanged after its original source accounting is projected. -/
theorem ratchet (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (request : ratchet.SymmetricRatchetKdfRequest) (before : RegistrationWorldAgreement.State n Auxiliary) :
    Prod.map id project <$>
      ((RegistrationNativePlatformServerCompletion.records coins setup codec (.ratchetKdf request)).run before) =
      pure (.Some (RawCtxSourceHkdf.response setup.source.crypto request), project before) := by
  let kind := RawCtxMixedOwner.callKind (.inl request)
  let primitive := ({ before.world.1.primitive.1 with
    native := Function.update before.world.1.primitive.1.native kind
      (before.world.1.primitive.1.native kind + 1) }, before.world.1.primitive.2)
  let after : RegistrationWorldAgreement.State n Auxiliary :=
    { before with
      recordRequests := before.recordRequests ++ [RegistrationWorldAgreement.recordCall (.ratchetKdf request)]
      world := ({ before.world.1 with primitive := primitive }, before.world.2) }
  have actual : (RegistrationWorldRecords.handler setup codec (.ratchetKdf request)).run before =
      pure (.Some (RawCtxSourceHkdf.response setup.source.crypto request), after) := rfl
  change Prod.map id project <$> simulateQ coins
    ((RegistrationWorldRecords.handler setup codec (.ratchetKdf request)).run before) = _
  rw [actual, simulateQ_pure, map_pure]
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
