-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAgreement
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Owned replay and the real stateful allocator precede the actual open indexed collector. Closing the reached common-monad run restores the same native one-use capability without a freshness, allocation-success or whole-handler premise. The actual private provider/memo state remains in the source execution. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAfterAuthentication
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformServerOpenControl
open RegistrationNativePlatformServerOpenKernel (handler)
open RegistrationNativePlatformServerOpenSource (callbacks)
variable {n : Nat} {ι KemSK Extra : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

private theorem sdk_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (reserve : m Bool) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : RegistrationServerFrontendCompiler.State n) :
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run before =
      (if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
       else do
         let admitted ← reserve
         if admitted then do
           let completed ← simulateQ coins ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before)
           match completed.1 with
           | .fail error => pure (.fail error, completed.2)
           | .div => pure (.div, completed.2)
           | .ok (.ServerComplete accepted) => simulateQ coins ((RegistrationServerNativeSource.retain created accepted).run completed.2)
           | .ok _ => pure (.ok none, completed.2)
         else pure (.ok none, before)) := by
  simp only [RegistrationNativePlatformServerSdk.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · rw [StateT.run_bind, StateT.run_lift]
    simp only [bind_assoc, pure_bind]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      rw [StateT.run_bind]
      apply bind_congr
      rintro ⟨completed, current⟩
      cases completed with
      | fail error | div => rfl
      | ok effect => cases effect <;> rfl

theorem native (coins : QueryImpl unifSpec m)
    (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (created : PqxdhLiveServerConstruction.Created Unit) (scalar : PqxdhJointGapDh.ScalarBytes)
    (remember : Extra → Message → Option RootOutput → Extra)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n)) (StateT (Private n KemSK Extra) m))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) m))
    (reserve : m Bool) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n KemSK Extra) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar)) <$>
      (close (afterAuthentication (handler coins setup (callbacks setup created.seed scalar remember services demand publication))
        (StateT.lift reserve) setup checks packet authenticated)).run before =
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve)
      representation created packet authenticated).run
      (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh created.seed scalar
  change Prod.map id (project roots) <$> _ =
    (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated).run (project roots before)
  unfold afterAuthentication
  rw [close_bind, StateT.run_bind, close_get, pure_bind, sdk_run]
  have consumed : (project roots before).consumed = before.1.consumed := rfl
  rw [consumed]
  by_cases replayed : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ↓reduceIte, close_pure, map_pure]
    rfl
  · have fresh := Bool.eq_false_iff.mpr replayed
    simp only [fresh, Bool.false_eq_true, ↓reduceIte]
    rw [close_bind, StateT.run_bind, close_reserve, map_bind, bind_map_left]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => simp only [Bool.false_eq_true, ↓reduceIte, close_pure, map_pure]; rfl
    | true =>
      simp only [↓reduceIte]
      rw [close_bind, StateT.run_bind, map_bind,
        ← RegistrationNativePlatformServerOpenAgreement.native coins setup checks representation correct created scalar remember services demand publication packet authenticated before fresh, bind_map_left]
      apply bind_congr
      rintro ⟨accepted, current⟩
      cases accepted with
      | fail error | div => simp only [close_pure, map_pure, Prod.map_def, id_eq, RegistrationServerReferenceSourceClient.restore, roots]
      | ok accepted => cases accepted with
        | none => simp only [close_pure, map_pure, Prod.map_def, id_eq, RegistrationServerReferenceSourceClient.restore, roots]
        | some ready => exact RegistrationNativePlatformServerOpenAgreement.retain_native coins roots ready current created

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAfterAuthentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAfterAuthentication.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAfterAuthentication.native
