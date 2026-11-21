-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenAuthentication
import BeaconcryptCore.Computational.RegistrationNativePlatformHashReceipt
import BeaconcryptCore.Computational.RegistrationServerReferenceMemoReceipt
/-! Successful corrected indexed agreement has an actual private root memo receipt. The source collector, common platform poststate and memo update remain in the same run; no successful-prepare or global source-security premise is used. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRelatedFamily (Message)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationServerReferenceMemoReceipt (MemoStore remember)
open RegistrationNativePlatformServerOpenControl (State close)
open RegistrationNativePlatformServerOpenKernel (handler agreement)
open RegistrationNativePlatformServerOpenSource (callbacks)
variable {n : Nat} {ι KemSK Extra Platform : Type} {base : OracleSpec ι} [MemoStore Extra]

omit [MemoStore Extra] in
private theorem close_apply {Value : Type}
    (work : RegistrationNativePlatformServerReferenceAccept.PublicM
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)) Value) (before : State n KemSK Extra) :
    (close work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (RegistrationNativePlatformServerOpenKernel.closeEnvironment (work.run before.1)).run before.2 := rfl

omit [MemoStore Extra] in
private theorem environment_apply {Value : Type}
    (work : StateT RegistrationServerReferenceCompiler.Environment
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)) Value)
    (before : RegistrationNativeKemReferenceBackend.State n KemSK Extra) :
    (RegistrationNativePlatformServerOpenKernel.closeEnvironment work).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$> ((work.run before.1).run before.2) := rfl

/-- The literal corrected agreement retains its full indexed private state and public platform history after exact source interpretation. -/
theorem agreement_run (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : State n KemSK Extra) (previous : Platform) :
    ((close (agreement (handler coins setup (callbacks setup seed scalar remember services demand publication))
      setup checks packet authenticated)).run before).run previous =
      (fun result => ((result.1.1, (before.1, result.1.2)), result.2)) <$>
        (simulateQ coins ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services
          packet authenticated).run before.2)).run previous := by
  have compared := congrArg (fun work => (fun result => (result.1, (before.1, result.2))) <$> work)
    (RegistrationNativePlatformServerOpenSource.source coins setup checks seed scalar remember services demand publication packet authenticated before.2)
  have folded : (close (agreement (handler coins setup (callbacks setup seed scalar remember services demand publication))
      setup checks packet authenticated)).run before =
      (fun result => (result.1, (before.1, result.2))) <$>
        simulateQ coins ((RegistrationServerOpenReferenceSourceStage.agreement setup checks seed scalar remember services
          packet authenticated).run before.2) := by
    rw [close_apply, RegistrationNativePlatformServerOpenKernel.agreement_factor, StateT.run_lift]
    simpa only [environment_apply, bind_pure_comp, StateT.run_map, Functor.map_map] using compared
  have evaluated := congrArg (fun action => action.run previous) folded
  simpa only [StateT.run_map] using evaluated

/-- Every returned Ready is backed by its actual source root in the same reached private memo, with the complete caller state preserved. -/
theorem agreement_receipt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Extra)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Extra) (StateT Platform ProbComp)))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (ready : RegistrationServerReferenceRoot.Ready)
    (before after : State n KemSK Extra) (previous next : Platform)
    (supported : ((.ok (some ready), after), next) ∈ support
      (((close (agreement (handler coins setup (callbacks setup seed scalar remember services demand publication))
        setup checks packet authenticated)).run before).run previous)) :
    after.1 = before.1 ∧ ∃ root, MemoStore.read after.2.2.extra ready.reference = some root ∧
      RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar ready.reference = some root := by
  rw [agreement_run, support_map] at supported
  obtain ⟨⟨⟨reply, current⟩, last⟩, reached, equal⟩ := supported
  rcases before with ⟨front, initial⟩
  rcases after with ⟨final, after⟩
  simp only [Prod.mk.injEq] at equal
  rcases equal with ⟨⟨rfl, ⟨rfl, rfl⟩⟩, rfl⟩
  have actual := RegistrationNativePlatformHashReceipt.native_support coins _ _ previous last reached
  exact ⟨rfl, RegistrationServerReferenceMemoReceipt.agreement setup checks seed scalar services packet authenticated
    ready initial current actual⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo.agreement_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo.agreement_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo.agreement_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenMemo.agreement_receipt
