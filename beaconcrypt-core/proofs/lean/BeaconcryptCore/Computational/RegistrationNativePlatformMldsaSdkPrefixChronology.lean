-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaServerChronology

/-! Pure full-pin selection, the actual shared AD hash, external reservation and native peer occupancy contain no signing leaf and retain the exact native receipt list and private signer table. These source-body frames retain all failed outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology
open RegistrationNativeMldsaOpaque (handleSource)
open RegistrationNativePlatformMldsaPublicationChronology (Keeps closed)
open RegistrationNativePlatformMldsaProgram (lift)
variable {n : Nat} {Platform : Type} (source : RegistrationNativeMldsa.Source)

def receipts (before : RegistrationServerFrontendCompiler.State n) := before.world.world.2

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual pure full-pin selection retains the full signing receipt list and private table. -/
theorem pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    Keeps source (receipts (n := n)) (lift (RegistrationNativePlatformSourceBuild.pin coins)) := by
  apply closed
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run] at supported
  cases supported
  rfl

/-- The real shared hash and owned AD continuation retain native signing receipts before reservation. -/
theorem adHash (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (pending : registration.ServerAdHash) :
    Keeps source (receipts (n := n)) (lift (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending)) := by
  apply closed
  intro before previous result supported
  simp only [RegistrationNativePlatformCompletionSdk.nativeAdHash, RegistrationNativePlatformServerSdk.adHash,
    RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  cases same
  change inner.1.2.world.2 = before.world.world.2
  apply RegistrationServerAdHash.state_preserves
    (fun request => do
      let digest ← RegistrationNativePlatformServerCompletion.capability coins
        (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest)))
    (fun current => current.world.2) _ pending before.world inner.1.2 previous inner.2 inner.1.1 called
  intro request current prior reply after next reached
  simp only [RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationWorldServerCompletion.capability, StateT.run,
    bind_pure_comp, simulateQ_map, map_apply, Functor.map_map, support_map] at reached
  obtain ⟨drawn, _sampled, returned⟩ := reached
  exact (congrArg (fun value => value.1.2.world.2) returned).symm

/-- Stateful external capacity reservation retains all native receipts and every actual private signing attempt. -/
theorem reserve (work : StateT Platform ProbComp Bool) :
    Keeps source (receipts (n := n)) (lift (StateT.lift work)) := by
  apply closed
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => receipts value.1.2) same).symm

/-- Actual native occupancy reads no private signing history and preserves the complete native receipt log. -/
theorem present (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (keyId : U64) :
    Keeps source (receipts (n := n)) (lift (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId)) := by
  apply closed
  intro before previous result supported
  simp only [RegistrationNativePlatformCompletionSdk.nativePresent, RegistrationNativePlatformServerSdk.world,
    RegistrationNativePlatformServerCompletion.capability, RegistrationNativePlatformServerCompletion.liftNative,
    RegistrationWorldServerCompletion.capability, StateT.run, simulateQ_map, map_apply, Functor.map_map, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  exact (congrArg (fun value => receipts value.1.2) same).symm

end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.reserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.present' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.present

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.adHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaSdkPrefixChronology.adHash
