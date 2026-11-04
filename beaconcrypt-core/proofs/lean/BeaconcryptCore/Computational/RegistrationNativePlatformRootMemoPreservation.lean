-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerAcceptMemo
import BeaconcryptCore.Computational.RegistrationNativePublicSourceMemo
/-! Literal source root preparation preserves all earlier successful private roots. The common platform state and indexed private pool remain in the execution; the excluded services are absent by the actual collector's structural zero-query proof. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhSecretInputKdf (RootOutput)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativePlatformServerOpenKernel (handler)
open RegistrationNativePlatformServerOpenSource (callbacks)
open RegistrationServerReferenceMemoReceipt (remember)
open RegistrationNativePublicSourceState (MemoCorrect)
open RegistrationNativePlatformServerOpenServiceFree (IsService)
abbrev Memo := RegistrationNativeReferenceInterpreter.State
variable {n : Nat} {ι KemSK Platform Value : Type} {base : OracleSpec ι}

def Stable (setup : Setup base KemSK) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (before after : Memo) : Prop :=
  MemoCorrect setup seed scalar after ∧ ∀ message root, before message = some root → after message = some root

private theorem effect_extra (request : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (before after : Private n KemSK Memo) (reply : (PqxdhRecordLiftInterface.EnvEffects n).Range request)
    (supported : (reply, after) ∈ support ((RegistrationNativeKemReferenceWorld.effect request).run before)) :
    after.extra = before.extra := by
  change (reply, after) ∈ support ((fun result => (result.1, { before with world := result.2 })) <$>
    (PqxdhRecordLiftWorld.effects request).run before.world) at supported
  rw [support_map] at supported
  obtain ⟨result, _reached, equal⟩ := supported
  exact congrArg (fun value => value.2.extra) equal.symm

private theorem kem_extra (setup : Setup base KemSK)
    (other : QueryImpl RegistrationNativeKemInterface.OtherSpec ProbComp)
    (request : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Domain)
    (before after : Private n KemSK Memo)
    (reply : (RegistrationNativeKemInterface.Spec RegistrationNativeKemInterface.OtherSpec KemSK).Range request)
    (supported : (reply, after) ∈ support ((RegistrationNativeKemReferenceWorld.kem setup other request).run before)) :
    after.extra = before.extra := by
  change (reply, after) ∈ support (do
    let result ← (PqxdhRecordLiftWorld.sampled
      ((RegistrationNativeKemInterface.source setup.baseImpl setup.kem RegistrationNativeKemInterface.OtherSpec
        (fun request => StateT.lift (other request)) request).run ((), before.pool))).run before.world
    pure (result.1.1, { before with world := result.2, pool := result.1.2.2 })) at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨result, _reached, returned⟩ := supported
  rw [mem_support_pure_iff] at returned
  exact congrArg (fun value => value.2.extra) returned

/-- Every actual non-service request preserves correct earlier roots; literal preparation may add its own source-derived entry. -/
theorem query (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Memo)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Memo) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Memo) (StateT Platform ProbComp)))
    (request : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Domain) (allowed : ¬ IsService (KemSK := KemSK) request)
    (before after : Private n KemSK Memo) (previous next : Platform)
    (reply : (RegistrationNativeKemReferenceCompiler.Spec n KemSK).Range request)
    (correct : MemoCorrect setup seed scalar before.extra)
    (supported : ((reply, after), next) ∈ support
      (((handler coins setup (callbacks setup seed scalar remember services demand publication) request).run before).run previous)) :
    Stable setup seed scalar before.extra after.extra := by
  cases request with
  | inl message =>
      change ((reply, after), next) ∈ support (pure
        (((RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message).map (fun _ => message),
          { before with extra := (Function.update before.extra message
            (RegistrationNativeSourceRoot.value setup.source setup.joint setup.dh seed scalar message)) }), previous)) at supported
      rw [mem_support_pure_iff] at supported
      cases supported
      exact ⟨RegistrationNativePublicSourceMemo.update_correct setup seed scalar before.extra correct message,
        RegistrationNativePublicSourceMemo.update_keeps setup seed scalar before.extra correct message⟩
  | inr request => cases request with
    | inl request => cases request with
      | inl _ => exact (allowed trivial).elim
      | inr request => cases request with
        | inl _ => exact (allowed trivial).elim
        | inr request =>
            have actual := RegistrationNativePlatformHashReceipt.native_support coins
              ((RegistrationNativeKemReferenceWorld.effect request).run before) (reply, after) previous next supported
            have same := effect_extra request before after reply actual
            rw [Stable, same]
            exact ⟨correct, fun _ _ stored => stored⟩
    | inr request =>
        have actual := RegistrationNativePlatformHashReceipt.native_support coins
          ((RegistrationNativeKemReferenceWorld.kem setup services.other request).run before) (reply, after) previous next supported
        have same := kem_extra setup services.other request before after reply actual
        rw [Stable, same]
        exact ⟨correct, fun _ _ stored => stored⟩

/-- Arbitrary adaptive service-free source syntax retains all previous root receipts and source correctness in the same platform execution. -/
theorem program (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (services : RegistrationNativeKemReferenceEffects.Callbacks n KemSK Memo)
    (demand : QueryImpl (Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (StateT (Private n KemSK Memo) (StateT Platform ProbComp)))
    (publication : QueryImpl RegistrationBoundPublication.Spec (StateT (Private n KemSK Memo) (StateT Platform ProbComp)))
    (work : OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK) Value)
    (free : work.IsQueryBoundP (IsService (KemSK := KemSK)) 0)
    (before after : Private n KemSK Memo) (previous next : Platform) (reply : Value)
    (correct : MemoCorrect setup seed scalar before.extra)
    (supported : ((reply, after), next) ∈ support
      (((simulateQ (handler coins setup (callbacks setup seed scalar remember services demand publication)) work).run before).run previous)) :
    Stable setup seed scalar before.extra after.extra := by
  induction work using OracleComp.inductionOn generalizing before previous with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact ⟨correct, fun _ _ stored => stored⟩
  | query_bind request continuation ih =>
      rw [isQueryBoundP_query_bind_iff] at free
      have allowed : ¬ IsService (KemSK := KemSK) request := free.1.resolve_right (Nat.lt_irrefl 0)
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨⟨answer, current⟩, atContinuation⟩, called, continued⟩ := supported
      have first := query coins setup seed scalar services demand publication request allowed before current previous
        atContinuation answer correct called
      have rest := ih answer (by simpa only [allowed, ite_false] using free.2 answer)
        current atContinuation first.1 continued
      exact ⟨rest.1, fun message root stored => rest.2 message root (first.2 message root stored)⟩


end BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation.query

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRootMemoPreservation.program
