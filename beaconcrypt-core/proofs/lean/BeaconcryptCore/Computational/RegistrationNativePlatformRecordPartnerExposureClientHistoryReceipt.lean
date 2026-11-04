-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClient
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordRecoveryBound
/-! A protected material request in the literal candidate-independent client starts with its actual Combined key query, before cache reads or allocation refusal. Its literal therefore enters the same persistent ordinary recovery log. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativePlatformRecordPartnerExposureClient (Roots Private Shared lowerWith implementationWith)
variable {n : Nat} {I KemSK Physical A : Type} {base : OracleSpec I}
private theorem bind_apply {S X Y : Type} {m : Type →Type} [Monad m]
    (work : StateT S m X) (next : X →StateT S m Y) (before : S) :
    (work >>=next) before=(work before >>=fun result=>next result.1 result.2) := rfl
private theorem map_apply {S X Y : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (observe : X →Y) (work : StateT S m X) (before : S) :
    (observe <$>work) before=Prod.map observe id <$>work before := StateT.run_map _ _ _
private theorem lift_apply {S X : Type} {m : Type →Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) : (StateT.lift work : StateT S m X) before=(fun value=>(value,before)) <$>work := bind_pure_comp _ _

variable (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest →ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
local notation "input" => RegistrationNativeSecretWordMessage.input setup.joint setup.dh seed scalar
local notation "inside" => RegistrationNativeSecretWordProtection.inside (setup.joint.staticDh seed (setup.dh.publicKey scalar))

/-- The actual lower material leaf emits its protected key before any lookup, sampling or overflow branch. -/
theorem lower_head (message : Message) (key : Key)
    (realized : input message=some key) (protectedInput : inside key.head=true)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n) :
    ∃next : PqxdhServerAuthKeySchedule.Output →OracleComp (Shared n)
        (Option (RegistrationNativePairedChoice.Choice n) × (RegistrationNativeSecretWordInterpreter.State n KemSK ×Roots n)),
      (lowerWith setup wire sign seed scalar provider id (.inl (.inr (.inl (.inl message))))).run before=
        (((Shared n).query (.inl (.inl (.inr key))) : OracleComp (Shared n) PqxdhServerAuthKeySchedule.Output) >>=next) := by
  rw [RegistrationNativePlatformRecordPartnerExposureClient.lower_run]
  simp only [RegistrationNativePlatformLorOpenDictionary.handler,RegistrationNativePlatformLorOpenDictionary.root,StateT.run,
    simulateQ_map,simulateQ_spec_query,map_apply,RegistrationNativePlatformRecordPartnerExposureClient.closing,
    RegistrationNativePlatformRecordPartnerExposureRoot.handler,RegistrationNativePlatformRecordPartnerExposureRoot.demand,
    id_eq,realized,protectedInput,ite_true,map_bind,Functor.map_map]
  exact ⟨_,rfl⟩

/-- The complete candidate-independent client retains that same leading query with its original private and physical state. -/
theorem material_head (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (message : Message) (key : Key) (realized : input message=some key) (protectedInput : inside key.head=true)
    (before : Private n KemSK Physical) :
    ∃next : PqxdhServerAuthKeySchedule.Output →OracleComp Combined
        (Option (RegistrationNativePairedChoice.Choice n) × Private n KemSK Physical),
      (implementationWith setup wire sign seed scalar provider physical id (.inl (.inr (.inl (.inl message))))).run before=
        ((Combined.query (.inl (.inr key)) : OracleComp Combined _) >>=next) := by
  obtain ⟨next,source⟩ := lower_head setup wire sign seed scalar provider message key realized protectedInput before.1
  rw [implementationWith,QueryImpl.flattenStateT_mapStateTBase_apply_run,source]
  simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformRecordPartnerExposureClient.ambient,
    StateT.run,bind_apply,lift_apply,map_bind,bind_map_left]
  exact ⟨_,rfl⟩
private theorem head_logged (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (candidate : RegistrationNativeSuffixKeyPrf.Secret) (key : Key) (literal : key.word=.literal candidate)
    (next : PqxdhServerAuthKeySchedule.Output →OracleComp Combined A)
    (before : RegistrationNativeSecretWordRecoveryCompiler.State) (result : A ×RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : result∈support ((simulateQ (RawCtxSelectedQueryTrace.recorded
      (RegistrationNativeSecretWordRecoveryCompiler.closed source candidate) RegistrationNativeSecretWordRecoveryCompiler.literals)
      ((Combined.query (.inl (.inr key)) : OracleComp Combined _) >>=next)).run before)) : candidate∈result.2.2 := by
  rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
  obtain ⟨reached,called,later⟩ := supported
  have member : candidate∈reached.2.2 := by
    simp only [RawCtxSelectedQueryTrace.recorded,StateT.run,mem_support_bind_iff,mem_support_pure_iff] at called
    obtain ⟨reply,_replied,equal⟩ := called
    cases equal
    rcases key with ⟨head,word⟩
    change word=.literal candidate at literal
    subst word
    simp only [RegistrationNativeSecretWordRecoveryCompiler.literals,RegistrationNativeSecretWord.literals]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  exact RegistrationNativeSecretWordAliasServiceReceipt.program_keeps source candidate (next reached.1) reached.2 result later member

/-- Every protected literal demand logs that literal in the same ordinary recovery execution, including refusals and cache hits. -/
theorem material_logged (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (candidate : RegistrationNativeSuffixKeyPrf.Secret) (message : Message) (key : Key)
    (realized : input message=some key) (protectedInput : inside key.head=true) (literal : key.word=.literal candidate)
    (before : Private n KemSK Physical) (history : RegistrationNativeSecretWordRecoveryCompiler.State)
    (result : (Option (RegistrationNativePairedChoice.Choice n) ×Private n KemSK Physical) ×RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : result∈support ((simulateQ (RawCtxSelectedQueryTrace.recorded
      (RegistrationNativeSecretWordRecoveryCompiler.closed setup.source candidate) RegistrationNativeSecretWordRecoveryCompiler.literals)
      ((implementationWith setup wire sign seed scalar provider physical id (.inl (.inr (.inl (.inl message))))).run before)).run history)) :
    candidate∈result.2.2 := by
  obtain ⟨next,source⟩ := material_head setup wire sign seed scalar provider physical message key realized protectedInput before
  rw [source] at supported
  exact head_logged setup.source candidate key literal next history result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.lower_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.lower_head
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.material_head' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.material_head

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.material_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.material_logged
