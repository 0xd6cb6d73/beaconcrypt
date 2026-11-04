-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomTraceDemand
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
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory
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

variable (physical : QueryImpl (PqxdhRecordLiftInterface.WorldSpec n) (StateT Physical ProbComp))
    (candidate : RegistrationNativeSuffixKeyPrf.Secret)
local notation "backend" => implementationWith setup wire sign seed scalar provider physical id
open RegistrationNativeSecretWordFrontendTrace (Event begin finish)
open RegistrationNativeSecretWordAliasServiceHistory (Holds)
open RegistrationNativeSecretWordRecoveryCompiler (closed literals)
local notation "Trace" => RegistrationNativeSecretWordFrontendTrace.State
local notation "History" => RegistrationNativeSecretWordRecoveryCompiler.State
local notation "recorded" => RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals

private theorem demand_new (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (reply : (RegistrationNativeSecretWordInterface.Spec n KemSK).Range query)
    (before : RegistrationNativeSecretWordFrontendTrace.State) (message : Message)
    (member : Event.demand message ∈ (finish query reply (begin query before)).events) :
    Event.demand message ∈ before.events ∨ query = .inl (.inr (.inl (.inl message))) := by
  by_cases old : Event.demand message ∈ before.events
  · exact Or.inl old
  · apply Or.inr
    rcases query with (prepare | (demand | (publication | environment)) | ((other | key) | (pool | key))) | record
    · simp [begin, finish, old] at member
    · simp only [begin, finish, List.mem_append, List.mem_singleton, Event.demand.injEq, old, false_or] at member
      subst demand
      rfl
    · exact False.elim (old member)
    · rcases environment with coin | capability
      · exact False.elim (old member)
      · cases capability with
        | installServer keyId binding kernel | installBeacon owner shell kernel =>
            cases current : before.current <;> cases reply <;>
              simp_all [begin, finish, RegistrationNativeSecretWordFrontendTrace.installed,
                RegistrationNativeSecretWordFrontendTrace.attempt]
        | _ => exact False.elim (old member)
    · exact False.elim (old member)
    · simp [begin, finish, old] at member
    · exact False.elim (old member)
    · simp [begin, finish, old] at member
    · exact False.elim (old member)

private theorem query_holds (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : Private n KemSK Physical) (observed : Trace) (history : History)
    (valid : Holds input inside candidate observed history.2)
    (reached : ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query ×Private n KemSK Physical) ×History)
    (supported : reached∈support ((simulateQ recorded ((backend query).run before)).run history)) :
    Holds input inside candidate (finish query reached.1.1 (begin query observed)) reached.2.2 := by
  intro message key member realized protectedInput literal
  rcases demand_new query reached.1.1 observed message member with old|current
  · exact RegistrationNativeSecretWordAliasServiceReceipt.program_keeps setup.source candidate
      ((backend query).run before) history reached supported (valid message key old realized protectedInput literal)
  · subst query
    exact RegistrationNativePlatformRecordPartnerExposureClientHistoryReceipt.material_logged setup wire sign seed scalar provider physical
      candidate message key realized protectedInput literal before history reached supported

/-- Every valid protected literal in the actual full Word demand trace enters the same persistent recovery log. -/
theorem program_holds (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : Private n KemSK Physical) (observed : Trace) (history : History)
    (valid : Holds input inside candidate observed history.2)
    (result : ((A ×Trace) ×Private n KemSK Physical) ×History)
    (supported : result∈support ((simulateQ recorded ((simulateQ backend
      ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run observed)).run before)).run history)) :
    Holds input inside candidate result.1.1.2 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before observed history with
  | pure value=>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact valid
  | query_bind query next ih=>
    simp only [simulateQ_bind,simulateQ_spec_query,StateT.run,bind_apply,
      RegistrationNativeSecretWordFrontendTrace.handler,bind_map_left,mem_support_bind_iff] at supported
    obtain ⟨reached,actual,later⟩ := supported
    have nextValid := query_holds setup wire sign seed scalar provider physical candidate query before observed history valid reached actual
    exact ih reached.1.1 reached.1.2 _ reached.2 nextValid later

/-- Cold observer execution of the candidate-independent client supplies all protected literal demand evidence internally. -/
theorem demands_logged (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : Private n KemSK Physical) (result : ((A ×Trace) ×Private n KemSK Physical) ×History)
    (supported : result∈support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial before))) : Holds input inside candidate result.1.1.2 result.2.2 :=
  program_holds setup wire sign seed scalar provider physical candidate work before RegistrationNativeSecretWordFrontendTrace.initial (∅,[])
    (by simp [Holds,RegistrationNativeSecretWordFrontendTrace.initial]) result supported

/-- Actual protected literal installation or attempted installation recovers the candidate in that same original client log. -/
theorem install_logged (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) A)
    (before : Private n KemSK Physical) (result : ((A ×Trace) ×Private n KemSK Physical) ×History)
    (supported : result∈support (RegistrationNativeSecretWordRecoveryBound.logged setup.source candidate
      (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical work
        RegistrationNativeSecretWordFrontendTrace.initial before)))
    (role : PqxdhRecordLiftInterface.Role) (message : Message) (key : Key)
    (member : Event.install role message∈result.1.1.2.events ∨Event.installAttempt role message∈result.1.1.2.events)
    (realized : input message=some key) (protectedInput : inside key.head=true) (literal : key.word=.literal candidate) :
    candidate∈result.2.2 := by
  have free : result.1∈support (RegistrationNativePlatformRecordPartnerExposureClient.client setup wire sign seed scalar provider physical
      work RegistrationNativeSecretWordFrontendTrace.initial before) := by
    apply OracleComp.support_simulateQ_run'_subset recorded _ (∅,[])
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst supported
  have traced : result.1.1∈support (RegistrationNativeSecretWordFrontendTrace.program work) := by
    apply OracleComp.support_simulateQ_run'_subset backend _ before
    rw [StateT.run'_eq,support_map]
    exact Set.mem_image_of_mem Prod.fst free
  have validTrace := RegistrationNativeSecretWordAtomTraceDemand.program work RegistrationNativeSecretWordFrontendTrace.initial
    (by simp [RegistrationNativeSecretWordAtomTraceDemand.Holds,RegistrationNativeSecretWordFrontendTrace.initial]) result.1.1 traced
  have demanded : Event.demand message∈result.1.1.2.events := by
    rcases member with installed|attempted
    · exact validTrace.2 (.install role message) installed message (List.mem_singleton_self _)
    · exact validTrace.2 (.installAttempt role message) attempted message (List.mem_singleton_self _)
  exact demands_logged setup wire sign seed scalar provider physical candidate work before result supported
    message key demanded realized protectedInput literal
end BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.program_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.program_holds
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.demands_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.demands_logged
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.install_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordPartnerExposureClientHistory.install_logged
