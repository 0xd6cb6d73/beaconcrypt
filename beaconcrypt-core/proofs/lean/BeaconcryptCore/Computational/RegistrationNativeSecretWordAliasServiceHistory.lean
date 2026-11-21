-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt
import BeaconcryptCore.Computational.RegistrationNativeSecretWordPreparedTransfer

/-! Every valid protected literal descriptor in the actual chronological demand trace has its literal in the concrete recovery log. Preparation is checked at the same supported query prefix, and the later log is persistent. The proof follows the actual observer and flag-enforcing service together rather than treating a demand event as a material query by definition. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordRecoveryCompiler (closed literals)
open RegistrationNativeSecretWordInterpreter (State Provider handler)
open RegistrationNativeSecretWordInterpreterChecked (AllPrepared)
open RegistrationNativeSecretWordFrontendTrace (Event begin finish)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def Holds (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (candidate : Secret) (trace : RegistrationNativeSecretWordFrontendTrace.State) (history : List Secret) : Prop :=
  ∀ message key, Event.demand message ∈ trace.events → input message = some key →
    inside key.head = true → key.word = .literal candidate → candidate ∈ history

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

private theorem query_holds (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : Secret) (query : (RegistrationNativeSecretWordInterface.Spec n KemSK).Domain)
    (before : State n KemSK) (observed : RegistrationNativeSecretWordFrontendTrace.State)
    (history : RegistrationNativeSecretWordRecoveryCompiler.State)
    (valid : Holds input inside candidate observed history.2)
    (prepared : RegistrationNativeSecretWordInterpreterChecked.Prepared input query before)
    (reached : ((RegistrationNativeSecretWordInterface.Spec n KemSK).Range query × State n KemSK) ×
      RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : reached ∈ support ((simulateQ (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals)
      ((handler setup wire route sign input inside provider query).run before)).run history)) :
    Holds input inside candidate (finish query reached.1.1 (begin query observed)) reached.2.2 := by
  intro message key member realized protectedInput literal
  rcases demand_new query reached.1.1 observed message member with old | current
  · exact RegistrationNativeSecretWordAliasServiceReceipt.program_keeps setup.source candidate
      ((handler setup wire route sign input inside provider query).run before) history reached supported
      (valid message key old realized protectedInput literal)
  · subst query
    have live : before.flags message = true := prepared (by simp only [realized, Option.isSome_some])
    obtain ⟨_output, _reply, logged⟩ := RegistrationNativeSecretWordAliasServiceReceipt.demand_prepared
      setup wire route sign input inside provider candidate message key realized protectedInput literal
      before live history reached.1.1 reached.1.2 reached.2 supported
    rw [logged]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let result ← work before; next result.1 result.2) := rfl

/-- Actual prepared query prefixes turn every protected literal demand in the complete observer into persistent concrete recovery evidence. -/
theorem program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (candidate : Secret) (work : OracleComp (RegistrationNativeSecretWordInterface.Spec n KemSK) Value)
    (before : State n KemSK) (observed : RegistrationNativeSecretWordFrontendTrace.State)
    (history : RegistrationNativeSecretWordRecoveryCompiler.State)
    (valid : Holds input inside candidate observed history.2)
    (prepared : AllPrepared input (handler setup wire route sign input inside provider) work before)
    (result : ((Value × RegistrationNativeSecretWordFrontendTrace.State) × State n KemSK) ×
      RegistrationNativeSecretWordRecoveryCompiler.State)
    (supported : result ∈ support ((simulateQ (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals)
      ((simulateQ (handler setup wire route sign input inside provider)
        ((simulateQ RegistrationNativeSecretWordFrontendTrace.handler work).run observed)).run before)).run history)) :
    Holds input inside candidate result.1.1.2 result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before observed history with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact valid
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run, state_bind_apply,
        RegistrationNativeSecretWordFrontendTrace.handler, bind_map_left, simulateQ_bind,
        simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reached, actual, later⟩ := supported
      have head := prepared query next before (.refl _ _)
      have nextValid := query_holds setup wire route sign input inside provider candidate query before observed history valid head reached actual
      have opened : reached.1 ∈ support ((handler setup wire route sign input inside provider query).run before) := by
        apply OracleComp.support_simulateQ_run'_subset (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals) _ history
        rw [StateT.run'_eq, support_map]
        exact Set.mem_image_of_mem Prod.fst actual
      apply ih reached.1.1 reached.1.2 _ reached.2 nextValid _ later
      intro current tail after path
      exact prepared current tail after (.step query next before reached.1.1 reached.1.2 _ after opened path)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceHistory.program
