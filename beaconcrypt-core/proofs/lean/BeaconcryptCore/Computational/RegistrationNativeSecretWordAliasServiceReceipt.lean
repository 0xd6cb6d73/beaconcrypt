-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter

/-! A successful protected literal demand performs its actual symbolic key lookup and appends that literal to the concrete recovery log. The flag receipt is derived from the successful reply. Later callbacks preserve every earlier logged literal, including callbacks that fail or use the ordinary suffix-key oracle. This finite service receipt does not identify an installation with an earlier successful demand; that separate controller provenance must retain the same supported execution. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt
open RegistrationNativeSecretWordRecoveryCompiler (closed literals State)
open RegistrationNativeSecretWordService (Combined)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSuffixKeyPrf (Secret)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem map_apply {Private X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT Private m X) (before : Private) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

private theorem pure_apply {Private X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : Private) : (pure value : StateT Private m X) before = pure (value, before) := rfl

/-- Every actual combined callback preserves the complete earlier literal history. -/
theorem query_keeps (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (query : Combined.Domain) (before : State) (after : Combined.Range query × State)
    (supported : after ∈ support ((RawCtxSelectedQueryTrace.recorded (closed source candidate) literals query).run before)) :
    before.2 ⊆ after.2.2 := by
  simp only [RawCtxSelectedQueryTrace.recorded, StateT.run, mem_support_bind_iff,
    mem_support_pure_iff] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  exact List.subset_append_left _ _

/-- Literal recovery evidence survives the entire supported adaptive continuation. -/
theorem program_keeps (source : FixedHkdfSha512NoSaltSource) (candidate : Secret)
    (work : OracleComp Combined Value) (before : State) (after : Value × State)
    (supported : after ∈ support ((simulateQ (RawCtxSelectedQueryTrace.recorded (closed source candidate) literals) work).run before)) :
    before.2 ⊆ after.2.2 := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact List.Subset.refl _
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨reached, first, later⟩ := supported
      exact List.Subset.trans (query_keeps source candidate query before reached first)
        (ih reached.1 reached.2 later)

/-- A successful protected demand for the candidate literal logs that literal at its actual material query. -/
theorem demand_literal (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (candidate : Secret) (message : Message) (key : Key)
    (realized : input message = some key) (protectedInput : inside key.head = true)
    (literal : key.word = .literal candidate)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (history : State)
    (choice : RegistrationNativePairedChoice.Choice n)
    (after : RegistrationNativeSecretWordInterpreter.State n KemSK) (reached : State)
    (supported : ((some choice, after), reached) ∈ support
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals)
        ((RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider
          (.inl (.inr (.inl (.inl message))))).run before)).run history)) :
    before.flags message = true ∧ reached.2 = history.2 ++ [candidate] := by
  cases prepared : before.flags message with
  | false =>
      simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
        StateT.run, RegistrationNativeSecretWordService.handler, prepared, Bool.false_eq_true,
        ite_false, map_pure, simulateQ_pure, pure_apply, mem_support_pure_iff] at supported
      cases supported
  | true =>
      constructor
      · rfl
      · simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
          StateT.run, RegistrationNativeSecretWordService.handler, prepared, ite_true, realized,
          RegistrationNativeSecretWordService.material_protected setup.source inside key protectedInput,
          simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map, support_map] at supported
        obtain ⟨output, possible, equal⟩ := supported
        cases equal
        simp only [RawCtxSelectedQueryTrace.recorded, literals, StateT.run,
          mem_support_bind_iff, mem_support_pure_iff] at possible
        obtain ⟨result, _, rfl⟩ := possible
        rcases key with ⟨head, word⟩
        dsimp only at literal
        subst word
        rfl

/-- A prepared valid protected demand necessarily returns known material and logs its literal, without a separate successful-reply hypothesis. -/
theorem demand_prepared (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (provider : RegistrationNativeSecretWordInterpreter.Provider KemSK)
    (candidate : Secret) (message : Message) (key : Key)
    (realized : input message = some key) (protectedInput : inside key.head = true)
    (literal : key.word = .literal candidate)
    (before : RegistrationNativeSecretWordInterpreter.State n KemSK) (prepared : before.flags message = true)
    (history : State) (reply : Option (RegistrationNativePairedChoice.Choice n))
    (after : RegistrationNativeSecretWordInterpreter.State n KemSK) (reached : State)
    (supported : ((reply, after), reached) ∈ support
      ((simulateQ (RawCtxSelectedQueryTrace.recorded (closed setup.source candidate) literals)
        ((RegistrationNativeSecretWordInterpreter.handler setup wire route sign input inside provider
          (.inl (.inr (.inl (.inl message))))).run before)).run history)) :
    ∃ output, reply = some (.known output) ∧ reached.2 = history.2 ++ [candidate] := by
  simp only [RegistrationNativeSecretWordInterpreter.handler, RegistrationNativeSecretWordInterpreter.roots,
    StateT.run, RegistrationNativeSecretWordService.handler, prepared, ite_true, realized,
    RegistrationNativeSecretWordService.material_protected setup.source inside key protectedInput,
    simulateQ_map, simulateQ_spec_query, map_apply, Functor.map_map, support_map] at supported
  obtain ⟨output, possible, equal⟩ := supported
  cases equal
  simp only [RawCtxSelectedQueryTrace.recorded, literals, StateT.run,
    mem_support_bind_iff, mem_support_pure_iff] at possible
  obtain ⟨result, _, rfl⟩ := possible
  refine ⟨result.1, rfl, ?_⟩
  rcases key with ⟨head, word⟩
  dsimp only at literal
  subst word
  rfl

end BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.query_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.query_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.program_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.program_keeps
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.demand_literal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.demand_literal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.demand_prepared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordAliasServiceReceipt.demand_prepared
