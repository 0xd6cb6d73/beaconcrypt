-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreter

/-! The finite checked source closure uses the same ordinary World, KEM provider and exact prepare flag updates as the actual combined alias interpreter. Only its material flag read is omitted. Actual live-Ready receipts at supported query prefixes suffice to recover the full stateful interpreter, including every original failure and all state coordinates. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked
open RegistrationNativeSecretWordInterpreter (State M Provider roots handler)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open PqxdhServerAuthExperiment (Setup)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

noncomputable def handlerChecked (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK) :
    QueryImpl (Spec n KemSK) (M n KemSK)
  | .inl (.inl message) => roots (RegistrationNativeSecretWordServiceChecked.checked (n := n) setup.source input inside (.inl message))
  | .inl (.inr (.inl (.inl message))) => roots (RegistrationNativeSecretWordServiceChecked.checked (n := n) setup.source input inside (.inr message))
  | query => handler setup wire route sign input inside provider query

def Prepared (input : Message → Option Key) : (Spec n KemSK).Domain → State n KemSK → Prop
  | .inl (.inr (.inl (.inl message))), before => (input message).isSome = true → before.flags message = true
  | _, _ => True

/-- The exact whole callback agrees once its actual material demand carries its derived live preparation flag. -/
theorem query_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (query : (Spec n KemSK).Domain) (before : State n KemSK) (prepared : Prepared input query before) :
    (handlerChecked setup wire route sign input inside provider query).run before =
      (handler setup wire route sign input inside provider query).run before := by
  rcases query with (message | (message | common) | kem) | record
  · rfl
  · simp only [handlerChecked, handler, roots, StateT.run]
    congr 1
    simpa only [StateT.run] using RegistrationNativeSecretWordServiceChecked.query_source setup.source input inside (.inr message) before.flags prepared
  · rfl
  · rfl
  · rfl

inductive Prefix (implementation : QueryImpl (Spec n KemSK) (M n KemSK)) :
    OracleComp (Spec n KemSK) Value → State n KemSK → OracleComp (Spec n KemSK) Value → State n KemSK → Prop where
  | refl (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) : Prefix implementation work before work before
  | step (query : (Spec n KemSK).Domain) (next : (Spec n KemSK).Range query → OracleComp (Spec n KemSK) Value)
      (before : State n KemSK) (reply : (Spec n KemSK).Range query) (middle : State n KemSK)
      (residual : OracleComp (Spec n KemSK) Value) (after : State n KemSK)
      (supported : (reply, middle) ∈ support ((implementation query).run before))
      (later : Prefix implementation (next reply) middle residual after) :
      Prefix implementation (((Spec n KemSK).query query : OracleComp (Spec n KemSK) ((Spec n KemSK).Range query)) >>= next)
        before residual after

def AllPrepared (input : Message → Option Key) (implementation : QueryImpl (Spec n KemSK) (M n KemSK))
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) : Prop :=
  ∀ (query : (Spec n KemSK).Domain) (next : (Spec n KemSK).Range query → OracleComp (Spec n KemSK) Value) (after : State n KemSK),
    Prefix implementation work before (((Spec n KemSK).query query : OracleComp (Spec n KemSK) ((Spec n KemSK).Range query)) >>= next) after →
      Prepared input query after

/-- The whole mixed checked execution recovers the actual flag service after the frontend derives its reached live-Ready receipts. -/
theorem program_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : beaconcrypt_core.registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK)
    (prepared : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before) :
    (simulateQ (handlerChecked setup wire route sign input inside provider) work).run before =
      (simulateQ (handler setup wire route sign input inside provider) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have current := prepared query next before (.refl _ _)
      rw [← query_source setup wire route sign input inside provider query before current]
      apply bind_congr_of_forall_mem_support
      intro reached supported
      apply ih reached.1 reached.2
      intro later tail after path
      exact prepared later tail after (.step query next before reached.1 reached.2 _ after supported path)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordInterpreterChecked.program_source
