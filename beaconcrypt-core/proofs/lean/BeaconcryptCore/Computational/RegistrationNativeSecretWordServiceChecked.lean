-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordService

/-! Checked echo preparation has the same private flag updates as the real alias service. Its finite source interpreter omits only the demand-time flag check. The exact replacement below is available when every actually supported demand has the preparation receipt derived by the frontend's live-Ready invariant. The certificate is an operational query-prefix property, not a security assumption or a final theorem eligibility condition. -/
open OracleComp OracleSpec CoreModels
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked
open RegistrationNativeSecretWordService (Flags Spec Combined handler material)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativePairedChoice (Choice)
open PqxdhJointKdfGame (FixedHkdfSha512NoSaltSource)
variable {n : Nat} {Value : Type}

def checked (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) :
    QueryImpl (Spec n) (StateT Flags (OracleComp Combined))
  | .inl message => handler source input inside (.inl message)
  | .inr message => fun before => match input message with
      | none => pure (none, before)
      | some key => (fun output => (some (Choice.known output), before)) <$> material source inside key

def Prepared (input : Message → Option Key) : (Spec n).Domain → Flags → Prop
  | .inl _, _ => True
  | .inr message, before => (input message).isSome = true → before message = true

/-- One checked callback and the actual flagged callback have the same complete outcome when a valid demand carries its earlier preparation receipt. -/
theorem query_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (query : (Spec n).Domain)
    (before : Flags) (prepared : Prepared input query before) :
    (checked source input inside query).run before = (handler source input inside query).run before := by
  cases query with
  | inl message => rfl
  | inr message =>
      cases realized : input message with
      | none =>
          simp only [checked, handler, StateT.run, realized]
          split <;> rfl
      | some key =>
          have active := prepared (by simp only [realized, Option.isSome_some])
          simp only [checked, handler, StateT.run, realized, active, ite_true]

/-- A supported query prefix retains the exact residual AST and reached private flags. -/
inductive Prefix (implementation : QueryImpl (Spec n) (StateT Flags (OracleComp Combined))) :
    OracleComp (Spec n) Value → Flags → OracleComp (Spec n) Value → Flags → Prop where
  | refl (work : OracleComp (Spec n) Value) (before : Flags) : Prefix implementation work before work before
  | step (query : (Spec n).Domain) (next : (Spec n).Range query → OracleComp (Spec n) Value)
      (before : Flags) (reply : (Spec n).Range query) (middle : Flags)
      (residual : OracleComp (Spec n) Value) (after : Flags)
      (supported : (reply, middle) ∈ support ((implementation query).run before))
      (later : Prefix implementation (next reply) middle residual after) :
      Prefix implementation (((Spec n).query query : OracleComp (Spec n) ((Spec n).Range query)) >>= next)
        before residual after

def AllPrepared (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (work : OracleComp (Spec n) Value) (before : Flags) : Prop :=
  ∀ (query : (Spec n).Domain) (next : (Spec n).Range query → OracleComp (Spec n) Value) (after : Flags),
    Prefix (checked source input inside) work before
      (((Spec n).query query : OracleComp (Spec n) ((Spec n).Range query)) >>= next) after → Prepared input query after

/-- The complete checked execution can substitute the actual flag service after its concrete frontend has derived all reached preparation receipts. -/
theorem program_source (source : FixedHkdfSha512NoSaltSource) (input : Message → Option Key)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (work : OracleComp (Spec n) Value)
    (before : Flags) (prepared : AllPrepared source input inside work before) :
    (simulateQ (checked source input inside) work).run before =
      (simulateQ (handler source input inside) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have current := prepared query next before (.refl _ _)
      rw [← query_source source input inside query before current]
      apply bind_congr_of_forall_mem_support
      intro reached supported
      apply ih reached.1 reached.2
      intro later tail after path
      exact prepared later tail after (.step query next before reached.1 reached.2 _ after supported path)

end BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked.query_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked.program_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordServiceChecked.program_source
