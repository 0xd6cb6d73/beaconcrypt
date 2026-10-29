-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveFlags

/-! Operational prefix rules compose actual checked preparation receipts through the complete private interpreter. These rules retain the reached World, opaque KEM pool and flags; they do not replace protocol execution by an assumed game relation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordInterpreter (State Provider M)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked Prefix AllPrepared Prepared)
open RegistrationNativeSecretWordLiveFlags (Valid Keeps)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}

private theorem node_inj (left right : (Spec n KemSK).Domain)
    (first : (Spec n KemSK).Range left → OracleComp (Spec n KemSK) Value)
    (second : (Spec n KemSK).Range right → OracleComp (Spec n KemSK) Value)
    (same : (((Spec n KemSK).query left : OracleComp (Spec n KemSK) _) >>= first) =
      (((Spec n KemSK).query right : OracleComp (Spec n KemSK) _) >>= second)) :
    ∃ equal : left = right, equal ▸ first = second := by
  change PFunctor.FreeM.liftBind (P := (Spec n KemSK).toPFunctor) left first = PFunctor.FreeM.liftBind (P := (Spec n KemSK).toPFunctor) right second at same
  exact (PFunctor.FreeM.liftBind_inj (P := (Spec n KemSK).toPFunctor) left right first second).mp same

/-- A checked query and all its actually supported continuations determine preparation safety of the whole query node. -/
theorem query (input : Message → Option Key) (implementation : QueryImpl (Spec n KemSK) (M n KemSK))
    (current : (Spec n KemSK).Domain) (next : (Spec n KemSK).Range current → OracleComp (Spec n KemSK) Value)
    (before : State n KemSK) (prepared : Prepared input current before)
    (later : ∀ result ∈ support ((implementation current).run before), AllPrepared input implementation (next result.1) result.2) :
    AllPrepared input implementation (((Spec n KemSK).query current : OracleComp (Spec n KemSK) _) >>= next) before := by
  intro selected tail after path
  generalize initial : (((Spec n KemSK).query current : OracleComp (Spec n KemSK) _) >>= next) = work at path
  cases path with
  | refl work state =>
      obtain ⟨equal, _continuation⟩ := node_inj current selected next tail initial
      subst selected
      exact prepared
  | step request continuation state reply middle residual final stepped remaining =>
      obtain ⟨equal, continuationEqual⟩ := node_inj current request next continuation initial
      subst request
      cases continuationEqual
      exact later (reply, middle) stepped selected tail after remaining

/-- Preparation safety composes through actual supported bind continuations. -/
theorem bind (input : Message → Option Key) (implementation : QueryImpl (Spec n KemSK) (M n KemSK))
    (work : OracleComp (Spec n KemSK) Value) (next : Value → OracleComp (Spec n KemSK) Next)
    (before : State n KemSK) (safe : AllPrepared input implementation work before)
    (later : ∀ result ∈ support ((simulateQ implementation work).run before), AllPrepared input implementation (next result.1) result.2) :
    AllPrepared input implementation (work >>= next) before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value =>
      simpa only [pure_bind] using later (value, before) (by simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff])
  | query_bind current continuation ih =>
      rw [bind_assoc]
      apply query input implementation current (fun reply => continuation reply >>= next) before
      · exact safe current continuation before (.refl _ _)
      · intro reached stepped
        apply ih reached.1 reached.2
        · intro selected tail after path
          exact safe selected tail after (.step current continuation before reached.1 reached.2 _ after stepped path)
        · intro completed finished
          apply later completed
          simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
          exact ⟨reached, stepped, finished⟩

/-- Every actual reached prefix retains all prior live flags and validity of the fixed optional input. -/
theorem receipts (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work residual : OracleComp (Spec n KemSK) Value) (before after : State n KemSK)
    (path : Prefix (handlerChecked setup wire route sign input inside provider) work before residual after)
    (valid : Valid input before) : Valid input after ∧ Keeps before after := by
  revert valid
  induction path with
  | refl work before => exact fun valid => ⟨valid, fun _ stored => stored⟩
  | step current continuation before reply middle residual after stepped remaining ih =>
      intro valid
      have first := RegistrationNativeSecretWordLiveFlags.query_receipts setup wire route sign input inside provider current before valid (reply, middle) stepped
      have last := ih first.1
      exact ⟨last.1, fun message stored => last.2 message (first.2 message stored)⟩

/-- A structural callback predicate remains true at every actual residual query tree. -/
theorem residual_queries (implementation : QueryImpl (Spec n KemSK) (M n KemSK))
    (predicate : (Spec n KemSK).Domain → Prop) (work residual : OracleComp (Spec n KemSK) Value)
    (before after : State n KemSK) (path : Prefix implementation work before residual after)
    (safe : AllQueriesSatisfy work predicate) : AllQueriesSatisfy residual predicate := by
  revert safe
  induction path with
  | refl work before => exact id
  | step current continuation before reply middle residual after stepped remaining ih =>
      intro safe
      exact ih (((allQueriesSatisfy_query_bind_iff _ _ _).mp safe).2 reply)

/-- A program using only already prepared material descriptors is safe at every reached prefix of the actual interpreter. -/
theorem supplied (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (before : State n KemSK) (valid : Valid input before)
    (safe : AllQueriesSatisfy work (fun query => Prepared input query before)) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) work before := by
  intro current continuation after path
  have allowed := residual_queries _ _ work _ before after path safe
  have prepared := ((allQueriesSatisfy_query_bind_iff _ _ _).mp allowed).1
  have kept := (receipts setup wire route sign input inside provider work _ before after path valid).2
  rcases current with (message | (message | common) | kem) | record
  · trivial
  · intro realized
    exact kept message (prepared realized)
  · trivial
  · trivial
  · trivial

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.bind
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.receipts
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.residual_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.residual_queries
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.supplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLivePrefix.supplied
