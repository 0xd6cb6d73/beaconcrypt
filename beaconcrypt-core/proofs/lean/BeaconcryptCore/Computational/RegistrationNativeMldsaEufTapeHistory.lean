-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaEufTape

/-! Complete ordinary-EUF signing history is contained in the eager challenge router's raw same-key attempt history, including failures. The source table restoration retains this raw history exactly. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaEufTape (Pool Token handler evaluate record)
open RegistrationNativeMldsaOpaque (handleSource Attempt)
open RegistrationNativeMldsaCandidate (requestsFor)
open RegistrationNativeMldsaChosenProgram (interpreted)
variable {Value : Type} (source : Source)

def Logged (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before : Pool source)
    (history : List registration.MldsaSigningRequest) : Prop :=
  ∀ request ∈ history, request ∈ requestsFor publicKey before.signing

private theorem requests_append (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before after : List Attempt) :
    requestsFor publicKey (before ++ after) = requestsFor publicKey before ++ requestsFor publicKey after := by
  simp only [requestsFor, List.filter_append, List.map_append]

private theorem logged_record (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source publicKey before history)
    (credential : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) :
    Logged source publicKey (RegistrationNativeMldsaEufTape.record source before credential request reply) history := by
  intro asked member
  have previous := old asked member
  change asked ∈ requestsFor publicKey (before.signing ++ [_])
  rw [requests_append]
  exact List.mem_append_left _ previous

private theorem recorded (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before : Pool source)
    (credential : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) (matching : request.public_key = publicKey) :
    request ∈ requestsFor publicKey (RegistrationNativeMldsaEufTape.record source before credential request reply).signing := by
  change request ∈ requestsFor publicKey (before.signing ++ [_])
  rw [requests_append]
  apply List.mem_append_right
  simp only [requestsFor, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, matching, beq_self_eq_true, ite_true]
  exact List.mem_cons_self

private theorem logged_sign (credential : Credential source) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) (matching : request.public_key = credential.publicKey) :
    Logged source credential.publicKey (RegistrationNativeMldsaEufTape.record source before handle request reply) (history ++ [request]) := by
  intro asked member
  rcases List.mem_append.mp member with previous | current
  · exact logged_record source credential.publicKey before history old handle request reply asked previous
  · have same : asked = request := List.mem_singleton.mp current
    subst asked
    exact recorded source credential.publicKey before handle request reply matching


/-- Every actual external signing request occurs in the literal raw attempt log at the same complete operands. -/
theorem query_logged (challenge : Credential source) (tape : List (Option (Token source)))
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source challenge.publicKey before history)
    (result : ((RegistrationNativeMldsaProgram.Spec (handleSource source)).Range query × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source challenge
      ((handler source challenge.publicKey tape query).run before) history)) :
    Logged source challenge.publicKey result.1.2 result.2 := by
  classical
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, interpreted,
        RegistrationNativeMldsaChosen.coins, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeMldsaEuf.handler, StateT.run_map, StateT.run_lift,
        bind_pure_comp, Functor.map_map, support_map] at supported
      obtain ⟨reply, _drawn, same⟩ := supported
      cases same
      exact old
  | inr query => cases query with
    | generate =>
        change result ∈ support (pure (RegistrationNativeMldsaEufTape.birth source challenge.publicKey before
          ((tape[before.attempts]?).getD none), history)) at supported
        have same := Set.mem_singleton_iff.mp supported
        cases same
        cases (tape[before.attempts]?).getD none <;> exact old
    | sign handle request =>
        simp only [handler, StateT.run] at supported
        cases found : before.keys[handle.secret]? with
        | none =>
            simp only [found, interpreted, simulateQ_pure, StateT.run_pure,
              support_pure, Set.mem_singleton_iff] at supported
            cases supported
            exact logged_record source challenge.publicKey before history old handle request _
        | some key =>
            simp only [found] at supported
            cases key with
            | some ordinary =>
                simp only [Option.elim_some] at supported
                by_cases owned : handle.publicKey = ordinary.publicKey
                · simp only [owned, ite_true, interpreted, simulateQ_map, StateT.run_map] at supported
                  change result ∈ support ((fun inner => (((inner.1, (0 : Nat)), record source before handle request inner.1), inner.2)) <$>
                    interpreted source challenge (RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsa.owned source ordinary request)) history) at supported
                  rw [RegistrationNativeMldsaChosenProgram.ordinary] at supported
                  simp only [Functor.map_map, support_map] at supported
                  obtain ⟨reply, _signed, same⟩ := supported
                  cases same
                  exact logged_record source challenge.publicKey before history old handle request _
                · simp only [owned, ite_false, interpreted, simulateQ_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at supported
                  cases supported
                  exact logged_record source challenge.publicKey before history old handle request _
            | none =>
                simp only [Option.elim_none] at supported
                by_cases owned : handle.publicKey = challenge.publicKey
                · simp only [owned, ite_true, interpreted, simulateQ_map, simulateQ_spec_query,
                    RegistrationNativeMldsaEuf.handler, StateT.run_map] at supported
                  by_cases matching : request.public_key = challenge.publicKey
                  · rw [RegistrationNativeMldsaEuf.signing_match source challenge request history matching] at supported
                    simp only [Functor.map_map, support_map] at supported
                    obtain ⟨reply, _signed, same⟩ := supported
                    cases same
                    exact logged_sign source challenge before history old handle request reply matching
                  · rw [RegistrationNativeMldsaEuf.signing_mismatch source challenge request history matching] at supported
                    simp only [map_pure, support_pure, Set.mem_singleton_iff] at supported
                    cases supported
                    exact logged_record source challenge.publicKey before history old handle request _
                · simp only [owned, ite_false, interpreted, simulateQ_pure, StateT.run_pure,
                    support_pure, Set.mem_singleton_iff] at supported
                  cases supported
                  exact logged_record source challenge.publicKey before history old handle request _

/-- Complete adaptive execution retains every ordinary challenger query inside the restored raw attempt history. -/
theorem program_logged (challenge : Credential source) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source challenge.publicKey before history)
    (result : (Value × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source challenge
      (evaluate source challenge.publicKey tape work before) history)) :
    Logged source challenge.publicKey result.1.2 result.2 := by
  induction work using OracleComp.inductionOn generalizing before history with
  | pure value =>
      simp only [evaluate, interpreted, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact old
  | query_bind query next ih =>
      simp only [evaluate, interpreted, simulateQ_bind, simulateQ_spec_query,
        StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1.1 middle.1.2 middle.2
        (query_logged source challenge tape query before history old middle queried) continued

/-- Freshness against all raw same-key attempts implies ordinary EUF freshness against the exact challenger history. -/
theorem fresh (challenge : Credential source) (tape : List (Option (Token source)))
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source challenge.publicKey before history)
    (result : (Value × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source challenge
      (evaluate source challenge.publicKey tape work before) history))
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (fresh : RegistrationNativeMldsaEuf.Fresh (requestsFor challenge.publicKey result.1.2.signing) forgery) :
    RegistrationNativeMldsaEuf.Fresh result.2 forgery := by
  intro request member
  exact fresh request (program_logged source challenge tape work before history old result supported request member)
end BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.query_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.query_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.program_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaEufTapeHistory.fresh
