-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaChosen
import BeaconcryptCore.Computational.RegistrationNativeMldsaCandidate

/-! The ordinary one-key EUF oracle is invoked only by the selected opaque challenge row. Every reached matching complete signing request, including failed replies, also occurs in the wrapper's raw chronological attempt log. Ordinary generated keys and private randomness create no additional EUF signing query. No challenge secret is stored in the adversary's chosen-key pool. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram
open RegistrationNativeMldsa (Source Credential)
open RegistrationNativeMldsaChosen (Pool)
open RegistrationNativeMldsaOpaque (handleSource Attempt)
open RegistrationNativeMldsaCandidate (requestsFor)
variable {Value : Type} (source : Source)

noncomputable def evaluate (selected : Nat) (publicKey : RegistrationNativeMldsaEuf.PublicKey)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source) :
    OracleComp RegistrationNativeMldsaEuf.Spec (Value × Pool source) :=
  (simulateQ (RegistrationNativeMldsaChosen.handler source selected publicKey) work).run before

noncomputable def interpreted (credential : Credential source) {Answer : Type}
    (work : OracleComp RegistrationNativeMldsaEuf.Spec Answer) (history : List registration.MldsaSigningRequest) :
    ProbComp (Answer × List registration.MldsaSigningRequest) :=
  (simulateQ (RegistrationNativeMldsaEuf.handler source credential) work).run history

/-- Ordinary source randomness retains the exact EUF query history and does not invoke its signing interface. -/
theorem ordinary (credential : Credential source) (work : ProbComp Value) (history : List registration.MldsaSigningRequest) :
    interpreted source credential (RegistrationNativeMldsaChosen.lift work) history = (fun value => (value, history)) <$> work := by
  induction work using OracleComp.inductionOn generalizing history with
  | pure value =>
      simp only [interpreted, RegistrationNativeMldsaChosen.lift, simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [interpreted, RegistrationNativeMldsaChosen.lift, simulateQ_bind, simulateQ_spec_query,
        RegistrationNativeMldsaChosen.coins, RegistrationNativeMldsaEuf.handler, StateT.run_bind, StateT.run_lift]
      simp only [bind_assoc, pure_bind, map_bind]
      apply bind_congr
      intro reply
      exact ih reply history

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
    Logged source publicKey (RegistrationNativeMldsaChosen.record source before credential request reply) history := by
  intro asked member
  have previous := old asked member
  change asked ∈ requestsFor publicKey (before.signing ++ [_])
  rw [requests_append]
  exact List.mem_append_left _ previous

private theorem recorded (publicKey : RegistrationNativeMldsaEuf.PublicKey) (before : Pool source)
    (credential : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) (matching : request.public_key = publicKey) :
    request ∈ requestsFor publicKey (RegistrationNativeMldsaChosen.record source before credential request reply).signing := by
  change request ∈ requestsFor publicKey (before.signing ++ [_])
  rw [requests_append]
  apply List.mem_append_right
  simp only [requestsFor, List.filter_cons, List.filter_nil, List.map_cons, List.map_nil, matching, beq_self_eq_true, ite_true]
  exact List.mem_cons_self

private theorem logged_sign (credential : Credential source) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (handle : Credential (handleSource source)) (request : registration.MldsaSigningRequest)
    (reply : RegistrationSigningShared.SignReply) (matching : request.public_key = credential.publicKey) :
    Logged source credential.publicKey (RegistrationNativeMldsaChosen.record source before handle request reply) (history ++ [request]) := by
  intro asked member
  rcases List.mem_append.mp member with previous | current
  · exact logged_record source credential.publicKey before history old handle request reply asked previous
  · have same : asked = request := List.mem_singleton.mp current
    subst asked
    exact recorded source credential.publicKey before handle request reply matching

/-- One actual chosen-wrapper capability call retains every ordinary EUF signing query in the same-key raw attempt log. -/
theorem capability_logged (credential : Credential source) (selected : Nat)
    (query : RegistrationNativeMldsaCapability.Request (handleSource source)) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (result : ((RegistrationNativeMldsaCapability.Spec (handleSource source)).Range query × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source credential
      ((RegistrationNativeMldsaChosen.capability source selected credential.publicKey query).run before) history)) :
    Logged source credential.publicKey result.1.2 result.2 := by
  classical
  cases query with
  | generate =>
      simp only [RegistrationNativeMldsaChosen.capability, StateT.run] at supported
      by_cases selectedHere : before.attempts = selected
      · simp only [selectedHere, ite_true, interpreted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        cases supported
        exact old
      · simp only [selectedHere, ite_false, interpreted, simulateQ_map, StateT.run_map] at supported
        change result ∈ support ((fun inner => ((RegistrationNativeMldsaChosen.birth source before inner.1), inner.2)) <$>
          interpreted source credential (RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsaCapability.actual source .generate)) history) at supported
        rw [ordinary] at supported
        simp only [Functor.map_map, support_map] at supported
        obtain ⟨generated, _drawn, same⟩ := supported
        cases same
        rcases generated with ⟨generated, count⟩
        cases generated <;> exact old
  | sign handle request =>
      simp only [RegistrationNativeMldsaChosen.capability, StateT.run] at supported
      cases found : before.keys[handle.secret]? with
      | none =>
          simp only [found, interpreted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          cases supported
          exact logged_record source credential.publicKey before history old handle request _
      | some key =>
          simp only [found] at supported
          cases key with
          | ordinary key =>
              by_cases owned : handle.publicKey = key.publicKey
              · simp only [owned, ite_true, interpreted, simulateQ_map, StateT.run_map] at supported
                change result ∈ support ((fun inner => ((inner.1, RegistrationNativeMldsaChosen.record source before handle request inner.1.1), inner.2)) <$>
                  interpreted source credential (RegistrationNativeMldsaChosen.lift (RegistrationNativeMldsaCapability.actual source (.sign key request))) history) at supported
                rw [ordinary] at supported
                simp only [Functor.map_map, support_map] at supported
                obtain ⟨answer, _signed, same⟩ := supported
                cases same
                exact logged_record source credential.publicKey before history old handle request _
              · simp only [owned, ite_false, interpreted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                cases supported
                exact logged_record source credential.publicKey before history old handle request _
          | challenge publicKey =>
              by_cases owned : handle.publicKey = publicKey ∧ request.public_key = publicKey
              · simp only [owned, and_self, ite_true, interpreted, simulateQ_map, simulateQ_spec_query, RegistrationNativeMldsaEuf.handler,
                  StateT.run_map] at supported
                by_cases matching : request.public_key = credential.publicKey
                · rw [RegistrationNativeMldsaEuf.signing_match source credential request history matching] at supported
                  simp only [Functor.map_map, support_map] at supported
                  obtain ⟨reply, _signed, same⟩ := supported
                  cases same
                  exact logged_sign source credential before history old handle request reply matching
                · rw [RegistrationNativeMldsaEuf.signing_mismatch source credential request history matching] at supported
                  simp only [map_pure, support_pure, Set.mem_singleton_iff] at supported
                  cases supported
                  exact logged_record source credential.publicKey before history old handle request _
              · simp only [owned, ite_false, interpreted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                cases supported
                exact logged_record source credential.publicKey before history old handle request _

/-- Every chosen-wrapper primitive step keeps the actual one-key signing history inside its raw displayed-key request prefix. -/
theorem query_logged (credential : Credential source) (selected : Nat)
    (query : (RegistrationNativeMldsaProgram.Spec (handleSource source)).Domain) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (result : ((RegistrationNativeMldsaProgram.Spec (handleSource source)).Range query × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source credential
      ((RegistrationNativeMldsaChosen.handler source selected credential.publicKey query).run before) history)) :
    Logged source credential.publicKey result.1.2 result.2 := by
  cases query with
  | inl coin =>
      simp only [RegistrationNativeMldsaChosen.handler, StateT.run_lift, bind_pure_comp,
        interpreted, RegistrationNativeMldsaChosen.coins, simulateQ_map, simulateQ_spec_query,
        RegistrationNativeMldsaEuf.handler, StateT.run_map, StateT.run_lift, bind_pure_comp,
        Functor.map_map, support_map] at supported
      obtain ⟨reply, _drawn, same⟩ := supported
      cases same
      exact old
  | inr query => exact capability_logged source credential selected query before history old result supported

/-- Arbitrary adaptive capability programs retain every actual ordinary-EUF signing request, including failed signatures, in their complete chronological raw log. -/
theorem program_logged (credential : Credential source) (selected : Nat)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (result : (Value × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source credential
      (evaluate source selected credential.publicKey work before) history)) :
    Logged source credential.publicKey result.1.2 result.2 := by
  induction work using OracleComp.inductionOn generalizing before history with
  | pure value =>
      simp only [evaluate, interpreted, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      exact old
  | query_bind query next ih =>
      simp only [evaluate, interpreted, simulateQ_bind, simulateQ_spec_query, StateT.run_bind,
        mem_support_bind_iff] at supported
      obtain ⟨middle, queried, continued⟩ := supported
      exact ih middle.1.1 middle.1.2 middle.2
        (query_logged source credential selected query before history old middle queried) continued

/-- Actual ordinary-EUF freshness follows from raw same-key prefix freshness through the checked query-history inclusion. -/
theorem fresh (credential : Credential source) (selected : Nat)
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Value) (before : Pool source)
    (history : List registration.MldsaSigningRequest) (old : Logged source credential.publicKey before history)
    (result : (Value × Pool source) × List registration.MldsaSigningRequest)
    (supported : result ∈ support (interpreted source credential
      (evaluate source selected credential.publicKey work before) history))
    (forgery : RegistrationNativeMldsaEuf.Forgery)
    (fresh : RegistrationNativeMldsaEuf.Fresh (requestsFor credential.publicKey result.1.2.signing) forgery) :
    RegistrationNativeMldsaEuf.Fresh result.2 forgery := by
  intro request member
  exact fresh request (program_logged source credential selected work before history old result supported request member)

end BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.ordinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.capability_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.capability_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.query_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.query_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.program_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.program_logged

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaChosenProgram.fresh
