import BeaconcryptCore.Computational.LivePublicObservation
import BeaconcryptCore.Computational.RawCtxProtocolReveals

/-!
Public requests for an honest record carry an application request value and an actual owner route, never the privately produced plaintext. A private application callback supplies the optional plaintext before the actual source send. The application callback is passed only its own private state and an explicit randomness interface; it is not passed the live protocol state or shared CTX cache. Initial states and callback parameters may be correlated; these operational equations do not establish target secrecy. Both native role families retain their single shared primitive state. Every original source capability remains available, including actual optional raw plaintext, public fixed HKDF and live reveal replies. Acceptance-only network delivery is an additional observation capability.

This module supplies exact adaptive execution and observation equations and explicit source/application request budgets. Application callback costs remain separately chargeable. Private message selection is an application interface, not a cryptographic assumption or proof that a revealed target remains confidential. Registration/identity creation and cryptographic hybrid composition remain separate consumers; snapshots and storage do not occur.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.LiveApplicationObservation

abbrev Owner := RawCtxProtocolReveals.Owner
abbrev SourceSpec := RawCtxProtocolReveals.SourceSpec

inductive Request (ApplicationRequest : Type) (serverCount beaconCount : Nat) where
  | source (request : (SourceSpec serverCount beaconCount).Domain)
  | honestSend (owner : Owner serverCount beaconCount) (request : ApplicationRequest)
  | deliverServer (index : Fin serverCount) (raw : Pqxdh.Bytes)
  | deliverBeacon (index : Fin beaconCount) (raw : Pqxdh.Bytes)

def Reply {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    Request ApplicationRequest serverCount beaconCount → Type
  | .source request => (SourceSpec serverCount beaconCount).Range request
  | .honestSend _ _ => Option RawCtxSourceSend.Encrypted
  | .deliverServer _ _ | .deliverBeacon _ _ => Bool

abbrev PublicSpec (ApplicationRequest : Type) (serverCount beaconCount : Nat) :
    OracleSpec (Request ApplicationRequest serverCount beaconCount) := Reply

abbrev ApplicationSpec (ApplicationRequest : Type) (serverCount beaconCount : Nat) :=
  (Owner serverCount beaconCount × ApplicationRequest) →ₒ Option Pqxdh.Bytes

abbrev PrivateSpec (ApplicationRequest : Type) (serverCount beaconCount : Nat) :=
  SourceSpec serverCount beaconCount + ApplicationSpec ApplicationRequest serverCount beaconCount

def sendRequest {serverCount beaconCount : Nat}
    (owner : Owner serverCount beaconCount) (plaintext : Pqxdh.Bytes) :
    (SourceSpec serverCount beaconCount).Domain :=
  match owner with
  | .server index peer => .inl (.inl ⟨index, .inl (plaintext, peer)⟩)
  | .beacon index => .inl (.inr (.inl ⟨index, .inl plaintext⟩))

def sendReply {serverCount beaconCount : Nat}
    (owner : Owner serverCount beaconCount) (plaintext : Pqxdh.Bytes) :
    (SourceSpec serverCount beaconCount).Range (sendRequest owner plaintext) → Option RawCtxSourceSend.Encrypted :=
  match owner with
  | .server _ _ => id
  | .beacon _ => id

def serverRaw {serverCount beaconCount : Nat} (index : Fin serverCount) (raw : Pqxdh.Bytes) :
    (SourceSpec serverCount beaconCount).Domain := .inl (.inl ⟨index, .inr raw⟩)

def beaconRaw {serverCount beaconCount : Nat} (index : Fin beaconCount) (raw : Pqxdh.Bytes) :
    (SourceSpec serverCount beaconCount).Domain := .inl (.inr (.inl ⟨index, .inr raw⟩))

def lower {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (OracleComp (PrivateSpec ApplicationRequest serverCount beaconCount))
  | .source request => do
      let reply ← (PrivateSpec ApplicationRequest serverCount beaconCount).query (.inl request)
      pure reply
  | .honestSend owner request => do
      let plaintext ← (PrivateSpec ApplicationRequest serverCount beaconCount).query (.inr (owner, request))
      match plaintext with
      | none => pure none
      | some plaintext => do
          let reply ← (PrivateSpec ApplicationRequest serverCount beaconCount).query (.inl (sendRequest owner plaintext))
          pure (sendReply owner plaintext reply)
  | .deliverServer index raw => do
      let reply ← (PrivateSpec ApplicationRequest serverCount beaconCount).query (.inl (serverRaw index raw))
      pure (LivePublicObservation.accepted reply)
  | .deliverBeacon index raw => do
      let reply ← (PrivateSpec ApplicationRequest serverCount beaconCount).query (.inl (beaconRaw index raw))
      pure (LivePublicObservation.accepted reply)

def publicImpl {ApplicationRequest : Type} {serverCount beaconCount : Nat}
    {m : Type → Type} [Monad m]
    (source : QueryImpl (SourceSpec serverCount beaconCount) m)
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount) m) :
    QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount) m
  | .source request => source request
  | .honestSend owner request => do
      let plaintext ← application (owner, request)
      match plaintext with
      | none => pure none
      | some plaintext => sendReply owner plaintext <$> source (sendRequest owner plaintext)
  | .deliverServer index raw => LivePublicObservation.accepted <$> source (serverRaw index raw)
  | .deliverBeacon index raw => LivePublicObservation.accepted <$> source (beaconRaw index raw)

set_option backward.isDefEq.respectTransparency false in
/-- One honest record request obtains its private optional application payload and then invokes the actual selected source send; all other source/reveal replies are preserved exactly. -/
theorem lower_query {ApplicationRequest : Type} {serverCount beaconCount : Nat}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : QueryImpl (SourceSpec serverCount beaconCount) m)
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount) m)
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain) :
    simulateQ (source + application) (lower request) = publicImpl source application request := by
  cases request <;> simp [lower, publicImpl]
  congr 1
  funext plaintext
  cases plaintext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Adaptive scheduling, stopping and all original optional replies are identical before any primitive randomness is evaluated. -/
theorem lower_client {ApplicationRequest Result : Type} {serverCount beaconCount : Nat}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (source : QueryImpl (SourceSpec serverCount beaconCount) m)
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount) m)
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result) :
    simulateQ (source + application) (simulateQ lower client) =
      simulateQ (publicImpl source application) client := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  exact lower_query source application request

abbrev SharedState (ProtocolState ApplicationState PrimitiveState : Type) :=
  (ProtocolState × ApplicationState) × PrimitiveState

def sourceLift {ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base))) :
    QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (SharedState ProtocolState ApplicationState PrimitiveState) (OracleComp base)) :=
  fun request state => do
    let result ← (source request).run (state.1.1, state.2)
    pure (result.1, ((result.2.1, state.1.2), result.2.2))

def applicationLift {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base))) :
    QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT (SharedState ProtocolState ApplicationState PrimitiveState) (OracleComp base)) :=
  fun request state => do
    let result ← (application request).run state.1.2
    pure (result.1, ((state.1.1, result.2), state.2))

/-- Private application work retains the untouched whole protocol and original shared primitive state. -/
theorem application_run {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (request : (ApplicationSpec ApplicationRequest serverCount beaconCount).Domain)
    (state : SharedState ProtocolState ApplicationState PrimitiveState) :
    (applicationLift application request).run state = (do
      let result ← (application request).run state.1.2
      pure (result.1, ((state.1.1, result.2), state.2))) := rfl

/-- A native source operation preserves the complete private application state and shares the same current primitive state. -/
theorem source_run {ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (request : (SourceSpec serverCount beaconCount).Domain)
    (state : SharedState ProtocolState ApplicationState PrimitiveState) :
    (sourceLift source request).run state = (do
      let result ← (source request).run (state.1.1, state.2)
      pure (result.1, ((result.2.1, state.1.2), result.2.2))) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The honest send runs the private application first, preserves its state on every source outcome and never gives that callback the protocol or primitive state. -/
theorem honest_send_complete {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (owner : Owner serverCount beaconCount) (request : ApplicationRequest)
    (state : SharedState ProtocolState ApplicationState PrimitiveState) :
    (publicImpl (sourceLift source) (applicationLift application) (.honestSend owner request)).run state = (do
      let payload ← (application (owner, request)).run state.1.2
      match payload.1 with
      | none => pure (none, ((state.1.1, payload.2), state.2))
      | some plaintext => do
          let result ← (source (sendRequest owner plaintext)).run (state.1.1, state.2)
          pure (sendReply owner plaintext result.1, ((result.2.1, payload.2), result.2.2))) := by
  unfold publicImpl
  rw [StateT.run_bind, application_run]
  simp only [bind_assoc, pure_bind]
  congr 1
  funext payload
  cases payload.1 with
  | none => rfl
  | some plaintext =>
      rw [StateT.run_map, source_run]
      simp

/-- Lifting the actual source retains every underlying query count exactly. -/
theorem source_query_bounds {ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (request : (SourceSpec serverCount beaconCount).Domain)
    (state : SharedState ProtocolState ApplicationState PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((sourceLift source request).run state).IsQueryBoundP predicate budget ↔
      ((source request).run (state.1.1, state.2)).IsQueryBoundP predicate budget := by
  rw [source_run]
  simp only [bind_pure_comp, isQueryBoundP_map_iff]

/-- Private application sampling and service work remain fully charged; only state packaging is erased. -/
theorem application_query_bounds {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (request : (ApplicationSpec ApplicationRequest serverCount beaconCount).Domain)
    (state : SharedState ProtocolState ApplicationState PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((applicationLift application request).run state).IsQueryBoundP predicate budget ↔
      ((application request).run state.1.2).IsQueryBoundP predicate budget := by
  rw [application_run]
  simp only [bind_pure_comp, isQueryBoundP_map_iff]

/-- Every honest request pays both its full private application bill and the possible actual source send bill, including optional failure. -/
theorem honest_send_bound {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (owner : Owner serverCount beaconCount) (request : ApplicationRequest)
    (state : SharedState ProtocolState ApplicationState PrimitiveState)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qApplication qSource : Nat)
    (applicationBound : ((application (owner, request)).run state.1.2).IsQueryBoundP predicate qApplication)
    (sourceBound : ∀ plaintext, ((source (sendRequest owner plaintext)).run
      (state.1.1, state.2)).IsQueryBoundP predicate qSource) :
    ((publicImpl (sourceLift source) (applicationLift application) (.honestSend owner request)).run
      state).IsQueryBoundP predicate (qApplication + qSource) := by
  rw [honest_send_complete]
  apply isQueryBoundP_bind applicationBound
  intro payload _
  cases payload.1 with
  | none => trivial
  | some plaintext => simpa only [bind_pure_comp, isQueryBoundP_map_iff] using sourceBound plaintext

abbrev Observation (ApplicationRequest : Type) (serverCount beaconCount : Nat) :=
  (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain) ×
    (PublicSpec ApplicationRequest serverCount beaconCount).Range request

abbrev Transcript (ApplicationRequest : Type) (serverCount beaconCount : Nat) :=
  List (Observation ApplicationRequest serverCount beaconCount)

def loggedImpl {ApplicationRequest State ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base))) :
    QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT (State × Transcript ApplicationRequest serverCount beaconCount) (OracleComp base)) :=
  fun request state => do
    let result ← (impl request).run state.1
    pure (result.1, (result.2, state.2 ++ [⟨request, result.1⟩]))

/-- Public instrumentation records the declared request and actual reply after its original effects; private application payloads are not extra event arguments. -/
theorem logged_query {ApplicationRequest State ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain)
    (state : State × Transcript ApplicationRequest serverCount beaconCount) :
    (loggedImpl impl request).run state = (do
      let result ← (impl request).run state.1
      pure (result.1, (result.2, state.2 ++ [⟨request, result.1⟩]))) := rfl

/-- Erasing the public log preserves every real source/application effect and complete private state. -/
theorem logged_query_erasure {ApplicationRequest State ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain)
    (state : State × Transcript ApplicationRequest serverCount beaconCount) :
    Prod.map id Prod.fst <$> (loggedImpl impl request).run state = (impl request).run state.1 := by
  rw [logged_query]
  simp

/-- Arbitrary adaptive logging preserves the original decision, all role/application fields and shared primitive state. -/
theorem logged_client_erasure {ApplicationRequest State Result ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result)
    (state : State × Transcript ApplicationRequest serverCount beaconCount) :
    Prod.map id Prod.fst <$> (simulateQ (loggedImpl impl) client).run state =
      (simulateQ impl client).run state.1 := by
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ Prod.fst
    (logged_query_erasure impl) client state

/-- The exposed experiment returns only the adaptive result and public log, with all private role/application/primitive state discarded from this output. -/
def publicObservation {ApplicationRequest State Result ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result) (state : State) :
    OracleComp base (Result × Transcript ApplicationRequest serverCount beaconCount) :=
  (fun result => (result.1, result.2.2)) <$> (simulateQ (loggedImpl impl) client).run (state, [])

set_option backward.isDefEq.respectTransparency false in
/-- The source compiler and direct service yield exactly the same public observation program, not just reply marginals. -/
theorem public_observation_compiler {ApplicationRequest State Result ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount) (StateT State (OracleComp base)))
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result) (state : State) :
    publicObservation ((source + application) ∘ₛ lower) client state =
      publicObservation (publicImpl source application) client state := by
  congr 1
  funext request
  exact lower_query source application request

def IsSource {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    (PrivateSpec ApplicationRequest serverCount beaconCount).Domain → Prop := fun query => query.isLeft = true

def IsApplication {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    (PrivateSpec ApplicationRequest serverCount beaconCount).Domain → Prop := fun query => query.isRight = true

instance {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    DecidablePred (IsSource (ApplicationRequest := ApplicationRequest)
      (serverCount := serverCount) (beaconCount := beaconCount)) := fun query => inferInstanceAs (Decidable (query.isLeft = true))

instance {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    DecidablePred (IsApplication (ApplicationRequest := ApplicationRequest)
      (serverCount := serverCount) (beaconCount := beaconCount)) := fun query => inferInstanceAs (Decidable (query.isRight = true))

def AsksApplication {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    (PublicSpec ApplicationRequest serverCount beaconCount).Domain → Prop
  | .honestSend _ _ => True
  | _ => False

instance {ApplicationRequest : Type} {serverCount beaconCount : Nat} :
    DecidablePred (AsksApplication (ApplicationRequest := ApplicationRequest)
      (serverCount := serverCount) (beaconCount := beaconCount)) := fun request => by
  cases request <;> simp only [AsksApplication] <;> infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Each public operation makes at most one original source request, counting every raw or reveal reply branch. -/
theorem lower_source_step {ApplicationRequest : Type} {serverCount beaconCount : Nat}
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain) :
    (lower request).IsQueryBoundP IsSource 1 := by
  cases request <;> simp [lower, IsSource]
  intro payload
  cases payload <;> simp [IsSource]

set_option backward.isDefEq.respectTransparency false in
/-- Only an honest application request invokes the private callback, exactly once before any actual send. -/
theorem lower_application_step {ApplicationRequest : Type} {serverCount beaconCount : Nat}
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain) :
    (lower request).IsQueryBoundP IsApplication (if AsksApplication request then 1 else 0) := by
  cases request <;> simp [lower, IsApplication, AsksApplication]
  intro payload
  cases payload <;> simp [IsApplication]

/-- An adaptive public schedule with at most `qPublic` requests makes at most that many original source calls, with no success-only filtering. -/
theorem lower_source_budget {ApplicationRequest Result : Type} {serverCount beaconCount : Nat}
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result)
    (qPublic : Nat) (bounded : client.IsTotalQueryBound qPublic) :
    (simulateQ lower client).IsQueryBoundP IsSource qPublic := by
  induction client using OracleComp.inductionOn generalizing qPublic with
  | pure value => simp
  | query_bind request next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      have remainder : 1 + (qPublic - 1) = qPublic := by omega
      simpa only [remainder] using isQueryBoundP_bind (lower_source_step request)
        (fun reply _ => ih reply (qPublic - 1) (bounded.2 reply))

/-- Honest application requests retain their own selective cap under arbitrary source, raw-delivery and reveal continuations. -/
theorem lower_application_budget {ApplicationRequest Result : Type} {serverCount beaconCount : Nat}
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result)
    (qHonest : Nat) (bounded : client.IsQueryBoundP AsksApplication qHonest) :
    (simulateQ lower client).IsQueryBoundP IsApplication qHonest := by
  induction client using OracleComp.inductionOn generalizing qHonest with
  | pure value => simp
  | query_bind request next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      rw [simulateQ_bind, simulateQ_spec_query]
      have remainder : (if AsksApplication request then 1 else 0) +
          (if AsksApplication request then qHonest - 1 else qHonest) = qHonest := by
        split
        · simp_all
          omega
        · simp_all
      simpa only [remainder] using isQueryBoundP_bind (lower_application_step request)
        (fun reply _ => ih reply _ (bounded.2 reply))

set_option backward.isDefEq.respectTransparency false in
/-- Every public operation pays its complete source bill; an honest request additionally pays the full private application callback. -/
theorem public_query_bound {ApplicationRequest ProtocolState ApplicationState PrimitiveState ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qSource qApplication : Nat)
    (sourceBound : ∀ request state, ((source request).run state).IsQueryBoundP predicate qSource)
    (applicationBound : ∀ request state, ((application request).run state).IsQueryBoundP predicate qApplication)
    (request : (PublicSpec ApplicationRequest serverCount beaconCount).Domain)
    (state : SharedState ProtocolState ApplicationState PrimitiveState) :
    ((publicImpl (sourceLift source) (applicationLift application) request).run state).IsQueryBoundP
      predicate (qSource + if AsksApplication request then qApplication else 0) := by
  cases request with
  | source request =>
      simpa only [publicImpl, AsksApplication, ite_false, Nat.add_zero] using
        (source_query_bounds source request state predicate qSource).mpr (sourceBound request (state.1.1, state.2))
  | honestSend owner request =>
      simpa only [AsksApplication, ite_true, Nat.add_comm] using honest_send_bound source application
        owner request state predicate qApplication qSource
        (applicationBound (owner, request) state.1.2)
        (fun plaintext => sourceBound (sendRequest owner plaintext) (state.1.1, state.2))
  | deliverServer index raw =>
      simpa only [publicImpl, AsksApplication, ite_false, Nat.add_zero, StateT.run_map,
        isQueryBoundP_map_iff] using
        (source_query_bounds source (serverRaw index raw) state predicate qSource).mpr
          (sourceBound (serverRaw index raw) (state.1.1, state.2))
  | deliverBeacon index raw =>
      simpa only [publicImpl, AsksApplication, ite_false, Nat.add_zero, StateT.run_map,
        isQueryBoundP_map_iff] using
        (source_query_bounds source (beaconRaw index raw) state predicate qSource).mpr
          (sourceBound (beaconRaw index raw) (state.1.1, state.2))

/-- Arbitrary adaptive schedules pay all source work and every private application invocation, including rejected requests and failed sends. -/
theorem public_schedule_bound {ApplicationRequest ProtocolState ApplicationState PrimitiveState Result ι : Type}
    {base : OracleSpec ι} {serverCount beaconCount : Nat}
    (source : QueryImpl (SourceSpec serverCount beaconCount)
      (StateT (ProtocolState × PrimitiveState) (OracleComp base)))
    (application : QueryImpl (ApplicationSpec ApplicationRequest serverCount beaconCount)
      (StateT ApplicationState (OracleComp base)))
    (predicate : base.Domain → Prop) [DecidablePred predicate] (qSource qApplication : Nat)
    (sourceBound : ∀ request state, ((source request).run state).IsQueryBoundP predicate qSource)
    (applicationBound : ∀ request state, ((application request).run state).IsQueryBoundP predicate qApplication)
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result)
    (qPublic qHonest : Nat) (bounded : client.IsTotalQueryBound qPublic)
    (honestBound : client.IsQueryBoundP AsksApplication qHonest)
    (state : SharedState ProtocolState ApplicationState PrimitiveState) :
    ((simulateQ (publicImpl (sourceLift source) (applicationLift application)) client).run state).IsQueryBoundP
      predicate (qPublic * qSource + qHonest * qApplication) := by
  induction client using OracleComp.inductionOn generalizing qPublic qHonest state with
  | pure value => simp
  | query_bind request next ih =>
      rw [isTotalQueryBound_query_bind_iff] at bounded
      rw [isQueryBoundP_query_bind_iff] at honestBound
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      have remainder : (qSource + if AsksApplication request then qApplication else 0) +
          ((qPublic - 1) * qSource + (if AsksApplication request then qHonest - 1 else qHonest) * qApplication) =
          qPublic * qSource + qHonest * qApplication := by
        have publicRest : qPublic - 1 + 1 = qPublic := by omega
        by_cases asks : AsksApplication request
        · have honestRest : qHonest - 1 + 1 = qHonest := by simp_all; omega
          simp only [ite_eq_left asks]
          nlinarith
        · simp only [ite_eq_right asks, Nat.add_zero]
          nlinarith
      simpa only [remainder] using isQueryBoundP_bind
        (public_query_bound source application predicate qSource qApplication sourceBound applicationBound request state)
        (fun reply _ => ih reply.1 (qPublic - 1) _ (bounded.2 reply.1) (honestBound.2 reply.1) reply.2)

/-- Public logging and private-state erasure preserve the complete underlying oracle bill exactly. -/
theorem public_observation_bound {ApplicationRequest State Result ι : Type} {base : OracleSpec ι}
    {serverCount beaconCount : Nat}
    (impl : QueryImpl (PublicSpec ApplicationRequest serverCount beaconCount)
      (StateT State (OracleComp base)))
    (client : OracleComp (PublicSpec ApplicationRequest serverCount beaconCount) Result) (state : State)
    (predicate : base.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (publicObservation impl client state).IsQueryBoundP predicate budget ↔
      ((simulateQ impl client).run state).IsQueryBoundP predicate budget := by
  unfold publicObservation
  rw [isQueryBoundP_map_iff]
  exact isQueryBoundP_iff_of_map_eq (logged_client_erasure impl client (state, []))

end BeaconcryptCore.Computational.LiveApplicationObservation

/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_query
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_client' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_client
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.application_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.application_run
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.source_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.source_run
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.honest_send_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.honest_send_complete
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.source_query_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.source_query_bounds
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.application_query_bounds' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.application_query_bounds
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.honest_send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.honest_send_bound
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.logged_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.logged_query
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.logged_query_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.logged_query_erasure
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.logged_client_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.logged_client_erasure
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.public_observation_compiler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.public_observation_compiler
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_source_step
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_application_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_application_step
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_source_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_source_budget
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.lower_application_budget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.lower_application_budget
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.public_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.public_query_bound
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.public_schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.public_schedule_bound
/-- info: 'BeaconcryptCore.Computational.LiveApplicationObservation.public_observation_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.LiveApplicationObservation.public_observation_bound
