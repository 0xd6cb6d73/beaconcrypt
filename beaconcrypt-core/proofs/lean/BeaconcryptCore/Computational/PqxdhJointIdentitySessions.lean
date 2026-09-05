import BeaconcryptCore.Computational.PqxdhJointIdentityFamily

/-!
# Session labels share the owning identity service

An arbitrary finite set of session labels maps to generated identity indices. Every session of one identity uses the same seed and signing/DH history. Adaptive session selection therefore induces an identity selection without independently sampling a key per session. This interface does not yet instantiate production session creation, public-key lookup, reveals, raw network parsing, or the global freshness monitor.
-/

open OracleSpec OracleComp ENNReal
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhJointIdentitySessions

open PqxdhJointIdentity PqxdhJointIdentityFamily

abbrev SessionSpec (sessions : ℕ) := FamilyAdversarySpec sessions

/-- Only public routing metadata changes; the request input and dependent reply type remain exact. -/
def sessionImpl {identities sessions : ℕ} (owner : Fin sessions → Fin identities) :
    QueryImpl (SessionSpec sessions) (OracleComp (FamilyAdversarySpec identities))
  | .inl coin => (FamilyAdversarySpec identities).query (.inl coin)
  | .inr (session, request) => (FamilyAdversarySpec identities).query (.inr (owner session, request))

/-- Retain the adversary's chosen session label before mapping it to its owning identity. -/
structure SessionForgery (sessions : ℕ) where
  session : Fin sessions
  forgery : Forgery

def toFamilyForgery {identities sessions : ℕ} (owner : Fin sessions → Fin identities)
    (result : SessionForgery sessions) : FamilyForgery identities :=
  ⟨owner result.session, result.forgery⟩

/-- Session routing preserves arbitrary client outputs and every identity's prior service history. -/
def route {identities sessions : ℕ} (owner : Fin sessions → Fin identities) {Result : Type}
    (client : OracleComp (SessionSpec sessions) Result) :
    OracleComp (FamilyAdversarySpec identities) Result := simulateQ (sessionImpl owner) client

/-- The complete direct session interpreter uses exactly the same identity state as the routed client. -/
theorem route_complete (primitives : Primitives) {identities sessions : ℕ}
    (owner : Fin sessions → Fin identities) (seeds : Fin identities → IdentitySeed)
    {Result : Type} (client : OracleComp (SessionSpec sessions) Result)
    (history : FamilyHistory identities) :
    (simulateQ (familyImpl primitives seeds) (route owner client)).run history =
      (simulateQ (fun query => simulateQ (familyImpl primitives seeds) (sessionImpl owner query)) client).run history := by
  exact congrArg (fun computation => computation.run history)
    (QueryImpl.simulateQ_compose (familyImpl primitives seeds) (sessionImpl owner) client).symm

/-- Session selection changes no forgery bytes and merges all earlier signing requests for the same identity. -/
def familyClient {identities sessions : ℕ} (owner : Fin sessions → Fin identities)
    (adversary : (Fin identities → PublicIdentity) →
      OracleComp (SessionSpec sessions) (SessionForgery sessions))
    (publicKeys : Fin identities → PublicIdentity) :
    OracleComp (FamilyAdversarySpec identities) (FamilyForgery identities) :=
  toFamilyForgery owner <$> route owner (adversary publicKeys)

/-- There is no extra session-selection loss when all sessions share their actual owning identity history. -/
theorem session_advantage_le_identity_sum (primitives : Primitives) (identities sessions : ℕ)
    (owner : Fin sessions → Fin (identities + 1))
    (adversary : (Fin (identities + 1) → PublicIdentity) →
      OracleComp (SessionSpec sessions) (SessionForgery sessions)) :
    Pr[fun result => familyTest primitives result = true |
      familyRun primitives (identities + 1) (familyClient owner adversary)] ≤
    ∑ target : Fin (identities + 1), advantage primitives
      (reduction primitives target (familyClient owner adversary)) :=
  family_advantage_le_sum primitives identities (familyClient owner adversary)

/-- Session labels introduce no extra primitive or uniform request and do not reset any identity budget. -/
theorem route_query_bound {identities sessions : ℕ} (owner : Fin sessions → Fin identities)
    {Result : Type} (client : OracleComp (SessionSpec sessions) Result) (kind : Kind) (bound : ℕ)
    (bounded : client.IsQueryBoundP (familyClass (IsClass kind)) bound) :
    (route owner client).IsQueryBoundP (familyClass (IsClass kind)) bound := by
  unfold route
  induction client using OracleComp.inductionOn generalizing bound with
  | pure value => simp
  | query_bind query rest ih =>
    rw [OracleComp.isQueryBoundP_query_bind_iff] at bounded
    rw [simulateQ_query_bind]
    cases query with
    | inl coin =>
      change (((FamilyAdversarySpec identities).query (.inl coin) : OracleComp (FamilyAdversarySpec identities) _) >>= fun answer =>
        simulateQ (sessionImpl owner) (rest answer)).IsQueryBoundP (familyClass (IsClass kind)) bound
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩
    | inr query =>
      rcases query with ⟨session, request⟩
      change (((FamilyAdversarySpec identities).query (.inr (owner session, request)) : OracleComp (FamilyAdversarySpec identities) _) >>= fun answer =>
        simulateQ (sessionImpl owner) (rest answer)).IsQueryBoundP (familyClass (IsClass kind)) bound
      rw [OracleComp.isQueryBoundP_query_bind_iff]
      exact ⟨bounded.1, fun answer => ih answer _ (bounded.2 answer)⟩

/-- The single-identity reduction for arbitrarily interleaved sessions retains source signing/DH caps and pays for every other identity seed. -/
theorem session_reduction_query_bound (primitives : Primitives) (identities sessions : ℕ)
    (owner : Fin sessions → Fin (identities + 1))
    (adversary : (Fin (identities + 1) → PublicIdentity) →
      OracleComp (SessionSpec sessions) (SessionForgery sessions))
    (target : Fin (identities + 1)) (kind : Kind) (bound : ℕ)
    (bounded : ∀ publicKeys, (adversary publicKeys).IsQueryBoundP (familyClass (IsClass kind)) bound)
    (jointPublic : PublicIdentity) :
    (reduction primitives target (familyClient owner adversary) jointPublic).IsQueryBoundP (IsClass kind)
      ((if kind = .uniform then 32 * identities else 0) + bound) := by
  apply reduction_query_bound primitives target (familyClient owner adversary) kind bound
  intro publicKeys
  simpa only [familyClient, OracleComp.isQueryBoundP_map_iff] using
    route_query_bound owner (adversary publicKeys) kind bound (bounded publicKeys)

end BeaconcryptCore.Computational.PqxdhJointIdentitySessions

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentitySessions.route_complete' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentitySessions.route_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentitySessions.session_advantage_le_identity_sum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentitySessions.session_advantage_le_identity_sum

/--
info: 'BeaconcryptCore.Computational.PqxdhJointIdentitySessions.session_reduction_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhJointIdentitySessions.session_reduction_query_bound
