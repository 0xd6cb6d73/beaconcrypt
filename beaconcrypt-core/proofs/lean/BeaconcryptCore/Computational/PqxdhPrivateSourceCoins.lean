import BeaconcryptCore.Computational.PqxdhJointPhase1AcceptanceComposition

/-!
Protocol-private uniform replies are separate from public source coins. Complete compiler equalities retain generated seeds, signing/DH/reveal histories, original public logs and arbitrary results. Only synthetic coin logging is restored. This concerns BareState, not original positions in native report instrumentation.
-/

open OracleComp OracleSpec ENNReal
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhPrivateSourceCoins
open PqxdhEd25519EufCma PqxdhJointIdentity PqxdhJointIdentityFamily PqxdhJointIdentityFreshness
open PqxdhDynamicIdentityPool PqxdhDynamicIdentityRouting PqxdhDynamicIdentityReports
open PqxdhJointPhase1Reports PqxdhPhase1AcceptanceOracle PqxdhJointPhase1AcceptanceComposition

/-- Protocol-private randomness is distinct from explicit public source coin requests. -/
abbrev PrivateSourceSpec := unifSpec + SourceSpec

/-- Private coin replies never enter the public source request/reply transcript. -/
def privateImpl (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) :
    QueryImpl PrivateSourceSpec (StateT (BareState count) ProbComp) := fun query state =>
  match query with
  | .inl coin => do
      let answer ← unifSpec.query coin
      pure (answer, state)
  | .inr request => (bareImpl attachedVerify primitives count request).run state

/-- The reduction uses its ordinary coins while separately reconstructing only the actual public source log. -/
def compile : QueryImpl PrivateSourceSpec (StateT (List Observation) (OracleComp SourceSpec)) :=
  fun query transcript => match query with
  | .inl coin => do
      let answer ← SourceSpec.query (.inl (.inl coin))
      pure (answer, transcript)
  | .inr (.inl request) => do
      let answer ← SourceSpec.query (.inl request)
      pure (answer, transcript ++ [⟨request, answer⟩])
  | .inr (.inr candidate) => do
      let answer ← SourceSpec.query (.inr candidate)
      pure (answer, transcript)

/-- Erase only synthetic public logging of reduction-internal coins; private identities and all joint histories are retained. -/
def restoreState {count : Nat} (state : BareState count) (transcript : List Observation) : BareState count :=
  (state.1, { state.2 with transcript := transcript })

def restore {count : Nat} {Result : Type}
    (output : (Result × List Observation) × BareState count) : Result × BareState count :=
  (output.1.1, restoreState output.2 output.1.2)

/-- General creation retains its sampled seed without unfolding the byte sampler. -/
theorem bare_create (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (state : BareState count) :
    (bareImpl attachedVerify primitives count (.inl (.inr .create))).run state =
      (fun seed => let generated := createdReply primitives state.2 seed
        (generated.1, (state.1, generated.2))) <$> sampleSeed := by
  change (sourceWithHistory count (lazyImpl primitives) (.inr .create)).run (state.1, state.2) = _
  rw [sourceWithHistory_run, lazyImpl_create]
  simp only [bind_pure_comp, historyUpdate, Functor.map_map]

theorem compile_create (transcript : List Observation) :
    (compile (.inr (.inl (.inr .create)))).run transcript = (do
      let answer ← (SourceSpec.query (.inl (.inr .create)) : OracleComp SourceSpec (Option (Nat × PublicIdentity)))
      pure (answer, transcript ++ [⟨.inr .create, answer⟩])) := rfl

theorem private_create (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (state : BareState count) :
    (privateImpl attachedVerify primitives count (.inr (.inl (.inr .create)))).run state =
      (bareImpl attachedVerify primitives count (.inl (.inr .create))).run state := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Each compiled step gives the actual reply and complete actual poststate, including precisely the original public log. -/
theorem compile_step (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (query : PrivateSourceSpec.Domain)
    (state : BareState count) (transcript : List Observation) :
    restore <$> ((simulateQ (bareImpl attachedVerify primitives count)
      ((compile query).run transcript)).run state) =
      (privateImpl attachedVerify primitives count query).run (restoreState state transcript) := by
  cases query with
  | inl coin =>
      simp only [compile, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
      rfl
  | inr request =>
      cases request with
      | inr candidate =>
          simp only [compile, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
          rfl
      | inl request =>
          cases request with
          | inl coin =>
              simp only [compile, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
              rfl
          | inr pool =>
              cases pool with
              | create =>
                  rw [compile_create, private_create]
                  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, simulateQ_pure,
                    StateT.run_pure, bare_create, bind_map_left, map_bind, map_pure]
                  rw [bind_pure_comp]
                  apply congrArg (fun transform : IdentitySeed → Option (Nat × PublicIdentity) × BareState count =>
                    transform <$> sampleSeed)
                  funext seed
                  rfl
              | service identity request =>
                  simp only [compile, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
                  rfl
              | reveal identity =>
                  simp only [compile, StateT.run, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
                  rfl


/-- Exact arbitrary-continuation compilation retains the whole actual publicSource transcript and private identity state. -/
theorem compile_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp PrivateSourceSpec Result)
    (state : BareState count) (transcript : List Observation) :
    restore <$> ((simulateQ (bareImpl attachedVerify primitives count)
      ((simulateQ compile client).run transcript)).run state) =
      (simulateQ (privateImpl attachedVerify primitives count) client).run (restoreState state transcript) := by
  induction client using OracleComp.inductionOn generalizing state transcript with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      simp_rw [ih]
      rw [← compile_step attachedVerify primitives count query state transcript, bind_map_left]
      rfl


/-- The compiler performs exactly one ordinary source request per original private or public slot. -/
def translated : PrivateSourceSpec.Domain → SourceSpec.Domain
  | .inl coin => .inl (.inl coin)
  | .inr request => request

/-- Logging instrumentation changes no class count, even for rejected and private-coin requests. -/
theorem compile_step_bound (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (query : PrivateSourceSpec.Domain) (transcript : List Observation) :
    ((compile query).run transcript).IsQueryBoundP predicate (if predicate (translated query) then 1 else 0) := by
  cases query with
  | inl coin =>
      change OracleComp.IsQueryBoundP
        ((SourceSpec.query (.inl (.inl coin)) : OracleComp SourceSpec _) >>= _) _ _
      rw [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
      intro chosen
      simp [translated, chosen]
  | inr request =>
      cases request with
      | inl request =>
          change OracleComp.IsQueryBoundP
            ((SourceSpec.query (.inl request) : OracleComp SourceSpec _) >>= _) _ _
          rw [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          intro chosen
          simp [translated, chosen]
      | inr candidate =>
          change OracleComp.IsQueryBoundP
            ((SourceSpec.query (.inr candidate) : OracleComp SourceSpec _) >>= _) _ _
          rw [bind_pure_comp, isQueryBoundP_map_iff, isQueryBoundP_query_iff]
          intro chosen
          simp [translated, chosen]

/-- Arbitrary complete continuations inherit their chosen source class budget without treating private coins as free. -/
theorem compile_bound {Result : Type} (client : OracleComp PrivateSourceSpec Result)
    (predicate : SourceSpec.Domain → Prop) [DecidablePred predicate]
    (bound : Nat) (bounded : client.IsQueryBoundP (fun query => predicate (translated query)) bound)
    (transcript : List Observation) :
    ((simulateQ compile client).run transcript).IsQueryBoundP predicate bound := by
  exact bounded.simulateQ_run_StateT_of_step (fun query transcript => compile_step_bound predicate query transcript) transcript

/-- Private generation is embedded through the explicit private channel, independently of nested uniform-instance selection. -/
def localCoins {Result : Type} (client : ProbComp Result) : OracleComp PrivateSourceSpec Result :=
  simulateQ (fun query => (PrivateSourceSpec.query (.inl query) : OracleComp PrivateSourceSpec _)) client

/-- Existing public source requests keep their distinct explicit channel. -/
def publicSource {Result : Type} (client : OracleComp SourceSpec Result) : OracleComp PrivateSourceSpec Result :=
  simulateQ (fun query => (PrivateSourceSpec.query (.inr query) : OracleComp PrivateSourceSpec _)) client

/-- Private generation coins are interpreted directly, retaining every existing identity state component exactly. -/
theorem private_local_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : ProbComp Result) (state : BareState count) :
    ((simulateQ (privateImpl attachedVerify primitives count) (localCoins client)).run state) =
      (fun result => (result, state)) <$> client := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [localCoins, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change (do let answer ← (unifSpec.query query : ProbComp _)
                 (simulateQ (privateImpl attachedVerify primitives count) (localCoins (next answer))).run state) = _
      simp only [ih, map_bind]

/-- Interpreting the public channel preserves the complete original source state and all public coin observations. -/
theorem private_public_complete {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp SourceSpec Result) (state : BareState count) :
    ((simulateQ (privateImpl attachedVerify primitives count) (publicSource client)).run state) =
      ((simulateQ (bareImpl attachedVerify primitives count) client).run state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value => rfl
  | query_bind query next ih =>
      simp only [publicSource, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      change ((bareImpl attachedVerify primitives count query).run state >>= fun answer =>
        (simulateQ (privateImpl attachedVerify primitives count) (publicSource (next answer.1))).run answer.2) = _
      simp only [ih]


/-- Complete actual source execution, with protocol coins kept off the public identity transcript. -/
def privateRun {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp PrivateSourceSpec Result) :
    ProbComp (Result × BareState count) :=
  (simulateQ (privateImpl attachedVerify primitives count) client).run
    (PqxdhPhase1AcceptanceOracle.initialState count).2.source

/-- The source compiler's complete initial-state projection is exact before evaluated distributions. -/
theorem privateRun_eq {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (client : OracleComp PrivateSourceSpec Result) :
    privateRun attachedVerify primitives count client =
      restore <$> bareRun attachedVerify primitives count ((simulateQ compile client).run []) := by
  exact (compile_complete attachedVerify primitives count client
    (PqxdhPhase1AcceptanceOracle.initialState count).2.source []).symm

/-- Creation costs 32 private seed draws; all public and protocol-private explicit coins are charged together, with no synthetic-log cost. -/
theorem privateRun_uniform_bound {Result : Type}
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (count : Nat) (client : OracleComp PrivateSourceSpec Result) (qCreate qUniform : Nat)
    (creates : client.IsQueryBoundP
      (fun query => IsSourceClass (SourceClass IsCreate) (translated query)) qCreate)
    (coins : client.IsQueryBoundP
      (fun query => IsSourceClass (SourceClass PqxdhDynamicIdentityPool.IsUniform) (translated query)) qUniform) :
    (privateRun attachedVerify primitives count client).IsTotalQueryBound (32 * qCreate + qUniform) := by
  rw [privateRun_eq, IsTotalQueryBound, isQueryBound_map_iff]
  exact bareRun_uniform_bound attachedVerify primitives adapter count _ qCreate qUniform
    (compile_bound client _ qCreate creates []) (compile_bound client _ qUniform coins [])


set_option backward.isDefEq.respectTransparency false in
/-- Explicit public embedding forwards the same dependent source reply type. -/
theorem publicSource_query (query : SourceSpec.Domain) :
    publicSource (SourceSpec.query query : OracleComp SourceSpec _) =
      (PrivateSourceSpec.query (.inr query) : OracleComp PrivateSourceSpec _) := by
  unfold publicSource
  rw [simulateQ_spec_query]

/-- Explicit private embedding forwards the same uniform request without passing through the public branch. -/
theorem localCoins_query (query : unifSpec.Domain) :
    localCoins (unifSpec.query query : ProbComp _) =
      (PrivateSourceSpec.query (.inl query) : OracleComp PrivateSourceSpec _) := by
  simp only [localCoins, simulateQ_spec_query]

end BeaconcryptCore.Computational.PqxdhPrivateSourceCoins

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.bare_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.bare_create

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_create' does not depend on any axioms
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_create

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_create

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_step

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_step_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.compile_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_local_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_local_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_public_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.private_public_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.privateRun_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.privateRun_eq

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.privateRun_uniform_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.privateRun_uniform_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.publicSource_query' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.publicSource_query

/--
info: 'BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.localCoins_query' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhPrivateSourceCoins.localCoins_query
