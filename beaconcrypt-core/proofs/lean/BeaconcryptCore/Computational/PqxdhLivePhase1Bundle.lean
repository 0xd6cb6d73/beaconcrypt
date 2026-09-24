import BeaconcryptCore.Computational.PqxdhBeaconPhase1Publication

/-!
A live registration request uses the existing full native Phase1 publication boundary. Only Fresh draws local one-time material; FreshWithCoins uses its retained pair. The key-free signing client issues prekey, one-time and KEM messages in that order, before the original optional writer. Every rejected callback is retained and successful publication consumes the Fresh phase. Repeated requests therefore keep all prior joint signing events; they do not justify the single-bundle three-message hypothesis.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhLivePhase1Bundle
open PqxdhEd25519EufCma PqxdhJointPhase1SourceWriter PqxdhDynamicIdentityPool
open PqxdhBeaconPhase1Publication

variable {I D K : Type}

abbrev GenerateSpec (D : Type) := Unit →ₒ Option D
abbrev Spec (D : Type) := GenerateSpec D + (DynamicSpec + WriterSpec)

/-- Public projections expose no identity seed, private DH pair or KEM secret to the signing or serialization client. -/
structure Public (I D K : Type) where
  index : I → Nat
  identity : I → Ed25519PublicKey
  dh : D → X25519PublicKey
  kem : K → MlKem768PublicKey

/-- The source control stores the same 32 identity bytes as the signing service. -/
def identityArray (identity : Ed25519PublicKey) : Std.Array Std.U8 32#usize :=
  PqxdhRootTableInitialization.rootArray identity

def signing (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    OracleComp (Spec D) (Option Phase1Candidate) :=
  simulateQ (fun request => ((Spec D).query (.inr (.inl request)) : OracleComp (Spec D) _))
    (signingProgram index identity keys)

def writing (identity : Std.Array Std.U8 32#usize) (bundle : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    OracleComp (Spec D) (Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) :=
  simulateQ (fun request => ((Spec D).query (.inr (.inr request)) : OracleComp (Spec D) _))
    (afterSigning identity bundle generated state)

/-- The whole source continuation retains the same original state until all three signatures and serialization succeed. -/
def afterGenerated (projection : Public I D K) (generated : Option D)
    (state : State (I := I) (D := D) (K := K)) :
    OracleComp (Spec D) (Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) := do
  match prepare state generated with
  | none => pure (none, state)
  | some prepared =>
      let identity := projection.identity state.beacon.identity
      let keys : Phase1KeyTuple := ⟨projection.dh prepared.prekey, projection.dh prepared.oneTime, projection.kem prepared.kem⟩
      let bundle ← signing (projection.index state.beacon.identity) identity keys
      match bundle with
      | none => pure (none, state)
      | some bundle => writing (identityArray identity) bundle generated state

/-- Actual admission precedes generation, except the explicit regeneration helper modeled separately. -/
def bundle (projection : Public I D K) (state : State (I := I) (D := D) (K := K)) :
    OracleComp (Spec D) (Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) := do
  match state.beacon.phase with
  | .fresh _ _ _ =>
      let generated ← (Spec D).query (.inl ())
      afterGenerated projection generated state
  | .freshWithCoins _ _ _ _ => afterGenerated projection none state
  | _ => pure (none, state)

set_option backward.isDefEq.respectTransparency false in
/-- The existing signing interpreter is routed unchanged; all its replies and full callback state survive. -/
theorem signing_interpretation {A : Type}
    (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple) :
    simulateQ implementation (signing index identity keys) =
      simulateQ (fun request => implementation (.inr (.inl request)))
        (signingProgram index identity keys) := by
  rw [signing, ← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  simp [QueryImpl.apply_compose]

set_option backward.isDefEq.respectTransparency false in
/-- Serialization uses the original complete-state publication interpreter, with its actual optional byte reply. -/
theorem writing_interpretation {A : Type}
    (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (identity : Std.Array Std.U8 32#usize) (candidate : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    simulateQ implementation (writing identity candidate generated state) =
      simulateQ (fun request => implementation (.inr (.inr request)))
        (afterSigning identity candidate generated state) := by
  rw [writing, ← QueryImpl.simulateQ_compose]
  congr 1
  funext request
  simp [QueryImpl.apply_compose]

set_option backward.isDefEq.respectTransparency false in
/-- The exact native signature order and optional serialization retain every earlier callback state before the complete continuation. -/
theorem afterGenerated_complete {A Result : Type}
    (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (projection : Public I D K) (generated : Option D)
    (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ implementation (afterGenerated projection generated state)).run auxiliary >>= next =
      match prepare state generated with
      | none => next ((none, state), auxiliary)
      | some prepared =>
          (simulateQ (fun request => implementation (.inr (.inl request)))
            (signingProgram (projection.index state.beacon.identity)
              (projection.identity state.beacon.identity)
              ⟨projection.dh prepared.prekey, projection.dh prepared.oneTime, projection.kem prepared.kem⟩)).run auxiliary >>= fun signed =>
            match signed.1 with
            | none => next ((none, state), signed.2)
            | some candidate =>
                (simulateQ (fun request => implementation (.inr (.inr request)))
                  (afterSigning (identityArray (projection.identity state.beacon.identity))
                    candidate generated state)).run signed.2 >>= next := by
  unfold afterGenerated
  split
  all_goals simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, pure_bind, bind_assoc, signing_interpretation]
  apply bind_congr
  rintro ⟨_ | candidate, post⟩
  all_goals simp [writing_interpretation]

set_option backward.isDefEq.respectTransparency false in
/-- Fresh generation remains at its actual request time; retained coins and inactive phases cause no draw. Every full primitive poststate reaches the continuation. -/
theorem bundle_complete {A Result : Type}
    (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (projection : Public I D K) (state : State (I := I) (D := D) (K := K)) (auxiliary : A)
    (next : ((Option Pqxdh.Bytes × State (I := I) (D := D) (K := K)) × A) → ProbComp Result) :
    (simulateQ implementation (bundle projection state)).run auxiliary >>= next =
      match state.beacon.phase with
      | .fresh _ _ _ =>
          (implementation (.inl ())).run auxiliary >>= fun generated =>
            (simulateQ implementation (afterGenerated projection generated.1 state)).run generated.2 >>= next
      | .freshWithCoins _ _ _ _ =>
          (simulateQ implementation (afterGenerated projection none state)).run auxiliary >>= next
      | _ => next ((none, state), auxiliary) := by
  cases phase : state.beacon.phase <;>
    simp [bundle, phase, simulateQ_bind, StateT.run_bind, bind_assoc]

inductive Kind where
  | generation
  | signing
  | serialization
  deriving DecidableEq

def IsKind (kind : Kind) : (Spec D).Domain → Prop
  | .inl _ => kind = .generation
  | .inr (.inl _) => kind = .signing
  | .inr (.inr _) => kind = .serialization

instance (kind : Kind) : DecidablePred (IsKind (D := D) kind) := fun request => by
  cases request with
  | inl _ => exact inferInstanceAs (Decidable (kind = .generation))
  | inr query => cases query with
    | inl _ => exact inferInstanceAs (Decidable (kind = .signing))
    | inr _ => exact inferInstanceAs (Decidable (kind = .serialization))

set_option backward.isDefEq.respectTransparency false in
/-- The source signing block spends at most three service attempts, and no generator or writer request. -/
theorem signing_bound (index : Nat) (identity : Ed25519PublicKey) (keys : Phase1KeyTuple)
    (kind : Kind) :
    (signing (D := D) index identity keys).IsQueryBoundP (IsKind (D := D) kind)
      (if kind = .signing then 3 else 0) := by
  cases kind <;> simp [signing, signingProgram, IsKind, isQueryBoundP_query_bind_iff]
  all_goals intro pre; cases pre <;> simp [IsKind, isQueryBoundP_query_bind_iff]
  all_goals intro one; cases one <;> simp [IsKind, isQueryBoundP_query_iff]

set_option backward.isDefEq.respectTransparency false in
/-- The original writer is charged once even on failure; it makes no signing or generation request. -/
theorem writing_bound (identity : Std.Array Std.U8 32#usize) (candidate : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) (kind : Kind) :
    (writing identity candidate generated state).IsQueryBoundP (IsKind (D := D) kind)
      (if kind = .serialization then 1 else 0) := by
  unfold writing afterSigning
  split
  all_goals cases kind <;> simp [IsKind, isQueryBoundP_query_bind_iff]
  all_goals intro reply; cases reply <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- Preparation adds no hidden calls: three signing attempts and one serialization attempt cover every optional branch. -/
theorem afterGenerated_bound (projection : Public I D K) (generated : Option D)
    (state : State (I := I) (D := D) (K := K)) (kind : Kind) :
    (afterGenerated projection generated state).IsQueryBoundP (IsKind (D := D) kind)
      ((if kind = .signing then 3 else 0) + (if kind = .serialization then 1 else 0)) := by
  unfold afterGenerated
  split
  all_goals simp only [isQueryBoundP_pure]
  apply isQueryBoundP_bind (signing_bound _ _ _ kind)
  rintro (_ | candidate) _
  all_goals simp only [writing_bound, isQueryBoundP_pure]

set_option backward.isDefEq.respectTransparency false in
/-- One live bundle request costs at most one one-time generation, three signature-service attempts and one writer call, including failures. -/
theorem bundle_bound (projection : Public I D K)
    (state : State (I := I) (D := D) (K := K)) (kind : Kind) :
    (bundle projection state).IsQueryBoundP (IsKind (D := D) kind)
      ((if kind = .generation then 1 else 0) +
        ((if kind = .signing then 3 else 0) + (if kind = .serialization then 1 else 0))) := by
  cases phase : state.beacon.phase <;> simp only [bundle, phase, isQueryBoundP_pure]
  case fresh =>
    apply isQueryBoundP_bind
    · cases kind <;> simp [IsKind, isQueryBoundP_query_iff]
    · exact fun generated _ => afterGenerated_bound projection generated state kind
  case freshWithCoins =>
    exact (afterGenerated_bound projection none state kind).mono (Nat.le_add_left _ _)

set_option backward.isDefEq.respectTransparency false in
/-- Replacing private identity/KEM payloads by handles leaves the entire optional writer computation unchanged. -/
theorem writing_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (identity : Std.Array Std.U8 32#usize) (candidate : Phase1Candidate)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (fun result => (result.1, mapState identityMap kemMap result.2)) <$>
      writing identity candidate generated state =
      writing identity candidate generated (mapState identityMap kemMap state) := by
  unfold writing
  rw [← simulateQ_map, afterSigning_map]

set_option backward.isDefEq.respectTransparency false in
/-- Equal public projections suffice for the complete signing/publication client under private handle erasure; no secret value is requested from a handle. -/
theorem afterGenerated_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : Public I D K) (mapped : Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (identities : ∀ owner, mapped.identity (identityMap owner) = projection.identity owner)
    (dh : mapped.dh = projection.dh)
    (keys : ∀ key, mapped.kem (kemMap key) = projection.kem key)
    (generated : Option D) (state : State (I := I) (D := D) (K := K)) :
    (fun result => (result.1, mapState identityMap kemMap result.2)) <$>
      afterGenerated projection generated state =
      afterGenerated mapped generated (mapState identityMap kemMap state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase =>
      cases phase <;> cases generated <;>
        simp [afterGenerated, prepare, mapState, mapPhase, map_bind, indices, identities, dh, keys]
      all_goals apply bind_congr
      all_goals intro reply; cases reply
      all_goals first | rfl | exact writing_map identityMap kemMap _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The live request commutes with the complete private-state representation map, retaining generation at the same source position. -/
theorem bundle_map {I' K' : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : Public I D K) (mapped : Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (identities : ∀ owner, mapped.identity (identityMap owner) = projection.identity owner)
    (dh : mapped.dh = projection.dh)
    (keys : ∀ key, mapped.kem (kemMap key) = projection.kem key)
    (state : State (I := I) (D := D) (K := K)) :
    (fun result => (result.1, mapState identityMap kemMap result.2)) <$>
      bundle projection state = bundle mapped (mapState identityMap kemMap state) := by
  cases state with
  | mk beacon attempts =>
    cases beacon with
    | mk owner kid pin phase =>
      cases phase <;> simp only [bundle, mapState, mapPhase, map_bind, map_pure]
      all_goals first
        | exact afterGenerated_map identityMap kemMap projection mapped indices identities dh keys _ _
        | apply bind_congr
      all_goals intro generated
      all_goals exact afterGenerated_map identityMap kemMap projection mapped indices identities dh keys _ _

set_option backward.isDefEq.respectTransparency false in
/-- Evaluating the mapped live client keeps the complete primitive/signing/cache state alongside the exact mapped native role. -/
theorem bundle_map_run {I' K' A : Type} (identityMap : I → I') (kemMap : K → K')
    (projection : Public I D K) (mapped : Public I' D K')
    (indices : ∀ owner, mapped.index (identityMap owner) = projection.index owner)
    (identities : ∀ owner, mapped.identity (identityMap owner) = projection.identity owner)
    (dh : mapped.dh = projection.dh)
    (keys : ∀ key, mapped.kem (kemMap key) = projection.kem key)
    (implementation : QueryImpl (Spec D) (StateT A ProbComp))
    (state : State (I := I) (D := D) (K := K)) (auxiliary : A) :
    (fun result => ((result.1.1, mapState identityMap kemMap result.1.2), result.2)) <$>
      (simulateQ implementation (bundle projection state)).run auxiliary =
      (simulateQ implementation (bundle mapped (mapState identityMap kemMap state))).run auxiliary := by
  rw [← bundle_map identityMap kemMap projection mapped indices identities dh keys state]
  simp only [simulateQ_map, StateT.run_map]

/-- A bundle caller receives only optional serialized bytes; the complete private native role stays in the owner interpreter. -/
abbrev ApiSpec := Unit →ₒ Option Pqxdh.Bytes

def owner (projection : Public I D K) :
    QueryImpl ApiSpec (StateT (State (I := I) (D := D) (K := K)) (OracleComp (Spec D))) :=
  fun _ state => bundle projection state

/-- The public API wraps the exact original bundle computation without exposing the retained role state as its reply. -/
theorem owner_complete {Result : Type} (projection : Public I D K)
    (state : State (I := I) (D := D) (K := K))
    (next : Option Pqxdh.Bytes → State (I := I) (D := D) (K := K) → OracleComp (Spec D) Result) :
    (owner projection ()).run state >>= (fun result => next result.1 result.2) =
      bundle projection state >>= (fun result => next result.1 result.2) := rfl

/-- Every adaptive bundle attempt is counted: at most qBundle generations, 3*qBundle signatures and qBundle writers, with no query-count multiplier for the private state. -/
theorem schedule_bound {Result : Type} (projection : Public I D K)
    (client : OracleComp ApiSpec Result) (qBundle : Nat)
    (bounded : client.IsTotalQueryBound qBundle)
    (state : State (I := I) (D := D) (K := K)) (kind : Kind) :
    ((simulateQ (owner projection) client).run state).IsQueryBoundP (IsKind (D := D) kind)
      (((if kind = .generation then 1 else 0) +
        ((if kind = .signing then 3 else 0) + (if kind = .serialization then 1 else 0))) * qBundle) := by
  induction client using OracleComp.inductionOn generalizing qBundle state with
  | pure value => trivial
  | query_bind request next ih =>
    rw [isTotalQueryBound_query_bind_iff] at bounded
    rw [simulateQ_query_bind, StateT.run_bind]
    apply (isQueryBoundP_bind (bundle_bound projection state kind)
      (fun result _ => ih result.1 (qBundle - 1) (bounded.2 result.1) result.2)).mono
    cases kind <;> simp only [reduceCtorEq, ↓reduceIte, Nat.zero_add, Nat.add_zero, Nat.one_mul] <;> omega

end BeaconcryptCore.Computational.PqxdhLivePhase1Bundle

/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.signing_interpretation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.signing_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_interpretation
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.signing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.signing_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_bound
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.writing_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.afterGenerated_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_map
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_map_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.bundle_map_run
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.owner_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.owner_complete
/-- info: 'BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhLivePhase1Bundle.schedule_bound
