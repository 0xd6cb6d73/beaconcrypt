-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPool

/-!
# The source side of the prefix at the challenger's pool (CE-11b, unit U5, route P-a, third layer)

Route P-a of the second compile lemma (design-v2 section 8.3) runs the prefix of the ideal game pointwise in the challenger's pool: owner `j` holds pool entry `j` (at the cut this is `PqxdhDeploymentIdealCut.cut_entry_key`). `PqxdhDeploymentIdealPool` gives CE-3's compile lemma with both creates reading the pool, down to source14's native handler with the pool create (`revealPool`). This module carries the pool through item 2's source layers, from that native execution to item 2's KEM command program (`PqxdhRegistrationJointKemCommands.program`, the level at which item 2's prephase `PqxdhDeploymentIdealParams.preOpaquePool` runs the source program) under item 2's stopped selected-first router at the pool. Item 2's own chain draws KEM keys on demand (`PqxdhLiveKemBirth.impl`); at the pool, KEM creations are answered from the pairs (`PqxdhLiveKemReservation.reserved`, here `reservedAt`), and every other request is unchanged.

- Erasure (`programPool_native`): the annotated source schedule with the pool create (`sourcePool`; the create reads pool entry `owners.length`, `createSourcePool` with `materialPool`) erases to source14's native execution with the pool create (`PqxdhRegistrationJointServerSchedule.program_native` with the pool). The create case is `createSourcePool_native` (through `createPool_install`); every other request is item 2's.
- Encoding (`program_reserved`): the open command backend executed with the reserved services (`executeWith`, `PqxdhRegistrationJointOpenBackend.execute` with another interpretation of the private services) has the encoded distribution of the annotated pool source execution (`PqxdhRegistrationJointServerClient.program_source` with the pool), from a state with the source-side invariant `PoolOwned` (item 2's source ownership facts `PqxdhRegistrationJointServerSchedule.Owned` and one KEM key pair per owner). The create case is `create_reserved`: under the reserved services the indexed constructor reads the KEM key pair at the KEM pool's size (`client_reserved`), which is the owner count by `PoolOwned`. Every other request compiles to a private-service program without a KEM creation (`client_noCreate`, from item 2's creation bound `PqxdhRegistrationJointKemCommands.creations`), on which the reserved and the actual services agree (`reserved_noCreate`), so item 2's `PqxdhRegistrationJointServerClient.query_source` applies (`query_reserved`). `query_poolOwned` keeps the invariant (`source_counts`: every other request keeps the KEM key pairs and the owner count).
- Router (`stopped_program`): a private-service program within the pool and without KEM reveal, run by item 2's stopped selected-first router at the pairs (`PqxdhDynamicKemJointRouter.stopped`) from the router state of a prefix pool (`routerOf`, `PoolPrefix`), is its run under the reserved services, with every reply present and the router state of the final pool. This is an exact equality, not only a projection (`stopped_step`, `reserved_step_prefix`).
- Composition (`kemCommands_reserved`, `kemCommands_stopped`): item 2's KEM command program of a source program with at most `budget (.inl 1)` creations that reads no identity or KEM field, under the stopped router at the pairs, is the annotated pool source execution read off as the router's reply, the joint identity state and the router state. Together with `programPool_native`, the source14 native execution with the pool create and item 2's routed KEM command program are both images of one annotated pool source execution.

These are program equalities and invariant facts. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhJointIdentity (IdentitySeed PublicIdentity)
open PqxdhLiveKemReservation (Pair)
open PqxdhDeploymentIdealSteps (createPool)
open PqxdhDeploymentIdealPool (revealPool handlerPool)
open PqxdhRegistrationJointSchedule (State)
open PqxdhRegistrationJointCreation (Material)
open PqxdhRegistrationJointGeneratedFinish (EncodedState encodeState encodeEntry)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-! ### Erasure: the annotated source schedule with the pool create -/

section Erase
variable (setup : Setup baseSpec KemSK)

/-- The source constructor's draws with the KEM key pair read from the pool at an index: identity seed, prekey, then pool entry `index` (beyond the pool a fresh key pair, as `PqxdhRegistrationJointCreation.material` draws). -/
noncomputable def materialPool (pairs : List (Pair KemSK)) (index : ℕ) : ProbComp (Material KemSK) := do
  let seed ← PqxdhJointIdentity.sampleSeed
  let prekey ← PqxdhJointGapDh.sampleScalar
  let keys ← match pairs[index]? with
    | some keys => pure keys
    | none => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  pure ⟨seed, prekey, keys⟩

/-- The pool create installs the material of `materialPool` at the new owner's index (`PqxdhRegistrationJointCreation.native_source` with the pool). -/
theorem createPool_install (pairs : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) :
    (createPool setup pairs pin keyId).run state =
      PqxdhRegistrationJointCreation.install pin keyId state <$> materialPool setup pairs state.owners.length := by
  simp only [createPool, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure, bind_assoc,
    pure_bind, materialPool, map_bind]
  refine bind_congr fun seed => bind_congr fun prekey => ?_
  cases pairs[state.owners.length]? <;> simp [PqxdhRegistrationJointCreation.install]

/-- The annotated source create with the KEM key pair read from the pool at the new owner's index. -/
noncomputable def createSourcePool (pairs : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) : StateT (State KemSK) ProbComp ℕ :=
  fun state => PqxdhRegistrationJointSchedule.created setup pin keyId state <$> materialPool setup pairs state.owners.length

/-- Erasing the annotations of the annotated pool create gives the native pool create. -/
theorem createSourcePool_native (pairs : List (Pair KemSK)) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
        (createSourcePool setup pairs pin keyId).run state =
      (createPool setup pairs pin keyId).run (PqxdhRegistrationJointSchedule.source state) := by
  rw [createPool_install]
  have length : (PqxdhRegistrationJointSchedule.source state).owners.length = state.owners.length := by
    simp [PqxdhRegistrationJointSchedule.source]
  simp only [createSourcePool, StateT.run, Functor.map_map, length]
  congr 1; funext value
  simp [PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointSchedule.source,
    PqxdhRegistrationJointSchedule.birth, PqxdhRegistrationJointCreation.install]

variable (codec : Codec Reader Response) (checks : Checks)

/-- The annotated source schedule with the pool create (`PqxdhRegistrationJointServerSchedule.source` with `create` replaced by `createSourcePool`). -/
noncomputable def sourcePool (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK)) :
    QueryImpl (PqxdhRegistrationJointRevealSchedule.Spec KemSK) (StateT (State KemSK) ProbComp)
  | .inl (.inr (.create pin keyId)) => createSourcePool setup pairs pin keyId
  | query => PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query

/-- Every request of the annotated pool source schedule erases to the native pool request. -/
theorem sourcePool_native (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
        (sourcePool setup codec checks seed identityIndex pairs query).run state =
      (revealPool setup codec checks seed pairs query).run (PqxdhRegistrationJointSchedule.source state) := by
  rcases query with (coin | request) | read
  · exact PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex (.inl (.inl coin)) state
  · cases request with
    | create pin keyId => exact createSourcePool_native setup pairs pin keyId state
    | _ => exact PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex _ state
  · exact PqxdhRegistrationJointServerSchedule.query_native setup codec checks seed identityIndex (.inr read) state

/-- The whole annotated pool source execution erases to the native pool execution (`PqxdhRegistrationJointServerSchedule.program_native` with the pool). -/
theorem programPool_native (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK) :
    (fun result => (result.1, PqxdhRegistrationJointSchedule.source result.2)) <$>
        (simulateQ (sourcePool setup codec checks seed identityIndex pairs) program).run state =
      (simulateQ (revealPool setup codec checks seed pairs) program).run (PqxdhRegistrationJointSchedule.source state) := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind, ih]
      simpa only [bind_map_left] using congrArg
        (fun work => work >>= fun result =>
          (simulateQ (revealPool setup codec checks seed pairs) (next result.1)).run result.2)
        (sourcePool_native setup codec checks seed identityIndex pairs query state)

end Erase


/-! ### Encoding: the open command backend with the reserved services -/

section Encode
variable (setup : Setup baseSpec KemSK)

/-- The private identity and KEM services with the KEM creations answered from the pool (`PqxdhLiveKemReservation.reserved`). -/
abbrev reservedAt (pairs : List (Pair KemSK)) :=
  PqxdhLiveKemReservation.reserved setup.baseImpl setup.joint setup.kem pairs

/-- A private-service request is a KEM creation exactly when its pool class is the KEM creation class. -/
theorem isCreate_class :
    (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) =
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .kemCreate) := by
  funext query
  rcases query with (coin | request) | (coin | request)
  case inl.inl => simp [PqxdhLiveKemReservation.IsCreate, PqxdhRegistrationJointServiceCosts.poolClass]
  case inl.inr =>
    cases request <;> simp only [PqxdhLiveKemReservation.IsCreate, PqxdhRegistrationJointServiceCosts.poolClass]
    case service index call => cases call <;> simp
    all_goals simp
  case inr.inl => simp [PqxdhLiveKemReservation.IsCreate, PqxdhRegistrationJointServiceCosts.poolClass]
  case inr.inr => cases request <;> simp [PqxdhLiveKemReservation.IsCreate, PqxdhRegistrationJointServiceCosts.poolClass]

/-- The reserved services agree with the actual services on every request other than a KEM creation. -/
theorem reserved_agree (pairs : List (Pair KemSK)) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (other : ¬ PqxdhLiveKemReservation.IsCreate query) :
    reservedAt setup pairs query = PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem query := by
  funext state
  rcases query with joint | (coin | request)
  · rfl
  · rfl
  · cases request with
    | create => exact absurd trivial other
    | _ => rfl

/-- A program without a KEM creation runs identically under the reserved and the actual services. -/
theorem reserved_noCreate {α : Type} (pairs : List (Pair KemSK)) (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α)
    (none : work.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0) :
    simulateQ (reservedAt setup pairs) work = simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) work :=
  PqxdhDeploymentIdealPool.simulateQ_congr_none _ _ _ (reserved_agree setup pairs) work none

/-- Local coins keep both private services under the reserved services (`PqxdhLiveKemBirth.coins_complete`). -/
theorem coins_reserved {α : Type} (pairs : List (Pair KemSK)) (work : ProbComp α) (state : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (reservedAt setup pairs) (PqxdhLiveKemBirth.coins work)).run state =
      (fun result => (result, state)) <$> work := by
  rw [reserved_noCreate setup pairs _ (by
    rw [PqxdhLiveKemBirth.coins_class]
    convert OracleComp.isQueryBoundP_false work 0 using 2
    simp [PqxdhLiveKemReservation.IsCreate]),
    PqxdhLiveKemBirth.coins_complete]

/-- The indexed constructor client under the reserved services draws the identity seed and the prekey and reads the KEM key pair from the pool at the KEM pool's size (`PqxdhRegistrationJointCreation.client_material` with the pool). -/
theorem client_reserved (pairs : List (Pair KemSK)) (pool : PqxdhLiveKemBirth.State KemSK) :
    (simulateQ (reservedAt setup pairs) (PqxdhRegistrationJointCreation.client (KemSK := KemSK))).run pool =
      PqxdhRegistrationJointCreation.serviceView setup pool <$> materialPool setup pairs pool.2.keys.length := by
  simp only [PqxdhRegistrationJointCreation.client, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem (.inl (.inr .create))).run pool >>= _) = _
  rw [PqxdhLiveKemBirth.joint_step, PqxdhDynamicIdentityPool.lazyImpl_create]
  simp only [bind_map_left, map_bind, PqxdhDynamicIdentityPool.createdReply, materialPool]
  refine bind_congr fun seed => ?_
  simp only [simulateQ_bind, StateT.run_bind, coins_reserved, bind_map_left, simulateQ_spec_query, simulateQ_pure,
    StateT.run_pure]
  refine bind_congr fun prekey => ?_
  rcases found : pairs[pool.2.keys.length]? with _ | keys
  · simp only [reservedAt, PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, PqxdhLiveKemBirth.poolImpl,
      StateT.run, found, bind_map_left, map_bind, map_pure]
    simp [PqxdhRegistrationJointCreation.serviceView, PqxdhLiveKemBirth.created, PqxdhDynamicIdentityPool.createdReply]
    exact (Functor.map_map _ _ _).trans rfl
  · simp [reservedAt, PqxdhLiveKemReservation.reserved, StateT.run, found,
      PqxdhRegistrationJointCreation.serviceView, PqxdhLiveKemBirth.created, PqxdhDynamicIdentityPool.createdReply]


variable (codec : Codec Reader Response) (checks : Checks)

/-- The open command backend run with any interpretation of the private identity and KEM services (`PqxdhRegistrationJointOpenBackend.run`, which uses the actual services `PqxdhLiveKemBirth.impl`). -/
def runWith {Local α : Type}
    (service : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp))
    (work : StateT Local (OracleComp (PqxdhLiveKemBirth.Spec KemSK)) α)
    (state : PqxdhRegistrationJointPreparation.Pool KemSK × Local) :
    ProbComp (α × (PqxdhRegistrationJointPreparation.Pool KemSK × Local)) :=
  (fun result => (result.1.1, (result.2, result.1.2))) <$> (simulateQ service (work.run state.2)).run state.1

/-- The open command client executed with any interpretation of the private services (`PqxdhRegistrationJointOpenBackend.execute` with `service`). -/
noncomputable def executeWith {α : Type}
    (service : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp))
    (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) (state : EncodedState KemSK) :
    ProbComp (α × EncodedState KemSK) :=
  (fun result => (result.1.1, ⟨result.2.1, result.2.2, result.1.2⟩)) <$>
    runWith service (PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity work
      state.owners) (state.pool, state.shared)

/-- With the actual private services, `executeWith` is the open backend's execution. -/
theorem executeWith_impl {α : Type} (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) (state : EncodedState KemSK) :
    executeWith setup codec checks (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) identityIndex
        publicIdentity work state =
      PqxdhRegistrationJointOpenBackend.execute setup codec checks identityIndex publicIdentity work state := rfl

/-- Reassociating the client and backend state keeps the continuation (`PqxdhRegistrationJointServerClient.execute_bind`). -/
theorem executeWith_bind {α β : Type}
    (service : QueryImpl (PqxdhLiveKemBirth.Spec KemSK) (StateT (PqxdhLiveKemBirth.State KemSK) ProbComp))
    (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α)
    (next : α → PqxdhRegistrationJointServiceSchedule.Client KemSK Response β) (state : EncodedState KemSK) :
    executeWith setup codec checks service identityIndex publicIdentity (work >>= next) state =
      (executeWith setup codec checks service identityIndex publicIdentity work state >>= fun result =>
        executeWith setup codec checks service identityIndex publicIdentity (next result.1) result.2) := by
  simp only [executeWith, runWith, PqxdhRegistrationJointOpenBackend.compile, StateT.run_bind, simulateQ_bind,
    map_bind, bind_map_left]

/-- A client whose compiled program creates no KEM key runs identically under the reserved and the actual services. -/
theorem executeWith_noCreate {α : Type} (pairs : List (Pair KemSK)) (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (work : PqxdhRegistrationJointServiceSchedule.Client KemSK Response α) (state : EncodedState KemSK)
    (none : ((PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity work
      state.owners).run state.shared).IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0) :
    executeWith setup codec checks (reservedAt setup pairs) identityIndex publicIdentity work state =
      PqxdhRegistrationJointOpenBackend.execute setup codec checks identityIndex publicIdentity work state := by
  rw [← executeWith_impl]
  simp only [executeWith, runWith, reserved_noCreate setup pairs _ none]

/-- Every source request other than a creation compiles to a private-service program without a KEM creation (`PqxdhRegistrationJointKemCommands.creations` for the one-request program). -/
theorem client_noCreate (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 1)
    (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ((PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity
      (PqxdhRegistrationJointRevealSchedule.client setup codec query) owners).run shared).IsQueryBoundP
        (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
  have bound := PqxdhRegistrationJointKemCommands.creations setup codec checks identityIndex publicIdentity
    ((PqxdhRegistrationJointRevealSchedule.Spec KemSK).query query)
    (fun source => if PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source then 1 else 0)
    (fun source => by
      rw [isQueryBoundP_query_iff]
      intro hit
      simp [hit])
    owners shared
  simpa only [PqxdhRegistrationJointKemCommands.program, simulateQ_spec_query, other, ↓reduceIte] using bound

/-- The open backend lifts a private-service program through the client's private-service channel without touching the native state. -/
theorem compile_poolLift {α : Type} (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (work : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    (simulateQ (PqxdhRegistrationJointOpenBackend.impl setup codec checks identityIndex publicIdentity)
      (simulateQ PqxdhRegistrationJointServiceSchedule.poolLift work)).run shared =
      (fun answer => (answer, shared)) <$> work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRegistrationJointServiceSchedule.poolLift,
        StateT.run_bind, map_bind]
      change (PqxdhRegistrationJointOpenBackend.pool query).run shared >>= _ = _
      simp only [PqxdhRegistrationJointOpenBackend.pool, StateT.run, bind_map_left]
      exact bind_congr fun answer => ih answer

/-- The open backend runs the executable constructor as the indexed constructor client, then installs the encoded owner. -/
theorem compile_create (identityIndex : ℕ) (publicIdentity : PublicIdentity) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (owners : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry)
    (shared : PqxdhServerAuthNative.NativeState KemSK) :
    (PqxdhRegistrationJointOpenBackend.compile setup codec checks identityIndex publicIdentity
      (PqxdhRegistrationJointServiceSchedule.create (Response := Response) pin keyId) owners).run shared =
      (fun value => ((owners.length, match value with
        | none => owners
        | some value => owners ++ [PqxdhRegistrationJointServiceSchedule.birth pin keyId value]), shared)) <$>
        PqxdhRegistrationJointCreation.client (KemSK := KemSK) := by
  have shape : (PqxdhRegistrationJointServiceSchedule.create (KemSK := KemSK) (Response := Response) pin keyId).run owners =
      (fun value => (owners.length, match value with
        | none => owners
        | some value => owners ++ [PqxdhRegistrationJointServiceSchedule.birth pin keyId value])) <$>
        simulateQ PqxdhRegistrationJointServiceSchedule.poolLift PqxdhRegistrationJointCreation.client := by
    simp only [PqxdhRegistrationJointServiceSchedule.create, StateT.run, bind_pure_comp]
    rfl
  rw [PqxdhRegistrationJointOpenBackend.compile, shape, simulateQ_map, StateT.run_map, compile_poolLift, Functor.map_map]

/-- The executable constructor under the reserved services has the encoded distribution of the annotated pool create, when the KEM pool holds one key pair per owner (`PqxdhRegistrationJointServerClient.create_source` with the pool). -/
theorem create_reserved (pairs : List (Pair KemSK)) (identityIndex : ℕ) (publicIdentity : PublicIdentity)
    (pin : PqxdhBeaconPhase2Preparation.Word32) (keyId : Std.U64) (state : State KemSK)
    (counted : state.pool.2.keys.length = state.owners.length) :
    executeWith setup codec checks (reservedAt setup pairs) identityIndex publicIdentity
        (PqxdhRegistrationJointServiceSchedule.create pin keyId) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$> (createSourcePool setup pairs pin keyId).run state := by
  rw [executeWith, runWith, compile_create, simulateQ_map, StateT.run_map, client_reserved]
  change _ = (fun result => (result.1, encodeState setup result.2)) <$>
    (PqxdhRegistrationJointSchedule.created setup pin keyId state <$> materialPool setup pairs state.owners.length)
  simp only [Functor.map_map]
  rw [show (encodeState setup state).pool.2.keys.length = state.owners.length from counted]
  refine congrArg (fun f => f <$> materialPool setup pairs state.owners.length) (funext fun value => ?_)
  simp [encodeState, encodeEntry, PqxdhRegistrationJointSchedule.created, PqxdhRegistrationJointSchedule.birth,
    PqxdhRegistrationJointCreation.serviceView, PqxdhRegistrationJointServiceSchedule.birth,
    PqxdhRegistrationJointBundle.encode, PqxdhBeaconPhase1Publication.mapState,
    PqxdhBeaconPhase1Publication.mapPhase, PqxdhRegistrationJointBundle.identityMap,
    PqxdhRegistrationJointBundle.keyMap]

/-- The source-side representation invariant at the pool: item 2's source ownership facts (`PqxdhRegistrationJointServerSchedule.Owned`, item 2's source-schedule representation invariant: every owner's slots, the Server's identity slot) and one KEM key pair per owner. -/
def PoolOwned (seed : IdentitySeed) (identityIndex : ℕ) (state : State KemSK) : Prop :=
  PqxdhRegistrationJointServerSchedule.Owned seed identityIndex state ∧ state.pool.2.keys.length = state.owners.length

/-- Every request of the annotated source schedule other than a creation keeps the KEM key pairs and the number of owners. -/
theorem source_counts (seed : IdentitySeed) (identityIndex : ℕ)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId))) (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (supported : result ∈ support
      ((PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query).run state)) :
    result.2.pool.2.keys = state.pool.2.keys ∧ result.2.owners.length = state.owners.length := by
  have shared : ∀ {Value : Type} (work : PqxdhServerAuthNative.NativeGame KemSK Value) (result : Value × State KemSK),
      result ∈ support ((PqxdhRegistrationJointSchedule.onShared work).run state) →
        result.2.pool.2.keys = state.pool.2.keys ∧ result.2.owners.length = state.owners.length := by
    intro Value work result member
    simp only [PqxdhRegistrationJointSchedule.onShared, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨reached, _, rfl⟩ := member
    exact ⟨rfl, rfl⟩
  rcases query with (coin | request) | read
  case inl.inl =>
    simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
      PqxdhRegistrationJointSchedule.handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
    obtain ⟨_, _, rfl⟩ := supported
    exact ⟨rfl, rfl⟩
  case inl.inr =>
    cases request with
    | create pin keyId => exact absurd rfl (notCreate pin keyId)
    | accept raw =>
        change result ∈ support ((PqxdhRegistrationJointServerSchedule.onBackend
          (PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw)).run state) at supported
        obtain ⟨reached, member, rfl⟩ : ∃ reached ∈ support
            ((PqxdhRegistrationJointServerAccept.source setup codec checks seed identityIndex raw).run
              (state.pool, state.shared)),
            (reached.1, { state with pool := reached.2.1, shared := reached.2.2 }) = result := by
          simpa only [PqxdhRegistrationJointServerSchedule.onBackend, StateT.run, support_map, Set.mem_image]
            using supported
        exact ⟨(PqxdhRegistrationJointServerAccept.source_slots setup codec checks seed identityIndex raw
          (state.pool, state.shared) reached member).2, rfl⟩
    | bundle address =>
        cases found : state.owners[address]? <;>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.bundle, StateT.run, found,
            support_map, Set.mem_image, mem_support_pure_iff] at supported
        case none => exact supported ▸ ⟨rfl, rfl⟩
        case some entry =>
          obtain ⟨reached, _, rfl⟩ := supported
          exact ⟨rfl, List.length_set⟩
    | finish address raw =>
        cases found : state.owners[address]? <;>
          simp only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source,
            PqxdhRegistrationJointSchedule.handler, PqxdhRegistrationJointSchedule.finish, StateT.run, found,
            support_map, Set.mem_image, mem_support_pure_iff] at supported
        case none => exact supported ▸ ⟨rfl, rfl⟩
        case some entry =>
          obtain ⟨reached, member, rfl⟩ := supported
          exact ⟨(PqxdhRegistrationJointFinish.annotated_program_slots setup codec entry.identityIndex entry.kemIndex
            (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw entry.owner) (state.pool, state.shared)
            reached member).2, List.length_set⟩
    | build session payload => exact shared _ result supported
    | hmac key message => exact shared _ result supported
    | hash bytes => exact shared _ result supported
    | reveal keyId => exact shared _ result supported
  case inr =>
    have reached : result = PqxdhRegistrationJointLiveRead.sourceStep read state := by
      simpa only [PqxdhRegistrationJointServerSchedule.source, PqxdhRegistrationJointRevealSchedule.source, StateT.run,
        support_pure, Set.mem_singleton_iff] using supported
    subst reached
    cases found : state.owners[read.1]? with
    | none => simp [PqxdhRegistrationJointLiveRead.sourceStep, found]
    | some entry =>
        simp only [PqxdhRegistrationJointLiveRead.sourceStep, found]
        exact ⟨(PqxdhRegistrationJointLiveRead.entry_slots read.2 entry state.pool).2, trivial⟩

/-- Every request of the annotated pool source schedule keeps the source-side representation invariant at the pool. -/
theorem query_poolOwned (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (result : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Range query × State KemSK)
    (owned : PoolOwned seed identityIndex state)
    (supported : result ∈ support ((sourcePool setup codec checks seed identityIndex pairs query).run state)) :
    PoolOwned seed identityIndex result.2 := by
  by_cases created : ∃ pin keyId, query = .inl (.inr (.create pin keyId))
  · obtain ⟨pin, keyId, rfl⟩ := created
    change result ∈ support (PqxdhRegistrationJointSchedule.created setup pin keyId state <$>
      materialPool setup pairs state.owners.length) at supported
    rw [support_map] at supported
    obtain ⟨material, _, rfl⟩ := supported
    refine ⟨⟨PqxdhRegistrationJointSchedule.created_owned setup pin keyId state material owned.1.1, ?_⟩, ?_⟩
    · change (state.pool.1.seeds ++ [material.seed])[identityIndex]? = some seed
      simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp owned.1.2).choose] using owned.1.2
    · change (state.pool.2.keys ++ [material.keys]).length = (state.owners ++ _).length
      simp only [List.length_append, List.length_singleton, owned.2]
  · have notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId)) := fun pin keyId same =>
      created ⟨pin, keyId, same⟩
    have same : sourcePool setup codec checks seed identityIndex pairs query =
        PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query := by
      rcases query with (coin | request) | read
      · rfl
      · cases request with
        | create pin keyId => exact absurd rfl (notCreate pin keyId)
        | _ => rfl
      · rfl
    rw [same] at supported
    have counts := source_counts setup codec checks seed identityIndex query notCreate state result supported
    exact ⟨PqxdhRegistrationJointServerSchedule.query_invariant setup codec checks seed identityIndex query state result
      owned.1 supported, by rw [counts.1, counts.2, owned.2]⟩

/-- Every source request, executed by the open backend with the reserved services, has the encoded distribution of the annotated pool source request (`PqxdhRegistrationJointServerClient.query_source` with the pool). -/
theorem query_reserved (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (state : State KemSK)
    (owned : PoolOwned seed identityIndex state) :
    executeWith setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        (PqxdhRegistrationJointRevealSchedule.client setup codec query) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (sourcePool setup codec checks seed identityIndex pairs query).run state := by
  by_cases created : ∃ pin keyId, query = .inl (.inr (.create pin keyId))
  · obtain ⟨pin, keyId, rfl⟩ := created
    exact create_reserved setup codec checks pairs identityIndex _ pin keyId state owned.2
  · have other : PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query ≠ .inl 1 := by
      intro kind
      apply created
      rcases query with (coin | request) | read
      · exact absurd kind (by simp [PqxdhRegistrationJointRevealCosts.sourceKind, PqxdhRegistrationSchedule.sourceKind])
      · cases request with
        | create pin keyId => exact ⟨pin, keyId, rfl⟩
        | _ => exact absurd kind (by simp [PqxdhRegistrationJointRevealCosts.sourceKind,
            PqxdhRegistrationSchedule.sourceKind])
      · exact absurd kind (by simp [PqxdhRegistrationJointRevealCosts.sourceKind])
    have same : sourcePool setup codec checks seed identityIndex pairs query =
        PqxdhRegistrationJointServerSchedule.source setup codec checks seed identityIndex query := by
      rcases query with (coin | request) | read
      · rfl
      · cases request with
        | create pin keyId => exact absurd ⟨pin, keyId, rfl⟩ created
        | _ => rfl
      · rfl
    rw [executeWith_noCreate setup codec checks pairs identityIndex _ _ _
        (client_noCreate setup codec checks identityIndex _ query other _ _),
      PqxdhRegistrationJointOpenBackend.execute_run,
      PqxdhRegistrationJointServerClient.query_source setup codec checks seed identityIndex query state owned.1, same]

/-- Any source program executed by the open backend with the reserved services has the encoded distribution of the annotated pool source execution (`PqxdhRegistrationJointServerClient.program_source` with the pool), from a state with the source-side representation invariant at the pool. -/
theorem program_reserved (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK)
    (owned : PoolOwned seed identityIndex state) :
    executeWith setup codec checks (reservedAt setup pairs) identityIndex (setup.joint.publicKeys seed)
        (simulateQ (PqxdhRegistrationJointRevealSchedule.client setup codec) program) (encodeState setup state) =
      (fun result => (result.1, encodeState setup result.2)) <$>
        (simulateQ (sourcePool setup codec checks seed identityIndex pairs) program).run state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure value => simp [executeWith, runWith, PqxdhRegistrationJointOpenBackend.compile, simulateQ_pure, StateT.run_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, executeWith_bind,
        query_reserved setup codec checks seed identityIndex pairs query state owned, bind_map_left, StateT.run_bind,
        map_bind]
      apply bind_congr_of_forall_mem_support
      exact fun result supported => ih result.1 result.2
        (query_poolOwned setup codec checks seed identityIndex pairs query state result owned supported)

end Encode


/-! ### The stopped selected-first router at the pool -/

section Router
variable (setup : Setup baseSpec KemSK)

/-- The router state of a KEM pool: one creation per key pair, the pool's history, no stop. -/
def routerOf (pool : PqxdhLiveKemBirth.Pool KemSK) : PqxdhDynamicKemRouter.State KemSK :=
  ⟨pool.keys.length, pool.transcript, false, false⟩

/-- A KEM pool whose key pairs are the first entries of the pairs, in order. -/
def PoolPrefix (pairs : List (Pair KemSK)) (pool : PqxdhLiveKemBirth.Pool KemSK) : Prop :=
  pool.keys = pairs.take pool.keys.length

/-- The empty KEM pool is a prefix of every list of pairs, and its router state is the empty router state. -/
theorem empty_prefix (pairs : List (Pair KemSK)) :
    PoolPrefix pairs PqxdhLiveKemBirth.empty ∧ routerOf (PqxdhLiveKemBirth.empty : PqxdhLiveKemBirth.Pool KemSK) =
      PqxdhDynamicKemRouter.empty :=
  ⟨by simp [PoolPrefix, PqxdhLiveKemBirth.empty], rfl⟩

/-- One request of the stopped selected-first router at the pairs, from the router state of a prefix pool, is the request under the reserved services followed by the router state of the new pool, for every request but a KEM reveal and within the pool. -/
theorem stopped_step (selected : ℕ) (pairs : List (Pair KemSK)) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (notReveal : PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query ≠ .other)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool)
    (room : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length) :
    ((PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs query).run).run
        (joint, routerOf pool) =
      (fun result => (some result.1, (result.2.1, routerOf result.2.2))) <$>
        (reservedAt setup pairs query).run (joint, pool) := by
  rcases query with request | (coin | request)
  · simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
      PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
  · simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
      PqxdhLiveKemReservation.reserved, PqxdhLiveKemBirth.impl, StateT.run, Functor.map_map]
  · cases request with
    | create =>
        have before : pool.keys.length < pairs.length := by
          simpa [PqxdhLiveKemReservation.IsCreate] using room
        have found : pairs[pool.keys.length]? = some pairs[pool.keys.length] :=
          List.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
        simp [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
          PqxdhLiveKemReservation.reserved, PqxdhDynamicKemRouter.source, StateT.run, routerOf, found,
          PqxdhLiveKemBirth.created, PqxdhDynamicKemRouter.record, PqxdhLiveKemBirth.record]
    | decapsulate index ciphertext =>
        have keys : pairs.take pool.keys.length = pool.keys := prefixed.symm
        simp only [PqxdhDynamicKemJointRouter.stopped, PqxdhDynamicKemJointRouter.combine, OptionT.run_mk, reservedAt,
          PqxdhLiveKemReservation.reserved, PqxdhDynamicKemRouter.source, PqxdhLiveKemBirth.impl,
          PqxdhLiveKemBirth.poolImpl, StateT.run, routerOf, keys]
        cases pool.keys[index]? <;>
          simp [PqxdhDynamicKemRouter.record, PqxdhLiveKemBirth.record, Functor.map_map]
    | reveal index => exact absurd rfl notReveal


/-- Every reply of the reserved services within the pool keeps a prefix pool, with one more key pair exactly after a KEM creation. -/
theorem reserved_step_prefix (pairs : List (Pair KemSK)) (query : (PqxdhLiveKemBirth.Spec KemSK).Domain)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool)
    (room : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤ pairs.length)
    (result : (PqxdhLiveKemBirth.Spec KemSK).Range query × PqxdhLiveKemBirth.State KemSK)
    (supported : result ∈ support ((reservedAt setup pairs query).run (joint, pool))) :
    PoolPrefix pairs result.2.2 ∧
      result.2.2.keys.length = pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) := by
  by_cases creates : PqxdhLiveKemReservation.IsCreate query
  · rcases query with request | (coin | request)
    · exact absurd creates id
    · exact absurd creates id
    · cases request with
      | create =>
          have before : pool.keys.length < pairs.length := by
            simpa [PqxdhLiveKemReservation.IsCreate] using room
          have found : pairs[pool.keys.length]? = some pairs[pool.keys.length] :=
            List.getElem?_eq_some_iff.mpr ⟨before, rfl⟩
          simp only [reservedAt, PqxdhLiveKemReservation.reserved, StateT.run, found, support_pure,
            Set.mem_singleton_iff] at supported
          subst supported
          refine ⟨?_, by simp [PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, PqxdhLiveKemReservation.IsCreate]⟩
          simp only [PoolPrefix, PqxdhLiveKemBirth.created, PqxdhLiveKemBirth.record, List.length_append,
            List.length_singleton]
          rw [List.take_add_one, ← prefixed, found]
          rfl
      | _ => exact absurd creates id
  · rw [reserved_agree setup pairs query creates] at supported
    have keys := PqxdhLiveKemReservation.noncreate_keys setup.baseImpl setup.joint setup.kem query creates
      (joint, pool) result supported
    refine ⟨?_, by simp [keys, creates]⟩
    simp only [PoolPrefix, keys]
    exact prefixed

/-- A private-service program with at most `qCreate` KEM creations within the pool and no KEM reveal (no request of the pool class `other`), run by item 2's stopped selected-first router at the pairs from the router state of a prefix pool, is its run under the reserved services, with every reply present and the router state of the final pool. -/
theorem stopped_program {α : Type} (selected : ℕ) (pairs : List (Pair KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (qCreate : ℕ)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (noReveal : client.IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool) (room : pool.keys.length + qCreate ≤ pairs.length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        client).run).run (joint, routerOf pool) =
      (fun result => (some result.1, (result.2.1, routerOf result.2.2))) <$>
        (simulateQ (reservedAt setup pairs) client).run (joint, pool) := by
  induction client using OracleComp.inductionOn generalizing qCreate joint pool with
  | pure value => simp
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded noReveal
      have notReveal : PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query ≠ .other := by
        intro other
        rcases noReveal.1 with absent | impossible
        · exact absent other
        · exact absurd impossible (Nat.lt_irrefl 0)
      have affordable : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤
          pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind,
        stopped_step setup selected pairs query notReveal joint pool prefixed affordable, bind_map_left,
        Option.elim_some]
      apply bind_congr_of_forall_mem_support
      rintro ⟨answer, after⟩ supported
      have step := reserved_step_prefix setup pairs query joint pool prefixed affordable (answer, after) supported
      have nextRoom : after.2.keys.length + (if PqxdhLiveKemReservation.IsCreate query then qCreate - 1 else qCreate) ≤
          pairs.length := by
        rw [step.2]
        split_ifs at affordable ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      exact ih answer _ (bounded.2 answer) (by simpa [notReveal] using noReveal.2 answer)
        after.1 after.2 step.1 nextRoom

/-- Every outcome of the reserved services on a private-service program with at most `qCreate` KEM creations, from a prefix pool with room for them, has a prefix pool with at most `qCreate` more key pairs. -/
theorem reserved_program_prefix {α : Type} (pairs : List (Pair KemSK))
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (qCreate : ℕ)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PoolPrefix pairs pool) (room : pool.keys.length + qCreate ≤ pairs.length)
    (result : α × PqxdhLiveKemBirth.State KemSK)
    (supported : result ∈ support ((simulateQ (reservedAt setup pairs) client).run (joint, pool))) :
    PoolPrefix pairs result.2.2 ∧ result.2.2.keys.length ≤ pool.keys.length + qCreate := by
  induction client using OracleComp.inductionOn generalizing qCreate joint pool with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      exact ⟨prefixed, Nat.le_add_right _ _⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      have affordable : pool.keys.length + (if PqxdhLiveKemReservation.IsCreate query then 1 else 0) ≤
          pairs.length := by
        split_ifs with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨⟨answer, after⟩, first, rest⟩ := supported
      have step := reserved_step_prefix setup pairs query joint pool prefixed affordable (answer, after) first
      have nextRoom : after.2.keys.length + (if PqxdhLiveKemReservation.IsCreate query then qCreate - 1 else qCreate) ≤
          pairs.length := by
        rw [step.2]
        split_ifs at affordable ⊢ with creates
        · have positive := bounded.1.resolve_left (not_not.mpr creates)
          omega
        · omega
      obtain ⟨prefixedNext, countNext⟩ := ih answer _ (bounded.2 answer) after.1 after.2 step.1 nextRoom rest
      refine ⟨prefixedNext, ?_⟩
      rw [step.2] at countNext
      split_ifs at countNext with creates
      · have positive := bounded.1.resolve_left (not_not.mpr creates)
        omega
      · omega

end Router


/-! ### Item 2's KEM commands at the pool -/

section Commands
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Item 2's KEM command program (`PqxdhRegistrationJointKemCommands.program`, the source program compiled to the open private-service interface) under the reserved services, from the encoded state of an annotated source state with the source-side invariant at the pool, is the annotated pool source execution with the result, the encoded owners, the native state and the private pools read off its final state. -/
theorem kemCommands_reserved (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result) (state : State KemSK)
    (owned : PoolOwned seed identityIndex state) :
    (simulateQ (reservedAt setup pairs) (PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex
        (setup.joint.publicKeys seed) program (encodeState setup state).owners state.shared)).run state.pool =
      (fun result => (((result.1, (encodeState setup result.2).owners), result.2.shared), result.2.pool)) <$>
        (simulateQ (sourcePool setup codec checks seed identityIndex pairs) program).run state := by
  have source := program_reserved setup codec checks seed identityIndex pairs program state owned
  simp only [executeWith, runWith, Functor.map_map] at source
  have back := congrArg (fun work => (fun result : Result × EncodedState KemSK =>
    (((result.1, result.2.owners), result.2.shared), result.2.pool)) <$> work) source
  simp only [Functor.map_map, Prod.mk.eta, id_map'] at back
  exact back

/-- Item 2's KEM command program of a source program with at most `budget (.inl 1)` creations that reads no identity or KEM field, run by item 2's stopped selected-first router at the pairs from the router state of a prefix pool with room for the creations, is the annotated pool source execution read off as the router's reply, joint identity state and router state (`stopped_program` and `kemCommands_reserved`). -/
theorem kemCommands_stopped (selected : ℕ) (seed : IdentitySeed) (identityIndex : ℕ) (pairs : List (Pair KemSK))
    (program : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) Result)
    (budget : PqxdhRegistrationJointRevealCosts.SourceKind → ℕ)
    (certified : ∀ source, program.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (unreadIdentity : budget (.inr 0) = 0) (unreadKem : budget (.inr 1) = 0)
    (state : State KemSK) (owned : PoolOwned seed identityIndex state) (prefixed : PoolPrefix pairs state.pool.2)
    (room : state.pool.2.keys.length + budget (.inl 1) ≤ pairs.length) :
    ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected pairs)
        (PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex (setup.joint.publicKeys seed)
          program (encodeState setup state).owners state.shared)).run).run (state.pool.1, routerOf state.pool.2) =
      (fun result => (some (((result.1, (encodeState setup result.2).owners), result.2.shared)),
          (result.2.pool.1, routerOf result.2.pool.2))) <$>
        (simulateQ (sourcePool setup codec checks seed identityIndex pairs) program).run state := by
  have creations := PqxdhRegistrationJointKemCommands.creations setup codec checks identityIndex
    (setup.joint.publicKeys seed) program budget certified (encodeState setup state).owners state.shared
  have reveals := PqxdhRegistrationJointOpenCosts.command_program setup codec checks identityIndex
    (setup.joint.publicKeys seed) program budget certified (encodeState setup state).owners state.shared .other
    (by decide)
  simp only [PqxdhRegistrationJointOpenCosts.privateTotal, unreadIdentity, unreadKem] at reveals
  rw [stopped_program setup selected pairs _ _ creations reveals state.pool.1 state.pool.2 prefixed room]
  change _ <$> (simulateQ (reservedAt setup pairs) _).run state.pool = _
  rw [kemCommands_reserved setup codec checks seed identityIndex pairs program state owned, Functor.map_map]

end Commands

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.createPool_install' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.createPool_install

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.createSourcePool_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.createSourcePool_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.sourcePool_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.sourcePool_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.programPool_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.programPool_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.isCreate_class' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.isCreate_class

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_agree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_agree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_noCreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_noCreate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.coins_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.coins_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.client_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.client_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_impl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_impl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_bind

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_noCreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.executeWith_noCreate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.client_noCreate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.client_noCreate

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.compile_poolLift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.compile_poolLift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.compile_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.compile_create

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.create_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.create_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.source_counts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.source_counts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.query_poolOwned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.query_poolOwned

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.query_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.query_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.program_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.program_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.empty_prefix' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.empty_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.stopped_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.stopped_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_step_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_step_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.stopped_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.stopped_program

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_program_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.reserved_program_prefix

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.kemCommands_reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.kemCommands_reserved

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.kemCommands_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPoolSource.kemCommands_stopped
