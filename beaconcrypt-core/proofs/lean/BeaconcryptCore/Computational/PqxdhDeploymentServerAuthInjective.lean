-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills
import BeaconcryptCore.Computational.PqxdhIdentityCollisionReduction

/-! Identity-key collisions of the deployment owners (CE-8, `ε_inj`). Every native step other than a create keeps the identity seeds of all owners (`base_identities`, from `owner_identity` and `bundle_identity`). `seedEager` takes the identity seed of each create, in order, from a list drawn before the run; for a program with at most `count` creates the native run and the eager run on `count` independently drawn seeds have the same distribution (`seeds_eager`, the argument of `PqxdhDynamicIdentityPool.lazy_eager_complete` for the source14 constructor), and on the eager side the owners' identity seeds are a prefix of the list (`eager_identities`). Hence a collision of identity keys between two owners (`Collision`) is at most a collision among `count` drawn seeds (`owners_collision`). The collision reduction `B^coll_t` (`collider`, owner input 17) is a joint-use weak-EUF adversary that receives the challenge identity at index `t`, draws the seeds of the other `count` identities itself and, when the challenge's Ed25519 key equals the key of one of its seeds at a lower index, signs the empty message with that colliding seed itself and returns the signature as a forgery; by signing correctness (`joint_correct`, from the source wiring and the attached-signature correctness of the source primitives) it then wins (`lower_wins`). Every collision among `count + 1` drawn seeds is a collision of its higher index with a lower one (`collision_lower`), and drawing the seed at index `t` first is a distribution equality (`PqxdhJointIdentityFamily.sampleFamily_target_first`), so a collision among `count + 1` seeds is at most the sum over the identity indices of the joint-use weak-EUF advantage of `B^coll_t` (`lower_le_advantage`, `collision_bound`). `B^coll_t` makes no signing and no static-DH query; it draws `32·count` uniform bytes, and its whole joint-use weak-EUF game makes at most `32·(count + 1)` uniform queries (`collider_queries`, `collider_bills`). No distributional property of key generation is assumed. -/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective
open PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhJointGapDh (ScalarBytes)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhDeploymentInterface (FreshBounds ModeSpec Mode Budget)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhDeploymentCompile (Local)
open PqxdhDeploymentCompileSecrecy (compileFull mergeFull)
open PqxdhDeploymentServerAuthEvent (SourceEntry Reg regsOf summarizeReg accepted MatchedAt)
open PqxdhDeploymentServerAuthEmbed (SourceSpec Owner)
open PqxdhDeploymentServerAuthLocal (State base)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response X Result : Type}

/-! ## Owners keep their identity seeds -/

/-- The Phase 2 owner program keeps the owner's identity seed on every outcome. -/
theorem owner_identity (completedBinding : beaconcrypt_core.session.CompletedRegistrationBinding)
    {I D K Y Response' : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K)
    (result : Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K)
    (member : result ∈ support (PqxdhBeaconPhase2Publication.owner (completedBinding := completedBinding) (X := Y) (Response := Response') decode raw state)) :
    result.2.beacon.identity = state.beacon.identity := by
  have finished : ∀ control staged, (PqxdhBeaconPhase2Publication.finish control state staged).2.beacon.identity =
      state.beacon.identity := by
    intro control staged
    unfold PqxdhBeaconPhase2Publication.finish
    cases staged with
    | none => exact (PqxdhBeaconPhase2Preparation.abort_fields control state).1
    | some staged =>
        dsimp only
        split_ifs
        · exact (PqxdhBeaconPhase2Preparation.abort_fields control state).1
        · exact (PqxdhBeaconPhase2Preparation.abort_fields control state).1
        · exact (PqxdhBeaconPhase2Publication.publish_fields state staged).2.1
  unfold PqxdhBeaconPhase2Publication.owner at member
  split at member
  · simp only [mem_support_bind_iff] at member
    obtain ⟨prepared, _, member⟩ := member
    cases prepared with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at member
        rw [member]
        exact finished _ _
    | some prepared =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨staged, _, rfl⟩ := member
        exact finished _ _
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]

/-- The native Phase 1 bundle program keeps the owner's identity seed on every outcome. -/
theorem bundle_identity {I : Type} (projection : PqxdhLivePhase1Bundle.Public I ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (state : PqxdhBeaconPhase1Publication.State (I := I) (D := ScalarBytes) (K := PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (result : Option Pqxdh.Bytes × PqxdhBeaconPhase1Publication.State (I := I) (D := ScalarBytes)
      (K := PqxdhKemIndCca.MlKem768PublicKey × KemSK))
    (member : result ∈ support (PqxdhLivePhase1Bundle.bundle projection state)) :
    result.2.beacon.identity = state.beacon.identity := by
  have after : ∀ generated, result ∈ support (PqxdhLivePhase1Bundle.afterGenerated projection generated state) →
      result.2.beacon.identity = state.beacon.identity := by
    intro generated reached
    unfold PqxdhLivePhase1Bundle.afterGenerated at reached
    cases prepared : PqxdhBeaconPhase1Publication.prepare state generated with
    | none =>
        simp only [prepared, support_pure, Set.mem_singleton_iff] at reached
        rw [reached]
    | some ready =>
        simp only [prepared, mem_support_bind_iff] at reached
        obtain ⟨signed, _, reached⟩ := reached
        cases signed with
        | none =>
            simp only [support_pure, Set.mem_singleton_iff] at reached
            rw [reached]
        | some candidate =>
            have inner := PqxdhDeploymentServerAuthChain.support_simulateQ_subset _ _ reached
            unfold PqxdhBeaconPhase1Publication.afterSigning at inner
            simp only [prepared, mem_support_bind_iff] at inner
            obtain ⟨serialized, _, inner⟩ := inner
            cases serialized with
            | none =>
                simp only [support_pure, Set.mem_singleton_iff] at inner
                rw [inner]
            | some written =>
                simp only [support_pure, Set.mem_singleton_iff] at inner
                rw [inner]
                rfl
  unfold PqxdhLivePhase1Bundle.bundle at member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨generated, _, reached⟩ := member
    exact after generated reached
  · exact after none member
  · simp only [support_pure, Set.mem_singleton_iff] at member
    rw [member]

/-- Setting an entry of a list to its own value keeps the list. -/
theorem set_same {α : Type} (list : List α) (index : Nat) (value : α) (found : list[index]? = some value) :
    list.set index value = list := by
  apply List.ext_getElem?
  intro other
  by_cases same : index = other
  · subst same
    rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1, found]
  · rw [List.getElem?_set_ne same]

/-- The identity seeds of the owners, in creation order. -/
def identities (state : State KemSK) : List IdentitySeed := state.owners.map fun owner => owner.beacon.identity

/-- Every native step other than a create keeps the identity seeds of all owners. -/
theorem base_identities (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain)
    (notCreate : ∀ pin keyId, query ≠ .inl (.inr (.create pin keyId)))
    (state : State KemSK) (result : (SourceSpec KemSK).Range query × State KemSK)
    (member : result ∈ support ((base setup codec checks seed query).run state)) :
    identities result.2 = identities state := by
  rcases query with (coin | request) | request
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, PqxdhRegistrationSchedule.handler, StateT.run_lift,
      support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · cases request with
    | create pin keyId => exact absurd rfl (notCreate pin keyId)
    | bundle other =>
        rw [PqxdhDeploymentServerAuthLocal.base_bundle] at member
        cases found : state.owners[other]? with
        | none =>
            rw [PqxdhDeploymentServerAuthLocal.bundle_missing setup codec other state found, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            rfl
        | some bundled =>
            rw [PqxdhDeploymentServerAuthLocal.bundle_found setup codec other state bundled found, support_map] at member
            obtain ⟨inner, innerMember, rfl⟩ := member
            have logged : inner.1 ∈ support (PqxdhDeploymentServerAuthEmbed.localBundle setup codec other bundled) := by
              rw [← PqxdhDeploymentServerAuthEmbed.localBundleLog_fst, support_map]
              exact Set.mem_image_of_mem _ innerMember
            have same := bundle_identity _ _ inner.1
              (PqxdhDeploymentServerAuthChain.support_simulateQ_subset _ _ logged)
            simp only [identities, List.map_set]
            rw [same]
            exact set_same _ _ _ (by simp [found])
    | finish other raw =>
        rw [PqxdhDeploymentServerAuthLocal.base_finish] at member
        cases found : state.owners[other]? with
        | none =>
            rw [PqxdhRegistrationSchedule.finish_missing setup codec other raw state found, support_pure,
              Set.mem_singleton_iff] at member
            subst member
            rfl
        | some finished =>
            rw [PqxdhDeploymentServerAuthLocal.finish_found setup codec other raw state finished found, support_map] at member
            obtain ⟨inner, innerMember, rfl⟩ := member
            have same : inner.1.2.beacon.identity = finished.beacon.identity := by
              unfold PqxdhRegistrationSchedule.ownerFinish at innerMember
              split at innerMember
              · split at innerMember
                · rename_i control _ _ _ _ _ _ _ _ _ _
                  rw [StateT.run_bind, mem_support_bind_iff] at innerMember
                  obtain ⟨hashed, _, member⟩ := innerMember
                  have program : inner.1 ∈ support (PqxdhBeaconPhase2Publication.nativeOwner
                      (completedBinding := PqxdhTranscriptAd.completedOf control hashed.1) (X := IdentitySeed)
                      (Response := Response) codec.frameRead raw finished) := by
                    apply support_simulateQ_run'_subset (PqxdhRegistrationSchedule.callbacks setup codec) _ hashed.2
                    rw [StateT.run'_eq, support_map]
                    exact Set.mem_image_of_mem _ member
                  exact owner_identity (PqxdhTranscriptAd.completedOf control hashed.1) codec.frameRead raw finished
                    inner.1 (PqxdhDeploymentServerAuthChain.support_simulateQ_subset _ _ program)
                · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
                  subst innerMember
                  exact (PqxdhBeaconPhase2Preparation.abort_fields _ finished).1
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at innerMember
                subst innerMember
                rfl
            simp only [identities, List.map_set]
            rw [same]
            exact set_same _ _ _ (by simp [found])
    | accept raw =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        simp only [identities, keep]
    | build session payload =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        simp only [identities, keep]
    | hmac key message =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        simp only [identities, keep]
    | hash bytes =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        simp only [identities, keep]
    | reveal keyId =>
        have keep := PqxdhDeploymentServerAuthLocalize.onShared_owners _ state result member
        simp only [identities, keep]
  · simp only [base, PqxdhRegistrationJointRevealSchedule.native, StateT.run, support_pure,
      Set.mem_singleton_iff] at member
    subst member
    rfl

/-! ## Identity seeds drawn before the run -/

/-- A create query. -/
def IsCreate : (SourceSpec KemSK).Domain → Prop
  | .inl (.inr (.create _ _)) => True
  | _ => False

instance : DecidablePred (IsCreate (KemSK := KemSK)) := fun query => by
  rcases query with (coin | request) | read
  · exact isFalse id
  · cases request
    case create => exact isTrue trivial
    all_goals exact isFalse id
  · exact isFalse id

/-- The native constructor with a given identity seed: the prekey and KEM draws and the new owner. -/
noncomputable def createWith (setup : Setup baseSpec KemSK) (identity : IdentitySeed) (pin : Word32) (keyId : Std.U64)
    (state : State KemSK) : ProbComp (Nat × State KemSK) := do
  let prekey ← PqxdhJointGapDh.sampleScalar
  let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
  pure (state.owners.length, { state with owners := state.owners ++ [⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩] })

/-- The native constructor is its identity draw followed by the constructor with that seed. -/
theorem create_with (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) (state : State KemSK) :
    PqxdhRegistrationSchedule.create setup pin keyId state =
      sampleSeed >>= fun identity => createWith setup identity pin keyId state := by
  rw [PqxdhRegistrationSchedule.create_source]
  rfl

/-- The native handler with the identity seeds of the creates taken, in order, from a list drawn before the run; a create with an empty list draws its seed as the native constructor does. -/
noncomputable def seedEager (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) : QueryImpl (SourceSpec KemSK) (StateT (State KemSK × List IdentitySeed) ProbComp) := fun query =>
  match query with
  | .inl (.inr (.create pin keyId)) => fun state =>
      match state.2 with
      | identity :: rest => (fun result => (result.1, (result.2, rest))) <$> createWith setup identity pin keyId state.1
      | [] => (fun result => (result.1, (result.2, []))) <$>
          (base setup codec checks seed (.inl (.inr (.create pin keyId)))).run state.1
  | other => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (base setup codec checks seed other).run state.1

/-- A step of the eager handler other than a create is the native step with the list kept. -/
theorem seedEager_other (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (query : (SourceSpec KemSK).Domain) (notCreate : ¬ IsCreate query)
    (state : State KemSK × List IdentitySeed) :
    (seedEager setup codec checks seed query).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (base setup codec checks seed query).run state.1 := by
  rcases query with (coin | request) | read
  · rfl
  · cases request
    case create => exact absurd trivial notCreate
    all_goals rfl
  · rfl

/-- A create of the eager handler with a nonempty list takes the first seed. -/
theorem seedEager_create (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (pin : Word32) (keyId : Std.U64) (state : State KemSK) (identity : IdentitySeed)
    (rest : List IdentitySeed) :
    (seedEager setup codec checks seed (.inl (.inr (.create pin keyId)))).run (state, identity :: rest) =
      (fun result => (result.1, (result.2, rest))) <$> createWith setup identity pin keyId state := rfl

/-- Drawing the identity seeds of at most `count` creates before the run: for every program with at most `count` creates and every state, the native run and the eager run on a list of `count` seeds drawn first have the same distribution of result and final state. -/
theorem seeds_eager (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (count : Nat)
    (bounded : program.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) (state : State KemSK) :
    EvalDistEq ((simulateQ (base setup codec checks seed) program).run state)
      (do
        let pool ← PqxdhDynamicIdentityPool.sampleSeeds count
        (fun result : Result × (State KemSK × List IdentitySeed) => (result.1, result.2.1)) <$>
          (simulateQ (seedEager setup codec checks seed) program).run (state, pool)) := by
  induction program using OracleComp.inductionOn generalizing count state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (PqxdhDynamicIdentityPool.sampleSeeds_unused count _).symm
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind]
      by_cases creates : IsCreate (KemSK := KemSK) query
      · obtain ⟨pin, keyId, rfl⟩ : ∃ pin keyId, query = .inl (.inr (.create pin keyId)) := by
          rcases query with (coin | request) | read
          · exact absurd creates id
          · cases request
            case create pin keyId => exact ⟨pin, keyId, rfl⟩
            all_goals exact absurd creates id
          · exact absurd creates id
        have positive : 0 < count := bounded.1.resolve_left (not_not.mpr creates)
        obtain ⟨fewer, rfl⟩ : ∃ fewer, count = fewer + 1 := ⟨count - 1, by omega⟩
        rw [PqxdhDeploymentServerAuthLocal.base_create, create_with, PqxdhDynamicIdentityPool.sampleSeeds_succ]
        simp only [bind_assoc, pure_bind]
        apply EvalDistEq.bind_right
        intro identity
        simp only [seedEager_create, bind_map_left]
        refine EvalDistEq.trans ?_ (PqxdhSecretInputKdf.evalSPMF_sample_comm (PqxdhDynamicIdentityPool.sampleSeeds fewer)
          (createWith setup identity pin keyId state) _).symm
        apply EvalDistEq.bind_right
        intro result
        have rest := bounded.2 result.1
        simp only [creates, ite_true] at rest
        exact ih result.1 fewer rest result.2
      · simp only [seedEager_other setup codec checks seed query creates, bind_map_left]
        refine EvalDistEq.trans ?_ (PqxdhSecretInputKdf.evalSPMF_sample_comm (PqxdhDynamicIdentityPool.sampleSeeds count)
          ((base setup codec checks seed query).run state) _).symm
        apply EvalDistEq.bind_right
        intro result
        have rest := bounded.2 result.1
        simp only [creates, ite_false] at rest
        exact ih result.1 count rest result.2


/-- On every outcome of the eager run of a program with at most as many creates as the list has seeds, the identity seeds of the owners are the initial ones followed by a prefix of the list. -/
theorem eager_identities (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (state : State KemSK)
    (pool : List IdentitySeed) (bounded : program.IsQueryBoundP (IsCreate (KemSK := KemSK)) pool.length)
    (outcome : Result × (State KemSK × List IdentitySeed))
    (member : outcome ∈ support ((simulateQ (seedEager setup codec checks seed) program).run (state, pool))) :
    ∃ taken, identities outcome.2.1 = identities state ++ pool.take taken := by
  induction program using OracleComp.inductionOn generalizing state pool with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact ⟨0, by simp⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      have other : ¬ IsCreate (KemSK := KemSK) query → ∃ taken, identities outcome.2.1 = identities state ++ pool.take taken := by
        intro creates
        rw [seedEager_other setup codec checks seed query creates, support_map] at stepMember
        obtain ⟨result, resultMember, rfl⟩ := stepMember
        have kept := base_identities setup codec checks seed query
          (fun pin keyId same => creates (by rw [same]; trivial)) state result resultMember
        have restBound := bounded.2 result.1
        simp only [creates, ite_false] at restBound
        obtain ⟨taken, same⟩ := ih result.1 result.2 pool restBound member
        exact ⟨taken, by rw [same, kept]⟩
      rcases query with (coin | request) | read
      · exact other id
      · cases request with
        | create pin keyId =>
            cases pool with
            | nil => simp [IsCreate] at bounded
            | cons identity rest =>
                rw [seedEager_create, support_map] at stepMember
                obtain ⟨made, madeMember, rfl⟩ := stepMember
                simp only [createWith, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at madeMember
                obtain ⟨prekey, _, keys, _, rfl⟩ := madeMember
                have restBound := bounded.2 state.owners.length
                simp only [IsCreate, ite_true, List.length_cons, Nat.add_sub_cancel] at restBound
                obtain ⟨taken, same⟩ := ih _ _ rest restBound member
                refine ⟨taken + 1, ?_⟩
                rw [same]
                simp [identities]
        | bundle index => exact other id
        | accept raw => exact other id
        | build session payload => exact other id
        | finish index raw => exact other id
        | hmac key message => exact other id
        | hash bytes => exact other id
        | reveal keyId => exact other id
      · exact other id

/-- Two computations with the same distribution give every event the same probability. -/
theorem probEvent_evalSPMF_eq {α : Type} {first second : ProbComp α} (same : EvalDistEq (first) (second))
    {event : α → Prop} : Pr{let x ← first}[event x] = Pr{let x ← second}[event x] :=
  same.prEvent_eq event

/-! ## Collisions of identity keys -/

/-- From a state with no owner, the probability that two owners of the native run of a program with at most `count` creates have equal identity keys is at most the probability of a collision in `count` seeds drawn independently. -/
theorem owners_collision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (count : Nat)
    (bounded : program.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) (state : State KemSK)
    (empty : state.owners = []) :
    Pr{let result ← (simulateQ (base setup codec checks seed) program).run state}[Collision setup.joint (identities result.2)] ≤
    Pr{let pool ← PqxdhDynamicIdentityPool.sampleSeeds count}[Collision setup.joint pool] := by
  rw [probEvent_evalSPMF_eq (seeds_eager setup codec checks seed program count bounded state)]
  refine prEvent_bind_le_prEvent_of_support _ _ _ _ fun pool poolMember free => ?_
  rw [OracleComp.prEvent_eq_zero_iff]
  intro outcome member collision
  rw [support_map] at member
  obtain ⟨eager, eagerMember, rfl⟩ := member
  have length := PqxdhDynamicIdentityPool.sampleSeeds_length count pool poolMember
  obtain ⟨taken, same⟩ := eager_identities setup codec checks seed program state pool (by rw [length]; exact bounded)
    eager eagerMember
  rw [same, identities, empty] at collision
  simp only [List.map_nil, List.nil_append] at collision
  exact free (collision_take setup.joint pool taken collision)


end BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owner_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owner_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.bundle_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.bundle_identity

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.set_same' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.set_same

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.base_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.base_identities

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.create_with' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.create_with

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seedEager_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seedEager_other

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seedEager_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seedEager_create

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seeds_eager' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.seeds_eager

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.eager_identities' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.eager_identities

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.probEvent_evalSPMF_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.probEvent_evalSPMF_eq


/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owners_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owners_collision
