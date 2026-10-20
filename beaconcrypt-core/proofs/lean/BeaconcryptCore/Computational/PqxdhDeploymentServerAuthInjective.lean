-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentServerAuthBills

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
theorem owner_identity {I D K Y Response' : Type} (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K)
    (result : Option Pqxdh.Bytes × PqxdhBeaconPhase2Preparation.State I D K)
    (member : result ∈ support (PqxdhBeaconPhase2Publication.owner (X := Y) (Response := Response') decode raw state)) :
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
            have same := bundle_identity _ _ inner
              (PqxdhDeploymentServerAuthChain.support_simulateQ_subset _ _ innerMember)
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
            have program : inner.1 ∈ support (PqxdhBeaconPhase2Publication.nativeOwner (X := IdentitySeed)
                (Response := Response) codec.frameRead raw finished) := by
              apply support_simulateQ_run'_subset (PqxdhRegistrationSchedule.callbacks setup codec) _ state.shared
              rw [StateT.run'_eq, support_map]
              exact Set.mem_image_of_mem _ innerMember
            have same := owner_identity codec.frameRead raw finished inner.1
              (PqxdhDeploymentServerAuthChain.support_simulateQ_subset _ _ program)
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

set_option linter.deprecated false in
/-- Drawing the identity seeds of at most `count` creates before the run: for every program with at most `count` creates and every state, the native run and the eager run on a list of `count` seeds drawn first have the same distribution of result and final state. -/
theorem seeds_eager (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (count : Nat)
    (bounded : program.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) (state : State KemSK) :
    𝒮[(simulateQ (base setup codec checks seed) program).run state] =
      𝒮[do
        let pool ← PqxdhDynamicIdentityPool.sampleSeeds count
        (fun result : Result × (State KemSK × List IdentitySeed) => (result.1, result.2.1)) <$>
          (simulateQ (seedEager setup codec checks seed) program).run (state, pool)] := by
  induction program using OracleComp.inductionOn generalizing count state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      exact (PqxdhDynamicIdentityPool.sampleSeeds_unused_vcvioLegacy count _).symm
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
        apply evalSPMF_bind_congr'
        intro identity
        change 𝒮[createWith setup identity pin keyId state >>= fun result =>
            (simulateQ (base setup codec checks seed) (next result.1)).run result.2] =
          𝒮[PqxdhDynamicIdentityPool.sampleSeeds fewer >>= fun rest =>
            ((fun result => (result.1, (result.2, rest))) <$> createWith setup identity pin keyId state) >>= fun result =>
              (fun result : Result × (State KemSK × List IdentitySeed) => (result.1, result.2.1)) <$>
                (simulateQ (seedEager setup codec checks seed) (next result.1)).run result.2]
        simp only [bind_map_left]
        rw [PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy (PqxdhDynamicIdentityPool.sampleSeeds fewer)
          (createWith setup identity pin keyId state)]
        apply evalSPMF_bind_congr'
        intro result
        have rest := bounded.2 result.1
        simp only [creates, ite_true] at rest
        exact ih result.1 fewer rest result.2
      · simp only [seedEager_other setup codec checks seed query creates, bind_map_left]
        rw [PqxdhSecretInputKdf.evalSPMF_sample_comm_vcvioLegacy (PqxdhDynamicIdentityPool.sampleSeeds count)
          ((base setup codec checks seed query).run state)]
        apply evalSPMF_bind_congr'
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

set_option linter.deprecated false in
/-- Two computations with the same distribution give every event the same probability. -/
theorem probEvent_evalSPMF_eq {α : Type} {first second : ProbComp α} (same : 𝒮[first] = 𝒮[second])
    {event : α → Prop} : Pr[event | first] = Pr[event | second] := by
  unfold probEvent
  rw [same]

/-! ## Collisions of identity keys -/

/-- Two distinct positions of a list of identity seeds carry equal Ed25519 identity keys. -/
def Collision (joint : Primitives) (seeds : List IdentitySeed) : Prop :=
  ∃ first second : Nat, first ≠ second ∧ ∃ left right, seeds[first]? = some left ∧ seeds[second]? = some right ∧
    (joint.publicKeys left).ed25519 = (joint.publicKeys right).ed25519

/-- A collision of a prefix is a collision of the list. -/
theorem collision_take (joint : Primitives) (seeds : List IdentitySeed) (taken : Nat)
    (collision : Collision joint (seeds.take taken)) : Collision joint seeds := by
  obtain ⟨first, second, different, left, right, leftFound, rightFound, same⟩ := collision
  have lift : ∀ (index : Nat) (value : IdentitySeed), (seeds.take taken)[index]? = some value → seeds[index]? = some value := by
    intro index value found
    rw [List.getElem?_take] at found
    split_ifs at found
    exact found
  exact ⟨first, second, different, left, right, lift _ _ leftFound, lift _ _ rightFound, same⟩

set_option linter.deprecated false in
/-- From a state with no owner, the probability that two owners of the native run of a program with at most `count` creates have equal identity keys is at most the probability of a collision in `count` seeds drawn independently. -/
theorem owners_collision (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : IdentitySeed) (program : OracleComp (SourceSpec KemSK) Result) (count : Nat)
    (bounded : program.IsQueryBoundP (IsCreate (KemSK := KemSK)) count) (state : State KemSK)
    (empty : state.owners = []) :
    Pr[fun result : Result × State KemSK => Collision setup.joint (identities result.2) |
      (simulateQ (base setup codec checks seed) program).run state] ≤
    Pr[fun pool => Collision setup.joint pool | PqxdhDynamicIdentityPool.sampleSeeds count] := by
  rw [probEvent_evalSPMF_eq (seeds_eager setup codec checks seed program count bounded state)]
  refine probEvent_bind_le_probEvent fun pool poolMember free => ?_
  rw [probEvent_eq_zero_iff]
  intro outcome member collision
  rw [support_map] at member
  obtain ⟨eager, eagerMember, rfl⟩ := member
  have length := PqxdhDynamicIdentityPool.sampleSeeds_length count pool poolMember
  obtain ⟨taken, same⟩ := eager_identities setup codec checks seed program state pool (by rw [length]; exact bounded)
    eager eagerMember
  rw [same, identities, empty] at collision
  simp only [List.map_nil, List.nil_append] at collision
  exact free (collision_take setup.joint pool taken collision)


/-- Signing correctness of the joint identity primitives, from the source wiring and the attached-signature correctness of the source primitives. -/
theorem joint_correct (setup : Setup baseSpec KemSK) (seed : IdentitySeed) (message : Pqxdh.Bytes) :
    setup.joint.verify (setup.joint.publicKeys seed).ed25519 message (setup.joint.sign seed message) = true := by
  have verified := PqxdhServerAuthNegativeControl.server_verify setup seed message
  rw [setup.wiring.verifyAttached] at verified
  split_ifs at verified with valid
  · exact valid

/-- The identity at index `target` of a family of identity seeds has the Ed25519 key of an identity at a lower index. -/
def LowerCollision (joint : Primitives) {count : Nat} (target : Fin count) (seeds : Fin count → IdentitySeed) : Prop :=
  ∃ lower : Fin count, lower < target ∧
    (joint.publicKeys (seeds lower)).ed25519 = (joint.publicKeys (seeds target)).ed25519

/-- The forgery of `B^coll_t` (`collider`) from the challenge identity and the seeds it drew for the other `count` indices of the family, with the challenge at index `target`: if the challenge's Ed25519 key equals the key of a drawn seed whose family index is below `target`, the signature of the empty message under that seed, computed by the reduction itself; otherwise the all-zero signature of the empty message. -/
noncomputable def colliderForgery (joint : Primitives) {count : Nat} (target : Fin (count + 1))
    (jointPublic : PublicIdentity) (others : Fin count → IdentitySeed) : Forgery := by
  classical
  exact if found : ∃ other : Fin count, other.val < target.val ∧
      (joint.publicKeys (others other)).ed25519 = jointPublic.ed25519 then
    ⟨[], joint.sign (others (Classical.choose found)) []⟩
  else ⟨[], List.Vector.replicate 64 0⟩

/-- `B^coll_t`, the zero-query collision reduction of `ε_inj` at identity index `t = target` (plan section 10, owner input 17): a joint-use weak-EUF adversary that receives the challenge identity, draws the seeds of the other `count` identities of the family itself (the challenge at index `target`, the drawn seeds at the other indices in order) and, if the challenge's Ed25519 key equals the key of a drawn seed at a lower index, signs the empty message with that colliding seed itself and returns the signature as its forgery (`colliderForgery`). It makes no signing and no static-DH query; its only oracle queries are the `32·count` uniform bytes of the seeds it draws (`collider_queries`). -/
noncomputable def collider (joint : Primitives) (count : Nat) (target : Fin (count + 1))
    (jointPublic : PublicIdentity) : OracleComp AdversarySpec Forgery := do
  let others ← OracleComp.liftComp (PqxdhJointIdentityFamily.sampleFamily count) AdversarySpec
  pure (colliderForgery joint target jointPublic others)

/-- The joint-use weak-EUF game of `B^coll_t` draws the challenge seed, then the reduction's own seeds, and tests the forgery against the empty signing history. -/
theorem collider_game (joint : Primitives) (count : Nat) (target : Fin (count + 1)) :
    game joint (collider joint count target) = (do
      let seed ← sampleSeed
      let others ← PqxdhJointIdentityFamily.sampleFamily count
      pure (wins joint (joint.publicKeys seed) (colliderForgery joint target (joint.publicKeys seed) others) [])) := by
  simp only [game, run, collider, simulateQ_bind, StateT.run_bind, PqxdhJointIdentityFamily.simulate_joint_uniform,
    simulateQ_pure, StateT.run_pure, bind_map_left, bind_assoc, pure_bind]

/-- If, in the family with the challenge seed at index `target` and the reduction's seeds at the other indices, the identity at `target` collides with a lower index, then `B^coll_t` wins: its forgery is a valid signature under the challenge key (signing correctness, `joint_correct`) on a message the challenger never signed. -/
theorem lower_wins (setup : Setup baseSpec KemSK) (count : Nat) (target : Fin (count + 1)) (seed : IdentitySeed)
    (others : Fin count → IdentitySeed) (lower : LowerCollision setup.joint target (target.insertNth seed others)) :
    wins setup.joint (setup.joint.publicKeys seed)
      (colliderForgery setup.joint target (setup.joint.publicKeys seed) others) [] = true := by
  classical
  obtain ⟨index, below, same⟩ := lower
  have bound : index.val < count := lt_of_lt_of_le below (Nat.lt_succ_iff.mp target.isLt)
  have position : target.succAbove ⟨index.val, bound⟩ = index := by
    rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.lt_def.mpr (Fin.lt_def.mp below))]
    rfl
  have found : ∃ other : Fin count, other.val < target.val ∧
      (setup.joint.publicKeys (others other)).ed25519 = (setup.joint.publicKeys seed).ed25519 := by
    refine ⟨⟨index.val, bound⟩, below, ?_⟩
    rw [← position, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same] at same
    exact same
  have chosen := (Classical.choose_spec found).2
  simp only [colliderForgery, dite_eq_left found, wins, signedMessages, List.filterMap_nil,
    List.not_mem_nil, decide_false, Bool.not_false, Bool.and_true]
  have valid := joint_correct setup (others (Classical.choose found)) []
  rwa [chosen] at valid

set_option linter.deprecated false in
/-- For every identity index `target`, the probability that, among `count + 1` independently drawn identity seeds, the identity at `target` collides with a lower index is at most the joint-use weak-EUF advantage of `B^coll_t`: drawing the seed at `target` first is a distribution equality (`PqxdhJointIdentityFamily.sampleFamily_target_first`), and then `lower_wins` applies on every draw. -/
theorem lower_le_advantage (setup : Setup baseSpec KemSK) (count : Nat) (target : Fin (count + 1)) :
    Pr[LowerCollision setup.joint target | PqxdhJointIdentityFamily.sampleFamily (count + 1)] ≤
      advantage setup.joint (collider setup.joint count target) := by
  classical
  have decided : Pr[LowerCollision setup.joint target | PqxdhJointIdentityFamily.sampleFamily (count + 1)] =
      Pr[= true | PqxdhJointIdentityFamily.sampleFamily (count + 1) >>= fun seeds =>
        pure (decide (LowerCollision setup.joint target seeds))] := by
    rw [bind_pure_comp, probOutput_map]
    simp only [decide_eq_true_eq]
  have moved := evalSPMF_ext_iff.mp (PqxdhJointIdentityFamily.sampleFamily_target_first_vcvioLegacy count target
    (fun seeds => pure (decide (LowerCollision setup.joint target seeds)))) true
  rw [decided, advantage, ← VCVioLegacy.probOutput_eq_prEvent, collider_game]
  refine le_of_eq_of_le moved ?_
  refine probOutput_bind_mono fun seed _ => probOutput_bind_mono fun others _ => ?_
  by_cases lower : LowerCollision setup.joint target (target.insertNth seed others)
  · rw [lower_wins setup count target seed others lower]
    simp [lower]
  · simp [lower]

/-- A collision of the list of a family of identity seeds is a collision of some index with a lower index. -/
theorem collision_lower (joint : Primitives) (count : Nat) (seeds : Fin count → IdentitySeed)
    (collision : Collision joint (List.ofFn seeds)) :
    ∃ target ∈ (Finset.univ : Finset (Fin count)), LowerCollision joint target seeds := by
  obtain ⟨first, second, different, left, right, leftFound, rightFound, same⟩ := collision
  simp only [List.getElem?_ofFn] at leftFound rightFound
  obtain ⟨firstBound, leftEq⟩ := Option.dite_none_right_eq_some.mp leftFound
  obtain ⟨secondBound, rightEq⟩ := Option.dite_none_right_eq_some.mp rightFound
  rcases Nat.lt_or_gt_of_ne different with less | greater
  · exact ⟨⟨second, secondBound⟩, Finset.mem_univ _, ⟨first, firstBound⟩, less, by
      rw [Option.some.inj leftEq, Option.some.inj rightEq]; exact same⟩
  · exact ⟨⟨first, firstBound⟩, Finset.mem_univ _, ⟨second, secondBound⟩, greater, by
      rw [Option.some.inj leftEq, Option.some.inj rightEq]; exact same.symm⟩

set_option linter.deprecated false in
/-- A collision among `count + 1` independently drawn identity seeds is at most the sum, over the `count + 1` identity indices `t`, of the joint-use weak-EUF advantage of the zero-query reduction `B^coll_t` (`collider`): a collision is a collision of its higher index with a lower one (`collision_lower`), the union bound sums over the higher index, and `lower_le_advantage` bounds each term. No assumption beyond joint-use weak-EUF is used: a collision gives a valid forgery by signing correctness. -/
theorem collision_bound (setup : Setup baseSpec KemSK) (count : Nat) :
    Pr[fun pool => Collision setup.joint pool | PqxdhDynamicIdentityPool.sampleSeeds (count + 1)] ≤
      ∑ target : Fin (count + 1), advantage setup.joint (collider setup.joint count target) := by
  rw [PqxdhDynamicIdentityPool.sampleSeeds, probEvent_map]
  refine (probEvent_mono fun seeds _ collision => collision_lower setup.joint (count + 1) seeds collision).trans ?_
  exact (probEvent_exists_finset_le_sum _ _ _).trans
    (Finset.sum_le_sum fun target _ => lower_le_advantage setup count target)

/-- `B^coll_t` makes, on every challenge identity, at most `32·count` uniform queries (the bytes of the seeds it draws) and no signing and no static-DH query. -/
theorem collider_queries (joint : Primitives) (count : Nat) (target : Fin (count + 1))
    (kind : PqxdhJointIdentityFamily.Kind) (jointPublic : PublicIdentity) :
    (collider joint count target jointPublic).IsQueryBoundP (PqxdhJointIdentityFamily.IsClass kind)
      (if kind = .uniform then 32 * count else 0) := by
  unfold collider
  have bound := OracleComp.isQueryBoundP_bind (PqxdhJointIdentityFamily.sampleFamily_lift_bound count kind)
    (fun others _ => isQueryBoundP_pure _ (colliderForgery joint target jointPublic others) 0)
  rwa [Nat.add_zero] at bound

/-- The bills of `B^coll_t`: on every challenge identity at most `32·count` uniform queries, no signing query and no static-DH query; its whole joint-use weak-EUF game, with the challenger's own seed draw, makes at most `32·(count + 1)` uniform queries. -/
theorem collider_bills (joint : Primitives) (count : Nat) (target : Fin (count + 1)) :
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .uniform) (32 * count)) ∧
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .sign) 0) ∧
    (∀ jointPublic, (collider joint count target jointPublic).IsQueryBoundP
      (PqxdhJointIdentityFamily.IsClass .staticDh) 0) ∧
    (game joint (collider joint count target)).IsTotalQueryBound (32 * (count + 1)) := by
  refine ⟨fun jointPublic => by simpa using collider_queries joint count target .uniform jointPublic,
    fun jointPublic => by simpa using collider_queries joint count target .sign jointPublic,
    fun jointPublic => by simpa using collider_queries joint count target .staticDh jointPublic, ?_⟩
  have counted := PqxdhJointIdentityFamily.jointGame_uniform_bound joint (collider joint count target) (32 * count)
    fun jointPublic => by simpa using collider_queries joint count target .uniform jointPublic
  convert counted using 1
  omega

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

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_take' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_take

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owners_collision' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.owners_collision

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.joint_correct' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.joint_correct

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_game

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_wins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_wins

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_le_advantage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.lower_le_advantage

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_lower' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_lower

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collision_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_queries

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_bills' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentServerAuthInjective.collider_bills
