import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceMarked
import BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnceRouter

/-!
# At most one marked Beacon finish after the challenge (item 2, stage T, post-challenge phase)

This module bounds the hidden reads of the post-challenge phase of the services skeleton (`PqxdhRegistrationJointKemPostSkeleton.postSkel`, for any services) by 2: one for the Server's private resumption root and one for a grouped Beacon finish on the challenge marker. Stage S2's bound `1 + qFinish` counted one hidden read per Beacon finish request; the tighter count needs the state of two layers at once:

- the owner list of the grouped client, where `ownerCount selected` counts the owners whose phase holds the selected KEM creation index;
- the creation counter of the KEM router, several layers below, which has not yet handed out the selected index exactly when `created ≤ selected`.

The potential `potential selected` is the sum of the two. The grouped client, the skeleton's native layer, the actual encapsulator and the router (forwarding the table oracles) are collapsed into one optional stateful interpreter (`topImpl`, by `composeOpt`), and every source request of the continuation is shown to make at most as many hidden reads as the potential drops (`top_step`):

- a raw `create` appends an owner whose KEM index is the counter before the request, and increments the counter (`client_created` through the forwarding layers, `create_low`), so an owner with the selected index appears exactly when the counter passes it, and the potential is unchanged;
- a grouped finish reads a hidden value only for an owner in phase `initSent` with the selected index (`groupedClient_marked`, `skelImpl_marked`), and leaves that owner aborted or established (`groupedClient_count`), so the potential drops by one;
- no other request increases the owner count, and no step decreases the counter (`combine_mono`).

`option_potential` then bounds the hidden reads of the continuation by the potential at the cut, and `postSkel_two` adds the resumption's one read. The potential at the cut is at most one when at most one owner holds the selected index and none does unless the router has handed it out (`KemOnce`); the prefix module proves this for every prechallenge context.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhRegistrationJointKemRootExpand (valueRead? fwd_hidden fwdOption_hidden HiddenC resumeImpl_hidden)
open PqxdhRegistrationJointKemRomSplit (isQueryBoundP_option_of_step resume_root)

/-! ### The collapsed post-challenge interpreter -/

section Stack

variable {ι ι' : Type} {baseSpec : OracleSpec ι} {spec' : OracleSpec.{0, 0} ι'} {KemSK Reader Response V : Type}

/-- The interpreters below the skeleton's native layer: the actual encapsulator, then a KEM router, each forwarding the table oracles. -/
noncomputable def lowImpl (setup : Setup baseSpec KemSK)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :
    QueryImpl (Enc KemSK + TSpec V)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp (spec' + TSpec V)))) :=
  fwdOption (T := TSpec V) router ∘ₛ fwd (T := TSpec V) (PqxdhRegistrationJointKemEncapsulation.actual setup)

/-- The skeleton's native layer collapsed onto the interpreters below it. -/
noncomputable def midImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (skelImpl setup codec checks identityIndex publicIdentity services) (lowImpl (V := V) setup router)

/-- The grouped client collapsed onto the skeleton's native layer and the interpreters below it. -/
noncomputable def topImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec')))) :=
  composeOpt (groupedClient setup codec selected challenge)
    (midImpl setup codec checks identityIndex publicIdentity services router)

/-- The potential of the post-challenge phase: the owners holding the selected KEM index, plus one while the router has not yet handed it out. -/
def potential (selected : Nat) {S : Type} (state : List EncodedEntry × (S × PqxdhDynamicKemJointSource.State KemSK)) :
    Nat :=
  ownerCount selected state.1 + pending selected (created state.2.2)

/-- The lower interpreters forward hidden reads one for one. -/
theorem low_hidden (setup : Setup baseSpec KemSK)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    {α : Type} (work : OracleComp (Enc KemSK + TSpec V) α) (n : ℕ)
    (bounded : work.IsQueryBoundP (fun query => valueRead? query = true) n) (state : PqxdhDynamicKemJointSource.State KemSK) :
    (((simulateQ (lowImpl (V := V) setup router) work).run).run state).IsQueryBoundP
      (fun query => valueRead? query = true) n := by
  rw [lowImpl, QueryImpl.simulateQ_compose]
  exact fwdOption_hidden _ _ n (fwd_hidden _ _ n bounded) state

/-- Every step of the collapsed native layer makes at most one hidden read, and only on a grouped finish with the challenge marker. -/
theorem mid_marked (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    (query : (GSpec KemSK Response).Domain) (state : SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK) :
    (((midImpl setup codec checks identityIndex publicIdentity services router query).run).run state).IsQueryBoundP
      (fun query => valueRead? query = true) (if markedGroup query = true then 1 else 0) := by
  rw [midImpl, composeOpt_step, isQueryBoundP_map_iff]
  exact low_hidden setup router _ _ (skelImpl_marked setup codec checks identityIndex publicIdentity services query state.1)
    state.2

variable {coins : {X : Type} → ProbComp X → OracleComp spec' X} {primitives : PqxdhJointIdentity.Primitives}
  {pool : QueryImpl (PqxdhLiveKemBirth.PoolSpec KemSK)
    (OptionT (StateT (PqxdhDynamicKemRouter.State KemSK) (OracleComp spec')))}

/-- No step of the lower interpreters decreases the KEM creation counter. -/
theorem low_mono (setup : Setup baseSpec KemSK) (counts : CountsCreates pool) :
    StepMono (lowImpl (V := V) setup (PqxdhDynamicKemJointRouter.combine coins primitives pool)) created :=
  stepMono_compose _ created (stepMono_fwdOption _ created (combine_mono coins primitives pool counts)) _

/-- No step of the collapsed native layer decreases the KEM creation counter. -/
theorem mid_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (counts : CountsCreates pool) :
    StepMono (midImpl setup codec checks identityIndex publicIdentity services
      (PqxdhDynamicKemJointRouter.combine coins primitives pool)) (fun state => created state.2) :=
  stepMono_composeOpt _ _ created (low_mono setup counts)

/-- A private-pool request of the grouped interface reaches the router unchanged, with the skeleton's state kept. -/
theorem mid_pool (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response)
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    (query : (PqxdhLiveKemBirth.Spec KemSK).Domain) (skel : SkelState KemSK V)
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    (((midImpl setup codec checks identityIndex publicIdentity services router
        (.inl (.inl (.inl query)))).run).run (skel, lower)) =
      (fun result => (result.1, (skel, result.2))) <$> (((router query).run).run lower).liftComp (spec' + TSpec V) := by
  have skelStep : (skelImpl setup codec checks identityIndex publicIdentity services
      (.inl (.inl (.inl query)))).run skel = (fun reply => (reply, skel)) <$> encLift (V := V) (KemSK := KemSK) (.inl query) :=
    rfl
  rw [midImpl, composeOpt_step, skelStep]
  simp only [encLift, simulateQ_map, simulateQ_spec_query, lowImpl, QueryImpl.apply_compose, fwd_inl,
    PqxdhRegistrationJointKemEncapsulation.actual, liftComp_inl, OptionT.run_map, StateT.run_map, fwdOption_inl,
    Functor.map_map]
  congr 1
  funext result
  rcases result with ⟨_ | reply, after⟩ <;> rfl

/-- A raw `create` of the grouped client keeps the potential: the born owner's KEM index is the router's counter before the request, and the counter is incremented. -/
theorem create_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool) (pin : PqxdhBeaconPhase2Preparation.Word32)
    (keyId : Std.U64) (owners : List EncodedEntry) (skel : SkelState KemSK V)
    (lower : PqxdhDynamicKemJointSource.State KemSK) :
    ∀ result ∈ support (((simulateQ (midImpl setup codec checks identityIndex publicIdentity services
        (PqxdhDynamicKemJointRouter.combine coins primitives pool))
        ((groupedClient setup codec selected challenge (.inl (.inr (.create pin keyId)))).run owners)).run).run
          (skel, lower)), ∀ value, result.1 = some value →
      ownerCount selected value.2 + pending selected (created result.2.2) ≤
        ownerCount selected owners + pending selected (created lower) := by
  intro result member value found
  have program : (groupedClient (KemSK := KemSK) setup codec selected challenge (.inl (.inr (.create pin keyId)))).run
      owners = simulateQ groupedLift ((PqxdhRegistrationJointRevealSchedule.client setup codec
        (.inl (.inr (.create pin keyId)))).run owners) := rfl
  rw [program, create_run, simulateQ_map, ← QueryImpl.simulateQ_compose, simulateQ_map, OptionT.run_map,
    StateT.run_map, ← QueryImpl.simulateQ_compose,
    option_lift_state (PqxdhDynamicKemJointRouter.combine coins primitives pool) _ (fun query extra below => by
      rw [QueryImpl.apply_compose, QueryImpl.apply_compose]
      simp only [PqxdhRegistrationJointServiceSchedule.poolLift, simulateQ_spec_query, groupedLift]
      exact mid_pool setup codec checks identityIndex publicIdentity services _ query extra below),
    Functor.map_map, support_map] at member
  obtain ⟨inner, reached, rfl⟩ := member
  have routed := mem_support_of_mem_support_liftComp _ _ inner reached
  have grows := option_monotone _ created (combine_mono coins primitives pool counts) _ lower inner routed
  rcases inner with ⟨_ | born, after⟩
  · cases found
  · simp only [Option.map_some, Option.some.injEq] at found
    subst found
    cases born with
    | none => simpa using pending_anti selected grows
    | some birth =>
        obtain ⟨index, step⟩ := client_created coins primitives pool counts lower _ routed birth rfl
        dsimp only
        rw [ownerCount_birth, step]
        simp only [index]
        have := pending_step selected (created lower)
        omega

/-- The hidden-read bound of one source request: one for a grouped finish of an owner that awaits its finish with the selected KEM index, none otherwise. -/
def finishBound (selected : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List EncodedEntry) : Nat :=
  match FinishAt query with
  | some request => finishMark selected owners request.1
  | none => 0

theorem finishBound_le (selected : Nat) (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (owners : List EncodedEntry) : finishBound selected query owners ≤ ownerCount selected owners := by
  unfold finishBound
  split
  · exact finishMark_le selected owners _
  · exact Nat.zero_le _

/-- Every source request of the continuation makes at most as many hidden reads as the potential drops; a stopped request ends with potential 0. -/
theorem top_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : List EncodedEntry × (SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK)) :
    PotBound (((topImpl setup codec checks identityIndex publicIdentity services selected challenge
        (PqxdhDynamicKemJointRouter.combine coins primitives pool) query).run).run state)
      (fun query => valueRead? query = true) (optPot (potential selected)) (potential selected state) := by
  rw [topImpl, composeOpt_step]
  apply potBound_map
  have dle := finishBound_le selected query state.1
  refine potBound_of_bound (d := finishBound selected query state.1)
    (isQueryBoundP_option_of_step _ _ _ (groupedClient_marked setup codec selected challenge query state.1)
      (fun query current => mid_marked setup codec checks identityIndex publicIdentity services _ query current) state.2)
    (dle.trans (Nat.le_add_right _ _)) ?_
  intro result member
  rcases result with ⟨_ | ⟨answer, owners⟩, after⟩
  · simp only [Function.comp, optPot, Option.map_none, zero_add]
    exact dle.trans (Nat.le_add_right _ _)
  · simp only [Function.comp, optPot, Option.map_some, Option.getD_some, potential]
    by_cases create : CreateKind query
    · obtain ⟨pin, keyId, rfl⟩ : ∃ pin keyId, query = .inl (.inr (.create pin keyId)) := by
        rcases query with (coin | request) | read
        · simp [CreateKind] at create
        · cases request with
          | create pin keyId => exact ⟨pin, keyId, rfl⟩
          | _ => simp [CreateKind] at create
        · simp [CreateKind] at create
      have := create_step setup codec checks identityIndex publicIdentity services selected challenge counts pin keyId
        state.1 state.2.1 state.2.2 _ member (answer, owners) rfl
      simpa [finishBound, FinishAt] using this
    · have reached := option_support _ _ _ _ member (answer, owners) rfl
      have counted := groupedClient_count setup codec selected challenge selected query create state.1 _ reached
      have grows := option_monotone _ _ (mid_mono setup codec checks identityIndex publicIdentity services counts) _
        state.2 _ member
      have pend := pending_anti selected grows
      have counted' : ownerCount selected owners + finishBound selected query state.1 ≤ ownerCount selected state.1 :=
        counted
      dsimp only at pend
      omega

/-- The hidden reads of the continuation are bounded by the potential at its start. -/
theorem top_potential (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) (selected : Nat)
    (challenge : MlKem768Ciphertext) (counts : CountsCreates pool) {α : Type}
    (work : OracleComp (PqxdhRegistrationJointRevealSchedule.Spec KemSK) α)
    (state : List EncodedEntry × (SkelState KemSK V × PqxdhDynamicKemJointSource.State KemSK)) :
    PotBound (((simulateQ (topImpl setup codec checks identityIndex publicIdentity services selected challenge
        (PqxdhDynamicKemJointRouter.combine coins primitives pool)) work).run).run state)
      (fun query => valueRead? query = true) (optPot (potential selected)) (potential selected state) :=
  option_potential _ _ (potential selected) (fun _ => True)
    (fun query current _ => top_step setup codec checks identityIndex publicIdentity services selected challenge counts
      query current)
    (fun _ _ _ _ _ _ _ => trivial) work state trivial

end Stack

/-! ### The post-challenge phase of the skeleton -/

section Skeleton

open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X V : Type}

/-- The prechallenge context of an active cut has at most one owner holding the selected KEM index, and none while the router has not yet handed it out: the potential at the cut is at most one. -/
def KemOnce (selected : Nat) {count : Nat} : OpaqueContext Reader KemSK A X count → Prop
  | .ready _ _ (some (.pending _ _ _ _ _ owners _)) state _ =>
      ownerCount selected owners + pending selected state.2.created ≤ 1
  | _ => True

/-- The actual encapsulator followed by the router is the lower interpreter. -/
theorem low_eq (setup : Setup baseSpec KemSK)
    {ι' : Type} {spec' : OracleSpec.{0, 0} ι'}
    (router : QueryImpl (PqxdhLiveKemBirth.Spec KemSK)
      (OptionT (StateT (PqxdhDynamicKemJointSource.State KemSK) (OracleComp spec'))))
    {α : Type} (work : OracleComp (Enc KemSK + TSpec V) α) :
    simulateQ (fwdOption (T := TSpec V) router)
        (simulateQ (fwd (T := TSpec V) (PqxdhRegistrationJointKemEncapsulation.actual setup)) work) =
      simulateQ (lowImpl (V := V) setup router) work := by
  rw [lowImpl, QueryImpl.simulateQ_compose]

/-- Stage T, the hidden reads of the post-challenge phase: for any services, the skeleton's post-challenge phase makes at most two hidden reads when the prechallenge context satisfies `KemOnce`: one at the Server's private resumption root and at most one at a grouped Beacon finish on the challenge marker. -/
theorem postSkel_two (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) (once : KemOnce selected.val context) :
    (postSkel setup codec checks decision count selected services chosen challenge context).IsQueryBoundP
      (fun query => valueRead? query = true) 2 := by
  rcases context with state | ⟨server, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  · trivial
  · trivial
  · trivial
  · simp only [postSkel]
    split
    · rw [isQueryBoundP_map_iff]
      refine fwd_hidden _ _ _ ?_
      rw [low_eq, skelResume, option_simulate_bind]
      refine isQueryBoundP_bind (n := 1) (m := 1) ?_ fun result reached => ?_
      · exact low_hidden setup _ _ 1 (IsQueryBoundP.simulateQ_run_StateT_of_step (resume_root setup codec checks _ _ raw
          value ephemeral _ _ native.2 consumed) (fun query current =>
            resumeImpl_hidden setup.hmac native.2.sessions services query current) _) _
      · rcases result with ⟨_ | answer, after⟩
        · trivial
        · dsimp only
          rw [composeOpt_run, isQueryBoundP_map_iff, composeOpt_run, isQueryBoundP_map_iff]
          have counts : CountsCreates (PqxdhDynamicKemRouter.post setup.kem selected.val
              (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
              PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder) := router_counts _ _ _
          have mono : StepMono (lowImpl (V := V) setup (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
              (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge
              PqxdhRegistrationJointBeaconOpaqueFinishRouter.placeholder)) created :=
            low_mono (coins := PqxdhPrivateKemSource.ccaCoins) (primitives := setup.joint) setup counts
          have grows := option_monotone _ created mono _ _ _ reached
          refine (isQueryBoundP_of_potBound (top_potential (V := V) (coins := PqxdhPrivateKemSource.ccaCoins)
            (primitives := setup.joint) setup codec checks _ _ services selected.val challenge counts _
            (owners, (answer.2, after)))).mono ?_
          have pend := pending_anti selected.val grows
          simp only [KemOnce] at once
          simp only [potential]
          change pending selected.val (created after) ≤ pending selected.val state.2.created at pend
          omega
    · trivial

end Skeleton

end BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_marked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_marked

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_pool' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.mid_pool

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.create_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.create_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finishBound_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.finishBound_le

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.top_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.top_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.top_potential' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.top_potential

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.low_eq

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.postSkel_two' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointBeaconFinishOnce.postSkel_two
