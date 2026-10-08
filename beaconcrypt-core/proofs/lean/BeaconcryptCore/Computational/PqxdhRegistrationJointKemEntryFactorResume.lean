import BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactorSteps

/-!
# The Server's resumption and the post-challenge phase under the factored services (item 2, stage S3b, resumption)

This module completes the native-layer comparison of stage S3b and carries it through the interpreter stack of the skeleton's post-challenge phase.

- `resume_rel`: the Server's private resumption of the selected raw accept, run from the cut state with no marks, is related for the native and the factored services. Its private root request on the challenge marker returns the root itself under the native services and the placeholder root under the factored services; the root reaches only the pending token published at the end of the resumption, so the two runs agree up to the projection `proj` once the token is published (`challenge_rel`). Every other part of the resumption reads no hidden value.
- `skelResume_factor`: the skeleton's resumed client with the native services, mapped by the projection, is the relabelled resumed client with the factored services.
- `postSkel_factor`: the skeleton's post-challenge phase with the native services is the post-challenge phase with the factored services, with every hidden read answered by the hidden root's 108-byte output `PqxdhServerAuthKeySchedule.fromRoot setup.source` (`relabelS`). The relabelling moves through the actual encapsulator, the post-challenge router and the CCA evaluation (`relabel_fwd`, `relabel_fwdOption`), and the decision reads none of the states.

These are program equalities; they charge nothing.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemPostSkeleton
open PqxdhSecretInputKdf (HmacBlock HmacOracle RootOutput)

/-! ### Relations on the exposed encapsulation interface -/

section RelC

variable {KemSK : Type}

theorem RelC.bind {α β γ δ : Type} {f : RootOutput → Output} {answer : α → β} {answer' : γ → δ}
    {P : SkelState KemSK RootOutput → Prop} {Q : α → SkelState KemSK RootOutput → Prop}
    {R : γ → SkelState KemSK RootOutput → Prop}
    {native : SClient KemSK RootOutput α} {factored : SClient KemSK Output β}
    {next : α → SClient KemSK RootOutput γ} {nextF : β → SClient KemSK Output δ}
    (first : RelC f answer P Q native factored)
    (rest : ∀ value, RelC f answer' (Q value) R (next value) (nextF (answer value))) :
    RelC f answer' P R (native >>= next) (factored >>= nextF) := by
  intro state holds
  obtain ⟨same, supported⟩ := first state holds
  refine ⟨?_, ?_⟩
  · simp only [StateT.run_bind, map_bind, simulateQ_bind]
    rw [← same, bind_map_left]
    exact bind_congr_of_forall_mem_support _ fun step member =>
      (rest step.1 step.2 (supported step member)).1
  · intro result member
    simp only [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨step, stepMember, member⟩ := member
    exact (rest step.1 step.2 (supported step stepMember)).2 result member

/-- A native-layer program lifted to the exposed encapsulation interface distributes over binds. -/
theorem liftT_bind {V α β : Type} (work : NGame KemSK V α) (next : α → NGame KemSK V β) :
    liftT (work >>= next) = liftT work >>= fun value => liftT (next value) := by
  apply StateT.ext
  intro state
  change simulateQ (fwd (T := TSpec V) (coinLift (KemSK := KemSK))) ((work >>= next).run state) = _
  rw [StateT.run_bind, simulateQ_bind]
  rfl

theorem liftT_pure {V α : Type} (value : α) :
    liftT (KemSK := KemSK) (V := V) (Pure.pure value) = Pure.pure value := by
  apply StateT.ext
  intro state
  change simulateQ (fwd (T := TSpec V) (coinLift (KemSK := KemSK))) ((Pure.pure value : NGame KemSK V α).run state) = _
  rw [StateT.run_pure, simulateQ_pure]
  rfl

end RelC

/-! ### The Server's resumption -/

section Resume

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The prefix of the resumption only forwards requests of the exposed encapsulation interface. -/
theorem resume_prefix_run {V α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (services : Services V Response) (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α)
    (state : SkelState KemSK V) :
    (simulateQ (resumeImpl (Reader := Reader) hmac index services)
        (simulateQ PqxdhRegistrationJointKemOpaqueResume.prefixLift work)).run state =
      (fun reply => (reply, state)) <$> simulateQ (encLift (V := V)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, map_bind]
      change ((fun reply => (reply, state)) <$> encLift (V := V) query) >>= _ = _
      rw [bind_map_left]
      exact bind_congr fun reply => ih reply

/-- The tail of the resumption runs the private native tail on the native layer. -/
theorem resume_tail_run {V α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (services : Services V Response)
    (work : OracleComp (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) α) :
    simulateQ (resumeImpl hmac index services) (simulateQ PqxdhRegistrationJointKemOpaqueResume.tailLift work) =
      liftT (simulateQ (resumeTail hmac index services) work) := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, liftT_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, PqxdhRegistrationJointKemOpaqueResume.tailLift, simulateQ_spec_query, liftT_bind]
      exact bind_congr fun reply => ih reply

/-- The prefix of the resumption is related to itself. -/
theorem resume_prefix_rel {α : Type} (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat)
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (f : RootOutput → Output)
    (P : SkelState KemSK RootOutput → Prop) (work : OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) α) :
    RelC f id P (fun _ => P)
      (simulateQ (resumeImpl (Reader := Reader) hmac index (nativeServices setup codec checks))
        (simulateQ PqxdhRegistrationJointKemOpaqueResume.prefixLift work))
      (simulateQ (resumeImpl (Reader := Reader) hmac index (factoredServices setup codec checks))
        (simulateQ PqxdhRegistrationJointKemOpaqueResume.prefixLift work)) := by
  intro state holds
  refine ⟨?_, ?_⟩
  · rw [resume_prefix_run, resume_prefix_run, simulateQ_map, relabelE_encLift, Functor.map_map]
    rfl
  · intro result member
    rw [resume_prefix_run, support_map] at member
    obtain ⟨reply, -, rfl⟩ := member
    exact holds

theorem mark_run {V : Type} (index : Nat) (value : V) (state : SkelState KemSK V) :
    (mark index value).run state = Pure.pure ((), (state.1, some (index, value))) := rfl

theorem consumeGame_run {V : Type} (rid : beaconcrypt_core.pqxdh.RegistrationId) (state : SkelState KemSK V) :
    (consumeGame rid).run state = Pure.pure ((), ({ state.1 with server := { state.1.server with
      consumed := state.1.server.consumed ++ [absBytes rid.bytes] } }, state.2)) := rfl

theorem modifyGame_run {V : Type} (change : GameState KemSK → GameState KemSK) (state : SkelState KemSK V) :
    (PqxdhRegistrationJointKemPostSkeleton.modifyGame change).run state = Pure.pure ((), (change state.1, state.2)) := rfl

theorem setGame_run {V : Type} (game : GameState KemSK) (state : SkelState KemSK V) :
    (PqxdhRegistrationJointKemPostSkeleton.setGame game).run state = Pure.pure ((), (game, state.2)) := rfl

/-- Publish a pending token at a session. -/
def publishAt (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned) (game : GameState KemSK) :
    GameState KemSK :=
  { game with pending := Function.update game.pending index (some token) }

/-- The private root on the challenge marker, the consumption and the publication: the native side publishes the root, the factored side the placeholder root; both mark the session. -/
theorem challenge_rel (f : RootOutput → Output) (index : Nat) (point : PqxdhCorrelatedExtractFamily.Message)
    (rid : beaconcrypt_core.pqxdh.RegistrationId) (token : beaconcrypt_core.pqxdh.PendingServerRegistration) :
    Rel (KemSK := KemSK) f id (fun state => state.2 = none ∧ index < state.1.sessions) (fun _ => Inv)
      (valueRead point >>= fun value => mark index value >>= fun _ => consumeGame rid >>= fun _ =>
        PqxdhRegistrationJointKemPostSkeleton.modifyGame (publishAt index ⟨value, token⟩) >>= fun _ =>
          Pure.pure (some index))
      (valueRead point >>= fun value => mark index value >>= fun _ => consumeGame rid >>= fun _ =>
        PqxdhRegistrationJointKemPostSkeleton.modifyGame
          (publishAt index ⟨PqxdhServerAuthEntryFactor.sentinel, token⟩) >>= fun _ =>
          Pure.pure (some index)) := by
  rintro ⟨game, marks⟩ ⟨none_marks, below⟩
  simp only at none_marks
  subst none_marks
  refine ⟨?_, ?_⟩
  · rw [proj_none]
    simp only [StateT.run_bind, valueRead_eq, mark_run, consumeGame_run, modifyGame_run, StateT.run_pure,
      bind_map_left, pure_bind, map_bind, map_pure, simulateQ_bind, simulateQ_pure]
    rw [relabel_query_value, bind_map_left]
    refine bind_congr fun root => ?_
    simp only [Prod.map_apply, id_eq, proj, Option.map_some, placeholderAt, publishAt, Function.update_self,
      placeholderToken, Function.update_idem]
  · intro result member
    simp only [StateT.run_bind, valueRead_eq, mark_run, consumeGame_run, modifyGame_run, StateT.run_pure,
      bind_map_left, pure_bind, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨root, -, rfl⟩ := member
    intro marked root' found
    simp only [Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨rfl, rfl⟩ := found
    refine ⟨below, fun token' found' => ?_⟩
    simp only [publishAt, Function.update_self, Option.some.injEq] at found'
    rw [← found']

/-- A state without marks satisfies the invariant. -/
theorem inv_none (game : GameState KemSK) : Inv ((game, none) : SkelState KemSK RootOutput) := by
  intro index root found
  cases found

/-- The private native tail of the Server's resumption, from the cut state without marks, is related for the native and the factored services. -/
theorem tail_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicIdentity : PublicIdentity) (game : GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes) :
    Rel (PqxdhServerAuthKeySchedule.fromRoot setup.source) id (fun state => state = (game, none)) (fun _ => Inv)
      (simulateQ (resumeTail setup.hmac game.sessions (nativeServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity game collected))
      (simulateQ (resumeTail setup.hmac game.sessions (factoredServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId publicIdentity game collected)) := by
  have noneFramed : Framed (KemSK := KemSK) fun state => state.2 = none := fun _ _ holds _ _ => holds
  have start : Rel (KemSK := KemSK) (PqxdhServerAuthKeySchedule.fromRoot setup.source) id
      (fun state => state = (game, none))
      (fun _ state => state.2 = none ∧ game.sessions < state.1.sessions)
      (PqxdhRegistrationJointKemPostSkeleton.setGame
        { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } })
      (PqxdhRegistrationJointKemPostSkeleton.setGame
        { game with sessions := game.sessions + 1, server := { game.server with consumed := collected.2 } }) :=
    Rel.setGame _ _ _ _ _ (fun state same => by subst same; rfl)
      (fun state same => by subst same; exact ⟨rfl, Nat.lt_succ_self _⟩)
  have stop : ∀ {α : Type} (value : α), Rel (KemSK := KemSK) (PqxdhServerAuthKeySchedule.fromRoot setup.source) id
      (fun state => state.2 = none ∧ game.sessions < state.1.sessions) (fun _ => Inv) (Pure.pure value)
      (Pure.pure value) := fun value => Rel.pure value fun state holds => by
    obtain ⟨g, m⟩ := state
    simp only at holds
    rw [holds.1]
    exact inv_none g
  rcases collected with ⟨_ | input, consumed⟩
  · simp only [PqxdhRegistrationJointKemOpaqueTail.tail, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
      resumeTail]
    exact Rel.bind start fun _ => stop none
  · obtain ⟨verified, ephemeral, ciphertext, converted, first, second, third, fourth, shared⟩ := input
    cases accepted : PqxdhRegistrationJointKemOpaqueCore.accept game.server.control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩
        ⟨verified, ephemeral, ciphertext, converted, first, second, third, fourth, shared⟩ with
    | ok result =>
        cases result with
        | Ok pair =>
            cases shared with
            | challenge =>
                simp only [PqxdhRegistrationJointKemOpaqueTail.tail, PqxdhRegistrationJointKemOpaqueClient.client,
                  accepted, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
                  PqxdhRegistrationJointKemOpaqueTail.forward, resumeTail, bind_assoc, pure_bind]
                exact Rel.bind start fun _ => challenge_rel _ _ _ _ _
            | known secret =>
                simp only [PqxdhRegistrationJointKemOpaqueTail.tail, PqxdhRegistrationJointKemOpaqueClient.client,
                  accepted, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
                  PqxdhRegistrationJointKemOpaqueTail.forward, resumeTail, bind_assoc, pure_bind]
                refine Rel.bind start fun _ => Rel.bind (Rel.tableRead _ _ _) fun block =>
                  Rel.bind (Rel.consume _ _ (framed_and noneFramed fun state game holds _ sessions => sessions ▸ holds) _)
                    fun _ => Rel.bind (Rel.modifyGame _ _ (fun _ state => state.2 = none ∧
                      game.sessions < state.1.sessions) _ (fun state holds => ?_) (fun state holds => ?_)) fun _ =>
                        stop _
                · rw [holds.1]
                  rfl
                · exact ⟨holds.1, holds.2⟩
        | Err error =>
            simp only [PqxdhRegistrationJointKemOpaqueTail.tail, PqxdhRegistrationJointKemOpaqueClient.client,
              accepted, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
              PqxdhRegistrationJointKemOpaqueTail.forward, resumeTail, bind_assoc, pure_bind]
            exact Rel.bind start fun _ => stop none
    | fail error =>
        simp only [PqxdhRegistrationJointKemOpaqueTail.tail, PqxdhRegistrationJointKemOpaqueClient.client,
          accepted, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
          PqxdhRegistrationJointKemOpaqueTail.forward, resumeTail, bind_assoc, pure_bind]
        exact Rel.bind start fun _ => stop none
    | div =>
        simp only [PqxdhRegistrationJointKemOpaqueTail.tail, PqxdhRegistrationJointKemOpaqueClient.client,
          accepted, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
          PqxdhRegistrationJointKemOpaqueTail.forward, resumeTail, bind_assoc, pure_bind]
        exact Rel.bind start fun _ => stop none

/-- The Server's private resumption, from the cut state without marks, is related for the native and the factored services. -/
theorem resume_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (game : GameState KemSK) (consumed : List Pqxdh.Bytes) :
    RelC (PqxdhServerAuthKeySchedule.fromRoot setup.source) id (fun state => state = (game, none)) (fun _ => Inv)
      (simulateQ (resumeImpl setup.hmac game.sessions (nativeServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
          ciphertext .challenge game consumed))
      (simulateQ (resumeImpl setup.hmac game.sessions (factoredServices setup codec checks))
        (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
          ciphertext .challenge game consumed)) := by
  simp only [PqxdhRegistrationJointKemOpaqueResume.resume, simulateQ_bind]
  refine RelC.bind (resume_prefix_rel setup.hmac game.sessions setup codec checks _ _ _) fun collected => ?_
  rw [resume_tail_run, resume_tail_run]
  exact liftT_rel (tail_rel setup codec checks publicIdentity game collected)

end Resume

/-! ### The post-challenge phase -/

section Post

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The skeleton's resumed client with the native services, mapped by the projection, is the relabelled resumed client with the factored services. -/
theorem skelResume_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat) (ciphertext : MlKem768Ciphertext) :
    Prod.map id (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source)) <$>
        skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners next
          selected ciphertext (nativeServices setup codec checks) =
      simulateQ (relabelE (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (skelResume setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners next
          selected ciphertext (factoredServices setup codec checks)) := by
  have resumed := resume_rel setup codec checks identityIndex publicIdentity raw value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray ciphertext) game consumed (game, none) rfl
  rw [proj_none] at resumed
  unfold skelResume
  rw [map_bind, simulateQ_bind, ← resumed.1, bind_map_left]
  exact bind_congr_of_forall_mem_support _ fun answer member =>
    (skelImpl_run setup codec checks identityIndex publicIdentity _ answer.2 (resumed.2 answer member)).1

/-- Stage S3b, native part. The skeleton's post-challenge phase with the native services is the post-challenge phase with the factored services, with every hidden read answered by the 108-byte output `PqxdhServerAuthKeySchedule.fromRoot setup.source` of the hidden root. -/
theorem postSkel_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) (context : OpaqueContext Reader KemSK A X count) :
    postSkel setup codec checks decision count selected (nativeServices setup codec checks) chosen challenge context =
      simulateQ (relabelS (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (postSkel setup codec checks decision count selected (factoredServices setup codec checks) chosen challenge
          context) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, next⟩),
    state, runtime⟩
  all_goals try (simp only [postSkel, simulateQ_pure]; done)
  by_cases active : value.keys.pqKey = chosen.1
  · simp only [postSkel, active, ↓reduceIte]
    rw [simulateQ_map, relabel_fwd, relabel_fwdOption, relabel_fwd, ← skelResume_factor,
      simulateQ_map (impl := PqxdhRegistrationJointKemPostSkeleton.fwd (PqxdhRegistrationJointKemEncapsulation.actual setup)),
      simulateQ_map, OptionT.run_map, StateT.run_map, simulateQ_map, Functor.map_map]
    congr 1
    funext result
    rcases result with ⟨_ | outcome, after⟩ <;> rfl
  · simp only [postSkel, active, ↓reduceIte, simulateQ_pure]

end Post

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.RelC.bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.RelC.bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_bind

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.liftT_pure

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_prefix_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_prefix_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_tail_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_tail_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_prefix_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_prefix_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mark_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.mark_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.consumeGame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.consumeGame_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.modifyGame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.modifyGame_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.setGame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.setGame_run

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.challenge_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.challenge_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.inv_none

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.tail_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.tail_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.resume_rel

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelResume_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.skelResume_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.postSkel_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemEntryFactor.postSkel_factor
