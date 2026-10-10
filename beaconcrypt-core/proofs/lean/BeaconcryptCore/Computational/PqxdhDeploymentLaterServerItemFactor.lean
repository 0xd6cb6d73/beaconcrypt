-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemRoot

/-! LQ-F upstream, unit A2: stage S3b of item 2 over the logged source (LQ-F upstream design-v2, section 4.4, module `…ItemFactor`). The uniform-root world of stage S2 over the logged source (`PqxdhCorrelatedExpandHybrid.uniformGame rootClientL`) is the key-schedule game `PqxdhServerAuthKeySchedule.rootHybrid setup.source entryDL` on the distinguisher `PqxdhDeploymentLaterServerItemTargets.entryDL` of unit D1, the 108 bytes of entry 0 of the logged branch (`uniformGameL_entry`, as an equality of output distributions).

- The logged skeleton with the native services and with the factored services are related step by step under the classical invariant `PqxdhRegistrationJointKemEntryFactor.Inv` and projection `proj` (the marked value becomes its 108-byte image, and the marked session's pending token holds the placeholder root): every classical request by `PqxdhRegistrationJointKemEntryFactor.skelImpl_rel`, and the logged accept by `acceptStepL_rel`, the proof of `acceptStep_rel` on the logged collector, whose logged scalar is fixed before the tail and passes through (`skelImplL_rel`, `skelImplL_run`).
- `skelResumeL_factor` and `postSkelL_factor`: the Server's private resumption is the classical one (`resume_rel`), so the logged postchallenge phase with the native services is the logged postchallenge phase with the factored services with every hidden read answered by the hidden root's 108-byte output (`relabelS (PqxdhServerAuthKeySchedule.fromRoot setup.source)`). The logged grouped client and the log do not depend on the services.
- `rootClientL_entry`, `eager_entryDL`, `uniformGameL_entry`, `rootClientL_entryDL`: as the classical `rootClient_entry`, `eager_entryD`, `uniformGame_entry`, `rootClient_entryD`, through `internalize_relabel`, `firstTable_relabel` and stage S3a (`PqxdhRootFirstEntry.uniformGame_first`).

These are program and distribution equalities; they charge nothing and add no assumption. The candidate does not occur: `rootClientL`, `entryClientL` and `entryDL` have no candidate argument. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option maxRecDepth 100000
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor
open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhSecretInputKdf (RootOutput)
open PqxdhRegistrationJointAcceptCutTag (Tag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemPostSkeleton (SkelState acceptTail liftT clean encLift nativeServices fwd)
open PqxdhRegistrationJointKemEntryFactor (Output RelC Inv proj relabelE relabelS relabelR relabelE_encLift liftT_rel
  acceptTail_rel skelImpl_rel map_run_inv simulateQ_mapRun relabel_fwd relabel_fwdOption internalize_relabel
  firstTable_relabel mapCache_empty eagerImpl_eq resume_rel proj_none factoredServices placeholderAt
  placeholderAt_server_eq)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhDeploymentLaterServerOpaque (OpaqueContext)
open PqxdhDeploymentLaterServerItemTargets (GSpecL acceptStepL skelImplL skelResumeL postSkelL rootClientL entryClientL
  entryDL)

/-! ### The logged skeleton under the factored services -/

section Native

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The logged skeleton accept unfolded: the logged collector from the consumed set of the skeleton state, then the classical accept tail on the collected input from that state, with the logged scalar returned beside the reply. -/
theorem acceptStepL_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) (state : SkelState KemSK V) :
    (acceptStepL (V := V) setup codec checks identityIndex publicIdentity raw).run state =
      simulateQ (encLift (V := V))
          ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run
            state.1.server.consumed) >>= fun collected =>
        (fun answer => ((answer.1, collected.1.2), answer.2)) <$>
          (liftT (acceptTail setup publicIdentity (clean state.1) (collected.1.1, collected.2))).run state := by
  simp only [acceptStepL, StateT.run_bind, bind_pure_comp, StateT.run_map]
  simp only [StateT.run, bind_map_left, pure_bind]

/-- The exposed logged raw accept of the logged skeleton is related to itself under the invariant: the logged collector reads no hidden value, and the accept tail is the classical one (`PqxdhRegistrationJointKemEntryFactor.acceptTail_rel`). -/
theorem acceptStepL_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) :
    RelC (PqxdhServerAuthKeySchedule.fromRoot setup.source) id Inv (fun _ => Inv)
      (acceptStepL (V := RootOutput) setup codec checks identityIndex publicIdentity raw)
      (acceptStepL (V := Output) setup codec checks identityIndex publicIdentity raw) := by
  intro state holds
  obtain ⟨game, marks⟩ := state
  have before : clean (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) (game, marks)).1 =
      placeholderAt (marks.map Prod.fst) (clean game) := by
    rcases marks with _ | ⟨index, root⟩ <;> rfl
  have consumed : (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) (game, marks)).1.server.consumed =
      game.server.consumed := by
    rw [proj, placeholderAt_server_eq]
  refine ⟨?_, ?_⟩
  · rw [acceptStepL_run, acceptStepL_run, before, consumed, map_bind, simulateQ_bind, relabelE_encLift]
    refine bind_congr fun collected => ?_
    have tail := (liftT_rel (acceptTail_rel setup publicIdentity game marks holds (collected.1.1, collected.2))
      (game, marks) rfl).1
    rw [Functor.map_map, simulateQ_map, ← tail, Functor.map_map]
    rfl
  · intro result member
    rw [acceptStepL_run, mem_support_bind_iff] at member
    obtain ⟨collected, -, member⟩ := member
    rw [support_map] at member
    obtain ⟨answer, reached, rfl⟩ := member
    exact (liftT_rel (acceptTail_rel setup publicIdentity game marks holds (collected.1.1, collected.2))
      (game, marks) rfl).2 answer reached

/-- Every step of the logged skeleton is related, under the invariant, for the native and the factored services: classical requests by `PqxdhRegistrationJointKemEntryFactor.skelImpl_rel`, the logged accept by `acceptStepL_rel`. -/
theorem skelImplL_rel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (query : (GSpecL KemSK Response).Domain) :
    RelC (PqxdhServerAuthKeySchedule.fromRoot setup.source) id Inv (fun _ => Inv)
      (skelImplL setup codec checks identityIndex publicIdentity (nativeServices setup codec checks) query)
      (skelImplL setup codec checks identityIndex publicIdentity (factoredServices setup codec checks) query) := by
  rcases query with query | raw
  · exact skelImpl_rel setup codec checks identityIndex publicIdentity query
  · exact acceptStepL_rel setup codec checks identityIndex publicIdentity raw

/-- Every program of the logged grouped interface: the logged skeleton with the native services, mapped by the projection, is the relabelled logged skeleton with the factored services from the projected state, under the invariant. -/
theorem skelImplL_run {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (GSpecL KemSK Response) α)
    (state : SkelState KemSK RootOutput) (holds : Inv state) :
    Prod.map id (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source)) <$>
        (simulateQ (skelImplL setup codec checks identityIndex publicIdentity (nativeServices setup codec checks))
          work).run state =
      simulateQ (relabelE (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        ((simulateQ (skelImplL setup codec checks identityIndex publicIdentity (factoredServices setup codec checks))
          work).run (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source) state)) ∧
      ∀ result ∈ support ((simulateQ (skelImplL setup codec checks identityIndex publicIdentity
        (nativeServices setup codec checks)) work).run state), Inv result.2 := by
  rw [simulateQ_mapRun]
  exact map_run_inv _ _ Inv _
    (fun query state holds => (skelImplL_rel setup codec checks identityIndex publicIdentity query state holds).2)
    (fun query state holds => (skelImplL_rel setup codec checks identityIndex publicIdentity query state holds).1)
    work state holds

end Native

/-! ### The logged postchallenge phase under the factored services -/

section Post

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The logged skeleton's resumed client with the native services, mapped by the projection, is the relabelled resumed client with the factored services. -/
theorem skelResumeL_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) :
    Prod.map id (proj (PqxdhServerAuthKeySchedule.fromRoot setup.source)) <$>
        skelResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners log
          next selected ciphertext (nativeServices setup codec checks) =
      simulateQ (relabelE (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (skelResumeL setup codec checks identityIndex publicIdentity observe raw value ephemeral consumed game owners
          log next selected ciphertext (factoredServices setup codec checks)) := by
  have resumed := resume_rel setup codec checks identityIndex publicIdentity raw value ephemeral
    (PqxdhAcceptedRegistration.ciphertextArray ciphertext) game consumed (game, none) rfl
  rw [proj_none] at resumed
  unfold skelResumeL
  rw [map_bind, simulateQ_bind, ← resumed.1, bind_map_left]
  exact bind_congr_of_forall_mem_support _ fun answer member =>
    (skelImplL_run setup codec checks identityIndex publicIdentity _ answer.2 (resumed.2 answer member)).1

/-- Stage S3b over the logged source, native part: the logged postchallenge phase with the native services is the logged postchallenge phase with the factored services, with every hidden read answered by the 108-byte output `PqxdhServerAuthKeySchedule.fromRoot setup.source` of the hidden root. -/
theorem postSkelL_factor (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (challenge : MlKem768Ciphertext) (context : OpaqueContext Reader KemSK A X count) :
    postSkelL setup codec checks decision count selected (nativeServices setup codec checks) chosen challenge context =
      simulateQ (relabelS (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (postSkelL setup codec checks decision count selected (factoredServices setup codec checks) chosen challenge
          context) := by
  rcases context with state | ⟨created, others, _ | (outcome | ⟨raw, value, ephemeral, consumed, native, owners, log,
    next⟩), state, runtime⟩
  all_goals try (simp only [postSkelL, simulateQ_pure]; done)
  by_cases active : value.keys.pqKey = chosen.1
  · simp only [postSkelL, active, ↓reduceIte]
    rw [simulateQ_map, relabel_fwd, relabel_fwdOption, relabel_fwd, ← skelResumeL_factor,
      simulateQ_map (impl := fwd (PqxdhRegistrationJointKemEncapsulation.actual setup)),
      simulateQ_map, OptionT.run_map, StateT.run_map, simulateQ_map, Functor.map_map]
    congr 1
    funext result
    rcases result with ⟨_ | outcome, after⟩ <;> rfl
  · simp only [postSkelL, active, ↓reduceIte, simulateQ_pure]

end Post

/-! ### Entry 0 of the logged branch -/

section Entry

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}

/-- The logged root client is the logged factored root client with every value request answered by the 108-byte output of the root at the same coordinates. -/
theorem rootClientL_entry (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index =
      simulateQ (relabelR (PqxdhServerAuthKeySchedule.fromRoot setup.source))
        (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index) := by
  unfold rootClientL entryClientL
  rw [← internalize_relabel]
  congr 1
  funext context
  exact postSkelL_factor setup codec checks decision count selected context.1 context.2.2 context.2.1

/-- The eager run of the logged root client with entry 0's root drawn first is `entryDL` at that root's 108-byte output. -/
theorem eager_entryDL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (root : RootOutput) :
    (simulateQ (PqxdhRootFirstEntry.eagerImpl root)
        (rootClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected
          index)).run' (∅, none) =
      entryDL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root) := by
  rw [rootClientL_entry, eagerImpl_eq, entryDL, StateT.run'_eq, StateT.run'_eq]
  have moved := firstTable_relabel (PqxdhServerAuthKeySchedule.fromRoot setup.source) root ($ᵗ RootOutput)
    (entryClientL (Reader := Reader) setup codec checks ensureInit supplied decision work runtime count selected index)
    (∅, none)
  rw [mapCache_empty] at moved
  rw [← moved, Functor.map_map]
  rfl

/-- Stage S3b over the logged source. The uniform-root world on the logged root client is the key-schedule game on entry 0's distinguisher `entryDL`: entry 0's 32-byte root is uniform, and the game reads it only through its 108-byte key-schedule output. An equality of output distributions; no value is programmed. -/
theorem uniformGameL_entry (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) :
    𝒟[PqxdhCorrelatedExpandHybrid.uniformGame (rootClientL (Reader := Reader) setup codec checks ensureInit supplied
        decision work runtime count selected index)] =
      𝒟[PqxdhServerAuthKeySchedule.rootHybrid setup.source (entryDL (Reader := Reader) setup codec checks ensureInit
        supplied decision work runtime count selected index)] := by
  rw [PqxdhRootFirstEntry.uniformGame_first]
  unfold PqxdhServerAuthKeySchedule.rootHybrid
  congr 2
  funext root
  exact eager_entryDL setup codec checks ensureInit supplied decision work runtime count selected index root

/-- Stage S3b over the logged source for advantages: against any game, the uniform-root world on the logged root client and the key-schedule game on `entryDL` have the same advantage. -/
theorem rootClientL_entryDL (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (runtime : A) (count : Nat)
    (selected : Fin (count + 1)) (index : Nat) (other : ProbComp Bool) :
    other.boolDistAdvantage (PqxdhCorrelatedExpandHybrid.uniformGame (rootClientL (Reader := Reader) setup codec
        checks ensureInit supplied decision work runtime count selected index)) =
      other.boolDistAdvantage (PqxdhServerAuthKeySchedule.rootHybrid setup.source (entryDL (Reader := Reader) setup
        codec checks ensureInit supplied decision work runtime count selected index)) := by
  unfold ProbComp.boolDistAdvantage
  rw [uniformGameL_entry]

end Entry

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.acceptStepL_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.acceptStepL_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.acceptStepL_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.acceptStepL_rel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelImplL_rel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelImplL_rel

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelImplL_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelImplL_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelResumeL_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.skelResumeL_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.postSkelL_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.postSkelL_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.rootClientL_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.rootClientL_entry

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.eager_entryDL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.eager_entryDL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.uniformGameL_entry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.uniformGameL_entry

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.rootClientL_entryDL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerItemFactor.rootClientL_entryDL
