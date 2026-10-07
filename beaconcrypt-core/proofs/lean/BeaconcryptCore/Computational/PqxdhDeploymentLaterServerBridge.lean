-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerInitialized

/-! LQ-F spike: theorem T4 for the logged source. The logged command compiler and the logged exposure are natural in the program result (`commands_map`, `exposeAt_map`), the identity-observation exposure interprets to the hidden logged command program of the tagged program (`exposeAt_tag`), and the scanned program of the KEM games at the logged exposure is the result map of the KEM scan of that exposure (`scanned_map`). A completed run of an active logged cut records the selected raw bytes (`rawResume_tag`), so a run event forces the encapsulation to the selected reserved key (`active_raw`). `run_le_real`, `commands_le_real` and `actual_le_real` are the proofs of `KemRawBridge` with the logged definitions: the logged initialized execution is first rewritten into the selected-first game of the logged source (`LaterServerInitialized.actual_source_first`), the generic monitor `PqxdhDynamicKemJointStopping.history_event` moves the event to the stopped router, the stopped run splits at the logged KEM cut, and an active cut is finished by the challenger's ordinary encapsulation followed by the saved logged continuation, which is the continuation of the KEM real game. The final-state event is the existing `KemRawBridge.Decided ∧ GoodKem ∧ KeyMatchFinal` on the logged outcome with its log forgotten; the decision reads the program result, which may hold the terminal Server reveal. The creation premise is a cap on the Beacon creations of the logged program. No assumption is added. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag accepted decideTag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointRawSignatures (verified)
open PqxdhRegistrationJointKemRawNatural (mapOutcome cutMap)
open PqxdhRegistrationJointKemRawBridge (Final Decided GoodKem KeyMatchFinal RunEvent prefix_lookup selected_lookup)
open PqxdhDeploymentLaterServerSource (Log Spec)
open PqxdhDeploymentLaterServerCommands (tag commands)
open PqxdhDeploymentLaterServerCut (exposeAt rawResume tagged)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R S Result Next : Type}

/-- The logged command compiler is natural in the program result. -/
theorem commands_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (f : R → S) (client : OracleComp (Spec KemSK) R)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    commands setup codec checks identityIndex publicIdentity (f <$> client) owners log state =
      mapOutcome f <$> commands setup codec checks identityIndex publicIdentity client owners log state := by
  simp only [commands, PqxdhDeploymentLaterServerCommands.run, simulateQ_map, StateT.run_map, Functor.map_map]
  rfl

/-- The logged exposure of the selected accept is natural in the observation of the tagged result. -/
theorem exposeAt_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (f : R → S)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) :
    exposeAt setup codec checks identityIndex publicIdentity (fun output => f (observe output)) work index owners log
        state =
      mapOutcome f <$> exposeAt setup codec checks identityIndex publicIdentity observe work index owners log state := by
  simp only [exposeAt, map_bind]
  apply bind_congr
  rintro ⟨⟨cut, after, logAt⟩, native⟩
  cases cut with
  | complete result => rw [map_pure]; rfl
  | pending raw next =>
    dsimp only
    rw [map_bind]
    apply bind_congr
    intro answer
    have same : tagged (fun output => f (observe output)) raw next answer.1.1 =
        f <$> tagged observe raw next answer.1.1 := by
      simp only [tagged, Functor.map_map]
    rw [same, commands_map, PqxdhRegistrationJointKemRawNatural.hide_map]

/-- With the identity observation, the logged exposure interprets under the actual encapsulator to the hidden logged command program of the tagged program. -/
theorem exposeAt_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (Spec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (log : Log) (state : NativeState KemSK) :
    simulateQ (actual setup) (exposeAt setup codec checks identityIndex publicIdentity id work index owners log state) =
      simulateQ (actual setup) (commands setup codec checks identityIndex publicIdentity (tag work index) owners log
        state) := by
  rw [PqxdhDeploymentLaterServerCut.exposeAt_actual, id_map]

/-- The scanned program of the KEM games for the logged source is the result map of the KEM scan of the identity-observation exposure. -/
theorem scanned_map (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index : Nat)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) :
    PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created =
      cutMap (mapOutcome (decideTag decision)) <$> PqxdhRegistrationJointKemCut.scan setup
        (exposeAt setup codec checks created.server.server.metadata.identityIndex created.publicIdentity id work index []
          [] (PqxdhRegistrationJointInitializedAccept.initial created)) 0 := by
  rw [← PqxdhRegistrationJointKemRawNatural.scan_map, ← exposeAt_map]
  rfl

/-- Every result of the saved continuation of an active logged cut records the selected raw bytes in its tag. -/
theorem rawResume_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (state : NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option Nat → OracleComp (Spec KemSK) X) (reply : PqxdhRegistrationJointKemCut.Reply)
    (outcome : Outcome KemSK R)
    (reached : outcome ∈ support (rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral
      consumed state owners log next reply)) :
    ∃ result answer, outcome.1.1 = observe (result, some (raw, answer)) := by
  simp only [rawResume, mem_support_bind_iff] at reached
  obtain ⟨_, _, answer, _, reached⟩ := reached
  have client := PqxdhDeploymentLaterServerCut.commands_support setup codec checks identityIndex publicIdentity
    _ _ _ _ _ (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _
      (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ reached))
  rw [tagged, support_map] at client
  obtain ⟨result, _, same⟩ := client
  exact ⟨result, answer.1, same.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- At a pending logged KEM cut of the identity-observation exposure, every completed stopped-router continuation that satisfies the run event encapsulated to the selected reserved key. -/
theorem active_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (Spec KemSK) X) (index : Nat) (owners : List EncodedEntry) (log : Log)
    (state : NativeState KemSK) (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (chosen : MlKem768PublicKey × KemSK) (reserved : pairs[selected]? = some chosen)
    (request : PqxdhRegistrationJointKemCut.Request)
    (resume : PqxdhRegistrationJointKemCut.Reply →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK (X × Tag)))
    (cutSupport : .pending request resume ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity id work index owners log state) 0))
    (reply : PqxdhRegistrationJointKemCut.Reply) (start : PqxdhDynamicKemJointSource.State KemSK)
    (reached : Option (Outcome KemSK (X × Tag)) × PqxdhDynamicKemJointSource.State KemSK)
    (reachedRun : reached ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint
      setup.kem selected pairs) (simulateQ (actual setup) (resume reply))).run).run start))
    (event : RunEvent setup codec checks decision selected pairs reached) : request.2 = chosen.1 := by
  obtain ⟨raw, next, value, ephemeral, consumed, native, after, logAt, _, checked, rfl, rfl⟩ :=
    PqxdhDeploymentLaterServerCut.rawCut_shape setup codec checks identityIndex publicIdentity id work index
      owners log state request resume cutSupport
  obtain ⟨outcome, raw', answer, value', found, _, _, tagged, checked', keyed⟩ := event
  rcases reached with ⟨_ | final, finalState⟩
  · cases found
  cases found
  have inner := PqxdhRegistrationJointKemRawNatural.router_support _ _ _ _ _ reachedRun
  obtain ⟨result, answer', same⟩ := rawResume_tag setup codec checks identityIndex publicIdentity id raw value
    ephemeral consumed native after logAt next reply outcome
    (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ inner)
  rw [same] at tagged
  simp only [id_eq, Option.some.injEq, Prod.mk.injEq] at tagged
  obtain ⟨rfl, -⟩ := tagged
  rw [checked, Option.some.injEq] at checked'
  subst checked'
  obtain ⟨pair, foundPair, first⟩ := Option.map_eq_some_iff.mp keyed
  have whole := prefix_lookup (List.take_prefix _ _) foundPair
  rw [reserved] at whole
  cases whole
  exact first.symm

set_option backward.isDefEq.respectTransparency false in
/-- Under the stopped selected-KEM router, the run event of the hidden logged command program of the tagged program is at most the probability that the logged raw-ordinal KEM real game, after the same prephase, returns `true`. -/
theorem run_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[(fun reached => decide (RunEvent setup codec checks decision selected.val
        (List.ofFn (selected.insertNth chosen others)) reached)) <$>
      ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (simulateQ (actual setup) (commands setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (tag work index) [] [] (PqxdhRegistrationJointInitializedAccept.initial created)))).run).run
        (joint, PqxdhDynamicKemRouter.empty)] {true} ≤
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} := by
  classical
  rw [← exposeAt_tag, ← PqxdhRegistrationJointKemCut.scan_finish _ _ 0,
    PqxdhRegistrationJointKemRawNatural.router_split, map_bind, scanned_map,
    PqxdhRegistrationJointKemRawNatural.router_map, bind_map_left, evalDist_apply_singleton, evalDist_apply_singleton]
  apply probOutput_bind_mono
  rintro ⟨_ | cut, after⟩ reachedCut
  · have absent : ¬RunEvent setup codec checks decision selected.val (List.ofFn (selected.insertNth chosen others))
        (none, after) := by
      rintro ⟨_, _, _, _, found, _⟩
      cases found
    rw [Option.elim_none, map_pure, decide_eq_false absent]
    rw [probOutput_eq_zero_of_not_mem_support (by simp)]
    exact zero_le
  · have cutSupport := PqxdhRegistrationJointKemRawNatural.router_support _ _ _ _ _ reachedCut
    cases cut with
    | complete outcome =>
      obtain ⟨result, tagValue, same, rejected⟩ := PqxdhDeploymentLaterServerCut.accepted_reached setup codec
        checks _ _ id work index _ _ _ outcome cutSupport
      have absent : ¬RunEvent setup codec checks decision selected.val (List.ofFn (selected.insertNth chosen others))
          (some outcome, after) := by
        rintro ⟨final, raw, answer, value, found, _, session, _⟩
        cases found
        rw [same] at session
        exact absurd session (by simpa using rejected)
      rw [Option.elim_some, PqxdhRegistrationJointKemCut.finish, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
        map_pure, decide_eq_false absent]
      rw [probOutput_eq_zero_of_not_mem_support (by simp)]
      exact zero_le
    | pending request resume =>
      dsimp only [Option.elim_some, Option.map_some]
      rw [PqxdhRegistrationJointKemRawNatural.finish_stopped, map_bind]
      by_cases active : request.2 = chosen.1
      · rw [active]
        apply probOutput_bind_mono
        intro encapsulated _
        rw [probOutput_bind_const, probFailure_eq_zero, tsub_zero, one_mul]
        simp only [PqxdhRegistrationJointKemResume.sourcePost, cutMap, active, ite_true, simulateQ_map,
          OptionT.run_map, StateT.run_map, bind_pure_comp, Functor.map_map]
        rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput, probEvent_map, probEvent_map]
        apply probEvent_mono
        rintro reached _ event
        simp only [Function.comp_apply, decide_eq_true_eq] at event ⊢
        obtain ⟨outcome, _, _, _, found, decided, session, _⟩ := event
        rcases reached with ⟨_ | final, state⟩
        · cases found
        · cases found
          simp only [Option.map_some, PqxdhRegistrationJointKemGame.decision, mapOutcome, decideTag, decided,
            session, Bool.and_self]
      · rw [probOutput_eq_zero_of_not_mem_support]
        · exact zero_le
        intro member
        rw [mem_support_bind_iff] at member
        obtain ⟨encapsulated, _, member⟩ := member
        rw [support_map] at member
        obtain ⟨reached, reachedRun, event⟩ := member
        rw [decide_eq_true_eq] at event
        exact active (active_raw setup codec checks decision _ _ work index _ _ _ selected.val _ chosen
          (selected_lookup selected chosen others) request resume cutSupport _ after reached reachedRun event)

set_option backward.isDefEq.respectTransparency false in
/-- For one initialized Server and one reservation, the final event of the logged monitored commands of the tagged program is at most the probability that the logged raw-ordinal KEM real game, after the same prephase, returns `true`. -/
theorem commands_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (Spec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      PqxdhDeploymentLaterServerInitialized.commands setup codec checks created (tag work index) joint runtime
        selected.val (List.ofFn (selected.insertNth chosen others))] {true} ≤
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} := by
  classical
  refine le_trans ?_ (run_le_real setup codec checks decision work index count selected created joint runtime chosen
    others)
  simp only [PqxdhDeploymentLaterServerInitialized.commands, Functor.map_map]
  rw [evalDist_apply_singleton, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  refine le_trans (probEvent_mono (q := fun reached => RunEvent setup codec checks decision selected.val
    (List.ofFn (selected.insertNth chosen others)) reached ∧
      reached.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected.val) = false) ?_) ?_
  · rintro ⟨_ | outcome, state⟩ _ final
    · simp only [Function.comp_apply, decide_eq_true_eq] at final
      obtain ⟨⟨_, found, _⟩, _⟩ := final
      cases found
    · simp only [Function.comp_apply, decide_eq_true_eq] at final
      obtain ⟨⟨_, found, decided, session⟩, good, ⟨_, raw, answer, value, found', tagged, checked, keyed⟩⟩ := final
      cases found
      cases found'
      exact ⟨⟨outcome, raw, answer, value, rfl, decided, session, tagged, checked, keyed⟩, good⟩
  refine le_trans (le_of_eq (PqxdhDynamicKemJointStopping.history_event setup.baseImpl setup.joint setup.kem
    selected.val (List.ofFn (selected.insertNth chosen others)) _ (joint, PqxdhDynamicKemRouter.empty) rfl
    (fun reached => RunEvent setup codec checks decision selected.val
      (List.ofFn (selected.insertNth chosen others)) reached))) ?_
  apply probEvent_mono
  intro reached _ event
  simpa only [Function.comp_apply, decide_eq_true_eq] using event.1

/-- The tagged logged program keeps every all-reply cap of the logged program. -/
theorem tag_bound (work : OracleComp (Spec KemSK) X) (index : Nat)
    (predicate : (Spec KemSK).Domain → Prop) [DecidablePred predicate] (cap : Nat)
    (bounded : work.IsQueryBoundP predicate cap) : (tag work index).IsQueryBoundP predicate cap := by
  apply (isQueryBoundP_map_iff (tag work index) Prod.fst cap).mp
  rw [PqxdhDeploymentLaterServerCommands.tag_erase]
  exact bounded

set_option backward.isDefEq.respectTransparency false in
/-- Theorem T4 for the logged source: in the logged initialized execution of the tagged logged program, with the log forgotten, the probability that the selected raw accept returned a session, the decision holds, KEM key `selected` was never disclosed and the verified PQ key of the recorded raw bytes is the final pool key at creation index `selected`, is at most the probability that the raw-ordinal KEM real game of the logged exposure returns `true`. The decision reads the program result, which may contain the terminal Server reveal. -/
theorem actual_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (Spec KemSK) X) (runtime : A) (count : Nat) (selected : Fin (count + 1)) (index : Nat)
    (bounded : work.IsQueryBoundP
      (fun query => PqxdhDeploymentLaterServerReserve.laterKind (KemSK := KemSK) query = some (.inl 1)) (count + 1)) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map fun outcome =>
          PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup outcome.1, result.2)) <$>
        (PqxdhDeploymentLaterServerSource.initialized setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} ≤
    𝒟[PqxdhDeploymentLaterServerKemHop.sourceReal setup ensureInit supplied
      (PqxdhDeploymentLaterServerCut.scanned setup codec checks decision work index) runtime count selected] {true} := by
  classical
  have same := PqxdhDeploymentLaterServerInitialized.actual_source_first setup codec checks ensureInit supplied
    (tag work index) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) rfl count selected
    (tag_bound work index _ _ bounded)
  rw [evalDist_apply_singleton, probOutput_def, evalSPMF_map, same, ← evalSPMF_map, ← probOutput_def,
    evalDist_apply_singleton]
  simp only [PqxdhDeploymentLaterServerInitialized.selectedFirst, PqxdhDeploymentLaterServerKemHop.sourceReal,
    PqxdhDeploymentLaterServerKemHop.sourcePre, map_bind, bind_assoc]
  apply probOutput_bind_mono
  intro chosen _
  apply probOutput_bind_mono
  rintro ⟨_ | created, after⟩ _
  · rw [map_pure, probOutput_eq_zero_of_not_mem_support]
    · exact zero_le
    rw [support_pure, Set.mem_singleton_iff]
    intro equal
    have event := equal.symm
    simp only [decide_eq_true_eq] at event
    obtain ⟨⟨_, found, _⟩, _⟩ := event
    cases found
  · dsimp only
    simp only [map_bind, bind_assoc, pure_bind]
    apply probOutput_bind_mono
    intro others _
    have core := commands_le_real setup codec checks decision work index count selected created after.1.1 after.2
      chosen others
    rw [evalDist_apply_singleton, evalDist_apply_singleton] at core
    simpa only [map_bind, bind_assoc, pure_bind] using core

end BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.commands_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.commands_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.exposeAt_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.exposeAt_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.exposeAt_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.exposeAt_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.scanned_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.scanned_map

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.rawResume_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.rawResume_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.active_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.active_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.run_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.run_le_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.commands_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.commands_le_real

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.tag_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.tag_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.actual_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentLaterServerBridge.actual_le_real
