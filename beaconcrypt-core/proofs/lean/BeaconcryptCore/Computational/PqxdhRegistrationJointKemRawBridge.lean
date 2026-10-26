-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawNatural

/-! Bridge from the actual initialized execution of the tagged program to the raw-ordinal KEM real game. The final-state event is that the selected raw accept returned a session, the adversary decision holds, KEM key `selected` was never disclosed, and the verified PQ key of the recorded raw bytes is the public key at creation index `selected` of the final KEM pool. The bridge is a probability inequality, obtained after the existing source-order equality `KemInitialization.actual_source_first`; it does not rewrite programs across that step. Under the selected-first reservation the final pool is a prefix of the reserved list, so the event forces the encapsulation of the selected raw accept to target the selected key; the selected-disclosure monitor moves the event from the ordinary router to the stopped router; the stopped run of the tagged program splits at the KEM cut of the selected accept; and an active cut is finished by exactly the challenger's ordinary encapsulation followed by the saved continuation, which is the continuation of the KEM real game. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge
open PqxdhKemIndCca PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhServerAuthNative (NativeState)
open PqxdhRegistrationJointKemEncapsulation (actual)
open PqxdhRegistrationJointKemCommands (SourceSpec Outcome)
open PqxdhRegistrationJointAcceptCutTag (Tag tag accepted decideTag)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointAcceptKemCut (exposeAt rawResume)
open PqxdhRegistrationJointRawSignatures (verified)
open PqxdhRegistrationJointKemRawNatural (mapOutcome cutMap)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R : Type}

/-- The final source result of the actual initialized execution of the tagged program. -/
abbrev Final (KemSK A X : Type) :=
  Option (PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (X × Tag)) ×
    PqxdhRegistrationJointServerPrefix.State KemSK A

/-- The selected raw accept returned a session and the adversary decision on the original result holds. -/
def Decided (decision : X → Bool) (final : Final KemSK A X) : Prop :=
  ∃ outcome, final.1 = some outcome ∧ decision outcome.2.1.1 = true ∧ accepted outcome.2.1.2 = true

/-- KEM key `kemIndex` was never disclosed: the final private KEM transcript has no successful reveal of that creation index. -/
def GoodKem {count : Nat} (kemIndex : Fin count) (final : Final KemSK A X) : Prop :=
  final.2.1.2.transcript.any (PqxdhDynamicKemStopping.disclosed kemIndex.val) = false

/-- The raw bytes recorded for the selected accept verify, and their verified PQ key is the public key at creation index `kemIndex` of the final KEM pool. -/
def KeyMatchFinal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) {count : Nat}
    (kemIndex : Fin count) (final : Final KemSK A X) : Prop :=
  ∃ outcome raw answer value, final.1 = some outcome ∧ outcome.2.1.2 = some (raw, answer) ∧
    verified setup codec checks raw = some value ∧
    (final.2.1.2.keys[kemIndex.val]?).map Prod.fst = some value.keys.pqKey

/-- Every result of the saved continuation of an active cut of `exposeAt` records the selected raw bytes in its tag, under any observation. -/
theorem rawResume_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (state : NativeState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (reply : PqxdhRegistrationJointKemCut.Reply)
    (outcome : Outcome KemSK R)
    (reached : outcome ∈ support (rawResume setup codec checks identityIndex publicIdentity observe raw value ephemeral
      consumed state owners next reply)) :
    ∃ result answer, outcome.1.1 = observe (result, some (raw, answer)) := by
  simp only [rawResume, mem_support_bind_iff] at reached
  obtain ⟨_, _, answer, _, reached⟩ := reached
  have client := PqxdhRegistrationJointAcceptKemCut.commands_support setup codec checks identityIndex publicIdentity
    _ _ _ _ (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _
      (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ reached))
  rw [PqxdhRegistrationJointAcceptKemCut.tagged, support_map] at client
  obtain ⟨result, _, same⟩ := client
  exact ⟨result, answer.1, same.symm⟩

/-- Every outcome of the actual source command program of the tagged client whose selected accept returned a session records raw bytes whose attached verification succeeds. -/
theorem program_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (work : OracleComp (SourceSpec KemSK) X) (index : Nat)
    (owners : List EncodedEntry) (state : NativeState KemSK) (outcome : Outcome KemSK (X × Tag))
    (reached : outcome ∈ support (PqxdhRegistrationJointKemCommands.program setup codec checks identityIndex
      publicIdentity (tag work index) owners state))
    (session : accepted outcome.1.1.2 = true) :
    ∃ raw answer value, outcome.1.1.2 = some (raw, answer) ∧ verified setup codec checks raw = some value := by
  rw [← PqxdhRegistrationJointKemRawNatural.exposeAt_tag, ← PqxdhRegistrationJointKemCut.scan_finish _ _ 0,
    mem_support_bind_iff] at reached
  obtain ⟨cut, cutReached, reached⟩ := reached
  cases cut with
  | complete final =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ reached
    obtain ⟨result, tagValue, same, rejected⟩ := PqxdhRegistrationJointAcceptKemCut.accepted_reached setup codec checks
      identityIndex publicIdentity id work index owners state _ cutReached
    rw [same] at session
    exact absurd session (by simpa using rejected)
  | pending request resume =>
    obtain ⟨raw, next, value, ephemeral, consumed, native, after, _, checked, _, rfl⟩ :=
      PqxdhRegistrationJointAcceptKemCut.rawCut_shape setup codec checks identityIndex publicIdentity id work index
        owners state request resume cutReached
    rw [PqxdhRegistrationJointKemCut.finish, mem_support_bind_iff] at reached
    obtain ⟨reply, _, reached⟩ := reached
    obtain ⟨result, answer, same⟩ := rawResume_tag setup codec checks identityIndex publicIdentity id raw value ephemeral
      consumed native after next reply outcome (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ reached)
    exact ⟨raw, answer, value, by rw [same]; rfl, checked⟩

/-- Under the ordinary selected-disclosure monitor started from the actual empty KEM pool, the monitor bit is clear exactly when the projected private KEM transcript has no successful reveal of the selected creation index. -/
theorem good_source (baseImpl : QueryImpl baseSpec ProbComp) (primitives : Primitives)
    (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (selected : Nat)
    (pairs : List (MlKem768PublicKey × KemSK)) {Result : Type}
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) Result) (joint : PqxdhDynamicIdentityPool.SourceState)
    (reached : Option Result × PqxdhDynamicKemJointSource.State KemSK)
    (supported : reached ∈ support (((simulateQ (PqxdhDynamicKemJointSource.normal baseImpl primitives kem selected pairs)
      client).run).run (joint, PqxdhDynamicKemRouter.empty))) :
    PqxdhDynamicKemJointStopping.Good reached.2 ↔
      (PqxdhDynamicKemJointSource.project pairs reached.2).2.transcript.any
        (PqxdhDynamicKemStopping.disclosed selected) = false := by
  have tracked := PqxdhDynamicKemJointStopping.schedule_tracked baseImpl primitives kem selected pairs client
    (joint, PqxdhDynamicKemRouter.empty) rfl reached supported
  change reached.2.2.forbiddenReveal = reached.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) at tracked
  change reached.2.2.forbiddenReveal = false ↔ reached.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected) = false
  rw [tracked]

/-- A lookup in a prefix of a list is the same lookup in the list. -/
theorem prefix_lookup {α : Type} {front whole : List α} (prefixed : front <+: whole) {position : Nat} {value : α}
    (found : front[position]? = some value) : whole[position]? = some value := by
  obtain ⟨bound, rfl⟩ := List.getElem?_eq_some_iff.mp found
  exact List.prefix_iff_getElem?.mp prefixed position bound

/-- The reserved list of the selected-first game holds the chosen pair at the selected creation index. -/
theorem selected_lookup {count : Nat} (selected : Fin (count + 1)) (chosen : MlKem768PublicKey × KemSK)
    (others : Fin count → MlKem768PublicKey × KemSK) :
    (List.ofFn (selected.insertNth chosen others))[selected.val]? = some chosen := by
  simpa only [List.nil_append, List.length_nil, Nat.zero_add] using
    PqxdhLiveKemSelection.selected_index [] selected chosen others

/-- The event on a selected-KEM router run of the tagged program: the run completed, the selected accept returned a session, the decision holds, and the recorded raw bytes verify to a PQ key equal to the public key reserved at creation index `selected` among the created pairs. -/
def RunEvent (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) (decision : X → Bool)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK))
    (reached : Option (Outcome KemSK (X × Tag)) × PqxdhDynamicKemJointSource.State KemSK) : Prop :=
  ∃ outcome raw answer value, reached.1 = some outcome ∧ decision outcome.1.1.1 = true ∧
    accepted outcome.1.1.2 = true ∧ outcome.1.1.2 = some (raw, answer) ∧ verified setup codec checks raw = some value ∧
    ((pairs.take reached.2.2.created)[selected]?).map Prod.fst = some value.keys.pqKey

set_option backward.isDefEq.respectTransparency false in
/-- At a pending KEM cut of the identity-observation exposure, every completed stopped-router continuation that satisfies the run event encapsulated to the selected reserved key: the recorded raw bytes are those of the cut, so their verified PQ key is the requested key, and the run event equates that key with the reserved key at the selected creation index. -/
theorem active_raw (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (identityIndex : Nat) (publicIdentity : PublicIdentity)
    (work : OracleComp (SourceSpec KemSK) X) (index : Nat) (owners : List EncodedEntry) (state : NativeState KemSK)
    (selected : Nat) (pairs : List (MlKem768PublicKey × KemSK)) (chosen : MlKem768PublicKey × KemSK)
    (reserved : pairs[selected]? = some chosen) (request : PqxdhRegistrationJointKemCut.Request)
    (resume : PqxdhRegistrationJointKemCut.Reply →
      OracleComp (PqxdhRegistrationJointKemEncapsulation.Spec KemSK) (Outcome KemSK (X × Tag)))
    (cutSupport : .pending request resume ∈ support (PqxdhRegistrationJointKemCut.scan setup
      (exposeAt setup codec checks identityIndex publicIdentity id work index owners state) 0))
    (reply : PqxdhRegistrationJointKemCut.Reply) (start : PqxdhDynamicKemJointSource.State KemSK)
    (reached : Option (Outcome KemSK (X × Tag)) × PqxdhDynamicKemJointSource.State KemSK)
    (reachedRun : reached ∈ support (((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint
      setup.kem selected pairs) (simulateQ (actual setup) (resume reply))).run).run start))
    (event : RunEvent setup codec checks decision selected pairs reached) : request.2 = chosen.1 := by
  obtain ⟨raw, next, value, ephemeral, consumed, native, after, _, checked, rfl, rfl⟩ :=
    PqxdhRegistrationJointAcceptKemCut.rawCut_shape setup codec checks identityIndex publicIdentity id work index
      owners state request resume cutSupport
  obtain ⟨outcome, raw', answer, value', found, _, _, tagged, checked', keyed⟩ := event
  rcases reached with ⟨_ | final, finalState⟩
  · cases found
  cases found
  have inner := PqxdhRegistrationJointKemRawNatural.router_support _ _ _ _ _ reachedRun
  obtain ⟨result, answer', same⟩ := rawResume_tag setup codec checks identityIndex publicIdentity id raw value
    ephemeral consumed native after next reply outcome (PqxdhRegistrationJointAcceptKemCut.support_simulate _ _ _ inner)
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
/-- Under the stopped selected-KEM router, the run event of the tagged program is at most the probability that the raw-ordinal KEM real game, after the same prephase, returns `true`. The stopped run splits at the KEM cut of the selected accept. A stop, a completion before encapsulation or an encapsulation to another key contributes nothing: completion leaves the selected accept without a session, and the recorded raw bytes of the event force the encapsulated key to be the reserved key at the selected index. An active cut is finished by one ordinary encapsulation to the selected key followed by the saved continuation, which is exactly the real-game continuation of the decision program; the challenger's extra uniform draw is lossless. -/
theorem run_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[(fun reached => decide (RunEvent setup codec checks decision selected.val
        (List.ofFn (selected.insertNth chosen others)) reached)) <$>
      ((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemCommands.program setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (tag work index) [] (PqxdhRegistrationJointInitializedAccept.initial created))).run).run
        (joint, PqxdhDynamicKemRouter.empty)] {true} ≤
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} := by
  classical
  rw [← PqxdhRegistrationJointKemRawNatural.exposeAt_tag, ← PqxdhRegistrationJointKemCut.scan_finish _ _ 0,
    PqxdhRegistrationJointKemRawNatural.router_split, map_bind, PqxdhRegistrationJointKemRawNatural.rawScan_map,
    PqxdhRegistrationJointKemRawNatural.router_map, bind_map_left, ← prEvent_eq_evalDist_singleton _ true,
    ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨_ | cut, after⟩ reachedCut
  · have absent : ¬RunEvent setup codec checks decision selected.val (List.ofFn (selected.insertNth chosen others))
        (none, after) := by
      rintro ⟨_, _, _, _, found, _⟩
      cases found
    rw [Option.elim_none, map_pure, decide_eq_false absent]
    rw [prEvent_eq_zero_of_not_mem_support]
    · exact zero_le
    · simp
  · have cutSupport := PqxdhRegistrationJointKemRawNatural.router_support _ _ _ _ _ reachedCut
    cases cut with
    | complete outcome =>
      obtain ⟨result, tagValue, same, rejected⟩ := PqxdhRegistrationJointAcceptKemCut.accepted_reached setup codec
        checks _ _ id work index _ _ outcome cutSupport
      have absent : ¬RunEvent setup codec checks decision selected.val (List.ofFn (selected.insertNth chosen others))
          (some outcome, after) := by
        rintro ⟨final, raw, answer, value, found, _, session, _⟩
        cases found
        rw [same] at session
        exact absurd session (by simpa using rejected)
      rw [Option.elim_some, PqxdhRegistrationJointKemCut.finish, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
        map_pure, decide_eq_false absent]
      rw [prEvent_eq_zero_of_not_mem_support]
      · exact zero_le
      · simp
    | pending request resume =>
      dsimp only [Option.elim_some, Option.map_some]
      rw [PqxdhRegistrationJointKemRawNatural.finish_stopped, map_bind]
      by_cases active : request.2 = chosen.1
      · rw [active]
        apply prEvent_bind_mono_of_forall_le_of_support
        intro encapsulated _
        conv_rhs => rw [(OracleComp.EvalDistEq.bind_const _ _).prEvent_eq (fun y => y = true)]
        rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
        simp only [PqxdhRegistrationJointKemResume.sourcePost, cutMap, active, ite_true, simulateQ_map,
          OptionT.run_map, StateT.run_map, bind_pure_comp, Functor.map_map]
        rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
        apply prEvent_mono_of_support
        rintro reached _ event
        simp only [decide_eq_true_eq] at event ⊢
        obtain ⟨outcome, _, _, _, found, decided, session, _⟩ := event
        rcases reached with ⟨_ | final, state⟩
        · cases found
        · cases found
          simp only [Option.map_some, PqxdhRegistrationJointKemGame.decision, mapOutcome, decideTag, decided,
            session, Bool.and_self]
      · rw [prEvent_eq_zero_of_not_mem_support]
        · exact zero_le
        intro member
        rw [mem_support_bind_iff] at member
        obtain ⟨encapsulated, _, member⟩ := member
        rw [support_map] at member
        obtain ⟨reached, reachedRun, event⟩ := member
        rw [decide_eq_true_eq] at event
        exact active (active_raw setup codec checks decision _ _ work index _ _ selected.val _ chosen
          (selected_lookup selected chosen others) request resume cutSupport _ after reached reachedRun event)

set_option backward.isDefEq.respectTransparency false in
/-- For one initialized Server and one reservation, the final event of the monitored actual source commands of the tagged program is at most the probability that the raw-ordinal KEM real game, after the same prephase, returns `true`. The ordinary monitor turns the never-disclosed condition into the stopped router with the same complete state (`PqxdhDynamicKemJointStopping.history_event` from the actual empty pool), and the final pool is the created prefix of the reserved list. -/
theorem commands_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (work : OracleComp (SourceSpec KemSK) X) (index count : Nat) (selected : Fin (count + 1))
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (joint : PqxdhDynamicIdentityPool.SourceState)
    (runtime : A) (chosen : MlKem768PublicKey × KemSK) (others : Fin count → MlKem768PublicKey × KemSK) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      PqxdhRegistrationJointKemInitialization.commands setup codec checks created (tag work index) joint runtime
        selected.val (List.ofFn (selected.insertNth chosen others))] {true} ≤
    𝒟[((simulateQ (PqxdhDynamicKemJointRouter.stopped setup.baseImpl setup.joint setup.kem selected.val
        (List.ofFn (selected.insertNth chosen others)))
        (PqxdhRegistrationJointKemRawChallenge.rawScan setup codec checks decision work index created)).run).run
        (joint, PqxdhDynamicKemRouter.empty) >>= fun result =>
      simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps chosen.1) >>=
        fun encapsulated => ($ᵗ MlKemSharedSecret) >>= fun _ =>
          PqxdhRegistrationJointKemGame.decision <$> PqxdhRegistrationJointKemResume.sourcePost setup count selected
            chosen ⟨chosen.1, encapsulated.1, .ready created others result.1 result.2 runtime⟩ encapsulated.2] {true} := by
  classical
  refine le_trans ?_ (run_le_real setup codec checks decision work index count selected created joint runtime chosen
    others)
  simp only [PqxdhRegistrationJointKemInitialization.commands, Functor.map_map]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  refine le_trans (prEvent_mono_of_support _ _ (fun reached => RunEvent setup codec checks decision selected.val
    (List.ofFn (selected.insertNth chosen others)) reached ∧
      reached.2.2.history.any (PqxdhDynamicKemStopping.disclosed selected.val) = false) ?_) ?_
  · rintro ⟨_ | outcome, state⟩ _ final
    · simp only [decide_eq_true_eq] at final
      obtain ⟨⟨_, found, _⟩, _⟩ := final
      cases found
    · simp only [decide_eq_true_eq] at final
      obtain ⟨⟨_, found, decided, session⟩, good, ⟨_, raw, answer, value, found', tagged, checked, keyed⟩⟩ := final
      cases found
      cases found'
      exact ⟨⟨outcome, raw, answer, value, rfl, decided, session, tagged, checked, keyed⟩, good⟩
  refine le_trans (le_of_eq (PqxdhDynamicKemJointStopping.history_event setup.baseImpl setup.joint setup.kem
    selected.val (List.ofFn (selected.insertNth chosen others)) _ (joint, PqxdhDynamicKemRouter.empty) rfl
    (fun reached => RunEvent setup codec checks decision selected.val
      (List.ofFn (selected.insertNth chosen others)) reached))) ?_
  apply prEvent_mono_of_support
  intro reached _ event
  simpa only [decide_eq_true_eq] using event.1

set_option backward.isDefEq.respectTransparency false in
/-- Theorem T4: in the actual initialized source execution of the tagged program, the probability that the selected raw accept returned a session, the decision holds, KEM key `selected` was never disclosed and the verified PQ key of the recorded raw bytes is the final pool key at creation index `selected`, is at most the probability that the raw-ordinal KEM real game returns `true`. The first step is the existing source-order equality `KemInitialization.actual_source_first`; every later step is a probability inequality on the selected-first game. -/
theorem actual_le_real (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (decision : X → Bool)
    (work : OracleComp (SourceSpec KemSK) X) (runtime : A) (budget : PqxdhRegistrationJointKemCommands.Budget)
    (certified : ∀ source, work.IsQueryBoundP
      (fun query => PqxdhRegistrationJointRevealCosts.sourceKind (KemSK := KemSK) query = source) (budget source))
    (count : Nat) (selected : Fin (count + 1)) (index : Nat) (room : budget (.inl 1) ≤ count + 1) :
    letI := Classical.propDecidable
    𝒟[(fun final => decide (Decided decision final ∧ GoodKem selected final ∧
        KeyMatchFinal setup codec checks selected final)) <$>
      ((fun result => (result.1.map (PqxdhRegistrationJointInitializedSchedule.encodeOutcome setup), result.2)) <$>
        (PqxdhRegistrationJointInitializedSchedule.source setup codec checks ensureInit supplied (tag work index)).run
          ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime))] {true} ≤
    𝒟[PqxdhRegistrationJointKemRawGame.sourceReal setup codec checks ensureInit supplied decision work runtime count
      selected index] {true} := by
  classical
  have same := PqxdhRegistrationJointKemInitialization.actual_source_first setup codec checks ensureInit supplied
    (tag work index) ((PqxdhDynamicIdentityPool.initialState, PqxdhLiveKemBirth.empty), runtime) rfl budget
    (fun source => PqxdhRegistrationJointAcceptCutTag.tag_bound work index _ _ (certified source)) count selected room
  rw [(same.map _).evalDist_eq]
  simp only [PqxdhRegistrationJointKemInitialization.selectedFirst, PqxdhRegistrationJointKemRawGame.sourceReal,
    PqxdhRegistrationJointKemRawChallenge.sourcePreRaw, map_bind, bind_assoc]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
  apply prEvent_bind_mono_of_forall_le_of_support
  intro chosen _
  apply prEvent_bind_mono_of_forall_le_of_support
  rintro ⟨_ | created, after⟩ _
  · rw [map_pure, prEvent_eq_zero_of_not_mem_support]
    · exact zero_le
    rw [support_pure, Set.mem_singleton_iff]
    intro equal
    have event := equal.symm
    simp only [decide_eq_true_eq] at event
    obtain ⟨⟨_, found, _⟩, _⟩ := event
    cases found
  · dsimp only
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    simp only [map_bind, bind_assoc, pure_bind]
    rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true]
    apply prEvent_bind_mono_of_forall_le_of_support
    intro others _
    have core := commands_le_real setup codec checks decision work index count selected created after.1.1 after.2
      chosen others
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    simpa only [map_bind, bind_assoc, pure_bind] using core

/-- Every outcome of the actual initialized source client of the tagged program whose selected accept returned a session records raw bytes whose attached verification succeeds. The client's final result is the result of the actual source command program of the tagged client, so `program_tag` applies. -/
theorem client_tag (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (ensureInit : StateT A ProbComp Bool) (supplied : Option Pqxdh.Bytes) (work : OracleComp (SourceSpec KemSK) X)
    (index : Nat) (state : PqxdhRegistrationJointServerPrefix.State KemSK A) (final : Final KemSK A X)
    (reached : final ∈ support ((PqxdhRegistrationJointInitializedSchedule.client setup codec checks ensureInit
      supplied (tag work index)).run state))
    (outcome : PqxdhRegistrationJointInitializedSchedule.Outcome KemSK (X × Tag)) (found : final.1 = some outcome)
    (session : accepted outcome.2.1.2 = true) :
    ∃ raw answer value, outcome.2.1.2 = some (raw, answer) ∧ verified setup codec checks raw = some value := by
  simp only [PqxdhRegistrationJointInitializedSchedule.client, StateT.run, mem_support_bind_iff] at reached
  obtain ⟨⟨_ | created, after⟩, _, reached⟩ := reached
  · rw [mem_support_pure_iff] at reached
    subst reached
    cases found
  · dsimp only at reached
    rw [← PqxdhRegistrationJointOpenBackend.execute_run, PqxdhRegistrationJointOpenBackend.execute,
      PqxdhRegistrationJointOpenBackend.run, Functor.map_map, Functor.map_map, support_map] at reached
    obtain ⟨executed, ran, rfl⟩ := reached
    cases found
    have program : executed.1 ∈ support (PqxdhRegistrationJointKemCommands.program setup codec checks
        created.server.server.metadata.identityIndex created.publicIdentity (tag work index) []
        (PqxdhRegistrationJointInitializedAccept.initial created)) := by
      apply support_simulateQ_run'_subset
        (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) _ (PqxdhRegistrationJointInitializedSchedule.initial
          after.1 created).pool
      rw [StateT.run'_eq, support_map]
      exact Set.mem_image_of_mem _ ran
    exact program_tag setup codec checks _ _ work index _ _ executed.1 program session

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.rawResume_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.rawResume_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.program_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.program_tag

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.good_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.good_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.prefix_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.prefix_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.selected_lookup' depends on axioms: [propext] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.selected_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.active_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.active_raw

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.run_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.run_le_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.commands_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.commands_le_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.actual_le_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.actual_le_real

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.client_tag' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationJointKemRawBridge.client_tag
