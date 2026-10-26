import BeaconcryptCore.Computational.PqxdhServerAuthRootInitialization
import BeaconcryptCore.Computational.PqxdhServerAuthPhase1Generation

/-! Same-run root provenance through the original pending-token map. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhServerAuthRootOccurrences
open PqxdhJointIdentity PqxdhJointGapDh PqxdhSecretInputKdf
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- Every rejected original accept retains the complete old pending-token map; optional prefix/root rejection does not create a token. -/
theorem rejected_pending (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (raw : Pqxdh.Bytes) (before after : GameState KemSK)
    (supported : (none, after) ∈ support ((acceptOracle setup codec checks publicValue raw).run before)) :
    after.pending = before.pending := by
  simp only [acceptOracle, StateT.run_bind, StateT.run_get, pure_bind] at supported
  obtain ⟨collected, lifted, continued⟩ := (mem_support_bind_iff _ _ _).mp supported
  obtain ⟨_, same⟩ := liftCoins_mem _ _ _ lifted
  simp only [StateT.run_set, pure_bind, same] at continued
  cases actual : collected.1.1 with
  | none =>
      simp only [actual, StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq,
        true_and] at continued
      rw [continued]
  | some input =>
      simp only [actual, StateT.run_bind, mem_support_bind_iff] at continued
      obtain ⟨returned, reached, continued⟩ := continued
      obtain ⟨consumed, extra, stateEq, _, _⟩ := client_run before.sessions (binding setup publicValue) input _ returned reached
      have pendingEq : returned.2.pending = before.pending := by rw [stateEq]
      rcases returned with ⟨outcome, state⟩
      rcases outcome with (_ | token) | error | _
      all_goals simp only [StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and, true_and] at continued
      all_goals rw [continued]; exact pendingEq

/-- A live token after one complete original API callback is either the identical old token, or the exact root-bearing token created by this callback's successful accept. -/
theorem step_token (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (query : ServerAuthSpec.Domain) (reply : ServerAuthSpec.Range query)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State)
    (supported : (reply, after) ∈ support
      ((interp (family setup seed scalar) (authHandler setup codec checks publicValue beaconSeed query)).run before))
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (found : after.1.pending index = some token) :
    before.1.pending index = some token ∨
      ∃ raw input consumed,
        (⟨query, reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = ⟨.inr (.accept raw), some index⟩ ∧
        index = before.1.sessions ∧
        (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run before.1.server.consumed) ∧
        token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
        RootAt setup seed scalar after.2.cache (PqxdhServerRelatedRootInput.message input) token.root ∧
        Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ after.1.ghost.touches := by
  have bare := interpreted_source setup seed scalar
    (authHandler setup codec checks publicValue beaconSeed query) before (reply, after) supported
  rcases query with coin | (raw | ⟨session, payload⟩ | raw | ⟨key, bytes⟩ | bytes | key)
  case inr.accept =>
    by_cases old : before.1.pending index = some token
    · exact Or.inl old
    · right
      have allocation := PqxdhServerAuthPendingBudget.accept_pending setup codec checks publicValue raw
        before.1 (reply, after.1) bare
      dsimp only at allocation
      have coordinate : index = before.1.sessions := by
        rcases allocation.2 with unchanged | ⟨created, installed⟩
        · exact (old (by simpa only [unchanged] using found)).elim
        · by_contra other
          exact old (by simpa only [installed, Function.update_of_ne other] using found)
      cases reply with
      | none =>
          have unchanged := rejected_pending setup codec checks publicValue raw before.1 after.1 bare
          exact (old (by simpa only [unchanged] using found)).elim
      | some allocated =>
          obtain ⟨input, root, consumed, allocatedEq, collected, _, _, rooted, stored, touches⟩ :=
            PqxdhServerAuthRootInitialization.accept_receipt setup codec checks seed scalar publicValue raw
              before allocated after supported
          have sameIndex : allocated = index := allocatedEq.trans coordinate.symm
          rw [sameIndex] at stored
          have sameToken := Option.some.inj (stored.symm.trans found)
          rw [← sameToken]
          refine ⟨raw, input, consumed, by rw [sameIndex], coordinate, collected, rfl, rooted, ?_⟩
          rw [touches, sameIndex]
          exact List.mem_append_right _ (List.mem_cons_self)
  case inr.build =>
    left
    have cleared := (PqxdhServerAuthPendingBudget.build_pending setup codec checks session payload
      before.1 (reply, after.1) bare).2
    dsimp only at cleared
    by_cases same : index = session
    · simp only [cleared, same, Function.update_self, reduceCtorEq] at found
    · simpa only [cleared, Function.update_of_ne same] using found
  all_goals
    left
    have quiet := PqxdhServerAuthPendingBudget.handler_pending_quiet setup codec checks publicValue beaconSeed
      _ (by simp only [IsAcceptQuery]; trivial) (by intros; simp) before.1 (reply, after.1) bare
    dsimp only at quiet
    simpa only [quiet.2] using found

/-- A token's actual accepting callback, including its literal slot, complete original prefix, stored token and returned-root receipt. The cache argument may be a later retained cache. -/
def TokenAt (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes)
    (cache : HmacOracle.QueryCache) (call : Call KemSK) (index : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned) : Prop :=
  call.after.pending index = some token ∧ ∃ raw input consumed,
    (⟨call.query, call.reply⟩ : (query : ServerAuthSpec.Domain) × ServerAuthSpec.Range query) = ⟨.inr (.accept raw), some index⟩ ∧
    index = call.before.sessions ∧
    (some input, consumed) ∈ support ((serverPrefix setup codec checks raw).run call.before.server.consumed) ∧
    token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
    RootAt setup seed scalar cache (PqxdhServerRelatedRootInput.message input) token.root ∧
    Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ call.after.ghost.touches

/-- The same accepting occurrence survives only by retention of its real cache cell, without identifying occurrences from equal output bytes. -/
theorem tokenAt_mono (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : HmacOracle.QueryCache) (grows : before ≤ after)
    (call : Call KemSK) (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (recorded : TokenAt setup codec checks publicValue seed scalar before call index token) :
    TokenAt setup codec checks publicValue seed scalar after call index token := by
  obtain ⟨stored, raw, input, consumed, actual, coordinate, collected, pending, rooted, touched⟩ := recorded
  exact ⟨stored, raw, input, consumed, actual, coordinate, collected, pending,
    root_mono setup seed scalar before after grows _ token.root rooted, touched⟩

/-- The complete actual callback path attributes every remaining token either to its identical initial slot or to a reached earlier accepting occurrence. The latter retains its exact source root at the final cache. -/
theorem path_token (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (index : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (found : after.1.pending index = some token) :
    before.1.pending index = some token ∨ ∃ call ∈ calls,
      TokenAt setup codec checks publicValue seed scalar after.2.cache call index token := by
  revert found
  induction path with
  | nil state primitive => exact fun found => Or.inl found
  | cons call primitive middle suffix final reached rest ih =>
      intro found
      rcases ih found with previous | ⟨original, member, receipt⟩
      · have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
        rcases step_token setup codec checks publicValue beaconSeed seed scalar call.query call.reply
          (call.before, primitive) (call.after, middle) source index token previous with old | created
        · exact Or.inl old
        · right
          exact ⟨call, List.mem_cons_self, tokenAt_mono setup codec checks publicValue seed scalar
            middle.cache final.2.cache
            (path_roots setup codec checks publicValue beaconSeed seed scalar _ _ suffix rest).1
            call index token ⟨previous, created⟩⟩
      · exact Or.inr ⟨original, List.mem_cons_of_mem call member, receipt⟩

/-- In an original run beginning with the literal empty pending map, a successful build consumes a token from a strictly earlier actual accept occurrence. Its installed kernel uses that same token root, whose source receipt remains at the final cache. -/
theorem path_build (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (beacon : RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (initial : PqxdhJointDhExtractFamily.State)
    (final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar
      (initialGameState setup publicValue beacon, initial) calls final)
    (index : Nat) (payload : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (before after : GameState KemSK) (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (member : (⟨.inr (.build index payload), some response, before, after, roots⟩ : Call KemSK) ∈ calls) :
    ∃ earlier later token candidate kernel logged cache original,
      calls = earlier ++ ⟨.inr (.build index payload), some response, before, after, roots⟩ :: later ∧
      original ∈ earlier ∧
      TokenAt setup codec checks publicValue seed scalar final.2.cache original index token ∧
      before.pending index = some token ∧
      Installed setup.source token.root kernel ∧
      after.server = PqxdhServerRegistrationPublication.publish before.server candidate kernel () ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish before.server candidate kernel ()),
        (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () before.server)).run
            ([], before.ctx)) := by
  obtain ⟨earlier, later, primitive, middle, split, preceding, reached, following⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar _ final calls path _ member
  have source := callback_source setup codec checks publicValue beaconSeed seed scalar _ primitive middle reached
  obtain ⟨token, candidate, kernel, logged, cache, found, familyEq, _, serverEq, installed, built, _, _⟩ :=
    PqxdhServerAuthRootInitialization.build_receipt setup codec checks seed scalar index payload
      (before, primitive) response (after, middle) source
  rcases path_token setup codec checks publicValue beaconSeed seed scalar _ _ earlier preceding
      index token found with impossible | ⟨original, atEarlier, receipt⟩
  · simp only [initialGameState, reduceCtorEq] at impossible
  · have retained := (path_roots setup codec checks publicValue beaconSeed seed scalar
        (after, middle) final later following).1
    dsimp only at familyEq retained
    rw [familyEq] at retained
    exact ⟨earlier, later, token, candidate, kernel, logged, cache, original, split, atEarlier,
      tokenAt_mono setup codec checks publicValue seed scalar primitive.cache final.2.cache retained
        original index token receipt, found, installed, serverEq, built⟩

/-- The original game invariant and complete monotone histories hold along the actual interpreted callback path. No root-origin or authentication property is added to the inherited invariant. -/
theorem path_inv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (initial : GameInv Reader Response setup publicValue before.1) :
    GameInv Reader Response setup publicValue after.1 ∧ Grows before.1 after.1 := by
  revert initial
  induction path with
  | nil state primitive => exact fun initial => ⟨initial, Grows.refl _⟩
  | cons call primitive middle suffix final reached rest ih =>
      intro initial
      have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
      have bare := interpreted_source setup seed scalar
        (authHandler setup codec checks publicValue beaconSeed call.query)
        (call.before, primitive) (call.reply, call.after, middle) source
      have step := authHandler_step (setup := setup) (publicValue := publicValue) codec checks beaconSeed
        call.query call.before (call.reply, call.after) bare
      obtain ⟨last, grows⟩ := ih (step.1 initial)
      exact ⟨last, step.2.1.trans grows⟩

/-- Every actual callback path retains prior ghost history, independently of authentication success. -/
theorem path_grows (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after) :
    Grows before.1 after.1 := by
  induction path with
  | nil state primitive => exact Grows.refl _
  | cons call primitive middle suffix final reached rest ih =>
      have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
      have bare := interpreted_source setup seed scalar
        (authHandler setup codec checks publicValue beaconSeed call.query)
        (call.before, primitive) (call.reply, call.after, middle) source
      exact (authHandler_step (setup := setup) (publicValue := publicValue) codec checks beaconSeed
        call.query call.before (call.reply, call.after) bare).2.1.trans ih

/-- A stored token's same accepting occurrence contributes its exact session/root touch to every later state in this actual path. -/
theorem token_final (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (call : Call KemSK) (member : call ∈ calls) (index : Nat)
    (token : PqxdhServerRelatedRootConsumer.Returned)
    (receipt : TokenAt setup codec checks publicValue seed scalar after.2.cache call index token) :
    ∃ input : PqxdhServerRootPreparation.Inputs Reader ScalarBytes PeerEncoding,
      token.pending = PqxdhServerClearedRoot.pending (binding setup publicValue) input ∧
      RootAt setup seed scalar after.2.cache (PqxdhServerRelatedRootInput.message input) token.root ∧
      Touch.session index (PqxdhServerRelatedRootInput.message input) (some token.root) ∈ after.1.ghost.touches := by
  obtain ⟨_, _, _, _, _, _, _, following⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar before after calls path call member
  obtain ⟨_, _, input, _, _, _, _, pending, rooted, touched⟩ := receipt
  exact ⟨input, pending, rooted,
    (path_grows setup codec checks publicValue beaconSeed seed scalar _ after _ following).touches.subset touched⟩

/-- A successful finish occurrence retains the actual root/initializer/publication path at the final cache and identifies the original first Beacon touch. Later callbacks can neither replace that occurrence nor erase its root receipt. -/
theorem path_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (initial final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar initial calls final)
    (invariant : GameInv Reader Response setup publicValue initial.1)
    (raw payload : Pqxdh.Bytes) (before after : GameState KemSK)
    (roots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (member : (⟨.inr (.finish raw), some payload, before, after, roots⟩ : Call KemSK) ∈ calls) :
    ∃ control prekey oneTime kem pending root staged,
      before.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
      some pending ∈ support ((beaconPrefix setup codec beaconSeed control before.beacon.beacon.identity
        oneTime kem raw).run' ()) ∧
      RootAt setup seed scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) root ∧
      firstBeacon final.1.ghost.touches =
        some (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) ∧
      (some staged, ((), after.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), before.ctx)) ∧
      after.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      payload = staged.opened.plaintext.drop 8 ∧
      control.expected_server_binding.identity_key_id = staged.authenticated.candidate.server_binding.identity_key_id := by
  obtain ⟨earlier, later, primitive, middle, _, preceding, reached, following⟩ :=
    path_occurrence setup codec checks publicValue beaconSeed seed scalar initial final calls path _ member
  have source := callback_source setup codec checks publicValue beaconSeed seed scalar _ primitive middle reached
  obtain ⟨control, prekey, oneTime, kem, pending, root, staged, active, prepared, _, rooted,
      initialized, installed, plaintext, pinned, touches⟩ :=
    PqxdhServerAuthRootInitialization.finish_root setup codec publicValue beaconSeed seed scalar raw payload
      (before, primitive) (after, middle) source
  have atBefore := (path_inv setup codec checks publicValue beaconSeed seed scalar initial
    (before, primitive) earlier preceding invariant).1
  have first : firstBeacon after.ghost.touches =
      some (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected) := by
    rw [touches]
    exact firstBeacon_after before.ghost.touches [] _
      (atBefore.clean ⟨control, prekey, oneTime, kem, active⟩)
  exact ⟨control, prekey, oneTime, kem, pending, root, staged, active, prepared,
    root_mono setup seed scalar middle.cache final.2.cache
      (path_roots setup codec checks publicValue beaconSeed seed scalar _ _ later following).1 _ root rooted,
    firstBeacon_prefix _ _ _ first
      (path_grows setup codec checks publicValue beaconSeed seed scalar _ _ later following).touches,
    initialized, installed, plaintext, pinned⟩

/-- On one complete actual path, the original partner relation links the root used by a successful owner build to the root used by the successful Beacon finish. Both roots come from their actual callbacks and are retained in one real cache; no installed-key or output injectivity is used. -/
theorem path_root_agreement (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (initial : PqxdhJointDhExtractFamily.State)
    (final : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      (contextState setup context, initial) calls final)
    (index : Nat) (data : Option Pqxdh.Bytes) (response : PqxdhServerRegistrationPublication.Response)
    (serverBefore serverAfter : GameState KemSK) (serverRoots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (built : (⟨.inr (.build index data), some response, serverBefore, serverAfter, serverRoots⟩ : Call KemSK) ∈ calls)
    (raw payload : Pqxdh.Bytes) (beaconBefore beaconAfter : GameState KemSK)
    (beaconRoots : QueryLog PqxdhJointDhExtractRoot.RootSpec)
    (finished : (⟨.inr (.finish raw), some payload, beaconBefore, beaconAfter, beaconRoots⟩ : Call KemSK) ∈ calls)
    (snap : Snapshot) (accepted : final.1.ghost.acceptance = some snap)
    (partner : Partner setup context.seed context.scalar snap index) :
    ∃ token candidate serverKernel logged cache pending root staged,
      serverBefore.pending index = some token ∧
      token.root = root ∧ Installed setup.source root serverKernel ∧
      serverAfter.server = PqxdhServerRegistrationPublication.publish serverBefore.server candidate serverKernel () ∧
      (ok (some response, PqxdhServerRegistrationPublication.publish serverBefore.server candidate serverKernel ()),
        (logged, cache)) ∈ support ((simulateQ (tailImpl setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root data () serverBefore.server)).run
            ([], serverBefore.ctx)) ∧
      RootAt setup context.seed context.scalar final.2.cache
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) root ∧
      (some staged, ((), beaconAfter.ctx)) ∈ support ((simulateQ (beaconNative setup codec)
        (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run
          ((), beaconBefore.ctx)) ∧
      beaconAfter.beacon.beacon.phase = .established
        ⟨staged.authenticated.candidate.server_binding, staged.authenticated.candidate.assigned_key_id⟩
        staged.associatedData staged.kernel ∧
      ∃ control prekey oneTime kem,
        beaconBefore.beacon.beacon.phase = .initSent control prekey oneTime kem ∧
        some pending ∈ support ((beaconPrefix setup codec context.beaconSeed control
          beaconBefore.beacon.beacon.identity oneTime kem raw).run' ()) ∧
        firstBeacon final.1.ghost.touches = some
          (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) := by
  have generated := PqxdhServerAuthPhase1Generation.context_generated setup codec context sampled
  have first := inv_initial setup codec context.beaconSeed (context.publicValue setup) context.oneTime
    context.keys.1 context.keys.2 context.published generated.2.2.2.2.2
  have last := (path_inv setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
    _ final calls path first).1
  obtain ⟨earlier, later, token, candidate, serverKernel, logged, cache, original, split, inEarlier,
      receipt, found, installed, serverEq, buildRun⟩ :=
    path_build setup codec checks (context.publicValue setup) context.beaconSeed context.seed context.scalar
      context.published.2 initial final calls path index data response serverBefore serverAfter serverRoots built
  have originalMember : original ∈ calls := by
    rw [split]
    exact List.mem_append_left _ inEarlier
  obtain ⟨input, _, serverRooted, touched⟩ := token_final setup codec checks (context.publicValue setup)
    context.beaconSeed context.seed context.scalar _ final calls path original originalMember index token receipt
  obtain ⟨control, prekey, oneTime, kem, pending, root, staged, active, prepared, beaconRooted, firstBeaconEq, nativeRun,
      phaseEq, _, _⟩ := path_finish setup codec checks (context.publicValue setup) context.beaconSeed
    context.seed context.scalar _ final calls path first raw payload beaconBefore beaconAfter beaconRoots finished
  obtain ⟨message, reply, bytes, partnerTouch, inputEq, beaconEq⟩ := partner
  have snapshot := (last.frozen snap accepted).1
  have messageEq := (last.sessionOnce index _ _ message reply touched (snapshot.subset partnerTouch)).1
  have sameInput : rootInput setup context.seed context.scalar (PqxdhServerRelatedRootInput.message input) =
      rootInput setup context.seed context.scalar
        (PqxdhJointDhExtractRoot.beaconMessage (context.publicValue setup) pending.collected) := by
    rw [messageEq, inputEq]
    have retained := beaconInput_prefix setup context.seed context.scalar _ _ bytes beaconEq snapshot
    simpa only [beaconInput, firstBeaconEq, Option.bind_some] using retained.symm
  have sameRoot := same_input setup context.seed context.scalar final.2.cache _ _ token.root root
    serverRooted beaconRooted sameInput
  exact ⟨token, candidate, serverKernel, logged, cache, pending, root, staged, found, sameRoot,
    sameRoot ▸ installed, serverEq, buildRun, beaconRooted, nativeRun, phaseEq,
    control, prekey, oneTime, kem, active, prepared, firstBeaconEq⟩

/-- A still-active target Beacon is the complete original Phase1 output: no intervening API operation replaces its control, private one-time/KEM handles or identity fields. Every finish leaves the active phase, including failures. -/
theorem path_active (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed seed : IdentitySeed) (scalar : ScalarBytes)
    (before after : GameState KemSK × PqxdhJointDhExtractFamily.State) (calls : List (Call KemSK))
    (path : Path setup codec checks publicValue beaconSeed seed scalar before calls after)
    (active : InitSent after.1) : after.1.beacon = before.1.beacon := by
  revert active
  induction path with
  | nil state primitive => exact fun _ => rfl
  | cons call primitive middle suffix final reached rest ih =>
      intro active
      have retained := ih active
      have stillActive : InitSent call.after := by
        obtain ⟨control, prekey, oneTime, kem, phase⟩ := active
        exact ⟨control, prekey, oneTime, kem, by rw [← retained]; exact phase⟩
      have source := callback_source setup codec checks publicValue beaconSeed seed scalar call primitive middle reached
      have bare := interpreted_source setup seed scalar
        (authHandler setup codec checks publicValue beaconSeed call.query)
        (call.before, primitive) (call.reply, call.after, middle) source
      by_cases finish : ∃ raw, call.query = .inr (.finish raw)
      · obtain ⟨raw, queryEq⟩ := finish
        cases call with
        | mk query reply previous current roots =>
          dsimp only at queryEq
          subst query
          exact ((finish_step (setup := setup) (publicValue := publicValue) codec beaconSeed raw previous
            (reply, current) bare).2.2.2.1 stillActive).elim
      · exact retained.trans ((authHandler_step (setup := setup) (publicValue := publicValue) codec checks beaconSeed
          call.query call.before (call.reply, call.after) bare).2.2.2.2 (by
            intro raw same
            exact finish ⟨raw, same⟩))

end BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance

/-! ## Checked theorem dependencies -/

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.rejected_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.rejected_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.step_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.step_token

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.tokenAt_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.tokenAt_mono

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_token

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_build

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_inv

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_grows

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.token_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.token_final

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_finish

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_root_agreement' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_root_agreement

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthRootProvenance.path_active
