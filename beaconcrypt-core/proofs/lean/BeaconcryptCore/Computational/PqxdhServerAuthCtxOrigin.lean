import BeaconcryptCore.Computational.PqxdhServerAuthBuildReceipt
import BeaconcryptCore.Computational.PqxdhServerAuthCtxFinish

/-! Session-indexed source origins for ordinary selected component receipts. The invariant records actual source touches and optional frame-writer outcomes; it does not infer a session from key bytes or from a ciphertext match. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhJointKdfGame CtxRomAuth
open PqxdhServerAuthBuildReceipt (FrameOrigin)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader WireResponse : Type}

/-- Each receipt has its actual session touch at the selected input and either a failed concrete frame writer or that session's successful source log entry. -/
def Origins (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (writer : RawCtxMixedShared.Writer) (ghost : Ghost) (hidden : Option Pqxdh.Bytes)
    (observer : RawCtxSelectedAuthenticationObserver.State) : Prop :=
  ∀ entry ∈ observer.seals, ∃ index message reply bytes sealContext sequence,
    Touch.session index message reply ∈ ghost.touches ∧
      hidden = some bytes ∧ rootInput setup context.seed context.scalar message = some bytes ∧
      PqxdhPhase2LocalMatching.KeyIdBound sealContext ∧
      PqxdhPhase2LocalMatching.Records entry sealContext ∧
      entry.input.context.ad.seq = sequence.val ∧
      entry.input.context.ad.sid = sealContext.senderId.val ∧
      (writer ⟨sequence, sealContext.senderId, entry.record.encode⟩ = none ∨
        (index, sealContext) ∈ ghost.seals)

/-- Exact source-history growth retains every existing receipt without reconstructing or guessing its session. -/
theorem Origins.grows (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (writer : RawCtxMixedShared.Writer) (before after : Ghost) (hidden : Option Pqxdh.Bytes)
    (observer : RawCtxSelectedAuthenticationObserver.State)
    (valid : Origins setup context writer before hidden observer)
    (touches : before.touches.IsPrefix after.touches) (seals : before.seals.IsPrefix after.seals) :
    Origins setup context writer after hidden observer := by
  intro entry found
  obtain ⟨index, message, reply, bytes, sealContext, sequence, touched, selected, input, bound,
    records, seq, sender, publication⟩ := valid entry found
  exact ⟨index, message, reply, bytes, sealContext, sequence, touches.subset touched, selected, input,
    bound, records, seq, sender, publication.imp_right (fun member => seals.subset member)⟩

/-- The actual compiled selected builder attaches every new component receipt to its reached session touch and exact source log update. Native writer/diagnostic failures retain the same attribution. -/
theorem build_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (game : GameState KemSK) (index : Nat) (hidden : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State)
    (valid : Origins setup context codec.frameWrite game.ghost hidden before)
    (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput) (bytes : Pqxdh.Bytes)
    (touched : Touch.session index message reply ∈ game.ghost.touches)
    (selected : hidden = some bytes)
    (input : rootInput setup context.seed context.scalar message = some bytes)
    (outcome : RustM (Option PqxdhServerRegistrationPublication.Response × ServerState))
    (log : PqxdhServerAuthBuildProgram.Log) (cache : CtxRO.QueryCache)
    (supported : ((some outcome, log), after) ∈ support
      (RawCtxSelectedAuthenticationObserver.monitor
        ((PqxdhServerAuthBuildProgram.compiled setup.source codec checks rest pending data () game.server).run.run []) before)) :
    Origins setup context codec.frameWrite (afterBuild index game (outcome, (log, cache))).2.ghost hidden after := by
  have receipts := (PqxdhServerAuthBuildReceipt.compiled_receipts setup.source codec checks rest pending data
    () game.server [] log before after (some outcome) supported).2
  intro entry found
  rcases receipts entry found with old | ⟨sealContext, sequence, bound, records, seq, sender, publication⟩
  · exact Origins.grows setup context codec.frameWrite game.ghost
      (afterBuild index game (outcome, (log, cache))).2.ghost hidden before valid
      (List.prefix_refl _) ⟨log.map (fun recordContext => (index, recordContext)), rfl⟩ entry old
  · refine ⟨index, message, reply, bytes, sealContext, sequence, touched, selected, input,
      bound, records, seq, sender, ?_⟩
    rcases publication with failed | logged
    · exact Or.inl failed
    · exact Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨sealContext, logged, rfl⟩)))

/-- A matched accepted selected opening has an actual earlier source seal with its source session and exact accepted fields. A failed concrete frame writer is excluded only by the actual decoded match. -/
theorem finish_origin (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse)
    (staged : PqxdhBeaconPhase2Publication.Staged) (ghost : Ghost) (hidden : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : Origins setup context codec.frameWrite ghost hidden before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before)) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true ∨
      ∃ index message reply bytes sealContext,
        Touch.session index message reply ∈ ghost.touches ∧ hidden = some bytes ∧
        rootInput setup context.seed context.scalar message = some bytes ∧
        (index, sealContext) ∈ ghost.seals ∧
        PqxdhPhase2LocalMatching.acceptedFields staged = PqxdhPhase2LocalMatching.sealedFields sealContext := by
  rcases PqxdhServerAuthFinishReceipt.program_or_match setup.source codec key rest pending staged before after
    good supported with won | matched
  · exact Or.inl won
  · obtain ⟨raw, target, kernel, entry, _, delivery, success, member, same, plaintext⟩ := matched
    obtain ⟨index, message, reply, bytes, sealContext, sequence, touched, selected, input, bound,
      records, seq, sender, publication⟩ := origins entry member
    obtain ⟨encoded, written⟩ := PqxdhServerAuthFinishReceipt.matched_writable codec.frameWrite codec.frameRead
      writable raw _ staged.opened target delivery entry same sequence sealContext.senderId seq sender
    refine Or.inr ⟨index, message, reply, bytes, sealContext, touched, selected, input,
      publication.resolve_left (by rw [written]; exact Option.some_ne_none encoded), ?_⟩
    exact PqxdhServerAuthFinishReceipt.matched_fields _ kernel staged success codec.frameRead raw target
      delivery entry same plaintext sealContext records bound

/-- The original first-acceptance event is impossible when its frozen source logs contain a partner's matching seal. This is an event calculation, not an authentication hypothesis. -/
theorem matching_excludes (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (ghost : Ghost) (staged : PqxdhBeaconPhase2Publication.Staged)
    (fresh : ghost.acceptance = none)
    (index : Nat) (message : PqxdhJointDhExtractFamily.Message) (reply : Option RootOutput)
    (bytes : Pqxdh.Bytes) (sealContext : RawCtxSourceSend.SealContext)
    (touched : Touch.session index message reply ∈ ghost.touches)
    (input : rootInput setup context.seed context.scalar message = some bytes)
    (beacon : beaconInput setup context.seed context.scalar ghost.touches = some bytes)
    (logged : (index, sealContext) ∈ ghost.seals)
    (fields : PqxdhPhase2LocalMatching.acceptedFields staged = PqxdhPhase2LocalMatching.sealedFields sealContext) :
    ¬ (W1 setup context.seed context.scalar (ghost.accept (some (Accepted.ofStaged staged))) ∨
       W2 setup context.seed context.scalar (ghost.accept (some (Accepted.ofStaged staged)))) := by
  have equal : sealed sealContext = Accepted.ofStaged staged := by
    have same := congrArg (fun value : Std.U64 × Pqxdh.Bytes × Pqxdh.Bytes =>
      (⟨value.1, value.2.1, value.2.2⟩ : Accepted)) fields
    exact same.symm
  intro failed
  rcases failed with ⟨snap, captured, absent⟩ | ⟨snap, captured, _, absent⟩
  · have snapEq : snap = ⟨Accepted.ofStaged staged, ghost.touches, ghost.seals⟩ := by
      simpa only [Ghost.accept, fresh, Option.some.injEq] using captured.symm
    subst snap
    exact absent index ⟨message, reply, bytes, touched, input, beacon⟩
  · have snapEq : snap = ⟨Accepted.ofStaged staged, ghost.touches, ghost.seals⟩ := by
      simpa only [Ghost.accept, fresh, Option.some.injEq] using captured.symm
    subst snap
    exact absent index ⟨message, reply, bytes, touched, input, beacon⟩ sealContext logged equal

/-- The actual selected finish's W1/W2 event implies the existing all-attempt observer wins, once the source state is the first-acceptance state at its selected input. The remaining whole-handler invariant supplies those operational facts. -/
theorem finish_event (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse)
    (control : pqxdh.BeaconInitSent) (staged : PqxdhBeaconPhase2Publication.Staged)
    (game : GameState KemSK) (hidden : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : Origins setup context codec.frameWrite game.ghost hidden before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (fresh : game.ghost.acceptance = none)
    (selected : beaconInput setup context.seed context.scalar game.ghost.touches = hidden)
    (supported : (some staged, after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before))
    (failed : W1 setup context.seed context.scalar (finishOutcome control game (some staged)).2.ghost ∨
      W2 setup context.seed context.scalar (finishOutcome control game (some staged)).2.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true := by
  rcases finish_origin setup codec context key rest pending staged game.ghost hidden before after origins
    writable good supported with won | ⟨index, message, reply, bytes, sealContext, touched, inputHidden, input, logged, fields⟩
  · exact won
  · have excluded := matching_excludes setup context game.ghost staged fresh index message reply bytes
      sealContext touched input (selected.trans inputHidden) logged fields
    cases returned : (PqxdhBeaconPhase2Publication.finish control game.beacon (some staged)).1 with
    | none =>
      simp only [finishOutcome, returned, acceptedOf, Option.isSome_none, Bool.false_eq_true,
        ite_false, Ghost.accept] at failed
      rcases failed with ⟨snap, captured, _⟩ | ⟨snap, captured, _⟩ <;> simp [fresh] at captured
    | some payload =>
      apply False.elim
      apply excluded
      simpa only [finishOutcome, returned, acceptedOf, Option.isSome_some, ite_true, Option.map_some] using failed

/-- The actual selected post-root handler, including its final publication gate and complete local state, inherits the same ordinary observer implication. No staged-success premise is supplied by the caller. -/
theorem selected_event (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse) (control : pqxdh.BeaconInitSent)
    (localBefore localAfter : PqxdhServerAuthCtxState.Local KemSK) (result : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : Origins setup context codec.frameWrite localBefore.1.1.ghost localBefore.1.2.2.hidden before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (fresh : localBefore.1.1.ghost.acceptance = none)
    (selected : beaconInput setup context.seed context.scalar localBefore.1.1.ghost.touches =
      localBefore.1.2.2.hidden)
    (supported : ((result, localAfter), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.selected setup.source codec rest control pending).run localBefore)).run before))
    (failed : W1 setup context.seed context.scalar localAfter.1.1.ghost ∨
      W2 setup context.seed context.scalar localAfter.1.1.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true := by
  change ((result, localAfter), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key)
    (PqxdhServerAuthCtxFinish.complete control localBefore <$>
      PqxdhServerAuthFinishMaterial.program setup.source codec rest pending)).run before) at supported
  rw [simulateQ_map, StateT.run_map, support_map] at supported
  obtain ⟨⟨staged, component⟩, reached, equal⟩ := supported
  have localEqual := congrArg (fun value => value.1.2) equal
  have observerEqual := congrArg Prod.snd equal
  dsimp only at localEqual observerEqual
  subst after
  rw [← localEqual] at failed
  cases staged with
  | none =>
    simp only [PqxdhServerAuthCtxFinish.complete, finishOutcome, acceptedOf, Option.map_none,
      ite_self, Ghost.accept] at failed
    rcases failed with ⟨snap, captured, _⟩ | ⟨snap, captured, _⟩ <;> simp [fresh] at captured
  | some staged =>
    exact finish_event setup codec context key rest pending control staged localBefore.1.1
      localBefore.1.2.2.hidden before component origins writable good fresh selected reached failed

/-- Both literal table routes identify the actual input whenever they return the hidden label. This uses the reached reply and retains rejected/cache-hit routes without conditioning their earlier sampling. -/
theorem table_input (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool)
    (message : PqxdhJointDhExtractFamily.Message) (before after : HiddenTable)
    (supported : (Reply.hidden, after) ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run before)) :
    ∃ bytes, after.hidden = some bytes ∧ rootInput setup context.seed context.scalar message = some bytes := by
  cases select with
  | false =>
    exact hiddenDerive_hidden setup context.seed context.scalar message before (.hidden, after) supported rfl
  | true =>
    simp only [PqxdhServerAuthCtxState.tableServices, ite_true, selectHidden, StateT.run] at supported
    cases input : PqxdhJointDhExtractFamily.input setup.joint setup.dh context.seed context.scalar message with
    | none => simp only [input, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
    | some bytes =>
      simp only [input] at supported
      cases cached : before.cache bytes with
      | some value =>
        simp only [cached, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
      | none =>
        simp only [cached, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, true_and] at supported
        subst after
        exact ⟨bytes, rfl, input⟩

/-- The source's reached hidden derivation followed by its actual first Beacon touch establishes the selected-input equality needed by the registration event consumer. -/
theorem touched_input (setup : Setup baseSpec KemSK) (context : Context KemSK) (select : Bool)
    (state : PqxdhServerAuthCtxState.Local KemSK) (message : PqxdhJointDhExtractFamily.Message)
    (after : HiddenTable) (clean : ∀ other, Touch.beacon other ∉ state.1.1.ghost.touches)
    (supported : (Reply.hidden, after) ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run state.1.2.2)) :
    beaconInput setup context.seed context.scalar (PqxdhServerAuthCtxFinish.touched state message after).1.1.ghost.touches =
      (PqxdhServerAuthCtxFinish.touched state message after).1.2.2.hidden := by
  obtain ⟨bytes, hidden, input⟩ := table_input setup context select message state.1.2.2 after supported
  change beaconInput setup context.seed context.scalar (state.1.1.ghost.touches ++ [.beacon message]) = after.hidden
  rw [beaconInput, firstBeacon_after _ [] message clean, Option.bind_some]
  exact input.trans hidden.symm

/-- The concrete hidden derive and first-touch source prefix discharge the selected-input condition for the complete accepted callback. Receipt and first-acceptance invariants remain explicit operational obligations of the enclosing adaptive handler. -/
theorem touched_event (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse)
    (context : Context KemSK) (key : RootOutput) (rest : PqxdhServerAuthCtxCalls.Residual)
    (pending : PqxdhPhase2DhMetadata.Prepared WireResponse) (control : pqxdh.BeaconInitSent)
    (select : Bool) (state localAfter : PqxdhServerAuthCtxState.Local KemSK)
    (message : PqxdhJointDhExtractFamily.Message) (table : HiddenTable) (result : Option Pqxdh.Bytes)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (origins : Origins setup context codec.frameWrite
      (PqxdhServerAuthCtxFinish.touched state message table).1.1.ghost table.hidden before.1)
    (writable : PqxdhFirstBeaconRecordCanonical.ReadWritable codec.frameWrite codec.frameRead)
    (good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key before)
    (fresh : state.1.1.ghost.acceptance = none)
    (clean : ∀ other, Touch.beacon other ∉ state.1.1.ghost.touches)
    (derived : (Reply.hidden, table) ∈ support
      (((PqxdhServerAuthCtxState.tableServices (WireResponse := Unit) setup context select).derive message).run state.1.2.2))
    (supported : ((result, localAfter), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxFinish.selected setup.source codec rest control pending).run
        (PqxdhServerAuthCtxFinish.touched state message table))).run before))
    (failed : W1 setup context.seed context.scalar localAfter.1.1.ghost ∨
      W2 setup context.seed context.scalar localAfter.1.1.ghost) :
    RawCtxSelectedAuthenticationObserver.won (RawCtxUniversalDecoder.decoder codec.frameRead) after.1 = true :=
  selected_event setup codec context key rest pending control
    (PqxdhServerAuthCtxFinish.touched state message table) localAfter result before after origins writable
    good fresh (touched_input setup context select state message table clean derived) supported failed

end BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.Origins.grows' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.Origins.grows
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.build_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.build_origins
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.finish_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.finish_origin
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.matching_excludes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.matching_excludes
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.finish_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.finish_event
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.selected_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.selected_event
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.table_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.table_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.touched_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.touched_input
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.touched_event' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxOrigin.touched_event
