import BeaconcryptCore.Computational.PqxdhServerAuthCtxAcceptanceHistory
import BeaconcryptCore.Computational.PqxdhServerAuthCtxHandler
import BeaconcryptCore.Computational.PqxdhServerAuthCtxHandlerBounds
import BeaconcryptCore.Computational.PqxdhServerAuthCtxReserve

/-! Joint source-origin and ordinary component-observer history for the actual API compiler. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor
open PqxdhSecretInputKdf PqxdhJointKdfGame PqxdhJointIdentity PqxdhJointGapDh
open PqxdhServerAuthCtxStop

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Existing source receipts remain attributed after a nonsealing component continuation and actual source-log growth, provided the already selected input is retained. -/
theorem origins_quiet {α : Type} (setup : Setup baseSpec KemSK) (context : Context KemSK)
    (codec : Codec Reader Response) (key : RootOutput)
    (client : OracleComp AdaptiveCtxDynamicKnownKeys.Spec α)
    (quiet : client.IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (before after : Ghost) (hidden next : Option Pqxdh.Bytes)
    (state : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : α × (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite before hidden state.1)
    (touches : before.touches <+: after.touches) (seals : before.seals <+: after.seals)
    (retained : ∀ bytes, hidden = some bytes → next = some bytes)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key) client).run state)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite after next result.2.1 := by
  have same := PqxdhFirstBeaconRecordCanonical.observed_seals _ _ _ client quiet state result supported
  intro entry member
  rw [same] at member
  obtain ⟨index, message, reply, bytes, recordContext, sequence, touched, selected, input, bound,
    records, seq, sender, publication⟩ := origins entry member
  exact ⟨index, message, reply, bytes, recordContext, sequence, touches.subset touched,
    retained bytes selected, input, bound, records, seq, sender,
    publication.imp_right (fun found => seals.subset found)⟩

/-- An ordinary raw finish retains the selected input through the actual prefix and every optional tail outcome. -/
theorem finish_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (raw : Pqxdh.Bytes)
    (state : FlatState KemSK HiddenTable) (result : Option Pqxdh.Bytes × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((finishStep setup codec (context.publicValue setup) context.beaconSeed
      (factorServices setup codec checks context value) raw).run state)) :
    result.2.2.2.hidden = state.2.2.hidden := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    simp only [phase, mem_support_bind_iff] at supported
    obtain ⟨prepared, _, supported⟩ := supported
    cases found : prepared with
    | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      rfl
    | some pending =>
      simp only [found, mem_support_bind_iff] at supported
      obtain ⟨derived, reached, supported⟩ := supported
      have kept := derive_retains setup context _ state.2.2 derived reached
      cases reply : derived.1 with
      | rejected =>
        simp only [reply, support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact kept
      | root root =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact kept
      | hidden =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact kept
  | _ =>
    simp only [phase, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    rfl

/-- After selection, every ordinary source capability retains the exact selected-input label. -/
theorem skeleton_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK HiddenTable)
    (result : ServerAuthSpec.Range query × FlatState KemSK HiddenTable)
    (supported : result ∈ support ((skeleton setup codec checks (context.publicValue setup) context.beaconSeed (factorServices setup codec checks context value) query).run state)) :
    result.2.2.2.hidden = state.2.2.hidden := by
  cases query with
  | inl coin =>
      simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      rfl
  | inr query =>
      cases query with
      | accept raw =>
          simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨collected, _, supported⟩ := supported
          cases found : collected.1 with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
          | some input =>
              simp only [found] at supported
              split_ifs at supported with nonzero
              · obtain ⟨derived, reached, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
                simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                exact derive_retains setup context _ state.2.2 derived reached
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst supported
                rfl
      | build session payload =>
          simp only [skeleton, buildStep, StateT.run] at supported
          cases found : state.1.pending session with
          | none =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
          | some token =>
              simp only [found, mem_support_bind_iff] at supported
              obtain ⟨built, _, supported⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              rfl
      | finish raw =>
          exact finish_hidden setup codec checks context value raw state result supported
      | hmac key bytes =>
          simp only [skeleton, hmacStep, StateT.run] at supported
          split_ifs at supported with inside
          · obtain ⟨read, reached, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            exact public_retains bytes state.2.2 read reached
          · simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            rfl
      | hash bytes =>
          simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
          obtain ⟨read, reached, supported⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl
      | reveal key =>
          simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          rfl

/-- Once the actual designation flag is set, the complete handler retains the selected input on every original API operation. -/
theorem handler_hidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) (Q : Nat) (j : Fin (Q + 1))
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK)
    (unselected : state.2 = false → state.1.2.2.hidden = none)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j
      (factorServices setup codec checks context value) query).run state)) :
    ∀ bytes, state.1.2.2.hidden = some bytes → result.2.1.2.2.hidden = some bytes := by
  intro bytes found
  have selected : state.2 = true := by
    cases flag : state.2
    · have impossible := (unselected flag).symm.trans found
      cases impossible
    · rfl
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  simp only [once, StateT.run, selected, ite_true,
    latch, support_map, Set.mem_image] at supported
  obtain ⟨step, reached, rfl⟩ := supported
  have kept := (skeleton_hidden setup codec checks context value query state.1 step reached).trans found
  simp only [keepHiddenBad]
  split <;> exact kept

/-- Erasing only the observer from a concrete interpreted callback retains the complete local and component result. -/
theorem evaluated_support {α : Type} (source : FixedHkdfSha512NoSaltSource) (key : RootOutput)
    (read : RawCtxReceive.FrameDecoder) (work : PqxdhServerAuthCtxState.Program KemSK α)
    (localState : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (result : (α × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder read)
        source.crypto key) (work.run localState)).run before)) :
    (result.1.1, (result.1.2, result.2.2)) ∈ support
      ((PqxdhServerAuthCtxState.evaluate source key read work).run (localState, before.2)) := by
  have erased := PqxdhFirstBeaconRecordCanonical.observed_component _ _ _ _ before result supported
  change (result.1.1, (result.1.2, result.2.2)) ∈ support
    (PqxdhSelectedStateInterpreter.pair <$> _)
  rw [support_map]
  exact ⟨(result.1, result.2.2), erased, rfl⟩

/-- The original source handler receives the exact reply and complete projected state of the observed compiled execution. Only the already explicit reached-builder Ready obligation is used. -/
theorem handler_source_support (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (localState, before.2))
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run localState)).run before)) :
    ∃ reply, result.1.1 = some reply ∧
      (reply, PqxdhServerAuthCtxState.project (result.1.2, result.2.2)) ∈ support
        ((hiddenHandler setup codec checks context Q j
          (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query).run
          (PqxdhServerAuthCtxState.project (localState, before.2))) := by
  have erased := evaluated_support setup.source key codec.frameRead _ localState before result supported
  have projected : (result.1.1, PqxdhServerAuthCtxState.project (result.1.2, result.2.2)) ∈ support
      (Prod.map id PqxdhServerAuthCtxState.project <$>
        (PqxdhServerAuthCtxState.evaluate setup.source key codec.frameRead
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run).run
          (localState, before.2)) := by
    rw [support_map]
    exact ⟨_, erased, rfl⟩
  rw [PqxdhServerAuthCtxHandler.handler_source setup codec checks context rest Q j query key
    (localState, before.2) ready, support_map] at projected
  obtain ⟨sourceResult, reached, equal⟩ := projected
  refine ⟨sourceResult.1, (congrArg Prod.fst equal).symm, ?_⟩
  have after : sourceResult.2 = PqxdhServerAuthCtxState.project (result.1.2, result.2.2) := congrArg Prod.snd equal
  rw [← after]
  exact reached

/-- A complete nonsealing original API callback retains every earlier component receipt's actual session and source publication alternative. -/
theorem handler_quiet_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState : PqxdhServerAuthCtxState.Local KemSK)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (localState, before.2))
    (unselected : localState.2 = false → localState.1.2.2.hidden = none)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      localState.1.1.ghost localState.1.2.2.hidden before.1)
    (quiet : ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run localState).IsQueryBoundP (AdaptiveCtxDynamicKnownBounds.TargetClass AdaptiveCtxQueryBounds.SourceSeal) 0)
    (result : (Option (ServerAuthSpec.Range query) × PqxdhServerAuthCtxState.Local KemSK) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run localState)).run before)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      result.1.2.1.1.ghost result.1.2.1.2.2.hidden result.2.1 := by
  obtain ⟨reply, _, reached⟩ := handler_source_support setup codec checks context rest key Q j query
    localState before ready result supported
  have grown := PqxdhServerAuthCtxAcceptanceHistory.handler_grows setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
    (PqxdhServerAuthCtxState.project (localState, before.2)) _ reached
  have retained := handler_hidden setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)
    Q j query (PqxdhServerAuthCtxState.project (localState, before.2)) unselected _ reached
  exact origins_quiet setup context codec key _ quiet _ _ _ _ before result origins
    grown.touches grown.seals retained supported

/-- The actual selected build callback attributes every new component seal to its reached source session and exact optional-writer log before returning its normal native reply. -/
theorem selected_build_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (localState afterLocal : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (trace : TraceInvariant setup context Q j localState) (marked : localState.1.2.1 session = true)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      localState.1.1.ghost localState.1.2.2.hidden before.1)
    (answer : Option PqxdhServerRegistrationPublication.Response)
    (supported : ((some answer, afterLocal), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxBuild.selected setup.source codec checks rest session token payload
        localState.1.1.server).run.run localState)).run before)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      afterLocal.1.1.ghost afterLocal.1.2.2.hidden after.1 := by
  change ((some answer, afterLocal), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxBuild.post session localState <$>
        (PqxdhServerAuthBuildProgram.compiled setup.source codec checks rest token.pending payload ()
          localState.1.1.server).run.run [])).run before) at supported
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨built, reached, equal⟩ := supported
  rcases built with ⟨⟨_ | outcome, log⟩, actual⟩
  · simp only [PqxdhServerAuthCtxBuild.post, Prod.mk.injEq, reduceCtorEq, false_and] at equal
  · simp only [PqxdhServerAuthCtxBuild.post, Prod.mk.injEq, Option.some.injEq] at equal
    rw [← equal.1.2, ← equal.2]
    obtain ⟨message, reply, bytes, touched, selected, input⟩ := trace.marked session marked
    exact PqxdhServerAuthCtxOrigin.build_origins setup codec checks context rest token.pending payload
      localState.1.1 session localState.1.2.2.hidden before.1 actual.1 origins message reply bytes touched
      selected input outcome log localState.1.1.ctx
      (PqxdhFirstBeaconRecordCanonical.observed_monitor _ _ _ _ before _ reached)

/-- The actual marked pending-token branch feeds the complete selected builder into unchanged source designation/refusal settlement. -/
theorem handler_build_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (session : Nat) (token : PqxdhServerRelatedRootConsumer.Returned)
    (payload : Option Pqxdh.Bytes) (localState afterLocal : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (trace : TraceInvariant setup context Q j localState) (marked : localState.1.2.1 session = true)
    (pending : localState.1.1.pending session = some token)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      localState.1.1.ghost localState.1.2.2.hidden before.1)
    (answer : Option PqxdhServerRegistrationPublication.Response)
    (supported : ((some answer, afterLocal), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j (.inr (.build session payload))).run.run
        localState)).run before)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      afterLocal.1.1.ghost afterLocal.1.2.2.hidden after.1 := by
  change ((some answer, afterLocal), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxHandler.settle Q j (.inr (.build session payload)) localState <$>
        ((PqxdhServerAuthCtxHandler.route setup codec checks context rest
          (!localState.2 && hiddenDesignated Q j (.inr (.build session payload)) localState.1)
          (.inr (.build session payload))).run.run localState))).run before) at supported
  simp only [PqxdhServerAuthCtxHandler.route, PqxdhServerAuthCtxBuild.build, OptionT.run_mk,
    StateT.run, pending, marked, ite_true] at supported
  change ((some answer, afterLocal), after) ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key) (PqxdhServerAuthCtxHandler.settle Q j (.inr (.build session payload)) localState <$>
        ((PqxdhServerAuthCtxBuild.selected setup.source codec checks rest session token payload
          localState.1.1.server).run.run localState))).run before) at supported
  simp only [simulateQ_map, StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨built, reached, equal⟩ := supported
  have normal : built.1.1 = some answer :=
    (PqxdhServerAuthCtxHandlerBounds.settle_fields Q j (.inr (.build session payload)) localState built.1).1.symm.trans
      (congrArg (fun value => value.1.1) equal)
  have valid := selected_build_origins setup codec checks context rest key Q j session token payload
    localState built.1.2 before built.2 trace marked origins answer (by rw [← normal]; exact reached)
  have localEq : (PqxdhServerAuthCtxHandler.settle Q j (.inr (.build session payload)) localState built.1).2 = afterLocal :=
    congrArg (fun value => value.1.2) equal
  have observerEq : built.2 = after := congrArg Prod.snd equal
  rw [← localEq, ← observerEq]
  unfold PqxdhServerAuthCtxHandler.settle keepHiddenBad
  split <;> exact valid

/-- Every normal complete API reply preserves exact source origins for the observer's full successful-seal history. Concrete attempted-query bills discharge every nonsealing case. -/
theorem handler_origins (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState afterLocal : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (localState, before.2))
    (trace : TraceInvariant setup context Q j localState)
    (origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      localState.1.1.ghost localState.1.2.2.hidden before.1)
    (answer : ServerAuthSpec.Range query)
    (supported : ((some answer, afterLocal), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run localState)).run before)) :
    PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
      afterLocal.1.1.ghost afterLocal.1.2.2.hidden after.1 := by
  by_cases quiet : buildBill query localState.1 = 0
  · apply handler_quiet_origins setup codec checks context rest key Q j query localState before ready
      trace.unselected origins _ _ supported
    simpa only [quiet] using (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query localState).1
  · cases query with
    | inl coin => simp only [buildBill, not_true_eq_false] at quiet
    | inr query =>
      cases query with
      | build session payload =>
        by_cases marked : localState.1.2.1 session = true
        · cases pending : localState.1.1.pending session with
          | none => simp only [buildBill, marked, ite_true, pending, PqxdhServerAuthPendingBudget.slotWeight, not_true_eq_false] at quiet
          | some token =>
            exact handler_build_origins setup codec checks context rest key Q j session token payload
              localState afterLocal before after trace marked pending origins answer supported
        · simp only [buildBill, marked, Bool.false_eq_true, ite_false, not_true_eq_false] at quiet
      | _ => simp only [buildBill, not_true_eq_false] at quiet

/-- The joint invariant records actual source chronology, table omission, seal origins and the ordinary observer's matched-plaintext correctness. It assumes no winning event or key independence. -/
structure Joint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (localState : PqxdhServerAuthCtxState.Local KemSK)
    (state : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState) : Prop where
  trace : TraceInvariant setup context Q j localState
  history : PqxdhServerAuthCtxAcceptanceHistory.History localState.1.1
  clean : localState.1.2.2.Clean
  origins : PqxdhServerAuthCtxOrigin.Origins setup context codec.frameWrite
    localState.1.1.ghost localState.1.2.2.hidden state.1
  good : RawCtxSelectedPlaintextOrigins.Good (RawCtxUniversalDecoder.decoder codec.frameRead)
    setup.source.crypto key state

/-- Every continuing actual handler transition preserves the complete source and observer invariant. The actual source equality supplies trace, first acceptance and omission; the original component interpreter supplies plaintext correctness. -/
theorem handler_joint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState afterLocal : PqxdhServerAuthCtxState.Local KemSK)
    (before after : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (localState, before.2))
    (invariant : Joint setup codec context key Q j localState before)
    (answer : ServerAuthSpec.Range query)
    (supported : ((some answer, afterLocal), after) ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run localState)).run before)) :
    Joint setup codec context key Q j afterLocal after := by
  obtain ⟨reply, _, sourceReached⟩ := handler_source_support setup codec checks context rest key Q j query
    localState before ready _ supported
  have beforeTrace : TraceInvariant setup context Q j (PqxdhServerAuthCtxState.project (localState, before.2)) :=
    ⟨⟨invariant.trace.shape.touched, invariant.trace.shape.once, invariant.trace.shape.clean⟩,
      invariant.trace.unselected, invariant.trace.selected, invariant.trace.marked⟩
  refine ⟨?_, ?_, ?_, handler_origins setup codec checks context rest key Q j query localState afterLocal
    before after ready invariant.trace invariant.origins answer supported, ?_⟩
  · have afterTrace := hidden_trace setup codec checks context Q j
      (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
      (PqxdhServerAuthCtxState.project (localState, before.2)) beforeTrace _ sourceReached
    exact ⟨⟨afterTrace.shape.touched, afterTrace.shape.once, afterTrace.shape.clean⟩,
      afterTrace.unselected, afterTrace.selected, afterTrace.marked⟩
  · have afterHistory := PqxdhServerAuthCtxAcceptanceHistory.handler_history setup codec checks context Q j
      (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest)) query
      (PqxdhServerAuthCtxState.project (localState, before.2)) beforeTrace.shape
      ⟨invariant.history.fresh, invariant.history.frozen, invariant.history.atomic⟩ _ sourceReached
    exact ⟨afterHistory.fresh, afterHistory.frozen, afterHistory.atomic⟩
  · exact (PqxdhServerAuthCtxChronology.handler_history setup codec checks context
      (PqxdhServerAuthCtxMaterial.output key rest) Q j query
      (PqxdhServerAuthCtxState.project (localState, before.2)) invariant.clean _ sourceReached).2
  · exact RawCtxSelectedPlaintextOrigins.schedule_good _ _ _ _ before invariant.good _ supported

/-- The literal sampled context and empty component instrumentation establish every joint invariant field for any selected key. -/
theorem Joint.initial (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) :
    Joint setup codec context key Q j
      ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false)
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource) := by
  exact ⟨TraceInvariant.initial setup context Q j, PqxdhServerAuthCtxAcceptanceHistory.History.initial setup context,
    (fun _ _ => rfl), (fun _ found => by cases found), RawCtxSelectedPlaintextOrigins.initial_good _ _ _⟩

/-- The actual post-callback stop changes only its control monitor. Every continuing reply retains the complete joint source and observer invariant. -/
theorem stopped_joint (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState : PqxdhServerAuthCtxState.Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (ready : PqxdhServerAuthCtxHandler.Ready query (localState.1, before.2))
    (invariant : Joint setup codec context key Q j localState.1 before)
    (result : (Option (ServerAuthSpec.Range query) ×
      (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run localState)).run before))
    (answer : ServerAuthSpec.Range query) (continues : result.1.1 = some answer) :
    Joint setup codec context key Q j result.1.2.1 result.2 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key)
    ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run localState)).run before) at supported
  simp only [PqxdhServerAuthCtxReserve.stopped, stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  cases returned : inner.1.1 with
  | none =>
    simp only [observe, returned] at continues
    cases continues
  | some reply =>
    have preserved := handler_joint setup codec checks context rest key Q j query localState.1 inner.1.2
      before inner.2 ready invariant reply (by rw [← returned]; exact reached)
    simpa only [observe_state] using preserved

/-- Erasing only instrumentation from the actual observed stopped callback supplies the reservation theorem with exactly the original component poststate. -/
theorem stopped_valid (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (localState : PqxdhServerAuthCtxState.Local KemSK × Option Nat)
    (before : RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)
    (valid : PqxdhServerAuthCtxReserve.Valid (localState, before.2))
    (result : (Option (ServerAuthSpec.Range query) ×
      (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run localState)).run before))
    (answer : ServerAuthSpec.Range query) (continues : result.1.1 = some answer) :
    PqxdhServerAuthCtxReserve.Valid (result.1.2, result.2.2) := by
  have erased := PqxdhFirstBeaconRecordCanonical.observed_component _ _ _ _ before result supported
  have evaluated : (result.1.1, (result.1.2, result.2.2)) ∈ support
      ((PqxdhServerAuthCtxNative.evaluate setup.source key codec.frameRead
        (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run).run
        (localState, before.2)) := by
    change (result.1.1, (result.1.2, result.2.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨(result.1, result.2.2), erased, rfl⟩
  exact PqxdhServerAuthCtxReserve.normal_valid setup.source key codec.frameRead
    (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)
    (PqxdhServerAuthCtxHandlerBounds.handler_footprint setup codec checks context rest Q j)
    (fun query state => (PqxdhServerAuthCtxHandlerBounds.handler_record_bills setup codec checks context rest Q j query state).1)
    query (localState, before.2) valid _ evaluated answer continues

/-- Actual executable control, full ordinary observer history and private component state. -/
abbrev ObservedState (KemSK : Type) :=
  (PqxdhServerAuthCtxState.Local KemSK × Option Nat) ×
    (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState)

/-- Reservation and complete source/observer provenance are retained together; neither field is an authentication assumption. -/
def Invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (state : ObservedState KemSK) : Prop :=
  PqxdhServerAuthCtxReserve.Valid (state.1, state.2.2) ∧
    Joint setup codec context key Q j state.1.1 state.2

/-- Mathematical evaluation of the actual stopped executable by the ordinary instrumented CTX challenger. This wrapper preserves every returned optional value and both states. -/
noncomputable def interpreted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) :
    QueryImpl ServerAuthSpec (OptionT (StateT (ObservedState KemSK) ProbComp)) :=
  fun query => OptionT.mk (PqxdhSelectedStateInterpreter.evaluate
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key)
    (PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run)

/-- Every continuing interpreted callback establishes the next complete invariant from the actual control reservation and concrete source execution. -/
theorem interpreted_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (state : ObservedState KemSK) (invariant : Invariant setup codec context key Q j state)
    (result : Option (ServerAuthSpec.Range query) × ObservedState KemSK)
    (supported : result ∈ support ((interpreted setup codec checks context rest key Q j query).run.run state))
    (answer : ServerAuthSpec.Range query) (continues : result.1 = some answer) :
    Invariant setup codec context key Q j result.2 := by
  simp only [interpreted, OptionT.run_mk, PqxdhSelectedStateInterpreter.evaluate, StateT.run,
    support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact ⟨stopped_valid setup codec checks context rest key Q j query state.1 state.2 invariant.1
      inner reached answer continues,
    stopped_joint setup codec checks context rest key Q j query state.1 state.2
      (PqxdhServerAuthCtxReserve.valid_ready query (state.1, state.2.2) invariant.1)
      invariant.2 inner reached answer continues⟩

/-- Arbitrary adaptive client continuations preserve the joint invariant on every normal terminal result. Refusal is explicit and does not fabricate a reply or continue the adversary. -/
theorem program_invariant {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (client : OracleComp ServerAuthSpec α)
    (state : ObservedState KemSK) (invariant : Invariant setup codec context key Q j state)
    (result : Option α × ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (interpreted setup codec checks context rest key Q j) client).run.run state))
    (answer : α) (continues : result.1 = some answer) :
    Invariant setup codec context key Q j result.2 := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    cases reply : middle.1 with
    | none =>
      simp only [reply, Option.elim_none, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases continues
    | some value =>
      simp only [reply, Option.elim_some] at supported
      exact ih value middle.2
        (interpreted_invariant setup codec checks context rest key Q j query state invariant middle reached value reply)
        supported

/-- The same complete optional program can be evaluated once by the ordinary observer, without an extra query or change to its actual reply-dependent continuation. -/
theorem program_interpreted {α : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (client : OracleComp ServerAuthSpec α) :
    PqxdhSelectedStateInterpreter.evaluate
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      (simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) client).run =
      (simulateQ (interpreted setup codec checks context rest key Q j) client).run := by
  rw [← RawCtxSelectedFamilyNonceCoupling.optional_client _ client,
    ← RawCtxSelectedFamilyNonceCoupling.optional_client _ client]
  exact PqxdhSelectedStateInterpreter.program _ _ _

/-- Literal initial state for the same stopped program and ordinary observer. -/
def initial (setup : Setup baseSpec KemSK) (context : Context KemSK) : ObservedState KemSK :=
  ((PqxdhServerAuthCtxReserve.initial setup context).1,
    RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource)

/-- Empty source and challenger instrumentation discharge all provenance, history and reservation premises for any sampled context and key. -/
theorem initial_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) :
    Invariant setup codec context key Q j (initial setup context) := by
  exact ⟨PqxdhServerAuthCtxReserve.initial_valid setup context, Joint.initial setup codec context key Q j⟩

/-- The original adaptive adversary's complete observed executable supplies its own joint origin and plaintext invariant; no trace, honesty or source-origin premise is supplied by the caller. -/
theorem run_invariant (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (adversary : Adversary)
    (result : (Option Unit × (PqxdhServerAuthCtxState.Local KemSK × Option Nat)) ×
      (RawCtxSelectedAuthenticationObserver.State × AdaptiveCtxDynamicKnownKeys.SourceState))
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
        (adversary (contextInput setup false context))).run.run (initial setup context).1)).run
      (initial setup context).2))
    (continues : result.1.1 = some ()) :
    Invariant setup codec context key Q j (result.1.2, result.2) := by
  have evaluated : (result.1.1, (result.1.2, result.2)) ∈ support
      ((PqxdhSelectedStateInterpreter.evaluate
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j))
          (adversary (contextInput setup false context))).run).run (initial setup context)) := by
    change (result.1.1, (result.1.2, result.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [program_interpreted] at evaluated
  exact program_invariant setup codec checks context rest key Q j _ (initial setup context)
    (initial_invariant setup codec context key Q j) _ evaluated () continues

end BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.origins_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.origins_quiet

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.finish_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.finish_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.skeleton_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.skeleton_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_hidden' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_hidden

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.evaluated_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.evaluated_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_source_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_source_support

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_quiet_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_quiet_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.selected_build_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.selected_build_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_build_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_build_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_origins

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.handler_joint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.Joint.initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.Joint.initial

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.stopped_joint' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.stopped_joint

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.stopped_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.stopped_valid

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.interpreted_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.interpreted_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.program_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.program_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.program_interpreted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.program_interpreted

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.initial_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.initial_invariant

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.run_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthCtxObserverHistory.run_invariant
