import BeaconcryptCore.Computational.RawCtxSelectedFamilySourceAudit

/-!
Actual native send events contain the original admitted private derivation and its ready sealing capability. The source interpreter is concrete: retained-table lookups are evaluated exactly and the native seal retains its full optional reply and primitive state. This supplies source provenance for nonce evidence without assuming that any sending chain is unique.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedSendEvents
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame
open RawCtxSelectedParentTable RawCtxSelectedParentEntry RawCtxSelectedMessageDriver
open RawCtxSelectedDriverAudit
variable {A Owner : Type}

private theorem state_bind_apply {X Y σ : Type} {m : Type → Type*} [Monad m]
    (work : StateT σ m X) (continuation : X → StateT σ m Y) (state : σ) :
    (work >>= continuation) state = (work state >>= fun result => continuation result.1 result.2) := rfl

private theorem state_pure_apply {X σ : Type} {m : Type → Type*} [Monad m]
    (value : X) (state : σ) : (pure value : StateT σ m X) state = pure (value, state) := rfl

private theorem state_map_apply {X Y σ : Type} {m : Type → Type*} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT σ m X) (state : σ) :
    (f <$> work) state = (fun result => (f result.1, result.2)) <$> work state := by
  change (f <$> work).run state = (fun result => (f result.1, result.2)) <$> work.run state
  rw [StateT.run_map]

noncomputable def route (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (request : SymmetricRatchetKdfRequest) :=
  match parent with
  | none => RawCtxSelectedMessageKdf.step prior target nonce next request
  | some entry => RawCtxSelectedMessageKdf.later prior entry target nonce next request

noncomputable def services (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput) :
    QueryImpl (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted)
      (OptionT (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp)) :=
  fun query => monadLift (sendServices (A := A) source writer prior parent key target nonce next query)

/-- The completed original private derivation records precisely its actual retained-table response and preserves the whole shared state. -/
theorem derived (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (request : SymmetricRatchetKdfRequest)
    (history : List (Event Owner)) (state : RawCtxSharedPrimitive.SharedState A) :
    ((simulateQ (observed (services source writer prior parent key target nonce next))
      (RawCtxSelectedDriverAudit.sendCompiler owner entry parent target nonce next (.inl request))).run).run (history, state) =
      pure (some (route prior parent target nonce next request),
        (history ++ [.derived owner true entry request (route prior parent target nonce next request)], state)) := by
  simp only [RawCtxSelectedDriverAudit.sendCompiler, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    ← QueryImpl.simulateQ_compose]
  have lookup : observed (services (A := A) source writer prior parent key target nonce next) ∘ₛ
      (fun address => (SendSpec Owner).query (.inl (.inl address)) : QueryImpl RawCtxSelectedMessageKdf.PriorSpec (OracleComp (SendSpec Owner))) =
      (fun address => (pure (prior address) : OptionT (StateT (List (Event Owner) × RawCtxSharedPrimitive.SharedState A) ProbComp) FullOutput)) := by
    funext address
    rfl
  rw [lookup, derive_evaluated]
  simp only [pure_bind, observed, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    StateT.run, pure_bind, Option.elimM, route]
  rfl

noncomputable def executed (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event Owner)) (state : RawCtxSharedPrimitive.SharedState A) :=
  ((simulateQ (observed (services source writer prior parent key target nonce next))
    (RawCtxSelectedDriverAudit.send owner entry parent target nonce next context)).run).run (history, state)

/-- An admitted original send emits its actual derivation and pending seal in source order, including a failed native writer. -/
theorem requested (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (request : RawCtxInterpretedSend.Kdf RawCtxSelectedMessageKey.Slot RawCtxSourceSend.SealContext)
    (admitted : RawCtxInterpretedSend.normalBegin entry context = .requested request)
    (history : List (Event Owner)) (state : RawCtxSharedPrimitive.SharedState A) :
    executed source writer prior parent key target nonce next owner entry context history state =
      (fun result => (some ((RawCtxInterpretedSend.ready request (route prior parent target nonce next request.request)).advanced, result.1),
        (history ++ [.derived owner true entry request.request (route prior parent target nonce next request.request),
          .sealing ⟨owner, entry, RawCtxInterpretedSend.ready request (route prior parent target nonce next request.request)⟩], result.2))) <$>
        (sendServices source writer prior parent key target nonce next
          (.inr (RawCtxInterpretedSend.ready request (route prior parent target nonce next request.request)))).run state := by
  simp only [executed, RawCtxSelectedDriverAudit.send, RawCtxInterpretedSend.send, admitted,
    RawCtxInterpretedSend.program, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    OptionT.run_bind, Option.elimM, StateT.run_bind]
  rw [derived]
  simp only [pure_bind, Option.elim_some]
  simp only [RawCtxSelectedDriverAudit.sendCompiler, simulateQ_bind, simulateQ_spec_query,
    observed, services, OptionT.run_bind, OptionT.run_mk, OptionT.run_monadLift,
    OptionT.run_pure, StateT.run, Option.elimM, monadLift_self]
  simp only [state_bind_apply, state_pure_apply, state_map_apply, pure_bind, bind_map_left,
    Option.elim_some, Functor.map_map, List.append_assoc, List.singleton_append]
  simp only [map_eq_bind_pure_comp, Function.comp_def]

noncomputable def events (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) : List (Event Owner) :=
  match RawCtxInterpretedSend.normalBegin entry context with
  | .exhausted _ _ => []
  | .requested request =>
      [.derived owner true entry request.request (route prior parent target nonce next request.request),
        .sealing ⟨owner, entry, RawCtxInterpretedSend.ready request (route prior parent target nonce next request.request)⟩]

/-- Every supported complete source send retains exactly its original two events, or no events on exhausted admission. Native writer failure does not remove its attempt. -/
theorem history_exact (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history afterHistory : List (Event Owner)) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (reply, (afterHistory, after)) ∈ support
      (executed source writer prior parent key target nonce next owner entry context history state)) :
    afterHistory = history ++ events prior parent target nonce next owner entry context := by
  cases admitted : RawCtxInterpretedSend.normalBegin entry context with
  | exhausted old oldContext =>
    simp only [executed, RawCtxSelectedDriverAudit.send, RawCtxInterpretedSend.send, admitted,
      RawCtxInterpretedSend.program, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
      mem_support_pure_iff, Prod.mk.injEq] at supported
    simpa only [events, admitted, List.append_nil] using supported.2.1
  | requested request =>
    rw [requested source writer prior parent key target nonce next owner entry context request admitted history state] at supported
    simp only [support_map] at supported
    obtain ⟨result, _, same⟩ := supported
    have equal := congrArg (fun value => value.2.1) same
    simpa only [events, admitted] using equal.symm

/-- A newly recorded sealing occurrence has its literal outer owner, entry kernel, source admission and exact ready capability; this is not a caller-supplied routing premise. -/
theorem sealing_routed (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ events prior parent target nonce next owner entry context) :
    occurrence.owner = owner ∧ occurrence.entry = entry ∧
      RawCtxSelectedSendTrace.Routed (route prior parent target nonce next) occurrence := by
  cases admitted : RawCtxInterpretedSend.normalBegin entry context with
  | exhausted old oldContext => simp only [events, admitted, List.not_mem_nil] at found
  | requested request =>
    simp only [events, admitted, List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, false_or, Event.sealing.injEq] at found
    subst occurrence
    refine ⟨rfl, rfl, request, ?_, rfl⟩
    have fields := RawCtxSelectedSendAddress.admitted_request entry context request admitted
    simpa only [RawCtxInterpretedSend.ready, fields.2.1] using admitted

/-- Every new seal in the literal native audit is attributed to this actual caller and admitted sending kernel, with its routing witness constructed from the execution. -/
theorem recorded_sealing (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history afterHistory : List (Event Owner)) (state after : RawCtxSharedPrimitive.SharedState A)
    (reply : Option (RawCtxSelectedMessageReveals.Kernel × Option RawCtxSourceSend.Encrypted))
    (supported : (reply, (afterHistory, after)) ∈ support
      (executed source writer prior parent key target nonce next owner entry context history state))
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ afterHistory.drop history.length) :
    occurrence.owner = owner ∧ occurrence.entry = entry ∧
      RawCtxSelectedSendTrace.Routed (route prior parent target nonce next) occurrence := by
  rw [history_exact source writer prior parent key target nonce next owner entry context history afterHistory state after reply supported] at found
  exact sealing_routed prior parent target nonce next owner entry context occurrence
    (by simpa only [List.drop_left] using found)

/-- A selected send event in the actual source trailer identifies its literal sending chain; retained predecessor priority is kept even when addresses collide. -/
theorem selected_chain (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce value : NonceOutput) (next : RootOutput) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (occurrence : RawCtxSelectedSendTrace.Occurrence Owner)
    (found : Event.sealing occurrence ∈ events prior parent target nonce next owner entry context)
    (selected : RawCtxSelectedSendTrace.nonce occurrence.pending = some value) :
    entry.send_chain = RawCtxFreshChainCut.concreteChain target ∧
      ∀ predecessor, parent = some predecessor →
        RawCtxSelectedPendingCut.requestAddress entry.send_chain ≠ predecessor.address := by
  obtain ⟨_, old, routed⟩ := sealing_routed prior parent target nonce next owner entry context occurrence found
  cases parent with
  | none =>
    have chain := RawCtxSelectedSendTrace.routed_chain prior target next nonce value occurrence routed selected
    refine ⟨old ▸ chain, ?_⟩
    intro _ impossible
    cases impossible
  | some predecessor =>
    have chain := RawCtxSelectedSendTrace.later_routed_chain prior predecessor target next nonce value occurrence routed selected
    refine ⟨old ▸ chain.2, ?_⟩
    intro candidate equal
    cases equal
    exact old ▸ chain.1

/-- Source admission records at most one private derivation and one seal attempt. These are instrumentation counts, not a waiver of source primitive or local work. -/
theorem events_length (prior : Prior) (parent : Option Entry) (target : RootOutput)
    (nonce : NonceOutput) (next : RootOutput) (owner : Owner)
    (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext) :
    (events prior parent target nonce next owner entry context).length ≤ 2 := by
  unfold events
  split <;> simp only [List.length_nil, List.length_cons] <;> omega

private theorem services_program {Value : Type} (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (work : OracleComp (SendServices RawCtxSourceSend.SealContext RawCtxSourceSend.Encrypted) Value) :
    (simulateQ (services (A := A) source writer prior parent key target nonce next) work).run =
      some <$> simulateQ (sendServices source writer prior parent key target nonce next) work := by
  induction work using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind query continuation ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, services, OptionT.run_bind,
      OptionT.run_monadLift, Option.elimM, bind_map_left, monadLift_self, Option.elim_some, ih, map_bind]

/-- Erasing only the private send events gives the same complete source operation and shared poststate, with every original optional ciphertext kept. -/
theorem erased_source (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event Owner)) (state : RawCtxSharedPrimitive.SharedState A) :
    Prod.map id Prod.snd <$> executed source writer prior parent key target nonce next owner entry context history state =
      (fun result => (some result.1, result.2)) <$>
        (simulateQ (sendServices source writer prior parent key target nonce next)
          (RawCtxSelectedMessageDriver.send parent target nonce next entry context)).run state := by
  rw [executed, observed_program, services_program, send_erased, StateT.run_map]

/-- Source events retain precisely the native source uniform-query budget, including unsuccessful writes and all prior-table work. -/
theorem uniform_queries (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (owner : Owner) (entry : RawCtxSelectedMessageReveals.Kernel) (context : RawCtxSourceSend.SealContext)
    (history : List (Event Owner)) (state : RawCtxSharedPrimitive.SharedState A) (budget : Nat) :
    (executed source writer prior parent key target nonce next owner entry context history state).IsTotalQueryBound budget ↔
      ((simulateQ (sendServices source writer prior parent key target nonce next)
        (RawCtxSelectedMessageDriver.send parent target nonce next entry context)).run state).IsTotalQueryBound budget := by
  have cost := congrArg (fun work => work.IsTotalQueryBound budget)
    (erased_source source writer prior parent key target nonce next owner entry context history state)
  simpa only [IsTotalQueryBound, isQueryBound_map_iff] using Iff.of_eq cost

end BeaconcryptCore.Computational.RawCtxSelectedSendEvents

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.derived' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.derived

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.requested' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.requested

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.history_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.history_exact

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.sealing_routed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.sealing_routed

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.recorded_sealing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.recorded_sealing

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.selected_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.selected_chain

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.events_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.events_length

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.erased_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.erased_source

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedSendEvents.uniform_queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedSendEvents.uniform_queries
