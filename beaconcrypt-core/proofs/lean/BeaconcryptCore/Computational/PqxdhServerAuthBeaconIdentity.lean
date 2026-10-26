import BeaconcryptCore.Computational.PqxdhServerAuthPhase1BuildOrigins

/-! Actual target Beacon control and metadata identities through source admission. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity
open PqxdhServerAuthExperiment PqxdhServerAuthEntryFactor PqxdhJointIdentity PqxdhJointGapDh
variable {ι KemSK Reader Response : Type} {baseSpec : OracleSpec ι}

/-- The original Phase1 publication installs the exact pinned Server and generated Beacon identity fields. -/
theorem phase1_control (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (beaconSeed : IdentitySeed)
    (publicValue : PublicChallenge) (oneTime : ScalarBytes) (kemPk : PqxdhKemIndCca.MlKem768PublicKey) (kemSk : KemSK)
    (result : Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State Unit (Unit ⊕ ScalarBytes) KemSK)
    (supported : result ∈ support (phase1Run setup codec beaconSeed publicValue oneTime kemPk kemSk)) :
    ∀ control prekey other kem, result.2.beacon.phase = .initSent control prekey other kem →
      control.expected_server_binding = binding setup publicValue ∧
      control.beacon_identity_public_key = PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys beaconSeed).ed25519 := by
  simp only [phase1Run, PqxdhLivePhase1Bundle.bundle, freshBeacon, simulateQ_bind, simulateQ_spec_query,
    mem_support_bind_iff] at supported
  obtain ⟨generated, _, supported⟩ := supported
  intro control prekey other kem phase
  cases generated with
  | none =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_none,
        simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
      subst supported
      cases phase
  | some generated =>
      simp only [PqxdhLivePhase1Bundle.afterGenerated, PqxdhBeaconPhase1Publication.prepare, Option.map_some,
        simulateQ_bind, mem_support_bind_iff] at supported
      obtain ⟨signed, _, supported⟩ := supported
      cases signed with
      | none =>
          simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          cases phase
      | some bundle =>
          simp only [PqxdhLivePhase1Bundle.writing, PqxdhBeaconPhase1Publication.afterSigning,
            PqxdhBeaconPhase1Publication.prepare, Option.map_some, simulateQ_bind, simulateQ_spec_query,
            mem_support_bind_iff] at supported
          obtain ⟨written, _, supported⟩ := supported
          cases written with
          | none =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              cases phase
          | some bytes =>
              simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at supported
              subst supported
              simp only [PqxdhBeaconPhase1Publication.publish, RawCtxBeaconLifecycle.Phase.initSent.injEq] at phase
              rw [← phase.1]
              exact ⟨rfl, rfl⟩

/-- The actual successful Beacon prefix supplies its original metadata admission equation. -/
theorem prefix_admitted (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (beaconSeed : IdentitySeed) (control : pqxdh.BeaconInitSent) (identity : Unit)
    (oneTime : Unit ⊕ ScalarBytes) (kem : KemSK) (raw : Pqxdh.Bytes)
    (pending : PqxdhPhase2DhMetadata.Prepared Response)
    (supported : some pending ∈ support ((beaconPrefix setup codec beaconSeed control identity oneTime kem raw).run' ())) :
    PqxdhPhase2DhMetadata.admitted control pending.collected = some pending.metadata := by
  simp only [beaconPrefix, PqxdhPhase2DhMetadata.prepare, simulateQ_bind, simulateQ_pure,
    StateT.run'_eq, StateT.run_bind, StateT.run_pure, support_map, Set.mem_image,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨_, ⟨⟨collected, state⟩, reached, rfl⟩, same⟩ := supported
  cases collected with
  | none => cases same
  | some input =>
    simp only [Option.bind_some] at same
    cases admitted : PqxdhPhase2DhMetadata.admitted control input with
    | none => simp only [admitted, Option.map_none, reduceCtorEq] at same
    | some metadata =>
      simp only [admitted, Option.map_some, Option.some.injEq] at same
      cases same
      exact admitted

/-- Every successful original sequence/binding gate retains the candidate's literal associated data. -/
theorem opening_ad (candidate : pqxdh.BeaconRegistrationCandidate) (kernel : ConcreteRatchetKernel)
    (reply : core.option.Option RawCtxWholeOwner.Decrypted) (staged : PqxdhBeaconPhase2Publication.Staged)
    (accepted : PqxdhBeaconPhase2Publication.afterOpening candidate kernel reply = some staged) :
    staged.associatedData = candidate.associated_data := by
  unfold PqxdhBeaconPhase2Publication.afterOpening at accepted
  cases reply with
  | none => cases accepted
  | some opened =>
    dsimp only at accepted
    split_ifs at accepted
    split at accepted
    · contradiction
    · cases accepted
      rfl

/-- The complete concrete factored tail retains the actual admitted associated data for every successful optional result. -/
theorem factor_ad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (value : PqxdhServerAuthSendFactor.Factor)
    (before : RawCtxSharedPrimitive.SharedState Unit)
    (result : Option PqxdhBeaconPhase2Publication.Staged × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((PqxdhServerAuthBeaconFactor.factored
      (PqxdhServerAuthBeaconFactor.nativePrim setup codec) (fun entry _ => pure (entry, none)) setup.source
      (fun response => pure (codec.application response)) codec.frameRead
      (PqxdhPhase2DhRootConsumer.cleared pending) value).run before))
    (staged : PqxdhBeaconPhase2Publication.Staged) (returned : result.1 = some staged) :
    staged.associatedData = pending.metadata.associatedData := by
  simp only [PqxdhServerAuthBeaconFactor.factored, pure_bind] at supported
  cases raw : codec.application pending.collected.response with
  | none =>
    simp only [PqxdhPhase2DhRootConsumer.cleared, raw, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    cases returned
  | some raw =>
    simp only [PqxdhPhase2DhRootConsumer.cleared, raw, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact opening_ad _ _ _ staged returned

/-- The original known-root tail has the same associated-data property through its exact complete source factorization. -/
theorem native_ad (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (root : PqxdhSecretInputKdf.RootOutput)
    (before : RawCtxSharedPrimitive.SharedState Unit)
    (result : Option PqxdhBeaconPhase2Publication.Staged × RawCtxSharedPrimitive.SharedState Unit)
    (supported : result ∈ support ((simulateQ (beaconNative setup codec)
      (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))).run before))
    (staged : PqxdhBeaconPhase2Publication.Staged) (returned : result.1 = some staged) :
    staged.associatedData = pending.metadata.associatedData := by
  rw [PqxdhServerAuthBeaconFactor.beacon_afterRoot_run setup codec (fun entry _ => pure (entry, none))] at supported
  exact factor_ad setup codec pending _ before result supported staged returned

/-- The target identity pair as retained by an active original Beacon control. -/
def Control (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (control : pqxdh.BeaconInitSent) : Prop :=
  control.expected_server_binding = server ∧ control.beacon_identity_public_key = beacon

/-- Both identity fields are reflected by the existing exact associated-data layout. -/
theorem control_ad (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (control : pqxdh.BeaconInitSent) (bound : Control server beacon control) :
    absBytes (PqxdhBeaconPhase2Shared.associatedData control) =
      Pqxdh.assocData (absBytes server.identity_public_key) (absBytes beacon) := by
  rw [PqxdhServerAuthPublicationIdentity.beacon_bytes, bound.1, bound.2]

/-- The actual active control and any recorded acceptance retain the original target identity pair. -/
def Invariant (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (game : GameState KemSK) : Prop :=
  (∀ control prekey oneTime kem, game.beacon.beacon.phase = .initSent control prekey oneTime kem →
    Control server beacon control) ∧
  ∀ snap, game.ghost.acceptance = some snap →
    snap.accepted.associatedData = Pqxdh.assocData (absBytes server.identity_public_key) (absBytes beacon)

/-- Original final gates make the Beacon inactive and preserve the accepted identity pair even when no new acceptance is recorded. -/
theorem finish_invariant (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (game : GameState KemSK) (invariant : Invariant server beacon game)
    (control : pqxdh.BeaconInitSent) (bound : Control server beacon control)
    (staged : Option PqxdhBeaconPhase2Publication.Staged)
    (metadata : ∀ value, staged = some value → value.associatedData = PqxdhBeaconPhase2Shared.associatedData control) :
    Invariant server beacon (finishOutcome control game staged).2 := by
  refine ⟨?_, ?_⟩
  · intro other prekey oneTime kem phase
    exact (finish_phase control game.beacon staged other prekey oneTime kem phase).elim
  · intro snap captured
    cases old : game.ghost.acceptance with
    | some prior =>
      have same := Ghost.accept_old game.ghost _ prior snap old captured
      subst snap
      exact invariant.2 prior old
    | none =>
      obtain ⟨fields, present, equal⟩ := Ghost.accept_new game.ghost _ snap captured old
      subst snap
      cases staged with
      | none => simp only [acceptedOf_none, reduceCtorEq] at present
      | some value =>
        simp only [acceptedOf, Option.map_some] at present
        split_ifs at present
        · cases present
          exact (congrArg absBytes (metadata value rfl)).trans (control_ad server beacon control bound)

/-- The hidden callback's functional metadata property; the concrete factor service discharges it below. -/
def TailAD {τ : Type} (services : Services Response τ) : Prop :=
  ∀ pending before result, result ∈ support ((services.hiddenAfter pending).run before) →
    ∀ staged, result.1 = some staged → staged.associatedData = pending.metadata.associatedData

/-- Uniform or real concrete factors retain the same source metadata without a condition on their sampled key bytes. -/
theorem factor_tail (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    TailAD (factorServices setup codec checks context value) := by
  intro pending before result supported staged returned
  exact factor_ad setup codec pending _ before result supported staged returned

/-- Every original finish branch preserves the target identities and any actual accepted associated data, including rejected preparation and ordinary or hidden derivation. -/
theorem finish_step {τ : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ)
    (tail : TailAD services) (raw : Pqxdh.Bytes)
    (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (state : FlatState KemSK τ) (invariant : Invariant server beacon state.1)
    (result : Option Pqxdh.Bytes × FlatState KemSK τ)
    (supported : result ∈ support ((finishStep setup codec publicValue beaconSeed services raw).run state)) :
    Invariant server beacon result.2.1 := by
  simp only [finishStep, StateT.run] at supported
  cases phase : state.1.beacon.beacon.phase with
  | initSent control prekey oneTime kem =>
    have bound := invariant.1 control prekey oneTime kem phase
    simp only [phase, mem_support_bind_iff] at supported
    obtain ⟨prepared, preparedRun, supported⟩ := supported
    cases found : prepared with
    | none =>
      simp only [found, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact finish_invariant server beacon state.1 invariant control bound none (by intro value equal; cases equal)
    | some pending =>
      have admitted := prefix_admitted setup codec beaconSeed control state.1.beacon.beacon.identity oneTime kem raw pending
        (by rw [← found]; exact preparedRun)
      have metadata : pending.metadata.associatedData = PqxdhBeaconPhase2Shared.associatedData control :=
        congrArg PqxdhBeaconPhase2Shared.Metadata.associatedData
          (PqxdhPhase2DhMetadata.admitted_fields control pending.collected pending.metadata admitted).2.2
      simp only [found, mem_support_bind_iff] at supported
      obtain ⟨derived, derivedRun, supported⟩ := supported
      cases reply : derived.1 with
      | rejected =>
        simp only [reply, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact finish_invariant server beacon
          { state.1 with ghost := { state.1.ghost with touches := state.1.ghost.touches ++
            [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] } }
          ⟨invariant.1, invariant.2⟩ control bound none
          (by intro value equal; cases equal)
      | root root =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, stagedRun, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact finish_invariant server beacon
          { state.1 with ctx := staged.2.2, ghost := { state.1.ghost with touches := state.1.ghost.touches ++
            [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] } }
          ⟨invariant.1, invariant.2⟩ control bound staged.1
          (fun value equal => (native_ad setup codec pending root _ staged stagedRun value equal).trans metadata)
      | hidden =>
        simp only [reply, mem_support_bind_iff] at supported
        obtain ⟨staged, stagedRun, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact finish_invariant server beacon
          { state.1 with ctx := staged.2.2, ghost := { state.1.ghost with touches := state.1.ghost.touches ++
            [.beacon (PqxdhJointDhExtractRoot.beaconMessage publicValue pending.collected)] } }
          ⟨invariant.1, invariant.2⟩ control bound staged.1
          (fun value equal => (tail pending _ staged stagedRun value equal).trans metadata)
  | _ =>
    simp only [phase, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact invariant

/-- Every other complete API operation preserves the Beacon control and recorded associated data; finish uses its actual source metadata property. -/
theorem skeleton_identity {τ : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (publicValue : PublicChallenge) (beaconSeed : IdentitySeed) (services : Services Response τ) (tail : TailAD services)
    (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (query : ServerAuthSpec.Domain) (state : FlatState KemSK τ) (invariant : Invariant server beacon state.1)
    (result : ServerAuthSpec.Range query × FlatState KemSK τ)
    (supported : result ∈ support ((skeleton setup codec checks publicValue beaconSeed services query).run state)) :
    Invariant server beacon result.2.1 := by
  cases query with
  | inl coin =>
    simp only [skeleton, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    exact invariant
  | inr query =>
    cases query with
    | accept raw =>
      simp only [skeleton, acceptStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨collected, _, supported⟩ := supported
      cases found : collected.1 with
      | none =>
        simp only [found, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact invariant
      | some input =>
        simp only [found] at supported
        split_ifs at supported
        · obtain ⟨derived, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
          simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          cases derived.1 <;> exact ⟨invariant.1, invariant.2⟩
        · simp only [support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact invariant
    | build session payload =>
      simp only [skeleton, buildStep, StateT.run] at supported
      cases found : state.1.pending session with
      | none =>
        simp only [found, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact invariant
      | some token =>
        simp only [found, mem_support_bind_iff] at supported
        obtain ⟨built, _, supported⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨invariant.1, invariant.2⟩
    | finish raw => exact finish_step setup codec publicValue beaconSeed services tail raw server beacon state invariant result supported
    | hmac key bytes =>
      simp only [skeleton, hmacStep, StateT.run] at supported
      split_ifs at supported
      · obtain ⟨read, _, supported⟩ := (mem_support_bind_iff _ _ _).1 supported
        simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact ⟨invariant.1, invariant.2⟩
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact invariant
    | hash bytes =>
      simp only [skeleton, hashStep, StateT.run, mem_support_bind_iff] at supported
      obtain ⟨read, _, supported⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact invariant
    | reveal key =>
      simp only [skeleton, StateT.run, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact invariant

/-- Designation and sticky refusal keep the same actual control and accepted-field invariant. -/
theorem handler_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (tail : TailAD services) (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (query : ServerAuthSpec.Domain) (state : HiddenState KemSK) (invariant : Invariant server beacon state.1.1)
    (result : ServerAuthSpec.Range query × HiddenState KemSK)
    (supported : result ∈ support ((hiddenHandler setup codec checks context Q j services query).run state)) :
    Invariant server beacon result.2.1.1 := by
  simp only [hiddenHandler, StateT.run, support_map, Set.mem_image] at supported
  obtain ⟨middle, supported, rfl⟩ := supported
  rw [keepHiddenBad_game]
  simp only [once, StateT.run] at supported
  split_ifs at supported
  all_goals
    simp only [latch, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨step, supported, rfl⟩ := supported
    refine skeleton_identity setup codec checks (context.publicValue setup) context.beaconSeed _ ?_
      server beacon query state.1 invariant step supported
    exact tail

/-- Complete adaptive original source execution retains the target identity invariant without a winning-event premise. -/
theorem program_identity {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (Q : Nat) (j : Fin (Q + 1)) (services : Services Response HiddenTable)
    (tail : TailAD services) (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (work : OracleComp ServerAuthSpec Result) (state : HiddenState KemSK) (invariant : Invariant server beacon state.1.1)
    (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j services) work).run state)) :
    Invariant server beacon result.2.1.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    exact ih middle.1 middle.2
      (handler_identity setup codec checks context Q j services tail server beacon query state invariant middle reached) supported

/-- The literal context sampler installs the exact generated target pair before the adversary starts; no arbitrary-context well-formedness premise is inferred. -/
theorem context_identity (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (context : Context KemSK) (supported : context ∈ support (contextSample setup codec)) :
    Invariant (binding setup (context.publicValue setup))
      (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519)
      (contextState setup context) := by
  simp only [contextSample, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨seed, _, scalar, _, beaconSeed, _, oneTime, _, keys, _, published, publishedRun, rfl⟩ := supported
  refine ⟨?_, ?_⟩
  · exact phase1_control setup codec beaconSeed _ oneTime keys.1 keys.2 published publishedRun
  · intro snap captured
    cases captured

/-- Every complete original factor-side run from the actual sampled context preserves the target's ordered raw identities. The factor output and adaptive client remain arbitrary. -/
theorem initial_identity {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (Q : Nat) (j : Fin (Q + 1)) (value : PqxdhServerAuthKeySchedule.Output)
    (work : OracleComp ServerAuthSpec Result) (result : Result × HiddenState KemSK)
    (supported : result ∈ support ((simulateQ (hiddenHandler setup codec checks context Q j
      (factorServices setup codec checks context value)) work).run
      ((contextState setup context, fun _ => false, ⟨∅, none, false⟩), false))) :
    Invariant (binding setup (context.publicValue setup))
      (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519) result.2.1.1 := by
  exact program_identity setup codec checks context Q j _ (factor_tail setup codec checks context value)
    _ _ work _ (context_identity setup codec context sampled) result supported

open PqxdhServerAuthCtxState PqxdhServerAuthCtxStop PqxdhSecretInputKdf
abbrev Observed := PqxdhServerAuthPublicationRecordReserve.Observed

/-- The actual ordinary component interpretation retains the source identity invariant; its cache projection changes no control or accepted field. -/
theorem observed_step (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (state : Local KemSK) (before : Observed)
    (ready : PqxdhServerAuthCtxHandler.Ready query (state, before.2))
    (invariant : Invariant server beacon state.1.1)
    (result : (Option (ServerAuthSpec.Range query) × Local KemSK) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j query).run.run state)).run before)) :
    Invariant server beacon result.1.2.1.1 := by
  obtain ⟨reply, returned, reached⟩ := PqxdhServerAuthCtxObserverHistory.handler_source_support setup codec checks context
    rest key Q j query state before ready result supported
  exact handler_identity setup codec checks context Q j
    (factorServices setup codec checks context (PqxdhServerAuthCtxMaterial.output key rest))
    (factor_tail setup codec checks context _) server beacon query
    (PqxdhServerAuthCtxState.project (state, before.2)) invariant _ reached

/-- The actual second-session checkpoint preserves both identities, including its explicit refusal result. -/
theorem observed_stopped (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput)
    (Q : Nat) (j : Fin (Q + 1)) (query : ServerAuthSpec.Domain)
    (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (state : Local KemSK × Option Nat) (before : Observed)
    (valid : PqxdhServerAuthCtxReserve.Valid (state, before.2))
    (invariant : Invariant server beacon state.1.1.1)
    (result : (Option (ServerAuthSpec.Range query) × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run.run state)).run before)) :
    Invariant server beacon result.1.2.1.1.1 := by
  change result ∈ support ((simulateQ
    (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
      setup.source.crypto key)
    ((PqxdhServerAuthCtxReserve.stopped
      (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j) query).run state)).run before) at supported
  simp only [PqxdhServerAuthCtxReserve.stopped, stopped_step, simulateQ_map,
    StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  have kept := observed_step setup codec checks context rest key Q j query server beacon state.1 before
    (PqxdhServerAuthCtxReserve.valid_ready query (state, before.2) valid) invariant inner reached
  simpa only [observe_state] using kept

/-- Complete adaptive interpretation preserves both target identities through normal replies and terminal refusal; the concrete reservation is propagated only while the client continues. -/
theorem interpreted_program {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (rest : PqxdhServerAuthCtxCalls.Residual)
    (key : RootOutput) (Q : Nat) (j : Fin (Q + 1)) (work : OracleComp ServerAuthSpec Result)
    (server : pqxdh.ServerBinding) (beacon : PqxdhBeaconPhase2Preparation.Word32)
    (state : PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (valid : PqxdhServerAuthCtxReserve.Valid (state.1, state.2.2))
    (invariant : Invariant server beacon state.1.1.1.1)
    (result : Option Result × PqxdhServerAuthCtxObserverHistory.ObservedState KemSK)
    (supported : result ∈ support ((simulateQ
      (PqxdhServerAuthCtxObserverHistory.interpreted setup codec checks context rest key Q j) work).run.run state)) :
    Invariant server beacon result.2.1.1.1.1 := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
    simp only [simulateQ_pure, OptionT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact invariant
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, OptionT.run_bind, Option.elimM,
      StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨middle, reached, supported⟩ := supported
    simp only [PqxdhServerAuthCtxObserverHistory.interpreted, OptionT.run_mk,
      PqxdhSelectedStateInterpreter.evaluate, StateT.run, support_map, Set.mem_image] at reached
    obtain ⟨inner, reached, rfl⟩ := reached
    have kept := observed_stopped setup codec checks context rest key Q j query server beacon
      state.1 state.2 valid invariant inner reached
    cases reply : inner.1.1 with
    | none =>
      simp only [PqxdhSelectedStateInterpreter.pair, reply, Option.elim_none,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact kept
    | some answer =>
      simp only [PqxdhSelectedStateInterpreter.pair, reply, Option.elim_some] at supported
      exact ih answer (inner.1.2, inner.2)
        (PqxdhServerAuthCtxObserverHistory.stopped_valid setup codec checks context rest key Q j query
          state.1 state.2 valid inner reached answer reply) kept supported

/-- Literal sampled initialization discharges all control and reservation premises for the complete observed executable, including a journaled adversary and any optional outcome. -/
theorem observed_initial {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (context : Context KemSK) (sampled : context ∈ support (contextSample setup codec))
    (rest : PqxdhServerAuthCtxCalls.Residual) (key : RootOutput) (Q : Nat) (j : Fin (Q + 1))
    (work : OracleComp ServerAuthSpec Result)
    (result : (Option Result × (Local KemSK × Option Nat)) × Observed)
    (supported : result ∈ support ((simulateQ
      (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
        setup.source.crypto key)
      ((simulateQ (PqxdhServerAuthCtxReserve.stopped
        (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run.run
        (PqxdhServerAuthCtxReserve.initial setup context).1)).run
      (RawCtxSelectedAuthenticationObserver.initialState, AdaptiveCtxDynamicKnownKeys.initialSource))) :
    Invariant (binding setup (context.publicValue setup))
      (PqxdhRootTableInitialization.rootArray (setup.joint.publicKeys context.beaconSeed).ed25519)
      result.1.2.1.1.1 := by
  have evaluated : (result.1.1, (result.1.2, result.2)) ∈ support
      ((PqxdhSelectedStateInterpreter.evaluate
        (RawCtxSelectedAuthenticationObserver.observed true (RawCtxUniversalDecoder.decoder codec.frameRead)
          setup.source.crypto key)
        (simulateQ (PqxdhServerAuthCtxReserve.stopped
          (PqxdhServerAuthCtxHandler.handler setup codec checks context rest Q j)) work).run).run
          (PqxdhServerAuthCtxObserverHistory.initial setup context)) := by
    change (result.1.1, (result.1.2, result.2)) ∈ support (PqxdhSelectedStateInterpreter.pair <$> _)
    rw [support_map]
    exact ⟨result, supported, rfl⟩
  rw [PqxdhServerAuthCtxObserverHistory.program_interpreted] at evaluated
  exact interpreted_program setup codec checks context rest key Q j work _ _
    (PqxdhServerAuthCtxObserverHistory.initial setup context)
    (PqxdhServerAuthCtxReserve.initial_valid setup context)
    (context_identity setup codec context sampled) _ evaluated

end BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.phase1_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.phase1_control
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.prefix_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.prefix_admitted
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.opening_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.opening_ad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_ad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.native_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.native_ad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.control_ad' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.control_ad
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.finish_invariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.finish_invariant
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_tail' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.factor_tail
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.finish_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.finish_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.skeleton_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.skeleton_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.handler_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.handler_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.program_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.program_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.context_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.context_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.initial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.initial_identity
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_step
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_stopped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_stopped
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.interpreted_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.interpreted_program
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconIdentity.observed_initial
