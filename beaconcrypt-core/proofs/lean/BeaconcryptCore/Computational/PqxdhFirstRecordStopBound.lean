import BeaconcryptCore.Computational.PqxdhFirstBeaconRecordIntegrity
import BeaconcryptCore.Computational.PqxdhFirstRecordNonceStop
/-!
First steps towards a statistical bound on the restricted stop term `stopMass` of `PqxdhFirstBeaconRecordIntegrity` (first record of Beacon `b`, number one, no ancestors and no disclosures).

Moving the stop term to the source-only run. `stopGame_le` shows that `stopMass`, the `true` mass of `PqxdhFirstBeaconRecordIntegrity.stopGame`, is at most the `true` mass of the explicit game `sourceStopGame`. That game draws the same samples as `stopGame` (actual preparation, 64-byte initializer block, selected nonce, next chain and key) and runs the same selected first Server builder. It then runs the history-extended original source post `PqxdhFirstRecordNonceStop.sourceObserved`, which has no CTX challenger and no selected-nonce ledger, from the builder's front and local state. Its event is that two ordered sealing positions of the history use the exact selected sending chain (`RepeatedInput`) while, at the end of the run, the selected chain and the target's ancestors are still undisclosed. The generic step `kept_input_bound` is C3's `source_input_bound` with an arbitrary predicate of the final projected source state kept on both sides; the only premise is an empty selected-nonce ledger, which holds for the CTX start state by `rfl`. `first_beacon_source_le` restates C4's `first_beacon_forgery_le` with `sourceStopGame` in place of `stopGame`.

No clones of the selected Beacon. A finish is marked (installs the selected chain) only if its prepared root carries the challenge marker. `existing_unchallenged` shows that the actual prepared preparation callback never answers a decapsulation at an existing (environment) KEM handle with the challenge marker, so `existing_unmarked` (through the generic `prepare_unmarked`) shows that no successful Phase-2 preparation of a Beacon holding an existing KEM handle carries the selected-message marker, whatever the raw response and its Diffie-Hellman handles. `front_only` shows that in every supported pending prepared context of the stop games only slot zero, the freshly generated Beacon, can hold a generated KEM handle: environment Beacons are embedded with existing handles and no Phase-2 record, reveal, selector or native finish of the prefix copies a KEM handle into another slot (`start_only`, `compiler_only`, `driver_only`, `prepare_only`). `build_only` shows that the selected first Server builder keeps this property. Hence the clone obstruction noted in `PqxdhFirstRecordNonceStop` (two Beacons of the prepared front finishing on the selected message) is excluded by handle allocation and needs no environment premise, once the following post-level facts, not formalized here, are added: every operation of the source post keeps every slot other than slot zero free of generated KEM handles; the finish of `PqxdhSelectedInitialOwnerCompiler` at a slot runs this preparation through the lifted callback on that slot's own KEM handle and installs the selected kernel only when the marker is set; and a finish attempt leaves the initSent phase (established on success, aborted on failure), to which no post operation returns. This module adds no premise.

Limits: `sourceStopGame` is not bounded here. The remaining lemma needs a target-free observer: a version of the source-only builder and post in which the selected chain is a symbolic tag (in the Server peer's receive kernel after the builder, in slot zero's sending kernel after its marked finish, and at the programmed private derivation), shown equal to the concrete run until a private derivation on a concrete chain equal to the selected chain or a reveal of the tag. With the selected half drawn after that observer (independent of the opposite half, the prepared context, nonce, next chain and key), `RawCtxSelectedInputCandidates.uniform_candidates` would then bound `sourceStopGame` by the number of concrete private derivations divided by 2^256, which is expected to be at most one (the builder's send on the opposite half) plus the post send budget plus 51 times the post raw-receive and finish budgets of the certificate. The facts above, completed by the post-level facts listed in the previous paragraph, would supply the one-shot uniqueness of the tagged sending kernel; the tagged interpreter itself touches every role, kernel and finish operation and is not built here.
-/
open OracleComp OracleSpec CoreModels Aeneas ENNReal
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhFirstRecordStopBound
open PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhNativeSharedPrefix
open RawCtxSelectedParentTable RawCtxSelectedParentEntry
open PqxdhSelectedPostCompiler (Optional Full)

section Generic
variable {ι I D K X Response Shared A N C M P Result : Type} {extra : OracleSpec ι} {S B : Nat}

/-- Two ordered sealing positions at the selected sending chain are decided classically. -/
noncomputable instance repeatedDecidable (target : RootOutput) :
    DecidablePred (RawCtxSelectedSourceSendInputs.RepeatedInput (Owner := RawCtxProtocolReveals.Owner S B) target) :=
  fun _ => Classical.propDecidable _

variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (ExternalState A N C) ProbComp))
    (application : Response → LocalCallback A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → LocalCallback A N C PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N C) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N C) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (parent : Option Entry) (key target : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (read : RawCtxReceive.FrameDecoder)

/-- The selected-nonce stop flag together with any predicate of the final projected source state is at most, with coefficient one, two ordered sealing positions at the exact selected sending chain together with the same predicate, in the history-extended original source post (no CTX component and no selected-nonce ledger) started from the projected state. -/
theorem kept_input_bound (client : OracleComp (Optional (PqxdhInitialGenericPost.Spec extra S B)) Result)
    (before : Full M P I D K A N C S B) (empty : before.2.selected.1.usedNonces = [])
    (kept : PqxdhSelectedPostCompiler.SourceState M P I D K A N C S B → Prop) [DecidablePred kept] :
    𝒟[(fun result => result.2.2 && decide (kept (PqxdhSelectedPostCompiler.project result.2.1))) <$>
      (simulateQ (RawCtxSelectedFamilyNonceCoupling.marked
        (PqxdhSelectedPostCompiler.augmented pre application initial selector aux source writer prior parent key target nonce next
          sender route read)
        (PqxdhSelectedPostCompiler.Stops (extra := extra) prior parent target nonce next sender)) client).run (before, false)] {true} ≤
      𝒟[(fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1 ∧ kept result.2.2)) <$>
        (simulateQ (PqxdhFirstRecordNonceStop.sourceObserved pre application initial selector aux source writer prior parent key target
          nonce next sender route read) client).run ([], PqxdhSelectedPostCompiler.project before)] {true} := by
  have flags := congrArg (fun work => (fun result => result.2.2 && decide (kept (PqxdhSelectedPostCompiler.project result.2.1))) <$> work)
    (PqxdhFirstRecordNonceStop.marked_program_erased pre application initial selector aux source writer prior parent key target
      nonce next sender route read client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq, PqxdhFirstRecordNonceStop.forgetHistory] at flags
  rw [← flags]
  have projected := congrArg (fun work => (fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1 ∧
      kept result.2.2)) <$> work)
    (PqxdhFirstRecordNonceStop.source_observed_program pre application initial selector aux source writer prior parent key target
      nonce next sender route read client ([], before))
  simp only [Functor.map_map, Prod.map_def, id_eq, PqxdhFirstRecordNonceStop.projectObserved] at projected
  rw [← projected]
  have histories := congrArg (fun work => (fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput target result.2.1 ∧
      kept (PqxdhSelectedPostCompiler.project result.2.2))) <$> work)
    (RawCtxSelectedFamilyNonceCoupling.marked_client
      (PqxdhFirstRecordNonceStop.observed pre application initial selector aux source writer prior parent key target nonce next
        sender route read)
      (PqxdhFirstRecordNonceStop.observedStops (extra := extra) prior parent target nonce next sender) client (([], before), false))
  simp only [Functor.map_map, Prod.map_def, id_eq] at histories
  rw [← histories]
  rw [← prEvent_eq_evalDist_singleton _ true, ← prEvent_eq_evalDist_singleton _ true, prEvent_map, prEvent_map]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  apply prEvent_mono_of_support
  intro result supported holds
  have consistent := PqxdhFirstRecordNonceStop.marked_program_consistent pre application initial selector aux source writer
    prior parent key target nonce next sender route read client (([], before), false) result supported
    ⟨RawCtxSelectedSendTrace.tracked_empty before.2 empty, fun _ impossible => False.elim (List.not_mem_nil impossible),
      fun impossible => False.elim (Bool.false_ne_true impossible)⟩
  exact ⟨PqxdhFirstRecordNonceStop.routed_input prior parent target nonce next result.2.1.1 consistent.2.1
    (consistent.2.2 holds.1), holds.2⟩

end Generic

/-- A Boolean game whose continuation is pointwise dominated by another continuation is dominated by the other game. -/
theorem bind_le {α : Type} (mx : ProbComp α) (f g : α → ProbComp Bool) (le : ∀ a, 𝒟[f a] {true} ≤ 𝒟[g a] {true}) :
    𝒟[mx >>= f] {true} ≤ 𝒟[mx >>= g] {true} := by
  have pointwise : ∀ a, Pr{let x ← f a}[x = true] ≤ Pr{let x ← g a}[x = true] := fun a => by
    rw [prEvent_eq_evalDist_singleton, prEvent_eq_evalDist_singleton]
    exact le a
  rw [← prEvent_eq_evalDist_singleton (mx >>= f), ← prEvent_eq_evalDist_singleton (mx >>= g)]
  simp only [OracleComp.prEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (pointwise a) zero_le

section First
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhFirstBeaconRecordIntegrity (Built firstBuild startOf stopRun Undisclosed)
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}
variable
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
    (before : PqxdhInitialOriginPostPath.Front M P I D K S B) (selected : RawCtxProtocolReveals.Owner S B)
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)

/-- The source-only restricted repetition run: after the selected first Server builder, the history-extended original source post (no CTX component, no selected-nonce ledger) runs from the builder's front and local state, and the event is that two ordered sealing positions of its history use the exact selected sending chain while, at its end, the selected chain and the listed ancestors are still undisclosed. -/
noncomputable def sourceStopRun (ancestors disclosed : List RatchetChain) : ProbComp Bool := do
  let built ← firstBuild pre application initial selector aux source writer previousRoot response64 sender index metadata ready
    before selected shared privateState cache store key nonce next
  (fun result => decide (RawCtxSelectedSourceSendInputs.RepeatedInput (PqxdhInitialSourceExperiment.root source previousRoot response64 selected)
      result.2.1 ∧ Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed result.2.2)) <$>
    (simulateQ (PqxdhFirstRecordNonceStop.sourceObserved pre application initial selector aux source writer (productionStream source.crypto) none key
      (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode)
      (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1))).run ([], (built.1.2, built.2))

/-- The restricted stop run of `PqxdhFirstBeaconRecordIntegrity` is at most the source-only restricted repetition run, pointwise in every sample. -/
theorem stop_le (ancestors disclosed : List RatchetChain) :
    𝒟[stopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} ≤
    𝒟[sourceStopRun pre application initial selector aux source writer previousRoot response64 sender route decode index metadata ready
      post before selected shared privateState cache store key nonce next ancestors disclosed] {true} := by
  unfold stopRun sourceStopRun
  refine bind_le _ _ _ fun built => ?_
  exact kept_input_bound pre application initial selector aux source writer (productionStream source.crypto) none key
    (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) nonce next sender route decode
    (RawCtxSelectedFamilyNonceCoupling.optionalClient (post built.1.1)) (startOf built) rfl
    (Undisclosed (PqxdhInitialSourceExperiment.root source previousRoot response64 selected) ancestors disclosed)

end First

section KemSlots
open PqxdhGeneratedBeaconState (KemHandle IdentityHandle)
open PqxdhPhase2KemProvenance (Owner)
open PqxdhStatefulPhase1EufCma (TargetKemPublicKey)
open PqxdhPhase2SourceScheduler PqxdhPhase2SourceAux PqxdhJointKdfGame

/-- A KEM handle that was carried over from the environment's initial state, not freshly generated. -/
def ExistingKem {K : Type} : KemHandle K → Prop
  | .existing _ => True
  | .generated _ _ => False

/-- The owner's phase holds no freshly generated KEM handle (phases without a KEM handle qualify). -/
def Retains {D K Kernel : Type} (phase : RawCtxBeaconLifecycle.Phase D (KemHandle K) Kernel) : Prop :=
  PqxdhPhase2KemProvenance.Phase ExistingKem phase

/-- Every Beacon slot other than slot zero holds no freshly generated KEM handle. -/
def OnlyFirst {D K Kernel : Type} {B : Nat} (phase : Fin (B + 1) → RawCtxBeaconLifecycle.Phase D (KemHandle K) Kernel) : Prop :=
  ∀ position, position ≠ 0 → Retains (phase position)

/-- Holding no generated KEM handle is the same as naming two different designated generation indices at once. -/
theorem retains_iff {I D K : Type} (publicKey : TargetKemPublicKey) (state : RawCtxBeaconLifecycle.State I D (KemHandle K)) :
    Retains state.beacon.phase ↔ Owner 1 publicKey state ∧ Owner 2 publicKey state := by
  rcases state with ⟨⟨identity, keyId, serverIdentity, phase⟩, attempts⟩
  cases phase <;> simp only [Retains, Owner, PqxdhPhase2KemProvenance.Phase, and_self]
  all_goals
    rename_i key
    cases key <;> simp [ExistingKem, PqxdhPhase2KemProvenance.Key]
    intro first _ second
    omega

/-- A fixed public key used only to name designated generation indices in `retains_iff`. -/
def witnessKey : TargetKemPublicKey := List.Vector.replicate 1184 0

/-- Holding no generated KEM handle depends only on the retained private role fields. -/
theorem retained_retains {I D K : Type} (before after : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Retains before.beacon.phase)
    (retained : RawCtxBeaconLifecycle.retained after = RawCtxBeaconLifecycle.retained before) :
    Retains after.beacon.phase := by
  have old := (retains_iff witnessKey before).mp valid
  exact (retains_iff witnessKey after).mpr ⟨PqxdhPhase2KemProvenance.retained_valid 1 witnessKey before after old.1 retained,
    PqxdhPhase2KemProvenance.retained_valid 2 witnessKey before after old.2 retained⟩

/-- An actual native Beacon finish never introduces a generated KEM handle. -/
theorem native_retains {I D K A X Response ι : Type} {base : OracleSpec ι}
    (handler : QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec I D (KemHandle K) X Response)
      (StateT A (OracleComp base)))
    (decodeFrame : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (state : RawCtxBeaconLifecycle.State I D (KemHandle K))
    (valid : Retains state.beacon.phase) (auxiliary : A)
    (result : (Option Pqxdh.Bytes × RawCtxBeaconLifecycle.State I D (KemHandle K)) × A)
    (supported : result ∈ support ((simulateQ handler
      (PqxdhBeaconPhase2Publication.nativeOwner decodeFrame raw state)).run auxiliary)) :
    Retains result.1.2.beacon.phase := by
  have old := (retains_iff witnessKey state).mp valid
  exact (retains_iff witnessKey result.1.2).mpr
    ⟨PqxdhPhase2KemProvenance.native_valid handler 1 witnessKey decodeFrame raw state old.1 auxiliary result supported,
      PqxdhPhase2KemProvenance.native_valid handler 2 witnessKey decodeFrame raw state old.2 auxiliary result supported⟩

/-- Simulating into another oracle computation never adds outputs. -/
private theorem support_simulation {κ μ Result : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (OracleComp target)) (work : OracleComp source Result) :
    support (simulateQ impl work) ⊆ support work := by
  have kept := support_simulateQ_run'_subset (impl.liftTarget (StateT Unit (OracleComp target))) work ()
  simpa [simulateQ_liftTarget, StateT.run'_eq, liftM_run_StateT] using kept

/-- The result of a stateful simulation is an output of the simulated computation. -/
private theorem support_state_simulation {κ μ Result Aux : Type} {source : OracleSpec κ} {target : OracleSpec μ}
    (impl : QueryImpl source (StateT Aux (OracleComp target))) (work : OracleComp source Result)
    (state : Aux) (result : Result × Aux) (supported : result ∈ support ((simulateQ impl work).run state)) :
    result.1 ∈ support work := by
  apply support_simulateQ_run'_subset impl work state
  rw [StateT.run'_eq, support_map]
  exact Set.mem_image_of_mem _ supported

variable {ι M P I D K X Response A : Type} {baseSpec : OracleSpec ι} {S B : Nat}

/-- Actual indexed record and public calls keep every slot other than slot zero free of generated KEM handles. -/
theorem role_step_only (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S (B + 1)).Domain)
    (state : RawCtxProtocolRoles.State M P I D (KemHandle K) S (B + 1) × RawCtxSharedPrimitive.SharedState A)
    (valid : OnlyFirst (fun position => (state.1.2 position).beacon.phase))
    (result : (RawCtxProtocolRoles.SourceSpec S (B + 1)).Range query ×
      (RawCtxProtocolRoles.State M P I D (KemHandle K) S (B + 1) × RawCtxSharedPrimitive.SharedState A))
    (supported : result ∈ support ((RawCtxProtocolRoles.sourceImpl source writer S (B + 1) senderId route decodeFrame query).run state)) :
    OnlyFirst (fun position => (result.2.1.2 position).beacon.phase) := by
  rcases query with server | (beacon | publicQuery)
  all_goals simp only [RawCtxProtocolRoles.sourceImpl, StateT.run, bind_pure_comp, support_map] at supported
  all_goals obtain ⟨original, originalSupport, rfl⟩ := supported
  case inr.inl =>
    simp only [RawCtxRoleFamily.sourceFamily, bind_pure_comp, support_map] at originalSupport
    obtain ⟨localResult, localSupport, rfl⟩ := originalSupport
    have preserved := RawCtxBeaconLifecycle.source_step _ decodeFrame beacon.2 _ localResult localSupport
    intro position nonzero
    by_cases same : position = beacon.1
    · subst position
      simpa only [Function.update_self] using retained_retains _ localResult.2.1 (valid beacon.1 nonzero) preserved.2
    · simpa only [Function.update_of_ne same] using valid position nonzero
  all_goals exact valid

/-- The actual public and live-reveal interface keeps every slot other than slot zero free of generated KEM handles. -/
theorem source_step_only (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S (B + 1)).Domain)
    (state : PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S (B + 1))
    (valid : OnlyFirst (fun position => (state.roles.1.2 position).beacon.phase))
    (result : (RawCtxProtocolReveals.SourceSpec S (B + 1)).Range query ×
      PqxdhRegistrationProtocolState.State M P I D (KemHandle K) A S (B + 1))
    (supported : result ∈ support ((PqxdhRegistrationProtocolState.sourceImpl source writer senderId route decodeFrame query).run state)) :
    OnlyFirst (fun position => (result.2.roles.1.2 position).beacon.phase) := by
  cases query with
  | inl request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, bind_pure_comp, support_map, Functor.map_map] at supported
    obtain ⟨original, originalSupport, rfl⟩ := supported
    exact role_step_only source writer senderId route decodeFrame request _ valid original originalSupport
  | inr request =>
    simp only [PqxdhRegistrationProtocolState.sourceImpl, PqxdhRegistrationProtocolState.project,
      RawCtxProtocolReveals.sourceImpl, StateT.run, pure_bind, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact valid

/-- Every concrete record, forwarded selector or native finish request of the Phase-2 source scheduler keeps every slot other than slot zero free of generated KEM handles. -/
theorem compiler_step_only
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (query : (Spec baseSpec S (B + 1)).Domain) (state : State M P I D K A S (B + 1))
    (valid : OnlyFirst (fun position => (state.roles.1.2 position).beacon.phase))
    (result : (Spec baseSpec S (B + 1)).Range query × State M P I D K A S (B + 1))
    (supported : result ∈ support ((PqxdhPhase2SourceScheduler.compiler source writer senderId route decodeFrame localImpl query).run state)) :
    OnlyFirst (fun position => (result.2.roles.1.2 position).beacon.phase) := by
  rcases query with ((record | forwarded) | finish)
  · exact source_step_only source writer senderId route decodeFrame record state valid result (support_simulation _ _ supported)
  · simp only [PqxdhPhase2SourceScheduler.compiler, PqxdhProtocolSelector.compiler, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact valid
  · cases finish with
    | finish selected raw =>
      simp only [PqxdhPhase2SourceScheduler.compiler, PqxdhPhase2LiveFinish.finishImpl, StateT.run_mk, bind_pure_comp, support_map] at supported
      obtain ⟨nativeResult, nativeSupported, rfl⟩ := supported
      intro position nonzero
      by_cases same : position = selected
      · subst position
        simpa only [PqxdhPhase2LiveFinish.install, Function.update_self] using
          native_retains (sourceNative source localImpl) decodeFrame raw (state.roles.1.2 selected) (valid selected nonzero)
            state.primitive nativeResult nativeSupported
      · simpa only [PqxdhPhase2LiveFinish.install, Function.update_of_ne same] using valid position nonzero

/-- The complete adaptive Phase-2 source schedule keeps every slot other than slot zero free of generated KEM handles. -/
theorem compiler_only {Result : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (senderId : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decodeFrame : RawCtxReceive.FrameDecoder)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (client : OracleComp (Spec baseSpec S (B + 1)) Result) (state : State M P I D K A S (B + 1))
    (valid : OnlyFirst (fun position => (state.roles.1.2 position).beacon.phase)) (result : Result × State M P I D K A S (B + 1))
    (supported : result ∈ support ((simulateQ (PqxdhPhase2SourceScheduler.compiler source writer senderId route decodeFrame localImpl) client).run state)) :
    OnlyFirst (fun position => (result.2.roles.1.2 position).beacon.phase) := by
  induction client using OracleComp.inductionOn generalizing state result with
  | pure value =>
    obtain rfl := OracleComp.eq_of_mem_support_pure _ supported
    exact valid
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨intermediate, first, rest⟩ := supported
    exact ih intermediate.1 intermediate.2
      (compiler_step_only source writer senderId route decodeFrame localImpl query state valid intermediate first) result rest

/-- Carrying an environment owner into the extended family tags its KEM handle as existing. -/
theorem existing_retains {I D K : Type} (beacon : RawCtxBeaconLifecycle.State I D K) :
    Retains (PqxdhBeaconPhase1Publication.mapState (PqxdhGeneratedBeaconState.IdentityHandle.existing (PriorIdentity := I))
      (KemHandle.existing (PriorKem := K)) beacon).beacon.phase := by
  rcases beacon with ⟨⟨identity, keyId, serverIdentity, phase⟩, attempts⟩
  cases phase <;> simp [Retains, PqxdhPhase2KemProvenance.Phase, PqxdhBeaconPhase1Publication.mapState,
    PqxdhBeaconPhase1Publication.mapPhase, ExistingKem]

/-- Changing only the kernel representation keeps the KEM handle of every phase. -/
theorem map_retains {D K Kernel Other : Type} (interpret : Kernel → Other)
    (phase : RawCtxBeaconLifecycle.Phase D (KemHandle K) Kernel) (valid : Retains phase) :
    Retains (RawCtxGenericRoleStorage.mapPhase interpret phase) := by
  cases phase <;> simp only [Retains, PqxdhPhase2KemProvenance.Phase, RawCtxGenericRoleStorage.mapPhase] at valid ⊢ <;> exact valid

/-- Installing the freshly generated Beacon at slot zero leaves every other slot with an existing KEM handle. -/
theorem start_only {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (writer : QueryImpl PqxdhBeaconPhase1Publication.WriterSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (index : Nat) (identity : PqxdhJointIdentity.PublicIdentity) (generated : PqxdhPrivateKemSource.Generated setup Unit)
    (binding : pqxdh.ServerBinding) (bundle : PqxdhEd25519EufCma.Phase1Candidate)
    (state : PqxdhGeneratedBeaconState.InitialState setup M P I K A S B)
    (result : Option Pqxdh.Bytes × PqxdhGeneratedBeaconState.State setup M P I K A S (B + 1))
    (supported : result ∈ support (PqxdhGeneratedBeaconState.start setup writer index identity generated binding bundle state)) :
    OnlyFirst (fun position => (result.2.roles.1.2 position).beacon.phase) := by
  unfold PqxdhGeneratedBeaconState.start at supported
  obtain ⟨inner, _, rfl⟩ := OracleComp.mem_support_map_peel _ _ supported
  intro position nonzero
  obtain ⟨prior, rfl⟩ := Fin.exists_succ_eq.mpr nonzero
  simp only [PqxdhGeneratedBeaconState.reinstall, Function.update_of_ne nonzero, PqxdhGeneratedBeaconState.extend,
    Fin.cons_succ, PqxdhGeneratedBeaconState.existing]
  exact existing_retains _

set_option backward.isDefEq.respectTransparency false in
/-- Every supported result of the generated-Beacon driver leaves every slot other than slot zero with an existing KEM handle. -/
theorem driver_only {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhPhase2GeneratedDriver.Environment setup M P I K X Response A S B)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (index : Nat) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (generated : PqxdhPrivateKemSource.Generated setup Unit) (transcript : PqxdhEd25519EufCma.Phase1PublicTranscript setup.Context)
    (result : PqxdhEd25519EufCma.Phase1Candidate × (PqxdhPhase2GeneratedDriver.driver env program).State)
    (supported : result ∈ support ((PqxdhPhase2GeneratedDriver.driver env program).main index publicIdentity generated transcript)) :
    OnlyFirst (fun position => (result.2.2.roles.1.2 position).beacon.phase) := by
  simp only [PqxdhPhase2GeneratedDriver.driver, mem_support_bind_iff] at supported
  obtain ⟨started, startSupport, selected, selectedSupport, finalSupport⟩ := supported
  obtain rfl := OracleComp.eq_of_mem_support_pure _ finalSupport
  have initial := start_only env.phase1Writer index publicIdentity generated env.binding
    (PqxdhGeneratedBeaconSelector.bundle transcript) env.initial started (support_simulation _ _ startSupport)
  exact compiler_only env.source env.recordWriter env.senderId env.route env.decode env.localImpl _ started.2 initial selected
    selectedSupport

/-- A pending mode of the authenticated-root dispatch carries exactly the prepared prefix it was given. -/
theorem dispatch_pending {KemSK : Type} {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec} {Selection : Type}
    (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK)) (parameters : PqxdhPrivateRootSource.Parameters baseSpec)
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : PqxdhJointIdentity.Primitives)
    (observer : PqxdhPrivateAcceptedRoot.Continuation setup Selection) (prepared : PqxdhPrivateRootSource.Prepared setup Selection)
    (other : PqxdhPrivateRootSource.Prepared setup Selection) (ephemeral : List.Vector UInt8 32)
    (supported : PqxdhPrivateRootSource.Mode.pending other ephemeral ∈
      support (PqxdhPrivateAcceptedRoot.dispatch kem parameters attachedVerify primitives setup observer prepared)) :
    other = prepared := by
  unfold PqxdhPrivateAcceptedRoot.dispatch at supported
  split_ifs at supported
  · simp at supported
  · simp only [mem_support_bind_iff] at supported
    obtain ⟨drawn, _, supported⟩ := supported
    split at supported
    · simp only [support_pure, Set.mem_singleton_iff, PqxdhPrivateRootSource.Mode.pending.injEq] at supported
      exact supported.1
    · simp at supported
  · simp at supported

set_option backward.isDefEq.respectTransparency false in
/-- In every supported prepared context of the authenticated-root experiment with a pending mode, every Beacon slot of the prepared protocol state other than slot zero holds an existing KEM handle. -/
theorem prepare_only {KemSK : Type} {setup : PqxdhStatefulPhase1EufCma.StatefulPhase1Setup baseSpec}
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : PqxdhKemIndCca.MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : PqxdhEd25519EufCma.Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : PqxdhJointIdentity.Primitives)
    (program : PqxdhPhase2GeneratedDriver.Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (context : PqxdhCorrelatedExtractFamily.Prepared (PqxdhAuthenticatedRootExperiment.protocol env kem attachedVerify primitives program post) KemSK)
    (supported : context ∈ support (PqxdhCorrelatedExtractFamily.prepare baseImpl kem
      (PqxdhAuthenticatedRootExperiment.protocol env kem attachedVerify primitives program post)))
    (prepared : PqxdhPrivateRootSource.Prepared setup (PqxdhPhase2GeneratedDriver.driver env.toDriverEnvironment program).State)
    (ephemeral : List.Vector UInt8 32) (pending : context.state = .pending prepared ephemeral) :
    OnlyFirst (fun position => (prepared.1.context.selection.2.roles.1.2 position).beacon.phase) := by
  simp only [PqxdhCorrelatedExtractFamily.prepare, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨pair, _, state, stateSupported, encapsulated, _, rfl⟩ := supported
  have inner := support_simulation _ _ (support_simulation _ _ stateSupported)
  simp only at pending
  subst pending
  simp only [PqxdhAuthenticatedRootExperiment.protocol, mem_support_bind_iff] at inner
  obtain ⟨prefixResult, prefixSupported, dispatched⟩ := inner
  obtain rfl := dispatch_pending kem _ attachedVerify primitives _ prefixResult prepared ephemeral dispatched
  simp only [PqxdhGeneratedRootSource.borrowedPrefix, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at prefixSupported
  obtain ⟨seed, _, before, _, after, _, selected, selectedSupport, rfl⟩ := prefixSupported
  exact driver_only env.toDriverEnvironment program 0 _ _ _ selected.1 (support_state_simulation _ _ _ _ selectedSupport)

end KemSlots

section Built
open PqxdhGeneratedBeaconState (KemHandle)
open PqxdhNativeSharedPrefix PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhCorrelatedExpand PqxdhSelectedFirstRecord
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The selected first Server builder rewrites only the selected Server slot of the front, so every Beacon slot other than slot zero that held no generated KEM handle before the builder still holds none in every supported builder result. -/
theorem build_only
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D (KemHandle K) X Response PqxdhPhase2DecapsulationRouting.Shared)
      (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (application : Response → LocalCallback A N RootOracle.QueryCache (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared →
      LocalCallback A N RootOracle.QueryCache PqxdhInitialNativeAudit.InitialReply)
    (selector : QueryImpl extra (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT (ExternalState A N RootOracle.QueryCache) ProbComp))
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (previousRoot : RootOutput) (response64 : PqxdhInitialRootLabelService.Response) (sender : M → Std.U64)
    (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
    (before : PqxdhInitialOriginPostPath.Front M P I D (KemHandle K) S (B + 1)) (selected : RawCtxProtocolReveals.Owner S (B + 1))
    (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)
    (store : RawCtxSelectiveChainGame.Store) (key : RootOutput) (nonce : NonceOutput) (next : RootOutput)
    (valid : OnlyFirst (fun position => (before.roles.1.2 position).beacon.phase))
    (built : PqxdhFirstBeaconRecordIntegrity.Built M P I D (KemHandle K) A N S (B + 1))
    (supported : built ∈ support (PqxdhFirstBeaconRecordIntegrity.firstBuild pre application initial selector aux source writer
      previousRoot response64 sender index metadata ready before selected shared privateState cache store key nonce next)) :
    OnlyFirst (fun position => (built.1.2.roles.1.2 position).beacon.phase) := by
  unfold PqxdhFirstBeaconRecordIntegrity.firstBuild selectedBuild at supported
  simp only [StateT.run_map, support_map, Set.mem_image] at supported
  obtain ⟨result, _, rfl⟩ := supported
  intro position nonzero
  rcases result with ⟨_ | _ | _, _⟩ <;>
    exact map_retains RawCtxSelectedMessageRevealInitialization.fromKernel _
      (map_retains ConcreteRatchetKernel.mk _ (valid position nonzero))

end Built

section Marker
open PqxdhBeaconPhase2Shared
open PqxdhPhase2SourceAux PqxdhEd25519EufCma PqxdhJointIdentity PqxdhPhase1AcceptanceOracle
open PqxdhKemIndCca PqxdhJointKdfGame PqxdhPrivateKemSource PqxdhInitializerSecrecy

/-- If the decapsulation callback at a KEM handle never replies with a given shared marker, the Beacon Phase-2 input collection at that handle never carries that marker. -/
theorem collect_shared {σ I D K X Response Shared : Type} (pre : QueryImpl (Spec I D K X Response Shared) (StateT σ ProbComp))
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes) (bad : Shared)
    (never : ∀ value state (reply : Option Shared × σ), reply ∈ support ((pre (.decapsulate value kem)).run state) → reply.1 ≠ some bad)
    (state : σ) (result : Option (Inputs Response Shared) × σ)
    (supported : result ∈ support ((simulateQ pre (collect identity prekey oneTime kem raw)).run state))
    (inputs : Inputs Response Shared) (found : result.1 = some inputs) : inputs.secrets.shared ≠ bad := by
  simp only [collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure, Option.elimM, simulateQ_bind,
    simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
  iterate 6
    all_goals try (
      obtain ⟨⟨_ | _, _⟩, _, supported⟩ := supported
      all_goals simp only [Option.elim, simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
        support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported)
  all_goals try (subst supported; simp at found)
  obtain ⟨⟨_ | shared, _⟩, decap, supported⟩ := supported
  all_goals simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
    support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported
  iterate 4
    all_goals try (
      obtain ⟨⟨_ | _, _⟩, _, supported⟩ := supported
      all_goals simp only [simulateQ_pure, simulateQ_bind, simulateQ_spec_query, StateT.run_pure, StateT.run_bind,
        support_pure, Set.mem_singleton_iff, mem_support_bind_iff] at supported)
  all_goals try (subst supported; simp at found)
  obtain ⟨⟨_ | _, _⟩, _, supported⟩ := supported
  all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  all_goals subst supported
  all_goals simp only [Option.some.injEq] at found
  all_goals try exact absurd found (by simp)
  subst found
  exact fun equal => never _ _ _ decap (by simp only at equal; rw [equal])

/-- If the decapsulation callback at a Beacon's KEM handle never replies with the challenge marker, no successful Phase-2 preparation of that Beacon carries the selected-message installation marker, whatever the raw response. -/
theorem prepare_unmarked {σ I D K X Response : Type}
    (pre : QueryImpl (Spec I D K X Response PqxdhPhase2DecapsulationRouting.Shared) (StateT σ ProbComp))
    (fixed : FixedHkdfSha512NoSaltSource) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (control : pqxdh.BeaconInitSent) (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (never : ∀ value state (reply : Option PqxdhPhase2DecapsulationRouting.Shared × σ),
      reply ∈ support ((pre (.decapsulate value kem)).run state) → reply.1 ≠ some .challenge)
    (state : σ) (result : Option (Prepared Response PqxdhPhase2DecapsulationRouting.Shared) × σ)
    (supported : result ∈ support ((simulateQ pre (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)).run state))
    (prepared : Prepared Response PqxdhPhase2DecapsulationRouting.Shared) (found : result.1 = some prepared) :
    PqxdhInitialSelectedOrigin.mark fixed selectedMessage prepared.root = false := by
  simp only [PqxdhBeaconPhase2Shared.prepare, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨_ | inputs, collected⟩, collectSupported, supported⟩ := supported
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst supported
    simp at found
  · have shared := collect_shared pre identity prekey oneTime kem raw .challenge never state _ collectSupported inputs rfl
    simp only [afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure,
      mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, rfl⟩ := supported
    cases admitted : admitted control inputs with
    | none => simp [admitted] at found
    | some metadata =>
      simp only [admitted, Option.map_some, Option.some.injEq] at found
      subst found
      cases secret : inputs.secrets.shared with
      | challenge => exact absurd secret shared
      | known value =>
        simp [PqxdhInitialSelectedOrigin.mark, PqxdhInitialSelectedOrigin.selectedRequest, PqxdhInitialRootLabelBridge.request,
          PqxdhBeaconPhase2Shared.prepared, secret]

variable {ι A I D K X Response KemSK : Type} {baseSpec : OracleSpec ι}

/-- The actual prepared preparation callback never answers a decapsulation at an existing KEM handle with the challenge marker: existing handles always decapsulate to a known shared secret. -/
theorem existing_unchallenged (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (value : PqxdhBeaconPhase2Preparation.Ciphertext) (prior : K)
    (state : PqxdhNativeSharedPrefix.ExternalState A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (result : Option PqxdhPhase2DecapsulationRouting.Shared ×
      PqxdhNativeSharedPrefix.ExternalState A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (supported : result ∈ support ((PqxdhPreparedPrefixCallbacks.preparation (I := I) (D := D) (X := X) (Response := Response)
      attachedVerify primitives count fixed localImpl baseImpl kem secret challenge
      (.decapsulate value (.existing prior))).run state)) :
    result.1 ≠ some .challenge := by
  simp only [PqxdhPreparedPrefixCallbacks.preparation, PqxdhPreparedPrefixCallbacks.rootLocal, StateT.run, support_map,
    Set.mem_image] at supported
  obtain ⟨inner, innerSupported, rfl⟩ := supported
  simp only [PqxdhInitialCtxFreeCallbacks.cacheFree, StateT.run, support_map, Set.mem_image] at innerSupported
  obtain ⟨core, coreSupported, rfl⟩ := innerSupported
  simp only [PqxdhInitialRootFreeCallbacks.interpreted, PqxdhInitialRootFreeCallbacks.work,
    PqxdhInitialRootFreeCallbacks.original] at coreSupported
  simp only [simulateQ_spec_query, PqxdhPhase2PostScheduler.handles, QueryImpl.apply_compose,
    PqxdhPhase2SharedKemHandles.full, PqxdhPhase2SharedKemHandles.preparation, PqxdhPhase2KemProvenance.encode,
    PqxdhBeaconPhase2Shared.preLift, PqxdhBeaconPhase2Routed.handles, StateT.run_map, simulateQ_map, support_map,
    Set.mem_image] at coreSupported
  obtain ⟨reply, _, rfl⟩ := coreSupported
  cases reply.1 <;> simp

/-- No successful Phase-2 preparation of a Beacon holding an existing KEM handle, under the actual prepared preparation callback, carries the selected-message installation marker: only a Beacon holding the freshly generated KEM handle can be finished on the selected message. -/
theorem existing_unmarked (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes)
    (primitives : Primitives) (count : Nat) (fixed : FixedHkdfSha512NoSaltSource)
    (localImpl : QueryImpl (LocalSpec I D K X Response) (StateT A ProbComp))
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (secret : KemSK) (challenge : MlKem768Ciphertext) (selectedMessage : PqxdhCorrelatedExtractFamily.Message)
    (control : pqxdh.BeaconInitSent) (identity : PqxdhGeneratedBeaconState.IdentityHandle I) (prekey oneTime : D) (prior : K)
    (raw : Pqxdh.Bytes)
    (state : PqxdhNativeSharedPrefix.ExternalState A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (result : Option (Prepared Response PqxdhPhase2DecapsulationRouting.Shared) ×
      PqxdhNativeSharedPrefix.ExternalState A (BareState count) PqxdhCorrelatedExpand.RootOracle.QueryCache)
    (supported : result ∈ support ((simulateQ (PqxdhPreparedPrefixCallbacks.preparation (I := I) (D := D) (X := X) (Response := Response)
      attachedVerify primitives count fixed localImpl baseImpl kem secret challenge)
      (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime (.existing prior) raw)).run state))
    (prepared : Prepared Response PqxdhPhase2DecapsulationRouting.Shared) (found : result.1 = some prepared) :
    PqxdhInitialSelectedOrigin.mark fixed selectedMessage prepared.root = false :=
  prepare_unmarked _ fixed selectedMessage control identity prekey oneTime _ raw
    (fun value current reply reached => existing_unchallenged attachedVerify primitives count fixed localImpl baseImpl kem secret
      challenge value prior current reply reached) state result supported prepared found

end Marker

section Prepared
open PqxdhNativeSharedPrefix PqxdhInitialBeaconAmbient PqxdhSecretInputKdf PqxdhFullSecretInputKdf PqxdhJointKdfGame PqxdhJointKdf
open PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily RawCtxSelectedParentTable PqxdhSelectedFirstRecord
open PqxdhKemIndCca PqxdhEd25519EufCma PqxdhJointIdentity PqxdhStatefulPhase1EufCma PqxdhPhase2GeneratedDriver
open PqxdhPrivateKemSource PqxdhGeneratedBeaconState PqxdhAdaptiveAcceptedResult PqxdhPhase1AcceptanceOracle
open PqxdhFirstBeaconRecordIntegrity (emptyStore stopObserve stopGame compiledGame firstBeacon forgeryPost certificate)
variable {ι M P I K X Response A KemSK : Type} {baseSpec : OracleSpec ι} {S B : Nat}
variable (setup : StatefulPhase1Setup baseSpec)
    (env : PqxdhAuthenticatedRootExperiment.Environment setup M P I K X Response A S B)
    (callbacks : PqxdhSourceAuxiliary.Callbacks A)
    (baseImpl : QueryImpl baseSpec ProbComp) (kem : MlKemScheme (baseSpec := baseSpec) (SK := KemSK))
    (attachedVerify : Ed25519PublicKey → Pqxdh.Bytes → Option Pqxdh.Bytes) (primitives : Primitives)
    (program : Program baseSpec setup.Context S (B + 1))
    (post : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))

local notation "env0" => PqxdhSourceSharedPreparation.environment setup env callbacks ∅
local notation "zeroRoot" => (List.Vector.replicate 32 0 : RootOutput)

/-- The source-only continuation of one prepared context: completed preparations give `false`; a pending preparation runs the selected first Server builder and reports whether the history-extended original source post visited the exact selected sending chain at two ordered sealing positions while, at its end, the selected chain and the target's ancestors were still undisclosed. -/
noncomputable def sourceStopObserve (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (initialBlock : HmacBlock) (nonce : NonceOutput) (chain key : RootOutput) : ProbComp Bool :=
  match PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | .inl _ => pure false
  | .inr input => sourceStopRun
      (PqxdhPreparedPrefixCallbacks.preparation attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (PqxdhPreparedPrefixCallbacks.application attachedVerify primitives 1 (env0).source (env0).localImpl baseImpl kem
        context.secretKey context.ciphertext)
      (initialLocal (A := A) (N := BareState 1) (env0).source input.selectedMessage zeroRoot
        (RawCtxSelectedInitialConstructor.response64 initialBlock))
      (PqxdhPreparedPrefixCallbacks.selectorLocal (A := A)
        (PqxdhInitialPendingCurrent.selector attachedVerify primitives 1 baseImpl kem context.secretKey context.ciphertext))
      (PqxdhPreparedPrefixCallbacks.auxiliaryLocal callbacks)
      (env0).source (env0).recordWriter zeroRoot (RawCtxSelectedInitialConstructor.response64 initialBlock)
      (env0).senderId (env0).route (env0).decode input.index input.metadata { input.ready with root := zeroRoot } input.post
      input.before input.selected input.shared input.privateState input.cache emptyStore key nonce chain
      target.ancestors target.disclosed

/-- The source-only restricted repetition game: the same samples as `stopGame` (actual preparation, 64-byte initializer block, selected nonce, next chain and key), then the source-only continuation. The CTX challenger and its selected-nonce ledger are gone; the key enters only as the programmed message key of the selected chain in the private derivations of the builder and of the source post. -/
noncomputable def sourceStopGame (target : Target S (B + 1)) : ProbComp Bool := do
  let context ← PqxdhCorrelatedExtractFamily.prepare baseImpl kem
    (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)
  let initialBlock ← $ᵗ HmacBlock
  let nonce ← $ᵗ NonceOutput
  let chain ← $ᵗ RootOutput
  let key ← $ᵗ RootOutput
  sourceStopObserve setup env callbacks baseImpl kem attachedVerify primitives program post target context initialBlock nonce chain key

/-- The restricted stop mass `stopMass` of `PqxdhFirstBeaconRecordIntegrity` is at most the source-only restricted repetition mass: two ordered sealing positions at the selected sending chain, with the selected chain and ancestors still undisclosed at the end, in the history-extended original source post after the selected first Server builder. -/
theorem stopGame_le (target : Target S (B + 1)) :
    𝒟[stopGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} ≤
    𝒟[sourceStopGame setup env callbacks baseImpl kem attachedVerify primitives program post target] {true} := by
  unfold stopGame sourceStopGame
  refine bind_le _ _ _ fun context => ?_
  refine bind_le _ _ _ fun initialBlock => ?_
  refine bind_le _ _ _ fun nonce => ?_
  refine bind_le _ _ _ fun chain => ?_
  refine bind_le _ _ _ fun key => ?_
  unfold stopObserve sourceStopObserve
  cases PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed with
  | inl _ => exact le_rfl
  | inr input => exact stop_le _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- First Beacon record integrity with the restricted stop term moved to the source-only run: the HB-112 actual game with the forgery proxy post, minus its constant-`false` continuation, is at most the compiled CTX game of `PqxdhFirstBeaconRecordIntegrity`, plus the source-only restricted repetition mass `sourceStopGame`, plus the first-record target loss and the completed-branch root loss, each the advantage of a constructed reduction. This is still an intermediate reduction: `compiledGame` and `sourceStopGame` are not yet bounded by assumption or statistical terms. -/
theorem first_beacon_source_le (post0 : PqxdhAuthenticatedRootExperiment.Post (baseSpec := baseSpec) program.Selection S (B + 1))
    (b : Fin (B + 1)) (c : PqxdhAuthenticatedRootBudgets.Certificate env0 baseImpl kem program post0)
    (compatible : PqxdhOptionalKemSource.HonestKeyCompatibility baseImpl kem (env0).native)
    (adapter : HasAttachedVerificationAdapter attachedVerify primitives.verify)
    (functional : PqxdhChallengeSecretRouting.FunctionalDecapsulation kem) (hmac : HmacSha512) (correct : SourceFullCorrect (env0).source hmac)
    (fallback : PqxdhDynamicIdentityRouting.DynamicForgery) (ordinaryFallback : Forgery) :
    (𝒟[PqxdhInitialRootEventSecrecy.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (.beacon b) 1#u64 [] []] {true}).toReal -
      (𝒟[PqxdhInitialRootEventExperiment.actual env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
        (PqxdhFirstRecordTarget.rejectAll env0 program)] {true}).toReal ≤
    (𝒟[compiledGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    (𝒟[sourceStopGame setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      (firstBeacon b)] {true}).toReal +
    PqxdhAdaptiveCoordinateSecrecy.targetLoss env0 baseImpl kem attachedVerify primitives program
      (PqxdhFirstRecordTarget.unitPost program (forgeryPost env0 program post0)) (PqxdhFirstRecordTarget.unitTargets (firstBeacon b))
      (PqxdhFirstRecordTarget.certificate env0 baseImpl kem program (forgeryPost env0 program post0)
        (certificate env0 baseImpl kem program post0 c)) hmac fallback ordinaryFallback () +
    PqxdhFirstRecordTarget.completedLoss env0 baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0)
      hmac fallback ordinaryFallback := by
  have integrity := PqxdhFirstBeaconRecordIntegrity.first_beacon_forgery_le setup env callbacks baseImpl kem attachedVerify primitives
    program post0 b c compatible adapter functional hmac correct fallback ordinaryFallback
  have moved := ENNReal.toReal_mono (PqxdhFirstRecordTarget.true_ne_top _)
    (stopGame_le setup env callbacks baseImpl kem attachedVerify primitives program (forgeryPost env0 program post0) (firstBeacon b))
  linarith

/-- In every supported prepared context with a pending mode, every Beacon slot of the prepared front used by the stop games, other than slot zero (the freshly generated Beacon), holds an existing KEM handle. With `build_only`, `existing_unmarked` and the post-level facts listed in the module documentation (not formalized here), only slot zero can ever be finished on the selected message, so two Beacons installing the selected chain through the selected message is excluded by handle allocation, without an environment premise. -/
theorem front_only (target : Target S (B + 1))
    (context : PqxdhInitialLegalObserver.Context env0 kem attachedVerify primitives program post)
    (supported : context ∈ support (PqxdhCorrelatedExtractFamily.prepare baseImpl kem
      (PqxdhAuthenticatedRootExperiment.protocol env0 kem attachedVerify primitives program post)))
    (input : PqxdhInitialPreparedSourceInput.Input (M := M) (P := P) (I := I) (K := K) (X := X) (Response := Response) (A := A)
      (S := S) (B := B) (setup := setup))
    (prepared : PqxdhInitialPreparedSourceInput.input env0 baseImpl kem attachedVerify primitives program post context
      target.owner target.number target.ancestors target.disclosed = .inr input) :
    OnlyFirst (fun position => (input.before.roles.1.2 position).beacon.phase) := by
  unfold PqxdhInitialPreparedSourceInput.input at prepared
  cases pending : context.state with
  | completed decision => simp [pending] at prepared
  | pending result ephemeral =>
    simp only [pending, Sum.inr.injEq] at prepared
    subst prepared
    have kept := prepare_only env0 baseImpl kem attachedVerify primitives program post context supported result ephemeral pending
    intro position nonzero
    exact map_retains _ _ (kept position nonzero)

end Prepared

end BeaconcryptCore.Computational.PqxdhFirstRecordStopBound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.kept_input_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.kept_input_bound

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.bind_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.bind_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.stop_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.stop_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.retains_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.retains_iff

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.retained_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.retained_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.native_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.native_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.role_step_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.role_step_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.source_step_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.source_step_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.compiler_step_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.compiler_step_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.compiler_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.compiler_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.map_retains' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.map_retains

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.start_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.start_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.driver_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.driver_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.dispatch_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.dispatch_pending

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.prepare_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.prepare_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.build_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.build_only

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.collect_shared' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.collect_shared

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.prepare_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.prepare_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_unchallenged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_unchallenged

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.existing_unmarked

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.stopGame_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.stopGame_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.first_beacon_source_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.first_beacon_source_le

/-- info: 'BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.front_only' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhFirstRecordStopBound.front_only
