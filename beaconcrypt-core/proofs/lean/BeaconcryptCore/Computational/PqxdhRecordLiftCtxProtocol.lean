-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftCtxOracle
import BeaconcryptCore.Computational.PqxdhRecordLiftProtocol

/-! The actual global protocol supplies the CTX raw-opening discipline before interpretation. Private service factoring preserves original optional replies, shared cache and attempted writer logs; operational source laws remain separate from distribution and advantage bounds. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol
open PqxdhRecordLiftInterface PqxdhRecordLiftProtocol
open PqxdhRecordLiftWorldCompiler (StoredKernel Owner)
variable {n : Nat}

/-- Only actual private opening services carry a raw-admission obligation. -/
def Admitted (read : RawCtxReceive.FrameDecoder) : Service n → Prop
  | .opening pending => PqxdhRecordLiftCtxOracle.Admitted read (.inr (.inl pending))
  | _ => True

/-- Mapping a source result does not change its emitted private service requests. -/
theorem admission_map {A B : Type} (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (ServiceSpec n) A) (f : A → B)
    (admitted : work.AllQueriesSatisfy (Admitted read)) :
    (f <$> work).AllQueriesSatisfy (Admitted read) := by
  rw [map_eq_bind_pure_comp]
  exact allQueriesSatisfy_bind admitted fun _ => by trivial

/-- The literal local-to-global service injection retains the exact opening request and its admission facts. -/
theorem local_admitted {Result : Type} (read : RawCtxReceive.FrameDecoder)
    (work : OracleComp (LocalSpec n) Result)
    (admitted : work.AllQueriesSatisfy (PqxdhRecordLiftCtxOracle.Admitted read)) :
    (simulateQ localLift work).AllQueriesSatisfy (Admitted read) := by
  induction work using OracleComp.inductionOn with
  | pure result => simp
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at admitted
      simp only [simulateQ_bind, simulateQ_spec_query]
      apply allQueriesSatisfy_bind _ (fun reply => ih reply (admitted.2 reply))
      rcases query with coordinate | (pending | pending) <;>
        simp only [localLift, allQueriesSatisfy_query_iff, Admitted]
      exact admitted.1

/-- Actual known and hidden send programs emit no raw opening. -/
theorem kernelSend_admitted (read : RawCtxReceive.FrameDecoder) (stored : StoredKernel n)
    (context : RawCtxSourceSend.SealContext) :
    (kernelSend stored context).AllQueriesSatisfy (Admitted read) := by
  cases stored with
  | known kernel => simp only [kernelSend, allQueriesSatisfy_query_bind_iff, Admitted, allQueriesSatisfy_pure,
      implies_true, and_true]
  | hidden slot kernel =>
      exact allQueriesSatisfy_bind
        (local_admitted read _ (PqxdhRecordLiftCtxOracle.send_admitted read kernel context)) fun _ => by trivial

/-- The actual hidden receive continuation uses the original frame sequence and raw context; caller-known receive remains a known native service. -/
theorem kernelReceive_admitted (read : RawCtxReceive.FrameDecoder) (stored : StoredKernel n)
    (context : RawCtxWholeOwner.OpenContext) (nonempty : context.raw.isEmpty = false)
    (decoded : read context.raw = some context.frame)
    (valid : RawCtxReceive.ValidFrame context.frame.sender context.associatedData context.frame) :
    (kernelReceive stored context.frame.sequence context).AllQueriesSatisfy (Admitted read) := by
  cases stored with
  | known kernel => simp only [kernelReceive, allQueriesSatisfy_query_bind_iff, Admitted, allQueriesSatisfy_pure,
      implies_true, and_true]
  | hidden slot kernel =>
      exact allQueriesSatisfy_bind
        (local_admitted read _ (PqxdhRecordLiftCtxOracle.receive_admitted read kernel context nonempty decoded valid))
        fun _ => by trivial

/-- The source empty-plaintext branch and every actual send have the same opening discipline. -/
theorem ownerSend_admitted (read : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (plaintext : Pqxdh.Bytes) (owner : Owner n) :
    (ownerSend sender plaintext owner).AllQueriesSatisfy (Admitted read) := by
  unfold ownerSend
  split
  · trivial
  · exact allQueriesSatisfy_bind (kernelSend_admitted read _ _) fun _ => by trivial

/-- The actual outer raw parser establishes all opening facts for any typed owner, including malformed rejection, without a reachability premise. -/
theorem ownerReceive_admitted (read : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (owner : Owner n) :
    (ownerReceive read raw owner).AllQueriesSatisfy (Admitted read) := by
  unfold ownerReceive
  by_cases empty : raw.isEmpty = true
  · simp only [empty, ite_true, allQueriesSatisfy_pure]
  · simp only [empty, Bool.false_eq_true, ite_false]
    cases decoded : read raw with
    | none => simp only [allQueriesSatisfy_pure]
    | some frame =>
        by_cases valid : RawCtxReceive.ValidFrame owner.expectedSender owner.associatedData frame
        · simp only [valid, ite_true]
          have nonempty : raw.isEmpty = false := by simpa using empty
          exact allQueriesSatisfy_bind
            (kernelReceive_admitted read owner.kernel ⟨raw, frame, owner.associatedData⟩ nonempty decoded
              ⟨rfl, valid.2⟩) fun _ => by trivial
        · simp only [valid, ite_false, allQueriesSatisfy_pure]


/-- The exact source owner dispatcher retains the parser-derived opening discipline. -/
theorem ownerStep_admitted (read : RawCtxReceive.FrameDecoder) (sender : Std.U64)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    (ownerStep sender read query owner).AllQueriesSatisfy (Admitted read) := by
  cases query with
  | inl plaintext => exact ownerSend_admitted read sender plaintext owner
  | inr raw => exact ownerReceive_admitted read raw owner

/-- Actual source publication adds only its Unit-returning tag service after the complete owner operation. -/
theorem ownerRun_admitted (read : RawCtxReceive.FrameDecoder) (tag : PqxdhDeploymentInterface.FrameTag)
    (sender : Std.U64) (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) :
    (ownerRun tag sender read query owner).AllQueriesSatisfy (Admitted read) := by
  apply allQueriesSatisfy_bind (ownerStep_admitted read sender query owner)
  intro _
  simp only [allQueriesSatisfy_query_bind_iff, Admitted, allQueriesSatisfy_pure, implies_true, and_true]

/-- Every dynamic Server route either rejects before opening or invokes the checked actual selected-owner operation. -/
theorem serverStep_admitted (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (state : Control n) :
    ((serverStep read route query).run state).AllQueriesSatisfy (Admitted read) := by
  change (serverStep read route query state).AllQueriesSatisfy _
  unfold serverStep
  cases state.server with
  | none => cases query <;> trivial
  | some server =>
      dsimp only
      rcases query with ⟨plaintext, keyId⟩ | raw
      · dsimp only
        cases server.peers keyId with
        | none => trivial
        | some peer => exact allQueriesSatisfy_bind (ownerRun_admitted read _ _ _ _) fun _ => by trivial
      · dsimp only
        cases route raw with
        | none => trivial
        | some keyId =>
            dsimp only
            cases server.peers keyId with
            | none => trivial
            | some peer => exact allQueriesSatisfy_bind (ownerRun_admitted read _ _ _ _) fun _ => by trivial

/-- Dynamic owner-list absence and inactive phases reject without opening; established owners retain the same source discipline. -/
theorem beaconStep_admitted (read : RawCtxReceive.FrameDecoder) (index : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : Control n) :
    ((beaconStep read index query).run state).AllQueriesSatisfy (Admitted read) := by
  change (beaconStep read index query state).AllQueriesSatisfy _
  unfold beaconStep
  cases state.owners[index]? with
  | none => trivial
  | some phase =>
      cases phase with
      | inactive phase => cases query <;> trivial
      | established shell kernel =>
          exact allQueriesSatisfy_bind (ownerRun_admitted read _ _ _ _) fun _ => by trivial

/-- Hidden installation requests only its actual seed allocation; caller-known kernels require no private callback. -/
theorem resolve_admitted (read : RawCtxReceive.FrameDecoder) (role : Role) (ref : KernelRef n) :
    (resolve role ref).AllQueriesSatisfy (Admitted read) := by
  cases ref <;> simp only [resolve, allQueriesSatisfy_pure, allQueriesSatisfy_query_bind_iff,
    Admitted, implies_true, and_true]

/-- Source peer admission and one-use checks do not introduce an opening request. -/
theorem installServer_admitted (read : RawCtxReceive.FrameDecoder) (keyId : Std.U64)
    (identity : RawCtxServerRouting.Identity) (ref : KernelRef n) (state : Control n) :
    ((installServer keyId identity ref).run state).AllQueriesSatisfy (Admitted read) := by
  change (installServer keyId identity ref state).AllQueriesSatisfy _
  unfold installServer
  split
  · trivial
  · split
    · exact allQueriesSatisfy_bind (resolve_admitted read _ _) fun _ => by trivial
    · trivial

/-- Source Beacon phase and one-use checks do not introduce an opening request. -/
theorem installBeacon_admitted (read : RawCtxReceive.FrameDecoder) (index : Nat)
    (shell : BeaconShell) (ref : KernelRef n) (state : Control n) :
    ((installBeacon index shell ref).run state).AllQueriesSatisfy (Admitted read) := by
  change (installBeacon index shell ref state).AllQueriesSatisfy _
  unfold installBeacon
  split
  · exact allQueriesSatisfy_bind (resolve_admitted read _ _) fun _ => by trivial
  · trivial


/-- Every administrative capability preserves the actual raw-opening discipline, including failed installation and phase changes. -/
theorem capability_admitted (read : RawCtxReceive.FrameDecoder) (query : Capability n) (state : Control n) :
    ((capability query).run state).AllQueriesSatisfy (Admitted read) := by
  cases query with
  | peerPresent keyId => trivial
  | ownerPresent index => trivial
  | appendOwner pin keyId phase => trivial
  | advanceOwner index phase =>
      change (capability (.advanceOwner index phase) state).AllQueriesSatisfy _
      dsimp only [capability]
      split
      · split <;> trivial
      · trivial
  | installServer keyId identity ref => exact installServer_admitted read keyId identity ref state
  | installBeacon index shell ref => exact installBeacon_admitted read index shell ref state
  | hash bytes => simp only [capability, StateT.run_lift, allQueriesSatisfy_query_bind_iff, Admitted,
      allQueriesSatisfy_pure, implies_true, and_true]

/-- Charging every real environment effect adds only its actual Unit service and retains the source capability dispatcher. -/
theorem effects_admitted (read : RawCtxReceive.FrameDecoder) (query : (EnvEffects n).Domain) (state : Control n) :
    ((effects query).run state).AllQueriesSatisfy (Admitted read) := by
  simp only [effects, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    allQueriesSatisfy_query_bind_iff, Admitted, true_and]
  intro _
  cases query with
  | inl coin => simp only [StateT.run_lift, allQueriesSatisfy_query_bind_iff, Admitted,
      allQueriesSatisfy_pure, implies_true, and_true]
  | inr request => exact capability_admitted read request state

/-- The complete actual dynamic WorldSpec dispatcher derives admission for every private opening, from arbitrary typed control. -/
theorem handler_admitted (read : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (state : Control n) :
    ((handler read route query).run state).AllQueriesSatisfy (Admitted read) := by
  rcases query with created | (effect | (server | ⟨owner, record⟩))
  · change (initializeServer created state).AllQueriesSatisfy _
    unfold initializeServer
    split <;> trivial
  · exact effects_admitted read effect state
  · cases server with
    | inl input => exact serverStep_admitted read route (.inl input) state
    | inr raw => exact serverStep_admitted read route (.inr raw) state
  · cases record with
    | inl plaintext => exact beaconStep_admitted read owner (.inl plaintext) state
    | inr raw => exact beaconStep_admitted read owner (.inr raw) state

/-- Every complete adaptive WorldSpec schedule inherits actual parser/validation/prepared-sequence discipline; no state-reachability premise is needed. -/
theorem schedule_admitted {Result : Type} (read : RawCtxReceive.FrameDecoder)
    (route : RawCtxServerRouting.SenderDecoder) (client : OracleComp (WorldSpec n) Result)
    (state : Control n) :
    (schedule read route client state).AllQueriesSatisfy (Admitted read) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => trivial
  | query_bind query next ih =>
      simp only [schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
      exact allQueriesSatisfy_bind (handler_admitted read route query state) fun result => ih result.1 result.2

/-- The frozen environment/adversary/secrecy-ledger program supplies the exact opening consumer facts for both security modes and every adaptive schedule. -/
theorem program_admitted {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary).AllQueriesSatisfy
      (Admitted codec.frameRead) :=
  schedule_admitted codec.frameRead route _ initialControl

open PqxdhRecordLiftCtxServices PqxdhRecordLiftLoggedAdapters
open CtxRomAuth AdaptiveCtxReceive AdaptiveCtxSharedModes AdaptiveCtxDynamicKnownKeys
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Result : Type}

/-- Caller-known native work keeps real functional KDF and AEAD calls, the shared public hash, and the actual writer attempt even on failure. -/
noncomputable def knownRom (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) :
    QueryImpl RawCtxMixedOwner.NativeSpec (StateT Frames (OracleComp CtxRO))
  | .inl request => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inl input) => pure (some (source.crypto.aeadSeal input.key input.nonce input.associatedData input.plaintext))
  | .inr (.inr (.inl input)) => pure (RawCtxSourceOpen.baseOpen source.crypto input)
  | .inr (.inr (.inr (.inl bytes))) => StateT.lift (do
      let digest ← CtxRO.query ((), bytes)
      pure (some digest.toList))
  | .inr (.inr (.inr (.inr frame))) => fun frames => pure (writer frame, frames ++ [frame])

/-- The ordinary native source interpreter and the public-ROM presentation agree on every actual query, including its complete cache and writer log. -/
theorem knownRom_step (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (query : RawCtxMixedOwner.NativeSpec.Domain) (state : CtxRO.QueryCache × Frames) :
    (loggedNative (PqxdhRecordLiftCtxServices.native setup codec) query).run state =
      (evaluateRom (knownRom setup.source codec.frameWrite query)).run state := by
  rcases query with request | (input | (input | (bytes | frame)))
  all_goals simp only [StateT.run]
  all_goals simp only [knownRom, loggedNative, evaluateRom,
    PqxdhDeploymentNative.frameLog, StateT.run_lift, StateT.run_pure, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, simulateQ_pure, StateT.run_map, Functor.map_map]
  all_goals simp only [StateT.run, simulateQ_map, simulateQ_spec_query, simulateQ_pure]
  all_goals try simp only [StateT.run, PqxdhRecordLiftCtxServices.native, PqxdhDeploymentNative.primitives,
    RawCtxMixedShared.sharedImpl, RawCtxMixedShared.sharedAdapter, QueryImpl.compose,
    simulateQ_pure, simulateQ_spec_query, RawCtxSharedPrimitive.nativeImpl,
    RawCtxSharedPrimitive.openingImpl, RawCtxSourceHkdf.kdfImpl,
    map_pure, bind_pure_comp, Functor.map_map]
  all_goals rfl

/-- Every complete caller-known native continuation retains its actual optional replies, real cache and writer frames under the public-ROM presentation. -/
theorem knownRom_program (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : CtxRO.QueryCache × Frames) :
    (simulateQ (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work).run state =
      (evaluateRom (simulateQ (knownRom setup.source codec.frameWrite) work)).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure result =>
      simp only [simulateQ_pure]
      change pure (result, state) = swapResult <$>
        (simulateQ ctxRandomOracle (pure (result, state.2))).run state.1
      simp [swapResult]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, evaluateRom_bind]
      rw [knownRom_step]
      exact bind_congr fun reply => ih reply.1 reply.2

/-- Arbitrary public-ROM work retains the exact cache and cannot change the selected nonce history. -/
theorem publicRom_state (real : Bool) (decode : RawDecoder) (crypto : Pqxdh.Crypto) (key : CtxKey)
    (work : OracleComp CtxRO Result) (before : SourceState) :
    (fun result => (result.1, (result.2.cache, result.2.selected.1.usedNonces))) <$>
      (simulateQ (sourceImpl real decode crypto key) (simulateQ publicRom work)).run before =
      (fun result => (result.1, (result.2, before.selected.1.usedNonces))) <$>
        (simulateQ ctxRandomOracle work).run before.cache := by
  rw [publicRom_complete]
  have cached := AdaptiveCtxSharedTarget.cache_schedule
    (simulateQ RawCtxSelectedMessageSealing.hashLift work) (before.cache, before.selected.1.publicInputs)
  rw [RawCtxSelectedMessageSealing.hash_interpretation] at cached
  have fact := congrArg (fun program =>
    (fun result => (result.1, (result.2, before.selected.1.usedNonces))) <$> program) cached
  simpa only [Functor.map_map, RawCtxSelectedSealConsumer.install, replaceShared,
    Prod.map_def, id_eq] using fact

/-- Complete caller-known programs forward only their real public commitment requests to the selected endpoint; their concrete KDF and AEAD inputs stay caller-known. -/
noncomputable def knownProgram (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) (work : OracleComp RawCtxMixedOwner.NativeSpec Result) :
    StateT Frames (OracleComp Spec) Result := fun frames =>
  simulateQ publicRom ((simulateQ (knownRom source writer) work).run frames)

/-- The whole known-key continuation agrees with real native execution and cannot consume a selected nonce. No byte-distinctness or nonce-uniqueness premise is used. -/
theorem knownProgram_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (decode : RawDecoder) (key : CtxKey)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (before : SourceState) (frames : Frames) :
    (fun result => (result.1.1, ((result.2.cache, result.1.2), result.2.selected.1.usedNonces))) <$>
      (simulateQ (sourceImpl true decode setup.source.crypto key)
        ((knownProgram setup.source codec.frameWrite work).run frames)).run before =
      (fun result => (result.1, (result.2, before.selected.1.usedNonces))) <$>
        (simulateQ (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work).run (before.cache, frames) := by
  have fact := congrArg (fun program =>
      (fun result => (result.1.1, ((result.2.1, result.1.2), result.2.2))) <$> program)
    (publicRom_state true decode setup.source.crypto key
      ((simulateQ (knownRom setup.source codec.frameWrite) work).run frames) before)
  rw [knownRom_program]
  simpa only [knownProgram, StateT.run, Functor.map_map, evaluateRom, swapResult] using fact

/-- The global reduction retains the actual seed cache, masked chain table, writer buffers and public effect ledger. The unavailable message key and hidden native instrumentation are absent. -/
structure Secret (n : Nat) where
  masked : PqxdhRecordLiftProjectionCut.Mask (Slot n)
  seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  pending : Frames
  effects : EffectKind → Nat

abbrev SourceSecret (n : Nat) := Secret n × (CtxRO.QueryCache × List CtxNonce)

def projectSecret (state : Secret n × SourceState) : SourceSecret n :=
  (state.1, (state.2.cache, state.2.selected.1.usedNonces))

def projectReply {Reply : Type} (result : (Reply × Secret n) × SourceState) : Reply × SourceSecret n :=
  (result.1.1, projectSecret (result.1.2, result.2))

noncomputable def seedAt (state : Secret n) : PqxdhRecordLiftChainTable.Seeds (Slot n) :=
  fun slot => (state.seeds.1 slot).getD Classical.ofNonempty

/-- Exact local private-state framing retains all other global fields, including at an explicit refusal. -/
def withLocal {m : Type → Type} [Monad m] {Reply : Type}
    (work : ExceptT Unit (StateT (PqxdhRecordLiftCtxOracle.Private (Slot n)) m) Reply) :
    ExceptT Unit (StateT (Secret n) m) Reply := ExceptT.mk fun state => do
  let result ← work.run.run (state.masked, state.pending)
  pure (result.1, { state with masked := result.2.1, pending := result.2.2 })

def withSourceLocal {Reply : Type}
    (work : ExceptT Unit (StateT (PqxdhRecordLiftCtxOracle.NativePrivate (Slot n)) ProbComp) Reply) :
    ExceptT Unit (StateT (SourceSecret n) ProbComp) Reply := ExceptT.mk fun state => do
  let result ← work.run.run ((state.1.masked, state.1.pending), state.2)
  pure (result.1, ({ state.1 with masked := result.2.1.1, pending := result.2.1.2 }, result.2.2))

def withKnown {Reply : Type}
    (work : StateT Frames (OracleComp Spec) Reply) : ExceptT Unit (StateT (Secret n) (OracleComp Spec)) Reply :=
  ExceptT.mk fun state => do
    let result ← work.run state.pending
    pure (.ok result.1, { state with pending := result.2 })

def withSourceKnown {Reply : Type}
    (work : StateT (CtxRO.QueryCache × Frames) ProbComp Reply) :
    ExceptT Unit (StateT (SourceSecret n) ProbComp) Reply := ExceptT.mk fun state => do
  let result ← work.run (state.2.1, state.1.pending)
  pure (.ok result.1, ({ state.1 with pending := result.2.2 }, (result.2.1, state.2.2)))

/-- The same ten private source services are implemented using one ordinary CTX endpoint. Public KDF, known-key AEAD and writer effects retain their literal source programs. -/
noncomputable def ctxInterpreter (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (ExceptT Unit (StateT (Secret n) (OracleComp Spec)))
  | .allocate allocated => ExceptT.mk fun state => do
      let result ← simulateQ PqxdhRecordLiftCtxOracle.coinLift
        ((PqxdhRecordLiftLazyTable.impl allocated).run state.seeds)
      pure (.ok (), { state with seeds := result.2 })
  | .coin coin => ExceptT.mk fun state => do
      let reply ← PqxdhRecordLiftCtxOracle.coinLift coin
      pure (.ok reply, state)
  | .hash bytes => ExceptT.mk fun state => do
      let reply ← publicRom ((), bytes)
      pure (.ok reply, state)
  | .charge kind => ExceptT.mk fun state => pure (.ok (), { state with
      effects := Function.update state.effects kind (state.effects kind + 1) })
  | .lookup coordinate => ExceptT.mk fun state =>
      (withLocal (PqxdhRecordLiftCtxOracle.interpreter slot source (seedAt state) ideal codec
        (.inl coordinate))).run.run state
  | .opening pending => ExceptT.mk fun state =>
      (withLocal (PqxdhRecordLiftCtxOracle.interpreter slot source (seedAt state) ideal codec
        (.inr (.inl pending)))).run.run state
  | .sealing pending => ExceptT.mk fun state =>
      (withLocal (PqxdhRecordLiftCtxOracle.interpreter slot source (seedAt state) ideal codec
        (.inr (.inr pending)))).run.run state
  | .knownSend kernel context => withKnown (knownProgram source codec.frameWrite
      (simulateQ RawCtxMixedOwner.sendAdapter (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))))
  | .knownReceive kernel target context => withKnown (knownProgram source codec.frameWrite
      (simulateQ RawCtxMixedOwner.receiveAdapter
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))))
  | .publish tag => ExceptT.mk fun state => pure (.ok (), { state with
      produced := state.produced ++ state.pending.map (fun frame => (tag, frame)), pending := [] })

/-- Literal source callbacks with the same global private fields, actual shared ROM and explicit selected nonce refusal. Only unobservable native counters and unrelated challenger histories are projected away. -/
noncomputable def sourceInterpreter (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (ExceptT Unit (StateT (SourceSecret n) ProbComp))
  | .allocate allocated => ExceptT.mk fun state => do
      let result ← (PqxdhRecordLiftLazyTable.impl allocated).run state.1.seeds
      pure (.ok (), ({ state.1 with seeds := result.2 }, state.2))
  | .coin coin => ExceptT.mk fun state => do
      let reply ← unifSpec.query coin
      pure (.ok reply, state)
  | .hash bytes => ExceptT.mk fun state => do
      let result ← (ctxRandomOracle ((), bytes)).run state.2.1
      pure (.ok result.1, (state.1, (result.2, state.2.2)))
  | .charge kind => ExceptT.mk fun state => pure (.ok (), ({ state.1 with
      effects := Function.update state.1.effects kind (state.1.effects kind + 1) }, state.2))
  | .lookup coordinate => ExceptT.mk fun state =>
      (withSourceLocal (PqxdhRecordLiftCtxOracle.nativeInterpreter setup codec (seedAt state.1) ideal key
        (.inl coordinate))).run.run state
  | .opening pending => ExceptT.mk fun state =>
      (withSourceLocal (PqxdhRecordLiftCtxOracle.nativeInterpreter setup codec (seedAt state.1) ideal key
        (.inr (.inl pending)))).run.run state
  | .sealing pending => ExceptT.mk fun state =>
      (withSourceLocal (PqxdhRecordLiftCtxOracle.nativeInterpreter setup codec (seedAt state.1) ideal key
        (.inr (.inr pending)))).run.run state
  | .knownSend kernel context => withSourceKnown
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))
  | .knownReceive kernel target context => withSourceKnown
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context)))
  | .publish tag => ExceptT.mk fun state => pure (.ok (), ({ state.1 with
      produced := state.1.produced ++ state.1.pending.map (fun frame => (tag, frame)), pending := [] }, state.2))

/-- Local stopped simulation frames the complete global seed cache, tagged history and public effect ledger without exposing hidden source counters. -/
theorem local_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (query : (PqxdhRecordLiftCtxOracle.LocalSpec (Slot n)).Domain) (state : Secret n) (before : SourceState)
    (admitted : PqxdhRecordLiftCtxOracle.Admitted codec.frameRead query) :
    projectReply <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((withLocal (PqxdhRecordLiftCtxOracle.interpreter slot setup.source (seedAt state) ideal codec query)).run.run state)).run before =
      ((withSourceLocal (PqxdhRecordLiftCtxOracle.nativeInterpreter setup codec (seedAt state) ideal key query)).run.run
        (projectSecret (state, before))) := by
  have mapApply {A B S : Type} (f : A → B) (work : StateT S ProbComp A) (s : S) :
      (f <$> work) s = (fun reply => (f reply.1, reply.2)) <$> work s := StateT.run_map _ _ _
  have fact := congrArg (fun work => (fun result =>
      (result.1, ({ state with masked := result.2.1.1, pending := result.2.1.2 }, result.2.2))) <$> work)
    (PqxdhRecordLiftCtxOracle.interpreter_source setup codec slot (seedAt state) ideal key query
      (state.masked, state.pending) before admitted)
  simpa only [withLocal, withSourceLocal, ExceptT.run, ExceptT.mk, StateT.run,
    bind_pure_comp, simulateQ_map, mapApply, Functor.map_map, projectReply, projectSecret,
    PqxdhRecordLiftCtxOracle.projectResult, PqxdhRecordLiftCtxOracle.project] using fact

/-- The complete known-key source continuation frames the same masked table and global cache, without applying the selected nonce rule to unrelated keys. -/
theorem known_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (key : CtxKey)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : Secret n) (before : SourceState) :
    projectReply <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((withKnown (knownProgram setup.source codec.frameWrite work)).run.run state)).run before =
      ((withSourceKnown (simulateQ (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work)).run.run
        (projectSecret (state, before))) := by
  have mapApply {A B S : Type} (f : A → B) (work : StateT S ProbComp A) (s : S) :
      (f <$> work) s = (fun reply => (f reply.1, reply.2)) <$> work s := StateT.run_map _ _ _
  have fact := congrArg (fun program => (fun result =>
      (Except.ok (ε := Unit) result.1, ({ state with pending := result.2.1.2 }, (result.2.1.1, result.2.2)))) <$> program)
    (knownProgram_source setup codec (RawCtxUniversalDecoder.decoder codec.frameRead) key work before state.pending)
  simpa only [withKnown, withSourceKnown, ExceptT.run, ExceptT.mk, StateT.run,
    bind_pure_comp, simulateQ_map, mapApply, Functor.map_map, projectReply, projectSecret] using fact

/-- Every one of the actual ten global services has the same optional reply and stopped source poststate under the ordinary CTX endpoint. All raw-opening side conditions are source-derived. -/
theorem query_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : Secret n) (before : SourceState)
    (admitted : Admitted codec.frameRead query) :
    projectReply <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((ctxInterpreter slot setup.source ideal codec query).run.run state)).run before =
      ((sourceInterpreter setup codec ideal key query).run.run (projectSecret (state, before))) := by
  cases query with
  | lookup coordinate => exact local_source setup codec slot ideal key (.inl coordinate) state before admitted
  | opening pending => exact local_source setup codec slot ideal key (.inr (.inl pending)) state before admitted
  | sealing pending => exact local_source setup codec slot ideal key (.inr (.inr pending)) state before admitted
  | knownSend kernel context =>
      simpa only [ctxInterpreter, sourceInterpreter, PqxdhRecordLiftWorldCompiler.sendNative,
        QueryImpl.simulateQ_compose] using
        known_source setup codec key (simulateQ RawCtxMixedOwner.sendAdapter
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))) state before
  | knownReceive kernel target context =>
      simpa only [ctxInterpreter, sourceInterpreter, PqxdhRecordLiftWorldCompiler.receiveNative,
        QueryImpl.simulateQ_compose] using
        known_source setup codec key (simulateQ RawCtxMixedOwner.receiveAdapter
          (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))) state before
  | allocate allocated =>
      simp only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
      change projectReply <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((fun result => (Except.ok (), { state with seeds := result.2 })) <$>
          simulateQ PqxdhRecordLiftCtxOracle.coinLift ((PqxdhRecordLiftLazyTable.impl allocated).run state.seeds))).run before = _
      rw [simulateQ_map, StateT.run_map, PqxdhRecordLiftCtxOracle.coin_program]
      simp only [Functor.map_map, sourceInterpreter, ExceptT.mk, StateT.run,
        bind_pure_comp, projectReply, projectSecret]
  | coin coin =>
      simp only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
      change projectReply <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((fun reply => (Except.ok reply, state)) <$> PqxdhRecordLiftCtxOracle.coinLift coin)).run before = _
      rw [simulateQ_map, StateT.run_map, PqxdhRecordLiftCtxOracle.coin_step]
      simp only [Functor.map_map, sourceInterpreter, ExceptT.mk,
        bind_pure_comp, projectReply, projectSecret]
  | hash bytes =>
      have fact := congrArg (fun program => (fun result =>
          (Except.ok (ε := Unit) result.1, (state, result.2))) <$> program)
        (publicRom_state true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
          (CtxRO.query ((), bytes)) before)
      simp only [simulateQ_spec_query] at fact
      simp only [ctxInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp]
      change projectReply <$> (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((fun reply => (Except.ok reply, state)) <$> publicRom ((), bytes))).run before = _
      rw [simulateQ_map, StateT.run_map]
      simpa only [Functor.map_map, sourceInterpreter, ExceptT.mk, StateT.run,
        bind_pure_comp, projectReply, projectSecret] using fact
  | charge kind => rfl
  | publish tag => rfl

/-- Full adaptive global continuations preserve every retained state field and stop at the exact source nonce-refusal point. Result may contain the complete environment and secrecy ledger. -/
theorem global_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : Secret n) (before : SourceState)
    (admitted : client.AllQueriesSatisfy (Admitted codec.frameRead)) :
    projectReply <$>
      (simulateQ (sourceImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        ((simulateQ (ctxInterpreter slot setup.source ideal codec) client).run.run state)).run before =
      ((simulateQ (sourceInterpreter setup codec ideal key) client).run.run (projectSecret (state, before))) := by
  induction client using OracleComp.inductionOn generalizing state before with
  | pure result => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at admitted
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxOracle.except_bind,
        simulateQ_bind, StateT.run_bind, map_bind]
      rw [← query_source setup codec slot ideal key query state before admitted.1, bind_map_left]
      apply bind_congr
      intro result
      rcases result with ⟨⟨reply, state'⟩, before'⟩
      cases reply with
      | error error => simp only [projectReply, simulateQ_pure, StateT.run_pure, map_pure]
      | ok reply => exact ih reply state' before' (admitted.2 reply)

/-- The actual reduction exposes only the ordinary selected-key CTX interface. Its input has no selected message key, while every known-key call uses the existing dynamic wrapper. -/
noncomputable def reduction (slot : Nat) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : Secret n)
    (others : ReductionState) : OracleComp ReceiveSpec ((Except Unit Result × Secret n) × ReductionState) :=
  wrapped source.crypto ((simulateQ (ctxInterpreter slot source ideal codec) client).run.run state) others

/-- The constructed reduction is exactly the same entire global stopped native continuation under the real ordinary CTX endpoint; no selected-key distribution assumption is introduced. -/
theorem reduction_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (admitted : client.AllQueriesSatisfy (Admitted codec.frameRead)) :
    (fun result => projectReply (AdaptiveCtxDynamicKnownKeys.erase result)) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec client state others)).run selected =
      (simulateQ (sourceInterpreter setup codec ideal key) client).run.run
        (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected))) := by
  have ordinary := AdaptiveCtxDynamicKnownKeys.schedule_interpretation true
    (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key
    ((simulateQ (ctxInterpreter slot setup.source ideal codec) client).run.run state) others selected
  have mapped := congrArg (fun work => projectReply <$> work) ordinary
  simp only [Functor.map_map] at mapped
  exact mapped.trans (global_source setup codec slot ideal key client state _ admitted)

/-- Every actual replicated/dynamic protocol schedule supplies admission without a separate raw-target premise, retaining its full returned environment, ledger and control. -/
theorem schedule_reduction_source (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (WorldSpec n) Result) (control : Control n) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State) :
    (fun result => projectReply (AdaptiveCtxDynamicKnownKeys.erase result)) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec (schedule codec.frameRead route client control) state others)).run selected =
      (simulateQ (sourceInterpreter setup codec ideal key) (schedule codec.frameRead route client control)).run.run
        (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected))) :=
  reduction_source setup codec slot ideal key _ state others selected
    (schedule_admitted codec.frameRead route client control)

/-- The counter-erased source view is independent of the selected key and mask. It retains all actual private bytes, shared ROM, seed accounting, writer logs and public-effect accounting. -/
structure Bare (n : Nat) where
  cache : CtxRO.QueryCache
  effects : EffectKind → Nat
  seeds : PqxdhRecordLiftLazyTable.State (PqxdhRecordLiftWorld.SeedSpec n)
  chain : PqxdhRecordLiftChainTable.Table (Slot n)
  produced : List (PqxdhDeploymentInterface.FrameTag × PqxdhDeploymentNative.Frame)
  pending : Frames

def erasePrivate (state : PqxdhRecordLiftProtocol.Private n) : Bare n :=
  ⟨state.primitive.2, state.primitive.1.effects, state.seeds, state.chain, state.produced, state.pending⟩

noncomputable def bareSeeds (state : Bare n) : PqxdhRecordLiftChainTable.Seeds (Slot n) :=
  fun slot => (state.seeds.1 slot).getD Classical.ofNonempty

def bareNative {Reply : Type} (work : StateT (CtxRO.QueryCache × Frames) ProbComp Reply) :
    StateT (Bare n) ProbComp Reply := fun state => do
  let result ← work.run (state.cache, state.pending)
  pure (result.1, { state with cache := result.2.1, pending := result.2.2 })

/-- The literal mixed-policy global source interpreter with only native/uniform analysis counters removed. It keeps the same full table, both directions, seeds and all actual native operations. -/
noncomputable def bareInterpreter (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT (Bare n) ProbComp)
  | .allocate slot => fun state => do
      let result ← (PqxdhRecordLiftLazyTable.impl slot).run state.seeds
      pure ((), { state with seeds := result.2 })
  | .coin coin => fun state => do
      let reply ← unifSpec.query coin
      pure (reply, state)
  | .hash bytes => fun state => do
      let result ← (ctxRandomOracle ((), bytes)).run state.cache
      pure (result.1, { state with cache := result.2 })
  | .charge kind => fun state => pure ((), { state with
      effects := Function.update state.effects kind (state.effects kind + 1) })
  | .lookup coordinate => fun state => do
      let result ← (PqxdhRecordLiftCtxOracle.bareLookup setup.source (bareSeeds state) ideal coordinate).run state.chain
      pure ((), { state with chain := result.2 })
  | .opening pending => fun state => (bareNative (PqxdhRecordLiftNativeAdapters.receiveOpen
      (PqxdhRecordLiftWorldCompiler.receiveNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
      (PqxdhRecordLiftMaterialTable.eraseOpening (bareSeeds state) state.chain pending))).run state
  | .sealing pending => fun state => (bareNative (PqxdhRecordLiftNativeAdapters.sendSeal
      (PqxdhRecordLiftWorldCompiler.sendNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
      (PqxdhRecordLiftMaterialTable.eraseSeal (bareSeeds state) state.chain pending))).run state
  | .knownSend kernel context => bareNative
      (simulateQ (PqxdhRecordLiftWorldCompiler.sendNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
        (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context)))
  | .knownReceive kernel target context => bareNative
      (simulateQ (PqxdhRecordLiftWorldCompiler.receiveNative (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)))
        (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context)))
  | .publish tag => fun state => pure ((), { state with
      produced := state.produced ++ state.pending.map (fun frame => (tag, frame)), pending := [] })

/-- Native writer logging cannot alter the public-effect counter function, even when the writer returns failure. -/
theorem logged_effects (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRecordLiftWorld.Primitive) (frames : Frames)
    (result : Result × (PqxdhRecordLiftWorld.Primitive × Frames))
    (supported : result ∈ support ((simulateQ (loggedNative (PqxdhRecordLiftWorld.primitives setup codec)) work).run (state, frames))) :
    result.2.1.1.effects = state.1.effects := by
  rw [program_logged, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact PqxdhRecordLiftWorldBudget.native_effects setup codec _ state inner reached

/-- Erasing only native/uniform counters retains the exact public-effect ledger, shared ROM and actual pending frames through every native continuation. -/
theorem logged_effects_erasure (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRecordLiftWorld.Primitive) (frames : Frames) :
    (fun result => (result.1, (result.2.1.1.effects, result.2.1.2, result.2.2))) <$>
      (simulateQ (loggedNative (PqxdhRecordLiftWorld.primitives setup codec)) work).run (state, frames) =
      (fun result => (result.1, (state.1.effects, result.2.1, result.2.2))) <$>
        (simulateQ (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work).run (state.2, frames) := by
  rw [← logged_counts_erasure setup codec work state frames]
  simp only [Functor.map_map, Prod.map_def, id_eq, eraseCounts]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  rw [logged_effects setup codec work state frames result supported]

/-- Every actual global native continuation erases only its native/uniform analysis counters; all source bytes, cache, seeds and tagged logs are retained. -/
theorem bare_native (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (work : OracleComp RawCtxMixedOwner.NativeSpec Result) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id erasePrivate <$>
      (PqxdhRecordLiftProtocol.withRecord (PqxdhRecordLiftProtocol.primitiveWork
        (simulateQ (PqxdhRecordLiftProtocol.recordNative setup codec) work))).run state =
      (bareNative (simulateQ (loggedNative (PqxdhRecordLiftCtxServices.native setup codec)) work)).run (erasePrivate state) := by
  have fact := congrArg (fun program => (fun result => (result.1,
      Bare.mk result.2.2.1 result.2.1 state.seeds state.chain state.produced result.2.2.2)) <$> program)
    (logged_effects_erasure setup codec work state.primitive state.pending)
  simpa only [PqxdhRecordLiftProtocol.withRecord, PqxdhRecordLiftProtocol.primitiveWork,
    PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.putRecord,
    PqxdhRecordLiftProtocol.recordNative, StateT.run, bind_pure_comp, Functor.map_map,
    Prod.map_def, id_eq, bareNative, erasePrivate] using fact

/-- Concrete mixed lookups retain public-effect accounting, including on every full76 miss draw. -/
theorem lookup_effects (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n))
    (state : PqxdhRecordLiftChainCompiler.Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (result : PqxdhFullSecretInputKdf.FullOutput × PqxdhRecordLiftChainCompiler.Execution (Slot n) PqxdhRecordLiftWorld.Primitive)
    (supported : result ∈ support ((PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run state)) :
    result.2.2.1.effects = state.2.1.effects := by
  cases selected : ideal coordinate with
  | false =>
      rw [PqxdhRecordLiftChainOracle.lookup_real _ _ _ _ _ selected,
        mem_support_pure_iff] at supported
      subst result
      rfl
  | true =>
      cases found : state.1 coordinate with
      | some output =>
          rw [PqxdhRecordLiftChainOracle.lookup_hit _ _ _ _ _ selected output found,
            mem_support_pure_iff] at supported
          subst result
          rfl
      | none =>
          rw [PqxdhRecordLiftChainOracle.lookup_miss _ _ _ _ _ selected found, support_map] at supported
          obtain ⟨output, _, rfl⟩ := supported
          rfl

/-- The original coordinate request and exact bare table/cache law have the same retained effect ledger. -/
theorem lookup_effects_erasure (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n))
    (table : PqxdhRecordLiftChainTable.Table (Slot n)) (primitive : PqxdhRecordLiftWorld.Primitive) :
    (fun result => ((), (result.2.1, result.2.2.1.effects, result.2.2.2))) <$>
      (PqxdhRecordLiftChainOracle.lookup source seeds ideal coordinate).run (table, primitive) =
      (fun result => ((), (result.2, primitive.1.effects, primitive.2))) <$>
        (PqxdhRecordLiftCtxOracle.bareLookup source seeds ideal coordinate).run table := by
  have erased := congrArg (fun program => (fun result =>
      ((), (result.2.1, primitive.1.effects, result.2.2))) <$> program)
    (PqxdhRecordLiftCtxOracle.lookup_native_erasure source seeds ideal coordinate table primitive)
  simp only [Functor.map_map] at erased
  rw [← erased]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  rw [lookup_effects source seeds ideal coordinate (table, primitive) result supported]

/-- Uniform instrumentation erasure preserves the entire sampled value and all unchanged private fields; no sampling operation is removed. -/
theorem sampled_bare (work : ProbComp Result) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id erasePrivate <$> (PqxdhRecordLiftProtocol.sampled work).run state =
      (fun value => (value, erasePrivate state)) <$> work := by
  have fact := congrArg (fun program => (fun value => (value, erasePrivate state)) <$> program)
    (PqxdhRecordLiftWorld.countCoin_forget work state.primitive.1.uniform)
  simpa only [PqxdhRecordLiftProtocol.sampled, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, erasePrivate] using fact

/-- Exact lookup erasure frames every global private field while retaining its real persistent table and effect ledger. -/
theorem bare_lookup (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id erasePrivate <$>
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
        setup codec (.lookup coordinate)).run state =
      (bareInterpreter setup codec ideal (.lookup coordinate)).run (erasePrivate state) := by
  have sameSeeds : bareSeeds (erasePrivate state) = PqxdhRecordLiftProtocol.cachedSeeds state := by rfl
  simp only [erasePrivate] at sameSeeds
  have mapApply {A B S : Type} (f : A → B) (work : StateT S ProbComp A) (s : S) :
      (f <$> work) s = (fun reply => (f reply.1, reply.2)) <$> work s := StateT.run_map _ _ _
  have fact := congrArg (fun program => (fun result => ((),
      Bare.mk result.2.2.2 result.2.2.1 state.seeds result.2.1 state.produced state.pending)) <$> program)
    (lookup_effects_erasure setup.source (PqxdhRecordLiftProtocol.cachedSeeds state) ideal coordinate state.chain state.primitive)
  simp only [PqxdhRecordLiftProtocol.interpreter,
    PqxdhRecordLiftProtocol.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter]
  simpa only [StateT.run, PqxdhRecordLiftProtocol.withRecord, mapApply,
    PqxdhRecordLiftLoggedAdapters.liftLookup, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, erasePrivate, bareInterpreter,
    PqxdhRecordLiftProtocol.recordState, PqxdhRecordLiftProtocol.putRecord,
    sameSeeds] using fact

/-- All ten actual global mixed-source services commute with native/uniform counter erasure. This relation is independent of any selected key, target coordinate or mask. -/
theorem bare_query (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id erasePrivate <$>
      (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
        setup codec query).run state =
      (bareInterpreter setup codec ideal query).run (erasePrivate state) := by
  cases query with
  | lookup coordinate => exact bare_lookup setup codec ideal coordinate state
  | knownSend kernel context =>
      simpa only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter,
        PqxdhRecordLiftWorldCompiler.sendNative, QueryImpl.simulateQ_compose] using
        bare_native setup codec (simulateQ RawCtxMixedOwner.sendAdapter
          (simulateQ RawCtxSourceSend.adapter (RawCtxSourceSend.send kernel context))) state
  | knownReceive kernel target context =>
      simpa only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter,
        PqxdhRecordLiftWorldCompiler.receiveNative, QueryImpl.simulateQ_compose] using
        bare_native setup codec (simulateQ RawCtxMixedOwner.receiveAdapter
          (simulateQ RawCtxWholeOwner.adapter (RawCtxOwnerOracle.receive kernel target context))) state
  | opening pending =>
      have fact := bare_native setup codec (simulateQ RawCtxMixedOwner.receiveAdapter
        (RawCtxWholeOwner.adapter (.inr (RawCtxInterpretedOpening.toNative
          (PqxdhRecordLiftMaterialTable.eraseOpening (PqxdhRecordLiftProtocol.cachedSeeds state) state.chain pending))))) state
      simp only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter,
        PqxdhRecordLiftProtocol.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
        PqxdhRecordLiftNativeAdapters.receiveOpen, PqxdhRecordLiftWorldCompiler.receiveNative,
        QueryImpl.simulateQ_compose, PqxdhRecordLiftProtocol.withRecord,
        PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.recordState,
        StateT.run] at fact ⊢
      exact fact
  | sealing pending =>
      have fact := bare_native setup codec (simulateQ RawCtxMixedOwner.sendAdapter
        (RawCtxSourceSend.adapter (.inr (RawCtxInterpretedSend.nativeSeal
          (PqxdhRecordLiftMaterialTable.eraseSeal (PqxdhRecordLiftProtocol.cachedSeeds state) state.chain pending))))) state
      simp only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter,
        PqxdhRecordLiftProtocol.localInterpreter, PqxdhRecordLiftOpaqueDrivers.interpreter,
        PqxdhRecordLiftNativeAdapters.sendSeal, PqxdhRecordLiftWorldCompiler.sendNative,
        QueryImpl.simulateQ_compose, PqxdhRecordLiftProtocol.withRecord,
        PqxdhRecordLiftProtocol.primitiveWork, PqxdhRecordLiftProtocol.recordState,
        StateT.run] at fact ⊢
      exact fact
  | coin coin => exact sampled_bare (unifSpec.query coin) state
  | allocate allocated =>
      have fact := congrArg (fun program => (fun result =>
          ((), { result.2 with seeds := result.1.2 })) <$> program)
        (sampled_bare ((PqxdhRecordLiftLazyTable.impl allocated).run state.seeds) state)
      simpa only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter, StateT.run,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, erasePrivate] using fact
  | hash bytes =>
      have fact := congrArg (fun program => (fun result =>
          (result.1.1, { result.2 with cache := result.1.2 })) <$> program)
        (sampled_bare ((ctxRandomOracle ((), bytes)).run state.primitive.2) state)
      simpa only [PqxdhRecordLiftProtocol.interpreter, bareInterpreter, StateT.run,
        bind_pure_comp, Functor.map_map, Prod.map_def, id_eq, erasePrivate] using fact
  | charge kind => rfl
  | publish tag => rfl

/-- The entire evaluated global source program retains its original Result and complete byte/cache/log state after native/uniform counter erasure, under every mixed selector. -/
theorem bare_schedule (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result) (state : PqxdhRecordLiftProtocol.Private n) :
    Prod.map id erasePrivate <$>
      (simulateQ (PqxdhRecordLiftProtocol.interpreter (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
        setup codec) client).run state =
      (simulateQ (bareInterpreter setup codec ideal) client).run (erasePrivate state) :=
  map_run_simulateQ_eq_of_query_map_eq _ _ erasePrivate (bare_query setup codec ideal) client state

/-- The stopped bare source retains only the selected coordinate/nonce and its attempt history beside the complete counter-erased source state. -/
structure CutState (n : Nat) where
  native : Bare n
  coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)
  nonce : CtxNonce
  used : List CtxNonce

noncomputable def realizeCut (key : CtxKey) (state : SourceSecret n) : CutState n :=
  ⟨⟨state.2.1, state.1.effects, state.1.seeds, PqxdhRecordLiftCtxOracle.keyTable state.1.masked key,
    state.1.produced, state.1.pending⟩, state.1.masked.coordinate, state.1.masked.value.2, state.2.2⟩

/-- Selection is structural and concerns only valid-width hidden sealing. Known-key equality of bytes never selects a record. -/
def SelectedSeal (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) : Service n → Prop
  | .sealing pending => pending.context.associatedData.length = 153 ∧ pending.material = coordinate
  | _ => False

open Classical in
noncomputable def advanceUsed (state : CutState n) (query : Service n) : List CtxNonce :=
  if SelectedSeal state.coordinate query then
    if state.nonce ∈ state.used then state.used else state.nonce :: state.used
  else state.used

open Classical in
/-- The explicit stop is added to the literal bare source interpreter before repeated selected seals. Actual writer failure remains an ordinary successful service reply containing None. -/
noncomputable def stoppedBareInterpreter (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (ExceptT Unit (StateT (CutState n) ProbComp)) :=
  fun query => ExceptT.mk fun state =>
    if SelectedSeal state.coordinate query ∧ state.nonce ∈ state.used then pure (.error (), state) else do
      let result ← (bareInterpreter setup codec ideal query).run state.native
      pure (.ok result.1, { state with native := result.2, used := advanceUsed state query })

/-- The local ordinary-endpoint refusal is exactly structural selection plus a previously attempted selected nonce. -/
theorem refusal_selected (state : SourceSecret n) (pending : Sealing n) :
    PqxdhRecordLiftCtxOracle.Refused state.1.masked pending state.2.2 ↔
      SelectedSeal state.1.masked.coordinate (.sealing pending) ∧ state.1.masked.value.2 ∈ state.2.2 := by
  by_cases same : pending.material = state.1.masked.coordinate
  · simp [PqxdhRecordLiftCtxOracle.Refused, PqxdhRecordLiftCtxServices.materialRoute, SelectedSeal, same]
  · simp [PqxdhRecordLiftCtxOracle.Refused, PqxdhRecordLiftCtxServices.materialRoute, SelectedSeal, same]

/-- The retained nonce history has exactly the same update as the ordinary selected service, including invalid width and known-key routes. -/
theorem advanceUsed_realize (key : CtxKey) (state : SourceSecret n) (pending : Sealing n) :
    advanceUsed (realizeCut key state) (.sealing pending) =
      PqxdhRecordLiftCtxOracle.sealNonces state.1.masked pending state.2.2 := by
  by_cases same : pending.material = state.1.masked.coordinate
  · simp [advanceUsed, realizeCut, SelectedSeal, PqxdhRecordLiftCtxOracle.sealNonces,
      PqxdhRecordLiftCtxServices.materialRoute, same]
    rfl
  · simp [advanceUsed, realizeCut, SelectedSeal, PqxdhRecordLiftCtxOracle.sealNonces,
      PqxdhRecordLiftCtxServices.materialRoute, same]

/-- Every retained-mask lookup preserves its selected coordinate and both non-key output projections. -/
theorem lookup_parameters (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n))
    (masked : PqxdhRecordLiftProjectionCut.Mask (Slot n))
    (result : Unit × PqxdhRecordLiftProjectionCut.Mask (Slot n))
    (supported : result ∈ support ((PqxdhRecordLiftCtxOracle.nativeLookup source seeds ideal key coordinate).run masked)) :
    result.2.coordinate = masked.coordinate ∧ result.2.value = masked.value := by
  change result ∈ support (PqxdhRecordLiftCtxOracle.nativeLookup source seeds ideal key coordinate masked) at supported
  unfold PqxdhRecordLiftCtxOracle.nativeLookup at supported
  split at supported
  · simpa only [mem_support_pure_iff] using supported ▸ And.intro rfl rfl
  · split at supported
    · split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        exact ⟨rfl, rfl⟩
      · simp only [support_map] at supported
        obtain ⟨output, _, rfl⟩ := supported
        exact ⟨rfl, rfl⟩
    · simp only [mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩

/-- Lookup realization retains both selected non-key projections and its coordinate together with the complete source table, for the already-ideal selected cache entry. -/
theorem lookup_full_realization (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (seeds : PqxdhRecordLiftChainTable.Seeds (Slot n))
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n))
    (masked : PqxdhRecordLiftProjectionCut.Mask (Slot n)) (parentIdeal : ideal masked.coordinate = true) :
    (fun result => (result.1, result.2.coordinate, result.2.value, PqxdhRecordLiftCtxOracle.keyTable result.2 key)) <$>
      (PqxdhRecordLiftCtxOracle.nativeLookup source seeds ideal key coordinate).run masked =
      (fun result => (result.1, masked.coordinate, masked.value, result.2)) <$>
        (PqxdhRecordLiftCtxOracle.bareLookup source seeds ideal coordinate).run
          (PqxdhRecordLiftCtxOracle.keyTable masked key) := by
  have fact := congrArg (fun program => (fun result =>
      (result.1, masked.coordinate, masked.value, result.2)) <$> program)
    (PqxdhRecordLiftCtxOracle.nativeLookup_realization source seeds ideal key coordinate masked parentIdeal)
  simp only [Functor.map_map, Prod.map_def, id_eq] at fact
  rw [← fact]
  simp only [← bind_pure_comp]
  apply bind_congr_of_forall_mem_support
  intro result supported
  obtain ⟨sameCoordinate, sameValue⟩ := lookup_parameters source seeds ideal key coordinate masked result supported
  rw [sameCoordinate, sameValue]

/-- The retained-mask lookup is the actual bare global source lookup, with the fixed selected coordinate/nonce ghost retained for the later explicit stop. -/
theorem lookup_cut (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (coordinate : PqxdhRecordLiftChainState.Coordinate (Slot n)) (state : SourceSecret n)
    (parentIdeal : ideal state.1.masked.coordinate = true) :
    Prod.map id (realizeCut key) <$>
      (sourceInterpreter setup codec ideal key (.lookup coordinate)).run.run state =
      (stoppedBareInterpreter setup codec ideal (.lookup coordinate)).run.run (realizeCut key state) := by
  have unused : advanceUsed (realizeCut key state) (.lookup coordinate) = state.2.2 := by
    simp only [advanceUsed]
    split <;> simp_all [SelectedSeal, realizeCut]
  simp only [realizeCut] at unused
  have fact := congrArg (fun program => (fun result =>
      (Except.ok (ε := Unit) (), CutState.mk
        (Bare.mk state.2.1 state.1.effects state.1.seeds result.2.2.2 state.1.produced state.1.pending)
        result.2.1 result.2.2.1.2 state.2.2)) <$> program)
    (lookup_full_realization setup.source (seedAt state.1) ideal key coordinate state.1.masked parentIdeal)
  simp only [sourceInterpreter, withSourceLocal, PqxdhRecordLiftCtxOracle.nativeInterpreter,
    stoppedBareInterpreter, SelectedSeal, false_and, ite_false, unused,
    bareInterpreter, ExceptT.run, ExceptT.mk, StateT.run, bind_pure_comp,
    Functor.map_map, Prod.map_def, id_eq, realizeCut] at fact ⊢
  convert fact using 1
  rfl


/-- The global native sealing callback has the same explicit refusal and exact attempted-frame effects as the literal stopped bare source. -/
theorem sealing_cut (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (pending : Sealing n) (state : SourceSecret n) :
    Prod.map id (realizeCut key) <$>
      (sourceInterpreter setup codec ideal key (.sealing pending)).run.run state =
      (stoppedBareInterpreter setup codec ideal (.sealing pending)).run.run (realizeCut key state) := by
  simp only [sourceInterpreter, withSourceLocal, PqxdhRecordLiftCtxOracle.nativeInterpreter,
    stoppedBareInterpreter, ExceptT.run, ExceptT.mk, StateT.run]
  by_cases refused : PqxdhRecordLiftCtxOracle.Refused state.1.masked pending state.2.2
  · have stopped : SelectedSeal (realizeCut key state).coordinate (.sealing pending) ∧
        (realizeCut key state).nonce ∈ (realizeCut key state).used := (refusal_selected state pending).mp refused
    simp only [refused, stopped, ite_true, pure_bind, map_pure]
    rfl
  · have unstopped : ¬ (SelectedSeal (realizeCut key state).coordinate (.sealing pending) ∧
        (realizeCut key state).nonce ∈ (realizeCut key state).used) :=
      (refusal_selected state pending).not.mp refused
    simp only [refused, unstopped, ite_false, advanceUsed_realize, bareInterpreter, bareNative,
      StateT.run, bind_pure_comp, Functor.map_map]
    rfl



/-- An unselected service executes its entire native operation and keeps the selected attempt history unchanged. -/
theorem stoppedBare_unselected (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (query : Service n) (state : CutState n) (unselected : ¬ SelectedSeal state.coordinate query) :
    (stoppedBareInterpreter setup codec ideal query).run.run state =
      (fun result => (Except.ok (ε := Unit) result.1, { state with native := result.2 })) <$>
        (bareInterpreter setup codec ideal query).run state.native := by
  simp only [stoppedBareInterpreter, ExceptT.run, ExceptT.mk, StateT.run, advanceUsed,
    unselected, false_and, ite_false, bind_pure_comp]


/-- Every private native comparator query realizes exactly the literal stopped bare source, keeping all table, seed, cache, log and effect fields. -/
theorem source_cut_query (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (query : Service n) (state : SourceSecret n) (parentIdeal : ideal state.1.masked.coordinate = true) :
    Prod.map id (realizeCut key) <$>
      (sourceInterpreter setup codec ideal key query).run.run state =
      (stoppedBareInterpreter setup codec ideal query).run.run (realizeCut key state) := by
  cases query with
  | lookup coordinate => exact lookup_cut setup codec ideal key coordinate state parentIdeal
  | sealing pending => exact sealing_cut setup codec ideal key pending state
  | _ =>
      rw [stoppedBare_unselected _ _ _ _ _ (by exact not_false)]
      simp only [sourceInterpreter, withSourceLocal, PqxdhRecordLiftCtxOracle.nativeInterpreter,
        withSourceKnown, bareInterpreter, bareNative, ExceptT.run, ExceptT.mk, StateT.run,
        bind_pure_comp, Functor.map_map, map_pure, Prod.map_def, id_eq, realizeCut]
      all_goals rfl


/-- Every stopped native outcome, including refusal, retains the selected coordinate and nonce. -/
theorem stoppedBare_parameters (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool)
    (query : Service n) (state : CutState n)
    (result : Except Unit ((ServiceSpec n).Range query) × CutState n)
    (supported : result ∈ support ((stoppedBareInterpreter setup codec ideal query).run.run state)) :
    result.2.coordinate = state.coordinate ∧ result.2.nonce = state.nonce := by
  simp only [stoppedBareInterpreter, ExceptT.run, ExceptT.mk, StateT.run] at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported
    subst result
    exact ⟨rfl, rfl⟩
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, _, rfl⟩ := supported
    exact ⟨rfl, rfl⟩


/-- Realizing any supported comparator result retains the same selected coordinate and nonce; the ideal-entry precondition is therefore stable through adaptive continuation. -/
theorem source_cut_parameters (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (query : Service n) (state : SourceSecret n) (parentIdeal : ideal state.1.masked.coordinate = true)
    (result : Except Unit ((ServiceSpec n).Range query) × SourceSecret n)
    (supported : result ∈ support ((sourceInterpreter setup codec ideal key query).run.run state)) :
    result.2.1.masked.coordinate = state.1.masked.coordinate ∧
      result.2.1.masked.value.2 = state.1.masked.value.2 := by
  apply stoppedBare_parameters setup codec ideal query (realizeCut key state)
    (Prod.map id (realizeCut key) result)
  rw [← source_cut_query setup codec ideal key query state parentIdeal, support_map]
  exact ⟨result, supported, rfl⟩


/-- The complete adaptive native comparator, including its exact stopped error state, realizes the same stopped bare source continuation. -/
theorem source_cut_schedule (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (ServiceSpec n) Result) (state : SourceSecret n)
    (parentIdeal : ideal state.1.masked.coordinate = true) :
    Prod.map id (realizeCut key) <$>
      (simulateQ (sourceInterpreter setup codec ideal key) client).run.run state =
      (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run (realizeCut key state) := by
  induction client using OracleComp.inductionOn generalizing state with
  | pure result => rfl
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, PqxdhRecordLiftCtxOracle.except_bind, map_bind]
      rw [← source_cut_query setup codec ideal key query state parentIdeal, bind_map_left]
      apply bind_congr_of_forall_mem_support
      intro result supported
      rcases result with ⟨reply, after⟩
      cases reply with
      | error error => simp only [Prod.map_def, id_eq, map_pure]
      | ok reply =>
          apply ih reply after
          rw [(source_cut_parameters setup codec ideal key query state parentIdeal (.ok reply, after) supported).1]
          exact parentIdeal


/-- The ordinary selected-key reduction recovers the entire literal stopped source continuation after restoring the unavailable key only on the proof side. -/
theorem reduction_cut (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (ServiceSpec n) Result) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (admitted : client.AllQueriesSatisfy (Admitted codec.frameRead))
    (parentIdeal : ideal state.masked.coordinate = true) :
    (fun result => Prod.map id (realizeCut key) (projectReply (AdaptiveCtxDynamicKnownKeys.erase result))) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec client state others)).run selected =
      (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run
        (realizeCut key (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected)))) := by
  have fact := congrArg (fun work => Prod.map id (realizeCut key) <$> work)
    (reduction_source setup codec slot ideal key client state others selected admitted)
  simpa only [Functor.map_map] using fact.trans
    (source_cut_schedule setup codec ideal key client _ parentIdeal)


/-- Actual global schedules discharge raw admission themselves and keep the original adaptive result/control beside the full stopped source state. -/
theorem schedule_reduction_cut (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (slot : Nat)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey)
    (client : OracleComp (WorldSpec n) Result) (control : Control n) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (parentIdeal : ideal state.masked.coordinate = true) :
    (fun result => Prod.map id (realizeCut key) (projectReply (AdaptiveCtxDynamicKnownKeys.erase result))) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec (schedule codec.frameRead route client control) state others)).run selected =
      (simulateQ (stoppedBareInterpreter setup codec ideal) (schedule codec.frameRead route client control)).run.run
        (realizeCut key (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected)))) :=
  reduction_cut setup codec slot ideal key _ state others selected
    (schedule_admitted codec.frameRead route client control) parentIdeal

/-- Both frozen environment/adversary/ledger programs use the same ordinary selected endpoint, without a selected honest-key, raw-target, or callback-realization premise. The explicit nonce stop remains. -/
theorem program_reduction_cut {E X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (slot : Nat)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) (key : CtxKey) (state : Secret n)
    (others : ReductionState) (selected : AdaptiveCtxSharedModes.State)
    (parentIdeal : ideal state.masked.coordinate = true) :
    let client := PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary
    (fun result => Prod.map id (realizeCut key) (projectReply (AdaptiveCtxDynamicKnownKeys.erase result))) <$>
      (simulateQ (targetImpl true (RawCtxUniversalDecoder.decoder codec.frameRead) setup.source.crypto key)
        (reduction slot setup.source ideal codec client state others)).run selected =
      (simulateQ (stoppedBareInterpreter setup codec ideal) client).run.run
        (realizeCut key (projectSecret (state, AdaptiveCtxDynamicKnownKeys.project (others, selected)))) :=
  reduction_cut setup codec slot ideal key _ state others selected
    (program_admitted env setup.source.crypto codec route serverKid bounds mode adversary) parentIdeal


/-- The complete initialized mixed World run, including arbitrary environment and private test/fresh ledger, has this exact bare-source projection. No selected key or mask occurs in this source law. -/
theorem program_bare {E X : Type} (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK)
    (codec : PqxdhServerAuthExperiment.Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
    (env : Environment n E) (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (ideal : PqxdhRecordLiftChainState.Coordinate (Slot n) → Bool) :
    (simulateQ (bareInterpreter setup codec ideal)
      (PqxdhRecordLiftProtocol.program env setup.source.crypto codec route serverKid bounds mode adversary)).run
        (erasePrivate initialPrivate) =
      (fun result => Prod.map id erasePrivate (splitResult result)) <$>
        PqxdhRecordLiftWorldCompiler.run (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
          setup codec route env serverKid bounds mode adversary := by
  have fact := congrArg (fun work => Prod.map id erasePrivate <$> work)
    (PqxdhRecordLiftProtocol.run_factor (PqxdhRecordLiftChainOracle.lookup setup.source · ideal)
      setup codec route env serverKid bounds mode adversary)
  rw [← bare_schedule setup codec ideal _ initialPrivate]
  simpa only [PqxdhRecordLiftProtocol.run, Functor.map_map] using fact

end BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.admission_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.admission_map

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.local_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.local_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.kernelSend_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.kernelSend_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.kernelReceive_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.kernelReceive_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerSend_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerSend_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerReceive_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerReceive_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerStep_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerStep_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerRun_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.ownerRun_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.serverStep_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.serverStep_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.beaconStep_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.beaconStep_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.resolve_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.resolve_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.installServer_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.installServer_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.installBeacon_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.installBeacon_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.capability_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.capability_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.effects_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.effects_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.handler_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.handler_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_admitted

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownRom_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownRom_step

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownRom_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownRom_program

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.publicRom_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.publicRom_state

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownProgram_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.knownProgram_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.local_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.local_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.known_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.query_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.query_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.global_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.global_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.reduction_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.reduction_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_reduction_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_reduction_source

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.logged_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.logged_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.logged_effects_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.logged_effects_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_native

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_effects

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_effects_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_effects_erasure

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.sampled_bare' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.sampled_bare

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_lookup

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.bare_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.refusal_selected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.refusal_selected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.advanceUsed_realize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.advanceUsed_realize

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_parameters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_full_realization' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_full_realization

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.lookup_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.sealing_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.sealing_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.stoppedBare_unselected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.stoppedBare_unselected

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_query

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.stoppedBare_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.stoppedBare_parameters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_parameters

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.source_cut_schedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.reduction_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.reduction_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_reduction_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.schedule_reduction_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_reduction_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_reduction_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_bare' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftCtxProtocol.program_bare
