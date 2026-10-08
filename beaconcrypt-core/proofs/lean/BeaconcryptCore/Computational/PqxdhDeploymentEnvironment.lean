-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftLater
import BeaconcryptCore.Computational.PqxdhDeploymentHiddenSplit
import BeaconcryptCore.Computational.PqxdhDeploymentSeedSplit
import BeaconcryptCore.Computational.PqxdhDeploymentBackend
import BeaconcryptCore.Computational.PqxdhRegistrationScheduleResources
import BeaconcryptCore.Computational.PqxdhServerAuthTailCosts

/-!
# The registration environment of the record lift (CE-11a, unit 11a-3)

The common deployment experiment's registration (create, bundle, accept, build, finish and the public HMAC) as an environment of the record-lift capability boundary (`PqxdhRecordLiftInterface.Environment`): every coin is a coin effect of the record world, every BLAKE2b query of the registration is the world's `.hash` capability on the one shared CTX cache, and every record-relevant change is an administrative capability (a new inactive owner, a phase advance, a Server or Beacon installation). The environment answers no record command, holds no secrecy ledger and has no capability that reads a seed, a kernel or the cache itself (BLAKE2b answers come only through `.hash`).

**State (commitment reply-final 4.4, critique M6).** `EnvState` keeps the registration state with every record coordinate stripped (`strip`): every Server peer kernel and every established owner kernel is `PqxdhDeploymentHiddenSplit.placeholderKernel` and the CTX cache is empty; besides, it holds the registration handler's backend, the LQ-F ghosts (the finish snapshot and the Server ephemeral log) and the environment's own copy of the constructed Server. Every environment step commits a stripped state (`realStep_stripped`). `start` is the actual Server constructor at a fixed runtime, mapped to `Option (Created Unit × EnvState)` (v1-check ack C.3; `start_created`, `start_initial`), with `qInit + 32` coins (`start_bound`).

**Capability form.** `primFwd`, `tailFwd` and `callbacksFwd` are the source primitives, the Server's logged response tail and the Beacon finish callbacks with the BLAKE2b request forwarded; `realStep` is the intended capability form of the LQ-F registration handler (`PqxdhDeploymentBackend.realReg`), the published peer and the established owner installed with their known kernels (`serverEffect`, `ownerEffect`), and `envReal` is the real environment (cuttable validation, critique m12); that `realStep` reproduces `realReg` command by command (the per-command splits behind `c1_real`) is not proved here. The capability-form factoring (`factor_program`, `tail_factor`, `owner_factor`) shows that the native build tail and the native finish are their forwarded forms with the forwarded BLAKE2b queries answered by the lazy CTX oracle on the cache (`ctxEffects`).

**C2a.** `allowanceG core firstTouch` adds the 44 coins of a slot's environment material at the first-touch classes, which for CE-11 are the accept and the finish (`ceFirstTouch`, plan section 35). `frame_real` frames the real environment by `baseAllowance` (one BLAKE2b query at build and at finish, at most one administrative capability per command), and `frame_wrapped` frames every environment that obtains first-touch material through `touch` before a core step by `allowanceG`. The split hidden wrappers in capability form, `buildSplitEnv` and `finishSplitEnv` (intended forms of `PqxdhDeploymentHiddenSplit.buildSplit` and `finishSplit`; their factoring against those forms is not proved here), issue no coin, at most one `.hash` and at most one administrative capability, the hidden installation `installServer keyId identity (.hidden j)` or `installBeacon owner shell (.hidden j)` or the abort (`buildSplit_env_cost`, `finishSplit_env_cost`). The single-install ingredients are `buildStep_consumes`, `buildStep_idle`, `finishStep_terminal` and `finishStep_retry`.

**C4 (plan sections 31 and 33).** `capsG B allowance` has shared-hash cap `qHash + S + R + envTotal(.hash)`; `c4_instance` instantiates `PqxdhRecordLiftWorldBudget.run_hash` and `run_kdf`, `c4_closed` gives `qHash + S + R + qBuild + qFinish` and `S + 51 R` for the one-hash-at-build-and-finish pattern, `c4_later` and `c4_later_closed` add the post-phase BLAKE2b budget through `PqxdhRecordLiftLater.run_hash`, and `c4_real` is the real instance.

These are definitions, equalities of programs and resource bounds. No security, secrecy or authentication claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentEnvironment
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhRecordLiftInterface (Slot Capability CapabilitySpec EnvEffects EnvQuery EnvSpec Environment EffectKind
  effectKind BeaconShell InactivePhase KernelRef)
open PqxdhDeploymentHiddenSplit (placeholderKernel)

/-! ### Stripped registration state -/

variable {KemSK : Type}

/-- An owner with its record coordinate stripped: an established kernel is the placeholder. -/
noncomputable def stripOwner (owner : PqxdhRegistrationSchedule.Owner KemSK) : PqxdhRegistrationSchedule.Owner KemSK :=
  match owner.beacon.phase with
  | .established control associatedData _ =>
      { owner with beacon := { owner.beacon with phase := .established control associatedData placeholderKernel } }
  | _ => owner

/-- A Server peer with its record coordinate stripped: the kernel is the placeholder. -/
noncomputable def stripPeer (peer : RawCtxServerRouting.Peer Unit) : RawCtxServerRouting.Peer Unit :=
  { peer with kernel := placeholderKernel }

/-- The registration state with every record coordinate stripped (commitment reply-final 4.4, critique M6): every Server peer kernel and every established owner kernel is the placeholder, and the CTX cache is empty. -/
noncomputable def strip (state : PqxdhRegistrationSchedule.State KemSK) : PqxdhRegistrationSchedule.State KemSK :=
  { shared := (state.shared.1, { state.shared.2 with
      ctx := ∅
      server := { state.shared.2.server with server := { state.shared.2.server.server with
        peers := fun keyId => (state.shared.2.server.server.peers keyId).map stripPeer } } })
    owners := state.owners.map stripOwner }

/-- A registration state holds no record coordinate. -/
def Stripped (state : PqxdhRegistrationSchedule.State KemSK) : Prop := strip state = state

/-- The environment state: the stripped registration state, the backend of the registration handler, the LQ-F ghosts (finish snapshot and Server ephemeral log) and the environment's own copy of the constructed Server. -/
structure EnvState (KemSK Bk : Type) where
  native : PqxdhRegistrationSchedule.State KemSK
  backend : Bk
  snap : PqxdhDeploymentLater.Snap
  log : PqxdhDeploymentLaterServerSource.Log
  created : PqxdhLiveServerConstruction.Created Unit

/-- An environment step: the six registration commands on the environment state, with every coin, BLAKE2b query and record-relevant change issued as an effect of the record world. -/
abbrev EnvStep (KemSK Bk : Type) (n : Nat) :=
  QueryImpl EnvSpec (StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)))

/-- The initial environment state of a constructed Server. -/
noncomputable def envInitial {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (backend : Bk) : EnvState KemSK Bk :=
  ⟨strip (PqxdhRegistrationSchedule.initial created), backend, PqxdhDeploymentLater.Snap.empty, [], created⟩

section Start
variable {ι : Type} {baseSpec : OracleSpec ι} {Bk A : Type} (setup : Setup baseSpec KemSK)

/-- The environment's startup (v1-check ack C.3): the actual Server constructor with a generated seed at a fixed runtime, the final runtime dropped, and the initial environment state of the constructed Server. -/
noncomputable def start (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) :
    ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × EnvState KemSK Bk)) :=
  (fun born => born.1.map fun created => (created, envInitial created (init created))) <$>
    (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime

end Start

/-! ### Capability-form tools -/

section Tools
variable {n : Nat}

/-- One coin of a registration computation as a coin effect of the record world. -/
def coinFx : QueryImpl unifSpec (OracleComp (EnvEffects n)) :=
  fun coin => ((EnvEffects n).query (.inl coin) : OracleComp (EnvEffects n) _)

/-- A probabilistic registration computation with its coins as coin effects. -/
def coins {α : Type} (work : ProbComp α) : OracleComp (EnvEffects n) α := simulateQ coinFx work

/-- One capability request. -/
def request (capability : Capability n) : OracleComp (EnvEffects n) ((CapabilitySpec n).Range capability) :=
  ((EnvEffects n).query (.inr capability) : OracleComp (EnvEffects n) _)

/-- A capability request whose reply is not used. -/
def issue (capability : Capability n) : OracleComp (EnvEffects n) Unit := do
  let _ ← request capability
  pure ()

/-- Run a registration step that changes no record coordinate on the environment's registration state, its coins as coin effects. -/
noncomputable def onEnv {Bk α : Type} (step : PqxdhRegistrationSchedule.Game KemSK α) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) α := fun state =>
  (fun result => (result.1, { state with native := strip result.2 })) <$> coins (step.run state.native)

end Tools

/-! ### Forwarded primitives: BLAKE2b as the world's `.hash` -/

section Forward
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The source primitives (real HKDF, BLAKE2b, AEAD opening) with the BLAKE2b request forwarded to the world's shared cache as a `.hash` capability; HKDF and opening are the source's deterministic functions. -/
def primFwd (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxSourceOpen.NativeSpec (OracleComp (EnvEffects n))
  | .inl request => pure (RawCtxSourceHkdf.response source.crypto request)
  | .inr (.inl bytes) => (fun digest : CtxRomAuth.CtxDigest => some digest.toList) <$> request (.hash bytes)
  | .inr (.inr input) => pure (RawCtxSourceOpen.baseOpen c input)

/-- The record primitives of the Server build (HKDF, AEAD seal, BLAKE2b, frame writer) with the BLAKE2b request forwarded. -/
def sharedFwd (c : Pqxdh.Crypto) (writer : RawCtxMixedShared.Writer)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) :
    QueryImpl RawCtxMixedOwner.NativeSpec (OracleComp (EnvEffects n)) :=
  primFwd c source ∘ₛ RawCtxMixedShared.sharedAdapter c writer

/-- The auxiliary callbacks of the Server's response tail, as constant replies. -/
def tailAuxFwd : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (OracleComp (EnvEffects n))
  | .checkIdentity identity => pure (checks.beaconIdentity identity)
  | .reservePeer => pure checks.reservePeer
  | .reservePlaintext length => pure (checks.reservePlaintext length)
  | .erase _ => pure ()
  | .write fields => pure (codec.write2 fields)

/-- The Server's native response tail with the BLAKE2b request forwarded (`PqxdhServerAuthExperiment.nativeTail`). -/
def nativeTailFwd : QueryImpl PqxdhServerRegistrationPublication.TailSpec (OracleComp (EnvEffects n)) :=
  (fun query => match query with
    | .inl request => (sharedFwd (n := n) setup.source.crypto codec.frameWrite setup.source ∘ₛ RawCtxMixedOwner.sendLift) request
    | .inr request => tailAuxFwd codec checks request) ∘ₛ PqxdhServerRegistrationPublication.nativeAdapter

/-- The Server's logged response tail with the BLAKE2b request forwarded (`PqxdhServerAuthExperiment.tailImpl`): a successful seal appends its context to the log. -/
def tailFwd : QueryImpl PqxdhServerRegistrationPublication.TailSpec
    (StateT (List RawCtxSourceSend.SealContext) (OracleComp (EnvEffects n)))
  | .inl (.inl request) => StateT.lift (nativeTailFwd setup codec checks (.inl (.inl request)))
  | .inl (.inr input) => fun log => do
      let sealed ← nativeTailFwd setup codec checks (.inl (.inr input))
      pure (sealed, if sealed.isSome then log ++ [input.context] else log)
  | .inr query => StateT.lift (nativeTailFwd setup codec checks (.inr query))

/-- The Beacon's native tail callbacks with the BLAKE2b request forwarded (`PqxdhServerAuthExperiment.beaconNative`). -/
def beaconFwd : QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (OracleComp (EnvEffects n))
  | .inl query => primFwd setup.source.crypto setup.source query
  | .inr (.root _) => pure none
  | .inr (.initial request) => pure (RawCtxSourceHkdf.initialResponse setup.source.crypto request)
  | .inr (.application response) => pure (codec.application response)

/-- The Beacon finish callbacks with every coin a coin effect and the BLAKE2b request forwarded (`PqxdhRegistrationSchedule.callbacks`): preparation and the root derivation on the Extract family keep their coins, every other tail callback is `beaconFwd`. -/
noncomputable def callbacksFwd :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response)
      (StateT (NativeState KemSK) (OracleComp (EnvEffects n)))
  | .inl query => StateT.lift (coins (PqxdhRegistrationSchedule.preparation setup codec query))
  | .inr query => PqxdhPhase2DhRootConsumer.withRoot
      (fun input state => coins ((PqxdhServerAuthNative.sourceRoot setup.hmac input).run state))
      (fun query => StateT.lift (beaconFwd setup codec query)) query

end Forward

/-! ### The capability-form registration steps -/

section Steps
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The inactive tag of a Beacon phase; an established phase has none. -/
def inactiveTag {D K : Type} : RawCtxBeaconLifecycle.Phase D K ConcreteRatchetKernel → Option InactivePhase
  | .fresh _ _ _ => some .fresh
  | .freshWithCoins _ _ _ _ => some .freshWithCoins
  | .initSent _ _ _ _ => some .initSent
  | .aborted _ => some .aborted
  | .established _ _ _ => none

/-- The capability that publishes one owner's registration change to the record world: a newly established owner is installed with its known kernel and the stored shell, any other change of the inactive tag is an advance, and no change issues nothing. -/
def ownerEffect (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK) : OracleComp (EnvEffects n) Unit :=
  match before.beacon.phase, after.beacon.phase with
  | .established _ _ _, _ => pure ()
  | _, .established control associatedData kernel =>
      issue (.installBeacon index ⟨after.beacon.identityKeyId, control, associatedData⟩ (.known kernel))
  | previous, current => match inactiveTag current with
      | some tag => if inactiveTag previous = some tag then pure () else issue (.advanceOwner index tag)
      | none => pure ()

/-- The capability that publishes a Server build to the record world: the peer the build published, at the key ID of its response, is installed with its known kernel. -/
def serverEffect (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) : OracleComp (EnvEffects n) Unit :=
  match settled.1 with
  | none => pure ()
  | some response => match settled.2.server.peers response.keyId with
      | none => pure ()
      | some peer => issue (.installServer response.keyId peer.identity (.known peer.kernel))

/-- `create`: the public pin parse, then the native owner construction with its coins as coin effects and the new inactive owner appended in the world. -/
noncomputable def createStep (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option Nat) :=
  match PqxdhDeploymentInterface.parsePin pin with
  | none => pure none
  | some word => do
      let index ← onEnv (PqxdhRegistrationSchedule.create setup word keyId)
      StateT.lift (issue (.appendOwner keyId word .fresh))
      pure (some index)

/-- Publish the change of the owner at `index` between two owner lists (`ownerEffect`); an absent owner issues nothing. -/
def ownerChange (index : Nat) (before after : List (PqxdhRegistrationSchedule.Owner KemSK)) : OracleComp (EnvEffects n) Unit :=
  match before[index]?, after[index]? with
  | some previous, some current => ownerEffect index previous current
  | _, _ => pure ()

/-- `bundle`: the native bundle with its coins as coin effects, then the owner's phase change published. -/
noncomputable def bundleStep (owner : Nat) : StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option Pqxdh.Bytes) :=
  fun state => do
    let result ← coins ((PqxdhRegistrationSchedule.bundle setup codec owner).run state.native)
    ownerChange owner state.native.owners result.2.owners
    pure (result.1, { state with native := strip result.2 })

/-- `accept`: the native logged accept (LQ-F) with its coins as coin effects; the ephemeral entry is appended to the log. -/
noncomputable def acceptStep (raw : Pqxdh.Bytes) : StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option Nat) :=
  fun state => (fun result => (result.1.1, { state with native := strip result.2, log := state.log ++ [result.1.2] })) <$>
    coins ((PqxdhRegistrationSchedule.onShared
      (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks state.created.seed raw)).run state.native)

/-- `build`: the native Server build (`PqxdhServerAuthNative.nativeBuild`) with the BLAKE2b request forwarded; the published peer is installed in the world with its known kernel and kept in the environment with the placeholder kernel, and the CTX cache is not touched. -/
noncomputable def buildStep (session : Nat) (payload : Option Pqxdh.Bytes) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option PqxdhServerRegistrationPublication.Response) :=
  fun state =>
    let game := state.native.shared.2
    match game.pending session with
    | none => pure (none, state)
    | some token => do
        let result ← (simulateQ (tailFwd setup codec checks)
          (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () game.server)).run []
        let settled := PqxdhServerAuthExperiment.settle game.server result.1
        serverEffect settled
        let native : PqxdhRegistrationSchedule.State KemSK := { state.native with shared := (state.native.shared.1, { game with
          pending := Function.update game.pending session none
          server := settled.2
          ghost := { game.ghost with seals := game.ghost.seals ++ result.2.map (fun context => (session, context)) } }) }
        pure (settled.1, { state with native := strip native })

/-- `finish`: the native owner finish (`PqxdhRegistrationSchedule.finish`) with every coin a coin effect and the BLAKE2b request forwarded; the owner's change is published (installation of an established owner with its known kernel, or the abort) and the owner is kept with the placeholder kernel. -/
noncomputable def finishStep (owner : Nat) (raw : Pqxdh.Bytes) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (Option Pqxdh.Bytes) :=
  fun state =>
    match state.native.owners[owner]? with
    | none => pure (none, state)
    | some before => do
        let result ← (simulateQ (callbacksFwd setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw before)).run state.native.shared
        ownerEffect owner before result.1.2
        let native : PqxdhRegistrationSchedule.State KemSK :=
          ⟨result.2, state.native.owners.set owner result.1.2⟩
        pure (result.1.1, { state with native := strip native })

/-- `hmac`: the native public HMAC with its coins as coin effects. -/
noncomputable def hmacStep (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) PqxdhSecretInputKdf.HmacBlock := fun state =>
  (onEnv (PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup state.created.seed
    PqxdhRegistrationSchedule.observationScalar key message))).run state

/-- The LQ-F finish snapshot: a finish captures the addressed owner's scalars before it runs. -/
def snapped {Bk : Type} (query : EnvQuery) (state : EnvState KemSK Bk) : EnvState KemSK Bk :=
  { state with snap := (PqxdhDeploymentLater.snapshotAt state.snap state.native.owners
    (PqxdhDeploymentLater.finishOwner (.inr query.val))) }

/-- The intended capability form of the real registration step `PqxdhDeploymentBackend.realReg`: the snapshot, then the command's step. That it reproduces `realReg` (the per-command splits behind `c1_real`) is not proved here. -/
noncomputable def realStep : EnvStep KemSK Bk n := fun query state =>
  match query with
  | ⟨.create pin keyId, _⟩ => (createStep setup pin keyId).run (snapped query state)
  | ⟨.bundle owner, _⟩ => (bundleStep setup codec owner).run (snapped query state)
  | ⟨.accept raw, _⟩ => (acceptStep setup codec checks raw).run (snapped query state)
  | ⟨.build session payload, _⟩ => (buildStep setup codec checks session payload).run (snapped query state)
  | ⟨.finish owner raw, _⟩ => (finishStep setup codec owner raw).run (snapped query state)
  | ⟨.hmac key message, _⟩ => (hmacStep setup key message).run (snapped query state)
  | ⟨.hash _, notEnv⟩ => absurd notEnv id
  | ⟨.serverSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.serverRaw _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconRaw _ _, notEnv⟩ => absurd notEnv id

end Steps

section Real
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The real registration as a record-lift environment (cuttable validation, critique m12). -/
noncomputable def envReal (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A) :
    Environment n (EnvState KemSK Unit) where
  start := start setup ensureInit identityIndex runtime (fun _ => ())
  step := realStep setup codec checks

end Real


/-! ### Stripped states and startup -/

/-- Stripping an owner twice strips it once. -/
theorem stripOwner_idem (owner : PqxdhRegistrationSchedule.Owner KemSK) : stripOwner (stripOwner owner) = stripOwner owner := by
  unfold stripOwner
  cases h : owner.beacon.phase <;> simp only [h]

/-- Stripping a peer twice strips it once. -/
theorem stripPeer_comp : stripPeer ∘ stripPeer = stripPeer := rfl

/-- Stripping owners twice strips them once. -/
theorem stripOwner_comp : stripOwner (KemSK := KemSK) ∘ stripOwner = stripOwner :=
  funext stripOwner_idem

/-- Stripping is idempotent. -/
theorem strip_idem (state : PqxdhRegistrationSchedule.State KemSK) : strip (strip state) = strip state := by
  simp only [strip, List.map_map, Option.map_map, stripPeer_comp, stripOwner_comp]

/-- Every stripped state holds no record coordinate. -/
theorem strip_stripped (state : PqxdhRegistrationSchedule.State KemSK) : Stripped (strip state) := strip_idem state

/-- The initial environment state holds no record coordinate. -/
theorem envInitial_stripped {Bk : Type} (created : PqxdhLiveServerConstruction.Created Unit) (backend : Bk) :
    Stripped (envInitial (KemSK := KemSK) created backend).native :=
  strip_stripped _

section StartFacts
variable {ι : Type} {baseSpec : OracleSpec ι} {Bk A : Type} (setup : Setup baseSpec KemSK)

/-- The environment's startup forgets nothing of the construction but the final runtime: its constructed Server is the actual constructor's. -/
theorem start_created (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) :
    Option.map Prod.fst <$> start setup ensureInit identityIndex runtime init =
      Prod.fst <$> (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run
        runtime := by
  simp only [start, Functor.map_map, Option.map_map]
  congr 1
  funext born
  cases born.1 <;> rfl

/-- Every startup outcome is the initial environment state of its constructed Server. -/
theorem start_initial (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat) (runtime : A)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk)
    (created : PqxdhLiveServerConstruction.Created Unit) (state : EnvState KemSK Bk)
    (supported : some (created, state) ∈ support (start setup ensureInit identityIndex runtime init)) :
    state = envInitial created (init created) := by
  simp only [start, support_map, Set.mem_image] at supported
  obtain ⟨born, _, same⟩ := supported
  cases hb : born.1 with
  | none => simp only [hb, Option.map_none, reduceCtorEq] at same
  | some made =>
      simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      rfl

/-- The startup draws at most `qInit + 32` coins: runtime initialization and the generated Server seed (`PqxdhLiveServerConstruction.construct_uniform`). -/
theorem start_bound (ensureInit : StateT A ProbComp Bool) (qInit : Nat)
    (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit) (identityIndex : Nat) (runtime : A)
    (init : PqxdhLiveServerConstruction.Created Unit → Bk) :
    (start setup ensureInit identityIndex runtime init).IsTotalQueryBound (qInit + 32) := by
  have bound := PqxdhLiveServerConstruction.construct_uniform (P := Unit) setup.joint ensureInit qInit initBound identityIndex
    setup.serverKeyId none runtime
  simpa only [start, IsTotalQueryBound, isQueryBound_map_iff, Option.isNone_none, ite_true] using bound

end StartFacts

/-! ### Effect bounds of the capability-form tools -/

section ToolBounds
variable {n : Nat}

/-- Coins of a registration computation are coin effects only: a computation with at most `k` coins issues at most `k` coin effects and no other effect. -/
theorem coins_bound {α : Type} (work : ProbComp α) (k : Nat) (bounded : work.IsTotalQueryBound k) (kind : EffectKind) :
    (coins (n := n) work).IsQueryBoundP (fun effect => effectKind effect = kind) (if kind = .coin then k else 0) := by
  by_cases coin : kind = .coin
  · subst coin
    simp only [ite_true]
    exact IsQueryBoundP.simulateQ_of_step ((isQueryBoundP_true_iff work k).mpr bounded)
      (fun _ _ => (isQueryBoundP_query_iff _ _ _).mpr fun _ => Nat.one_pos)
      (fun _ absurd => absurd.elim trivial)
  · simp only [coin, ite_false]
    exact IsQueryBoundP.simulateQ_of_step (isQueryBoundP_false work 0)
      (fun _ absurd => absurd.elim)
      (fun _ _ => (isQueryBoundP_query_iff _ _ _).mpr fun same => absurd same.symm coin)

/-- One capability request is one effect of its kind. -/
theorem issue_bound (capability : Capability n) (kind : EffectKind) :
    (issue capability).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = effectKind (n := n) (.inr capability) then 1 else 0) := by
  unfold issue request
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨?_, fun _ => trivial⟩
  by_cases same : kind = effectKind (n := n) (.inr capability)
  · exact Or.inr (by simp only [same, ite_true, Nat.one_pos])
  · exact Or.inl fun found => same found.symm

/-- A capability request that is not a BLAKE2b query is one administrative effect. -/
theorem issue_admin (capability : Capability n) (notHash : ∀ bytes, capability ≠ .hash bytes) (kind : EffectKind) :
    (issue capability).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .administrative then 1 else 0) := by
  have kindOf : effectKind (n := n) (.inr capability) = .administrative := by
    cases capability with
    | hash bytes => exact absurd rfl (notHash bytes)
    | _ => rfl
  simpa only [kindOf] using issue_bound capability kind

/-- Publishing one owner's change issues at most one administrative effect and nothing else. -/
theorem ownerEffect_bound (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK) (kind : EffectKind) :
    (ownerEffect (n := n) index before after).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .administrative then 1 else 0) := by
  unfold ownerEffect
  split
  · trivial
  · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind
  · split
    · split
      · trivial
      · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind
    · trivial

/-- Publishing a Server build issues at most one administrative effect and nothing else. -/
theorem serverEffect_bound (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) (kind : EffectKind) :
    (serverEffect (n := n) settled).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .administrative then 1 else 0) := by
  unfold serverEffect
  split
  · trivial
  · split
    · trivial
    · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind

end ToolBounds

/-! ### Allowances and C4 -/

/-- The first-touch allowance (plan sections 31, 33 and 35): the core's per-class allowance plus the 44 coins of a slot's environment material (key32, nonce12; `PqxdhDeploymentHiddenLayout.material_bound`) at every first-touch class. -/
def allowanceG (core : Fin 14 → EffectKind → Nat) (firstTouch : Fin 14 → Bool) : Fin 14 → EffectKind → Nat :=
  fun kind effect => core kind effect + if effect = .coin ∧ firstTouch kind = true then 44 else 0

/-- The first-touch classes of the hidden slots (plan section 35, item 2 plan section 20): the accept (class 3), where the selected accept first reads the Server slot, and the finish (class 5), where a Beacon slot is first read. -/
def ceFirstTouch : Fin 14 → Bool := fun kind => kind = 3 || kind = 5

/-- The material adds coins only: the first-touch allowance of BLAKE2b and administrative effects is the core's. -/
theorem allowanceG_other (core : Fin 14 → EffectKind → Nat) (firstTouch : Fin 14 → Bool) (kind : Fin 14)
    (effect : EffectKind) (notCoin : effect ≠ .coin) : allowanceG core firstTouch kind effect = core kind effect := by
  simp only [allowanceG, notCoin, false_and, ite_false, Nat.add_zero]

/-- The real environment's per-class allowance: create draws two 32-byte values and the KEM key pair and appends an owner; bundle draws the one-time scalar and advances the owner; accept draws the ephemeral, the encapsulation and the Extract-table value; build issues its sequence-one BLAKE2b query and installs the peer; finish draws the decapsulation and the Extract-table value within the 69-callback bound, issues at most one BLAKE2b query and installs or aborts the owner; HMAC draws one Extract-table value. -/
def baseAllowance (caps : PqxdhServerAuthSourceCosts.KemCaps) : Fin 14 → EffectKind → Nat
  | kind, .coin => ![0, 64 + caps.keygenCost, 32, 96 + caps.encapsCost, 0, 69 * max 64 caps.decapsCost, 64,
      0, 0, 0, 0, 0, 0, 0] kind
  | kind, .hash => if kind = 4 ∨ kind = 5 then 1 else 0
  | kind, .administrative => if kind = 1 ∨ kind = 2 ∨ kind = 4 ∨ kind = 5 then 1 else 0

/-- The CE-11 caps (plan section 31): the outer budget and the shared-hash cap `qHash + S + R + envTotal(.hash)`. -/
def capsG (B : PqxdhDeploymentInterface.Budget) (allowance : Fin 14 → EffectKind → Nat) : PqxdhRecordLiftInterface.Caps :=
  ⟨B, B.hash + B.sends + B.receives + PqxdhRecordLiftInterface.Caps.envTotal ⟨B, 0⟩ allowance .hash⟩

/-- An allowance with one BLAKE2b query at build and at finish and none elsewhere has the environment hash total `qBuild + qFinish`. -/
theorem envTotal_hash (B : PqxdhDeploymentInterface.Budget) (sharedHash : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (hashes : ∀ kind, allowance kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0) :
    PqxdhRecordLiftInterface.Caps.envTotal ⟨B, sharedHash⟩ allowance .hash = B.build + B.finish := by
  simp only [PqxdhRecordLiftInterface.Caps.envTotal, hashes, Fin.sum_univ_succ, Fin.sum_univ_zero,
    PqxdhDeploymentInterface.Budget.cap]
  simp

/-- The shared-hash cap of the CE-11 caps is `qHash + S + R + qBuild + qFinish` (plan section 31). -/
theorem capsG_sharedHash (B : PqxdhDeploymentInterface.Budget) (allowance : Fin 14 → EffectKind → Nat)
    (hashes : ∀ kind, allowance kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0) :
    (capsG B allowance).sharedHash = B.hash + B.sends + B.receives + B.build + B.finish := by
  simp only [capsG, envTotal_hash B 0 allowance hashes, Nat.add_assoc]

/-- The derivation allowance of the CE-11 caps is the frozen `sends + 51 * receives`. -/
theorem capsG_derivations (B : PqxdhDeploymentInterface.Budget) (allowance : Fin 14 → EffectKind → Nat) :
    (capsG B allowance).derivations = B.sends + 51 * B.receives := rfl

/-- The real allowance has one BLAKE2b query at build and at finish and none elsewhere. -/
theorem baseAllowance_hash (caps : PqxdhServerAuthSourceCosts.KemCaps) (kind : Fin 14) :
    baseAllowance caps kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0 := rfl

/-- The real allowance of the post-phase HMAC class (class 6) is one Extract-table value and nothing else (plan section 33: coin 64, hash 0, administrative 0). -/
theorem baseAllowance_six (caps : PqxdhServerAuthSourceCosts.KemCaps) (kind : EffectKind) :
    baseAllowance caps 6 kind = if kind = .coin then 64 else 0 := by
  cases kind <;> simp [baseAllowance]

/-- The CE first-touch classes do not include the HMAC class, so the first-touch allowance of class 6 is the core's. -/
theorem allowanceG_six (core : Fin 14 → EffectKind → Nat) (kind : EffectKind) :
    allowanceG core ceFirstTouch 6 kind = core 6 kind := by
  simp [allowanceG, ceFirstTouch]

/-- The CE first-touch allowance over any core with that BLAKE2b pattern keeps it. -/
theorem allowanceG_hash (core : Fin 14 → EffectKind → Nat) (firstTouch : Fin 14 → Bool)
    (hashes : ∀ kind, core kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0) (kind : Fin 14) :
    allowanceG core firstTouch kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0 := by
  rw [allowanceG_other core firstTouch kind .hash (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]), hashes]

section C4
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response E X : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)

/-- C4 (plan sections 31 and 33): for every environment framed by an allowance and every adversary respecting the budget `B`, every outcome of the record world has its two BLAKE2b routes within the CE-11 shared-hash cap and its record derivations within the frozen derivation cap. This instantiates `PqxdhRecordLiftWorldBudget.run_hash` and `run_kdf`. -/
theorem c4_instance (env : Environment n E) (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : PqxdhRecordLiftInterface.Frame env startupCoins allowance) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : B.Respects adversary) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤ (capsG B allowance).sharedHash ∧
        result.2.primitive.1.native .kdf ≤ (capsG B allowance).derivations :=
  fun result supported =>
    ⟨PqxdhRecordLiftWorldBudget.run_hash setup codec route env serverKid bounds mode (capsG B allowance) startupCoins
        allowance framed adversary respects result supported,
      PqxdhRecordLiftWorldBudget.run_kdf setup codec route env serverKid bounds mode (capsG B allowance) adversary
        respects result supported⟩

/-- C4 in closed form for an allowance with one BLAKE2b query at build and at finish: `qHash + S + R + qBuild + qFinish` and `S + 51 R`. -/
theorem c4_closed (env : Environment n E) (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : PqxdhRecordLiftInterface.Frame env startupCoins allowance)
    (hashes : ∀ kind, allowance kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (respects : B.Respects adversary) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route env serverKid bounds mode adversary),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          B.hash + B.sends + B.receives + B.build + B.finish ∧
        result.2.primitive.1.native .kdf ≤ B.sends + 51 * B.receives := by
  intro result supported
  have bound := c4_instance setup codec route env startupCoins allowance framed serverKid bounds mode B adversary
    respects result supported
  rw [capsG_sharedHash B allowance hashes, capsG_derivations] at bound
  exact bound

/-- Later-mode C4 (plan section 33, r6-later reply point 5): with no BLAKE2b allowance at the post-phase HMAC class, every outcome of the two-phase record world has its BLAKE2b routes within the CE-11 shared-hash cap plus the post-phase BLAKE2b budget, and its record derivations within the frozen cap. -/
theorem c4_later {Out R : Type} (env : Environment n E) (startupCoins : Nat) (allowance : Fin 14 → EffectKind → Nat)
    (framed : PqxdhRecordLiftInterface.Frame env startupCoins allowance) (sixHash : allowance 6 .hash = 0)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (post : PqxdhDeploymentLater.PostBudget) (reveal : E → R)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (respects : B.Respects first) (laterRespects : ∀ output disclosed, post.Respects (second output disclosed)) :
    ∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route env serverKid bounds mode reveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          (capsG B allowance).sharedHash + post.hash ∧
        result.2.primitive.1.native .kdf ≤ (capsG B allowance).derivations := by
  intro result supported
  have hashes := PqxdhRecordLiftLater.run_hash setup codec route env serverKid bounds mode (capsG B allowance) post
    reveal startupCoins allowance framed first second respects laterRespects result supported
  have kdf := PqxdhRecordLiftLater.run_kdf setup codec route env serverKid bounds mode (capsG B allowance) reveal
    first second respects result supported
  have postHash : PqxdhRecordLiftLater.postCost allowance post .hash = post.hash := by
    simp only [PqxdhRecordLiftLater.postCost, sixHash, Nat.zero_mul, Nat.add_zero]
  have shared : (capsG B allowance).sharedHash = (capsG B allowance).outer.hash + (capsG B allowance).outer.sends +
      (capsG B allowance).outer.receives + (capsG B allowance).envTotal allowance .hash := rfl
  rw [postHash] at hashes
  rw [shared]
  exact ⟨hashes, kdf⟩

/-- Later-mode C4 in closed form: `qHash + S + R + qBuild + qFinish + qHash₂` and `S + 51 R`. -/
theorem c4_later_closed {Out R : Type} (env : Environment n E) (startupCoins : Nat)
    (allowance : Fin 14 → EffectKind → Nat) (framed : PqxdhRecordLiftInterface.Frame env startupCoins allowance)
    (hashes : ∀ kind, allowance kind .hash = if kind = 4 ∨ kind = 5 then 1 else 0)
    (serverKid : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (B : PqxdhDeploymentInterface.Budget) (post : PqxdhDeploymentLater.PostBudget) (reveal : E → R)
    (first : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X)
    (second : X → R → OracleComp PqxdhDeploymentLater.PostSpec Out)
    (respects : B.Respects first) (laterRespects : ∀ output disclosed, post.Respects (second output disclosed)) :
    ∀ result ∈ support (PqxdhRecordLiftLater.run setup codec route env serverKid bounds mode reveal first second),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          B.hash + B.sends + B.receives + B.build + B.finish + post.hash ∧
        result.2.primitive.1.native .kdf ≤ B.sends + 51 * B.receives := by
  intro result supported
  have bound := c4_later setup codec route env startupCoins allowance framed (by rw [hashes]; decide) serverKid bounds
    mode B post reveal first second respects laterRespects result supported
  rw [capsG_sharedHash B allowance hashes, capsG_derivations] at bound
  exact bound

end C4


/-! ### Effect bounds of the forwarded build -/

section BuildBounds
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The registration primitives of the Server build with the BLAKE2b request forwarded: the factor of `nativeTailFwd` after the seal expansion. -/
def regFwd : QueryImpl PqxdhServerRegistrationPublication.NativeSpec (OracleComp (EnvEffects n)) := fun query =>
  match query with
  | .inl request => (sharedFwd (n := n) setup.source.crypto codec.frameWrite setup.source ∘ₛ RawCtxMixedOwner.sendLift) request
  | .inr request => tailAuxFwd codec checks request

/-- The forwarded Server tail is the forwarded registration primitives after the seal expansion. -/
theorem nativeTailFwd_compose {α : Type} (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α) :
    simulateQ (nativeTailFwd (n := n) setup codec checks) work =
      simulateQ (regFwd setup codec checks) (simulateQ PqxdhServerRegistrationPublication.nativeAdapter work) := by
  rw [← QueryImpl.simulateQ_compose]
  rfl

/-- The seal log of the forwarded Server tail changes no reply. -/
theorem tailFwd_forget {α : Type} (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α)
    (log : List RawCtxSourceSend.SealContext) :
    Prod.fst <$> (simulateQ (tailFwd (n := n) setup codec checks) work).run log =
      simulateQ (nativeTailFwd setup codec checks) work := by
  induction work using OracleComp.inductionOn generalizing log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind, ih]
      rcases query with (request | input) | request
      · simp only [tailFwd, StateT.run_lift, bind_assoc, pure_bind]
      · simp only [tailFwd, StateT.run, bind_assoc, pure_bind]
      · simp only [tailFwd, StateT.run_lift, bind_assoc, pure_bind]

/-- Every forwarded registration primitive issues at most one BLAKE2b effect, exactly when it is the BLAKE2b request, and no other effect. -/
theorem regFwd_bound (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (kind : EffectKind) :
    (regFwd (n := n) setup codec checks query).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash ∧ PqxdhServerAuthTailCosts.registrationHash query = true then 1 else 0) := by
  rcases query with (request | (input | (bytes | frame))) | request
  · simp only [regFwd, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, simulateQ_spec_query, sharedFwd,
      RawCtxMixedShared.sharedAdapter, primFwd]
    trivial
  · simp only [regFwd, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, simulateQ_spec_query, sharedFwd,
      RawCtxMixedShared.sharedAdapter, simulateQ_pure]
    trivial
  · simp only [regFwd, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, simulateQ_spec_query, sharedFwd,
      RawCtxMixedShared.sharedAdapter, primFwd, request, isQueryBoundP_map_iff]
    rw [isQueryBoundP_query_iff]
    intro same
    simp only [effectKind] at same
    subst same
    simp [PqxdhServerAuthTailCosts.registrationHash, PqxdhServerRegistrationPublication.leftPredicate,
      RawCtxSourceSeal.category, RawCtxSourceSeal.sealingPredicate, RawCtxSourceSeal.callKind]
  · simp only [regFwd, QueryImpl.apply_compose, RawCtxMixedOwner.sendLift, simulateQ_spec_query, sharedFwd,
      RawCtxMixedShared.sharedAdapter, simulateQ_pure]
    trivial
  · cases request <;> simp only [regFwd, tailAuxFwd] <;> trivial

/-- The forwarded Server build issues no coin, at most one BLAKE2b effect (its sequence-one seal) and no administrative effect. -/
theorem build_fwd_bound (pending : pqxdh.PendingServerRegistration) (root : PqxdhSecretInputKdf.RootOutput)
    (payload : Option Pqxdh.Bytes) (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes))
    (log : List RawCtxSourceSend.SealContext) (kind : EffectKind) :
    ((simulateQ (tailFwd (n := n) setup codec checks)
      (PqxdhServerRegistrationPublication.build setup.source pending root payload () server)).run log).IsQueryBoundP
        (fun effect => effectKind effect = kind) (if kind = .hash then 1 else 0) := by
  rw [← isQueryBoundP_map_iff _ Prod.fst, tailFwd_forget, nativeTailFwd_compose]
  by_cases hash : kind = .hash
  · simp only [hash, ite_true]
    apply RawCtxSourceOpen.simulate_bound _ (fun query => PqxdhServerAuthTailCosts.registrationHash query = true) _ _ 1
      ((PqxdhServerRegistrationPublication.native_build_bounds setup.source pending root payload () server).2.1 .hash)
    intro query
    have step := regFwd_bound (n := n) setup codec checks query .hash
    simp only [true_and] at step
    convert step using 2
    by_cases found : PqxdhServerAuthTailCosts.registrationHash query = true <;> simp only [found]
  · simp only [hash, ite_false]
    apply IsQueryBoundP.simulateQ_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim)
    intro query _
    have step := regFwd_bound (n := n) setup codec checks query kind
    simpa only [hash, false_and, ite_false] using step

end BuildBounds


/-! ### BLAKE2b requests of the Beacon finish -/

section FinishHash
variable {I D K X Response : Type}

/-- The BLAKE2b request among the Beacon's native tail callbacks. -/
def tailHash : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain → Bool
  | .inl query => RawCtxSourceOpen.openingPredicate Sum.isLeft query
  | .inr _ => false

/-- The BLAKE2b request among the Beacon's native finish callbacks. -/
def ownerHash : (PqxdhBeaconPhase2Publication.NativeSpec I D K X Response).Domain → Bool
  | .inl _ => false
  | .inr query => tailHash query

/-- The native Beacon tail after the root issues at most one BLAKE2b request: only the sequence-one opening of its finish-time receive hashes (`RawCtxSourceOpen.raw_primitive_bounds`). -/
theorem afterRoot_hash_bound (decode : RawCtxReceive.FrameDecoder)
    (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) (root : PqxdhBeaconPhase2Preparation.Word32) :
    (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.afterRoot decode prepared root)).IsQueryBoundP (fun query => tailHash query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.afterRoot PqxdhBeaconPhase2Publication.initialRun
  simp only [bind_assoc, pure_bind, simulateQ_bind, simulateQ_spec_query, PqxdhBeaconPhase2Publication.nativeTailAdapter]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp only [tailHash, Bool.false_eq_true, not_false_eq_true]), fun response => ?_⟩
  simp only [tailHash, Bool.false_eq_true, ite_false]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp only [Bool.false_eq_true, not_false_eq_true]), fun reply => ?_⟩
  simp only [Bool.false_eq_true, ite_false]
  cases reply with
  | none => simp only [simulateQ_pure]; trivial
  | some raw =>
      simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_raw_lift, isQueryBoundP_map_iff]
      apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Publication.nativeRawLift
        (fun query => RawCtxSourceOpen.openingPredicate Sum.isLeft query = true) _ _ 1
        (RawCtxSourceOpen.raw_primitive_bounds decode raw _).1
      intro query
      simp only [PqxdhBeaconPhase2Publication.nativeRawLift]
      exact (isQueryBoundP_query_iff _ _ _).mpr fun found => by simpa only [tailHash, found, ite_true] using Nat.one_pos

/-- The native Beacon tail issues at most one BLAKE2b request. -/
theorem tail_hash_bound (decode : RawCtxReceive.FrameDecoder) (prepared : PqxdhBeaconPhase2Preparation.Prepared Response) :
    (simulateQ PqxdhBeaconPhase2Publication.nativeTailAdapter
      (PqxdhBeaconPhase2Publication.tail decode prepared)).IsQueryBoundP (fun query => tailHash query = true) 1 := by
  unfold PqxdhBeaconPhase2Publication.tail
  simp only [simulateQ_bind, simulateQ_spec_query, PqxdhBeaconPhase2Publication.nativeTailAdapter]
  rw [isQueryBoundP_query_bind_iff]
  refine ⟨Or.inl (by simp only [tailHash, Bool.false_eq_true, not_false_eq_true]), fun reply => ?_⟩
  simp only [tailHash, Bool.false_eq_true, ite_false]
  cases reply with
  | none => simp only [simulateQ_pure]; trivial
  | some root => exact afterRoot_hash_bound decode prepared root

/-- The native Beacon finish issues at most one BLAKE2b request, whatever its raw input and owner. -/
theorem owner_hash_bound (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Publication.nativeOwner (X := X) (Response := Response) decode raw state).IsQueryBoundP
      (fun query => ownerHash query = true) 1 := by
  cases active : state.beacon.phase with
  | initSent control prekey oneTime kem =>
      simp only [PqxdhBeaconPhase2Publication.nativeOwner, PqxdhBeaconPhase2Publication.owner, active, simulateQ_bind]
      apply (isQueryBoundP_bind (n := 0) (m := 1) ?_ ?_).mono (by omega)
      · rw [← QueryImpl.simulateQ_compose]
        apply IsQueryBoundP.simulateQ_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim)
        intro query _
        simp only [QueryImpl.apply_compose, PqxdhBeaconPhase2Publication.preLift]
        rw [show simulateQ PqxdhBeaconPhase2Publication.nativeAdapter
            (liftM ((PqxdhBeaconPhase2Publication.FullSpec I D K X Response).query (.inl query))) =
          liftM ((PqxdhBeaconPhase2Publication.NativeSpec I D K X Response).query (.inl query)) from
          simulateQ_spec_query PqxdhBeaconPhase2Publication.nativeAdapter (.inl query)]
        exact (isQueryBoundP_query_iff _ _ _).mpr fun found => by simp only [ownerHash, Bool.false_eq_true] at found
      · intro prepared _
        cases prepared with
        | none => simp only [simulateQ_pure]; trivial
        | some prepared =>
            simp only [bind_pure_comp, simulateQ_map, PqxdhBeaconPhase2Bounds.native_tail_lift, isQueryBoundP_map_iff]
            apply RawCtxSourceOpen.simulate_bound PqxdhBeaconPhase2Publication.nativeTailLift
              (fun query => tailHash query = true) _ _ 1 (tail_hash_bound decode prepared)
            intro query
            simp only [PqxdhBeaconPhase2Publication.nativeTailLift]
            exact (isQueryBoundP_query_iff _ _ _).mpr fun found => by
              simp only [ownerHash] at found
              simp only [found, ite_true, Nat.one_pos]
  | _ => simp only [PqxdhBeaconPhase2Publication.nativeOwner, PqxdhBeaconPhase2Publication.owner, active,
      simulateQ_pure]; trivial

end FinishHash


/-! ### Effect bounds of the forwarded finish -/

section FinishBounds
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- A forwarded source primitive issues one BLAKE2b effect exactly when it is the BLAKE2b request, and no other effect. -/
theorem primFwd_bound (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (kind : EffectKind) :
    (primFwd (n := n) c source query).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash ∧ RawCtxSourceOpen.openingPredicate Sum.isLeft query = true then 1 else 0) := by
  rcases query with request | (bytes | input)
  · simp only [primFwd]; trivial
  · simp only [primFwd, request, isQueryBoundP_map_iff]
    rw [isQueryBoundP_query_iff]
    intro same
    simp only [effectKind] at same
    subst same
    simp [RawCtxSourceOpen.openingPredicate]
  · simp only [primFwd]; trivial

/-- A forwarded Beacon tail callback issues one BLAKE2b effect exactly when it is the BLAKE2b request, and no other effect. -/
theorem beaconFwd_bound (query : (PqxdhBeaconPhase2Publication.NativeTailSpec Response).Domain) (kind : EffectKind) :
    (beaconFwd (n := n) setup codec query).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash ∧ tailHash query = true then 1 else 0) := by
  rcases query with query | request
  · exact primFwd_bound setup.source.crypto setup.source query kind
  · cases request <;> simp only [beaconFwd] <;> trivial

/-- Every forwarded finish callback issues at most `max 64 decaps` coin effects (the decapsulation or one Extract-table value), one BLAKE2b effect exactly at the BLAKE2b request, and no administrative effect. -/
theorem callbacksFwd_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) (kind : EffectKind) :
    ((callbacksFwd (n := n) setup codec query).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .coin then max 64 caps.decapsCost else if kind = .hash ∧ ownerHash query = true then 1 else 0) := by
  rcases query with query | query
  · simp only [callbacksFwd, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, ownerHash, Bool.false_eq_true,
      and_false, ite_false]
    apply (coins_bound _ _ (PqxdhRegistrationSchedule.preparation_uniform setup codec caps bounded query) kind).mono
    by_cases coin : kind = .coin
    · simp only [coin, ite_true, le_max_right]
    · simp only [coin, ite_false, le_refl]
  · rcases query with query | request
    · simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, bind_pure_comp,
        isQueryBoundP_map_iff, ownerHash]
      apply (beaconFwd_bound setup codec (.inl query) kind).mono
      by_cases coin : kind = .coin
      · simp only [coin, reduceCtorEq, false_and, ite_false, ite_true, Nat.zero_le]
      · by_cases found : kind = .hash ∧ tailHash (Response := Response) (.inl query) = true <;>
          simp only [coin, found, and_self, reduceCtorEq, ite_true, ite_false, le_refl]
    · cases request with
      | root input =>
          simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, ownerHash, tailHash, Bool.false_eq_true,
            and_false, ite_false]
          apply (coins_bound _ _ (PqxdhRegistrationSchedule.sourceRoot_uniform setup.hmac input state) kind).mono
          by_cases coin : kind = .coin
          · simp only [coin, ite_true, le_max_left]
          · simp only [coin, ite_false, le_refl]
      | initial request =>
          simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, beaconFwd, pure_bind]
          trivial
      | application response =>
          simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, beaconFwd, pure_bind]
          trivial

/-- The forwarded Beacon finish issues at most `69 * max 64 decaps` coin effects, at most one BLAKE2b effect (its sequence-one opening) and no administrative effect. -/
theorem finish_fwd_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : NativeState KemSK) (kind : EffectKind) :
    ((simulateQ (callbacksFwd (n := n) setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state).IsQueryBoundP
        (fun effect => effectKind effect = kind)
        (if kind = .coin then 69 * max 64 caps.decapsCost else if kind = .hash then 1 else 0) := by
  by_cases coin : kind = .coin
  · subst coin
    simp only [ite_true]
    exact PqxdhBeaconPhase2Bounds.native_interpreted_bound _ _ _ (fun query current => by
      simpa only [ite_true] using callbacksFwd_bound setup codec caps bounded query current .coin) _ _ _ _
  · by_cases hash : kind = .hash
    · subst hash
      simp only [reduceCtorEq, ite_false, ite_true]
      refine IsQueryBoundP.simulateQ_run_of_step (owner_hash_bound _ _ _) (fun query found current => ?_)
        (fun query missing current => ?_) state
      · have step := callbacksFwd_bound (n := n) setup codec caps bounded query current .hash
        simp only [reduceCtorEq, ite_false, true_and] at step
        simpa only [found, ite_true] using step
      · have step := callbacksFwd_bound (n := n) setup codec caps bounded query current .hash
        simp only [reduceCtorEq, ite_false, true_and] at step
        simpa only [missing, Bool.false_eq_true, ite_false] using step
    · simp only [coin, hash, ite_false]
      have bound := PqxdhBeaconPhase2Bounds.native_interpreted_bound (callbacksFwd (n := n) setup codec)
        (fun effect => effectKind effect = kind) 0 (fun query current => by
          simpa only [coin, hash, false_and, ite_false] using callbacksFwd_bound setup codec caps bounded query current kind)
        codec.frameRead raw owner state
      simpa only [Nat.mul_zero] using bound

end FinishBounds


/-! ### Single-install ingredients: consumed tokens and terminal owners -/

section Once
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Stripping keeps the pending registration tokens. -/
theorem strip_pending (state : PqxdhRegistrationSchedule.State KemSK) :
    (strip state).shared.2.pending = state.shared.2.pending := rfl

/-- Stripping keeps the owner list's length. -/
theorem strip_owners_length (state : PqxdhRegistrationSchedule.State KemSK) :
    (strip state).owners.length = state.owners.length := List.length_map _

/-- A build consumes its session's token on every outcome (the Rust token is moved, `PqxdhRegistrationScheduleState.build_consumes`): after any build step the session has no pending token. -/
theorem buildStep_consumes (session : Nat) (payload : Option Pqxdh.Bytes) (state : EnvState KemSK Bk) :
    ∀ result ∈ support ((buildStep (n := n) setup codec checks session payload).run state),
      result.2.native.shared.2.pending session = none := by
  intro result supported
  change result ∈ support (buildStep setup codec checks session payload state) at supported
  unfold buildStep at supported
  dsimp only at supported
  split at supported
  · rename_i absent
    simp only [support_pure, Set.mem_singleton_iff] at supported
    subst supported
    exact absent
  · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
    obtain ⟨_, _, _, _, rfl⟩ := supported
    simp only [strip_pending, Function.update_self]

/-- A build at a session without a pending token issues no effect and changes nothing. -/
theorem buildStep_idle (session : Nat) (payload : Option Pqxdh.Bytes) (state : EnvState KemSK Bk)
    (absent : state.native.shared.2.pending session = none) :
    (buildStep (n := n) setup codec checks session payload).run state = pure (none, state) := by
  change buildStep setup codec checks session payload state = _
  unfold buildStep
  simp only [absent]

/-- A finish at a terminal owner (established or aborted) issues no effect and changes no stripped state (`PqxdhRegistrationSchedule.no_retry`, `terminal_native`). -/
theorem finishStep_retry (owner : Nat) (raw : Pqxdh.Bytes) (state : EnvState KemSK Bk)
    (stripped : Stripped state.native) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (found : state.native.owners[owner]? = some before) (terminal : PqxdhRegistrationSchedule.Terminal before) :
    (finishStep (n := n) setup codec owner raw).run state = pure (none, state) := by
  change finishStep setup codec owner raw state = _
  unfold finishStep
  simp only [found, PqxdhRegistrationSchedule.terminal_native codec.frameRead raw before terminal, simulateQ_pure,
    StateT.run_pure, pure_bind]
  have quiet : ownerEffect (n := n) owner before before = pure () := by
    unfold PqxdhRegistrationSchedule.Terminal at terminal
    unfold ownerEffect
    cases phase : before.beacon.phase <;> simp only [phase] at terminal ⊢
    · simp only [inactiveTag, ite_true]
  have same : (⟨state.native.shared, state.native.owners.set owner before⟩ : PqxdhRegistrationSchedule.State KemSK) =
      state.native := by
    obtain ⟨below, element⟩ := List.getElem?_eq_some_iff.mp found
    rw [← element, List.set_getElem_self]
  simp only [quiet, pure_bind, same]
  rw [show strip state.native = state.native from stripped]

/-- A stateless simulation only shrinks the support. -/
theorem support_simulateQ_subset {ι₁ ι₂ α : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (impl : QueryImpl spec₁ (OracleComp spec₂)) (work : OracleComp spec₁ α) :
    support (simulateQ impl work) ⊆ support work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, support_pure, subset_refl]
  | query_bind query next ih =>
      intro result supported
      simp only [simulateQ_query_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, member⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply member⟩

/-- A finish from an initSent owner leaves the owner terminal on every outcome (`PqxdhRegistrationSchedule.finish_terminal`), kept with its kernel stripped. -/
theorem finishStep_terminal (owner : Nat) (raw : Pqxdh.Bytes) (state : EnvState KemSK Bk)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (found : state.native.owners[owner]? = some before)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (active : before.beacon.phase = .initSent control prekey oneTime kem) :
    ∀ result ∈ support ((finishStep (n := n) setup codec owner raw).run state), ∃ after,
      result.2.native.owners[owner]? = some (stripOwner after) ∧ PqxdhRegistrationSchedule.Terminal after := by
  intro result supported
  change result ∈ support (finishStep setup codec owner raw state) at supported
  unfold finishStep at supported
  simp only [found, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨inner, member, _, _, rfl⟩ := supported
  have reached : inner.1 ∈ support (PqxdhBeaconPhase2Publication.nativeOwner (X := PqxdhJointIdentity.IdentitySeed)
      (Response := Response) codec.frameRead raw before) := by
    apply OracleComp.support_simulateQ_run'_subset (callbacksFwd (n := n) setup codec) _ state.native.shared
    rw [StateT.run'_eq, support_map]
    exact ⟨inner, member, rfl⟩
  have shape : ∃ staged, inner.1 = PqxdhBeaconPhase2Publication.finish control before staged := by
    have sourced := support_simulateQ_subset _ _ reached
    simp only [PqxdhBeaconPhase2Publication.owner, active, mem_support_bind_iff] at sourced
    obtain ⟨prepared, _, rest⟩ := sourced
    cases prepared with
    | none =>
        simp only [support_pure, Set.mem_singleton_iff] at rest
        exact ⟨none, rest⟩
    | some prepared =>
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at rest
        obtain ⟨staged, _, same⟩ := rest
        exact ⟨staged, same⟩
  obtain ⟨staged, same⟩ := shape
  obtain ⟨below, _⟩ := List.getElem?_eq_some_iff.mp found
  refine ⟨inner.1.2, ?_, ?_⟩
  · simp only [strip, List.getElem?_map, List.getElem?_set_self below, Option.map_some]
  · rw [same]
    exact PqxdhRegistrationSchedule.finish_terminal control before staged

end Once

/-! ### Split hidden wrappers in capability form -/

section GenericBuild
variable {ι₀ : Type} {spec₀ : OracleSpec ι₀} (p : ι₀ → Prop) [DecidablePred p]

/-- The first-send publication of the generic builder issues its send's effects and nothing more (`PqxdhServerAuthEntryFactor.generic_after_uniform`, for any counted effect). -/
theorem generic_after_bound {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ (OracleComp spec₀)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ (OracleComp spec₀))) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsQueryBoundP p cost)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP p 0)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (kernel : K)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata server).run
      state).IsQueryBoundP p cost := by
  simp only [PqxdhInitialGenericPublication.afterInitialization, StateT.run_bind]
  apply (isQueryBoundP_bind (m := 0) (sendBound _ _ state) ?_).mono (by omega)
  rintro ⟨⟨advanced, encrypted⟩, current⟩ _
  apply (isQueryBoundP_bind (n := 0) (m := 0) (auxBound (.erase authenticated) current) ?_).mono (by omega)
  intro erased _
  cases encrypted with
  | none => trivial
  | some encrypted =>
      apply (isQueryBoundP_bind (n := 0) (m := 0) (auxBound (.write _) erased.2) ?_).mono (by omega)
      rintro ⟨(_ | serialized), afterWrite⟩ _ <;> trivial

/-- All candidate admission, allocation and initialization branches of the generic builder issue at most its send's effects. -/
theorem generic_candidate_bound {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ (OracleComp spec₀)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ (OracleComp spec₀))) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsQueryBoundP p cost)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP p 0)
    (initial : RustM K) (candidate : pqxdh.ServerRegistrationCandidate) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata server).run state).IsQueryBoundP
      p cost := by
  simp only [PqxdhInitialGenericBuilder.candidate, StateT.run_bind]
  apply (isQueryBoundP_bind (n := 0) (m := cost) (auxBound (.checkIdentity _) state) ?_).mono (by omega)
  rintro ⟨valid, checked⟩ _
  cases valid with
  | false => trivial
  | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      apply (isQueryBoundP_bind (n := 0) (m := cost) (auxBound .reservePeer checked) ?_).mono (by omega)
      rintro ⟨reserved, reservedState⟩ _
      cases reserved with
      | false => trivial
      | true =>
          simp only [Bool.not_true, Bool.false_eq_true, ite_false]
          cases initial with
          | fail error => trivial
          | div => trivial
          | ok kernel =>
              simp only [PqxdhInitialGenericBuilder.continueRust]
              split_ifs
              · trivial
              · apply (isQueryBoundP_bind (n := 0) (m := cost) (auxBound (.reservePlaintext _) reservedState) ?_).mono
                  (by omega)
                rintro ⟨allocated, allocatedState⟩ _
                cases allocated with
                | false => trivial
                | true =>
                    simp only [Bool.not_true, Bool.false_eq_true, ite_false]
                    cases candidate.key_id_binding with
                    | fail error => trivial
                    | div => trivial
                    | ok binding =>
                        change ((ok <$> PqxdhInitialGenericPublication.afterInitialization calls aux candidate
                          (absBytes binding.bytes ++ data.getD PqxdhServerRegistrationPublication.registrationWitness)
                          kernel metadata server).run allocatedState).IsQueryBoundP p cost
                        rw [StateT.run_map, isQueryBoundP_map_iff]
                        exact generic_after_bound p calls aux cost sendBound auxBound candidate _ kernel metadata server
                          allocatedState
              · trivial

/-- The generic Server builder issues at most its send's effects through all key-ID, admission, allocation and writer branches. -/
theorem generic_build_bound {K σ Metadata PeerMetadata Consumed : Type}
    (calls : RawCtxChainOwner.Calls K (StateT σ (OracleComp spec₀)))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (StateT σ (OracleComp spec₀))) (cost : Nat)
    (sendBound : ∀ entry context state, ((calls.send entry context).run state).IsQueryBoundP p cost)
    (auxBound : ∀ query state, ((aux query).run state).IsQueryBoundP p 0)
    (initial : RustM K) (pending : pqxdh.PendingServerRegistration) (data : Option Pqxdh.Bytes)
    (metadata : PeerMetadata) (server : PqxdhInitialGenericPublication.State K Metadata PeerMetadata Consumed)
    (state : σ) :
    ((PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata server).run state).IsQueryBoundP
      p cost := by
  unfold PqxdhServerAuthSendFactor.genericBuild
  cases pqxdh.server_next_key_id server.control with
  | fail error => trivial
  | div => trivial
  | ok next =>
      cases next with
      | Err error => trivial
      | Ok next =>
          simp only [PqxdhInitialGenericBuilder.continueRust]
          cases pqxdh.server_prepare_commit server.control pending
              ⟨server.server.identity, server.identityKeyId⟩
              (if (server.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
          | fail error => trivial
          | div => trivial
          | ok prepared =>
              cases prepared with
              | Err error => trivial
              | Ok candidate =>
                  exact generic_candidate_bound p calls aux cost sendBound auxBound initial candidate data metadata
                    server state

end GenericBuild

section SplitWrappers
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- One forwarded Server tail callback issues one BLAKE2b effect at most, only for a seal, and no other effect. -/
theorem nativeTailFwd_bound (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (kind : EffectKind) :
    (nativeTailFwd (n := n) setup codec checks query).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash ∧ PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) := by
  have single : nativeTailFwd (n := n) setup codec checks query =
      simulateQ (regFwd setup codec checks) (simulateQ PqxdhServerRegistrationPublication.nativeAdapter
        (liftM (PqxdhServerRegistrationPublication.TailSpec.query query))) := by
    rw [← nativeTailFwd_compose, simulateQ_spec_query]
  rw [single]
  by_cases hash : kind = .hash
  · subst hash
    simp only [true_and]
    have seals : (liftM (PqxdhServerRegistrationPublication.TailSpec.query query) :
        OracleComp PqxdhServerRegistrationPublication.TailSpec _).IsQueryBoundP
        (fun request => PqxdhServerRegistrationPublication.callKind request = .seal)
        (if PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) :=
      (isQueryBoundP_query_iff _ _ _).mpr fun found => by simp only [found, ite_true, Nat.one_pos]
    apply RawCtxSourceOpen.simulate_bound _ (fun request => PqxdhServerAuthTailCosts.registrationHash request = true) _ _ _
      (PqxdhServerRegistrationPublication.native_seal_bound _ _ seals .hash)
    intro request
    have step := regFwd_bound (n := n) setup codec checks request .hash
    simp only [true_and] at step
    convert step using 2
    by_cases found : PqxdhServerAuthTailCosts.registrationHash request = true <;> simp only [found]
  · simp only [hash, false_and, ite_false]
    apply IsQueryBoundP.simulateQ_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim)
    intro request _
    simpa only [hash, false_and, ite_false] using regFwd_bound (n := n) setup codec checks request kind

/-- One forwarded logged tail callback issues one BLAKE2b effect at most, only for a seal, and no other effect. -/
theorem tailFwd_bound (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (log : List RawCtxSourceSend.SealContext) (kind : EffectKind) :
    ((tailFwd (n := n) setup codec checks query).run log).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .hash ∧ PqxdhServerRegistrationPublication.callKind query = .seal then 1 else 0) := by
  have forget := tailFwd_forget (n := n) setup codec checks
    (liftM (PqxdhServerRegistrationPublication.TailSpec.query query)) log
  simp only [simulateQ_spec_query] at forget
  rw [← isQueryBoundP_map_iff _ Prod.fst, forget]
  exact nativeTailFwd_bound setup codec checks query kind

/-- The intended capability form of the split hidden build `PqxdhDeploymentHiddenSplit.buildSplit`, with the BLAKE2b request forwarded: the factored Server build at the environment material and the dummy seed on the forwarded logged tail, publishing the placeholder kernel. Its factoring against `buildSplit` is not proved here; only the cost of `buildSplitEnv`, which runs it, is (`buildSplit_env_cost`). -/
noncomputable def buildSplitFwd (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    StateT (List RawCtxSourceSend.SealContext) (OracleComp (EnvEffects n))
      (RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState)) :=
  Functor.map (PqxdhDeploymentHiddenSplit.replaceRaw placeholderKernel) <$>
    PqxdhServerAuthLoggedSendFactor.factored (fun entry _ _ => pure (entry, .None))
      (fun query => tailFwd setup codec checks (.inl query)) setup.source
      (fun query => tailFwd setup codec checks (.inr query))
      (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
        PqxdhDeploymentHiddenSplit.dummySeed)) token.pending payload () server

/-- The hidden install of a split build: the published peer, at the key ID of the response, installed in the world with the World's Server kernel of the slot. -/
def hiddenServerEffect (slot : Slot n) (settled : Option PqxdhServerRegistrationPublication.Response ×
    PqxdhServerAuthEntryFactor.ServerState) : OracleComp (EnvEffects n) Unit :=
  match settled.1 with
  | none => pure ()
  | some response => match settled.2.server.peers response.keyId with
      | none => pure ()
      | some peer => issue (.installServer response.keyId peer.identity (.hidden slot))

/-- The split hidden build of a slot in capability form: the forwarded split build, settled as the native build settles it, then the hidden install of the published peer. -/
noncomputable def buildSplitEnv (material : PqxdhDeploymentHiddenLayout.Material) (slot : Slot n)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    StateT (List RawCtxSourceSend.SealContext) (OracleComp (EnvEffects n))
      (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState) := do
  let result ← buildSplitFwd setup codec checks material token payload server
  let settled := PqxdhServerAuthExperiment.settle server result
  StateT.lift (hiddenServerEffect slot settled)
  pure settled

/-- The BLAKE2b request forwarded as the world's `.hash` capability. -/
def hashFx : QueryImpl CtxRomAuth.CtxRO (OracleComp (EnvEffects n)) := fun query => request (.hash query.2)

/-- The intended capability form of the split hidden finish `PqxdhDeploymentHiddenSplit.finishSplit`, with the BLAKE2b request forwarded: the erased hidden finish at the environment material and the dummy seed, with the real HKDF and the opening's BLAKE2b query as the world's `.hash`, staging the placeholder kernel. Its factoring against `finishSplit` is not proved here; only the cost of `finishSplitEnv` is (`finishSplit_env_cost`). -/
noncomputable def finishSplitFwd (material : PqxdhDeploymentHiddenLayout.Material)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) : OracleComp (EnvEffects n) (Option PqxdhBeaconPhase2Publication.Staged) :=
  simulateQ hashFx (Option.map (PqxdhDeploymentHiddenSplit.withKernel placeholderKernel) <$>
    (Prod.fst <$> PqxdhDeploymentHiddenKernels.finishErased (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto)
      (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response)) codec.frameRead
      (PqxdhPhase2DhRootConsumer.cleared pending)
      (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
        PqxdhDeploymentHiddenSplit.dummySeed))))

/-- The capability that publishes a hidden owner's finish: an established owner is installed with the World's Beacon kernel of the slot and the stored shell, any other change of the inactive tag (the abort) is an advance. -/
def hiddenOwnerEffect (slot : Slot n) (index : Nat) (before after : PqxdhRegistrationSchedule.Owner KemSK) :
    OracleComp (EnvEffects n) Unit :=
  match before.beacon.phase, after.beacon.phase with
  | .established _ _ _, _ => pure ()
  | _, .established control associatedData _ =>
      issue (.installBeacon index ⟨after.beacon.identityKeyId, control, associatedData⟩ (.hidden slot))
  | previous, current => match inactiveTag current with
      | some tag => if inactiveTag previous = some tag then pure () else issue (.advanceOwner index tag)
      | none => pure ()

/-- The split hidden finish of a slot in capability form: the forwarded split finish, the source commit with the two outer pin checks (`PqxdhBeaconPhase2Publication.finish`), then the hidden install or the abort. -/
noncomputable def finishSplitEnv (material : PqxdhDeploymentHiddenLayout.Material) (slot : Slot n) (index : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) :
    OracleComp (EnvEffects n) (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) := do
  let staged ← finishSplitFwd setup codec material pending
  let committed := PqxdhBeaconPhase2Publication.finish control before staged
  hiddenOwnerEffect slot index before committed.2
  pure committed

/-- The forwarded Server seal and KDF primitives: a seal issues at most one BLAKE2b effect, and nothing else is issued. -/
theorem loggedFwd_send_bound (challenge : RatchetKdfResponse) (entry : RawCtxSelectedChain.Kernel)
    (context : RawCtxSourceSend.SealContext) (log : List RawCtxSourceSend.SealContext) (kind : EffectKind) :
    (((PqxdhServerAuthLoggedSendFactor.calls (fun entry _ _ => pure (entry, .None))
      (fun query => tailFwd (n := n) setup codec checks (.inl query)) setup.source challenge).send entry context).run
        log).IsQueryBoundP (fun effect => effectKind effect = kind) (if kind = .hash then 1 else 0) := by
  change ((simulateQ (PqxdhServerAuthSendFactor.primLabels (fun query => tailFwd (n := n) setup codec checks (.inl query))
      setup.source challenge) (RawCtxChainSend.execute entry context)).run log).IsQueryBoundP _ _
  by_cases hash : kind = .hash
  · subst hash
    simp only [ite_true]
    refine IsQueryBoundP.simulateQ_run_of_step (RawCtxChainSend.program_seal_bound _) (fun query sealing current => ?_)
      (fun query other current => ?_) log
    · rcases query with slot | pending
      · simp at sealing
      · simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
          simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
        apply (isQueryBoundP_bind (m := 0) (tailFwd_bound setup codec checks _ current .hash)
          fun _ _ => isQueryBoundP_pure _ _ _).mono
        simp only [PqxdhServerRegistrationPublication.callKind, and_self, ite_true, Nat.add_zero, le_refl]
    · rcases query with slot | pending
      · simp only [PqxdhServerAuthSendFactor.primLabels, StateT.run_pure]; trivial
      · simp at other
  · simp only [hash, ite_false]
    refine IsQueryBoundP.simulateQ_run_of_step (isQueryBoundP_false _ 0) (fun _ absurd => absurd.elim)
      (fun query _ current => ?_) log
    rcases query with slot | pending
    · simp only [PqxdhServerAuthSendFactor.primLabels, StateT.run_pure]; trivial
    · simp only [PqxdhServerAuthSendFactor.primLabels, QueryImpl.apply_compose, RawCtxSourceSend.adapter,
        simulateQ_bind, simulateQ_spec_query, simulateQ_pure, StateT.run_bind, StateT.run_pure]
      apply (isQueryBoundP_bind (m := 0) (tailFwd_bound setup codec checks _ current kind)
        fun _ _ => isQueryBoundP_pure _ _ _).mono
      simp only [hash, false_and, ite_false, Nat.add_zero, le_refl]

/-- The split hidden build of a slot in capability form issues no coin, at most one BLAKE2b effect (its sequence-one seal) and at most one administrative effect (the hidden Server install, `installServer keyId identity (.hidden slot)`); like every environment program it has no capability that reads a seed or a kernel. -/
theorem buildSplit_env_cost (material : PqxdhDeploymentHiddenLayout.Material) (slot : Slot n)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) (log : List RawCtxSourceSend.SealContext) (kind : EffectKind) :
    ((buildSplitEnv setup codec checks material slot token payload server).run log).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .coin then 0 else 1) := by
  have factored : ((buildSplitFwd (n := n) setup codec checks material token payload server).run log).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .hash then 1 else 0) := by
    simp only [buildSplitFwd, PqxdhServerAuthLoggedSendFactor.factored, StateT.run_map, isQueryBoundP_map_iff]
    exact generic_build_bound _ _ _ _ (fun entry context current => loggedFwd_send_bound setup codec checks _ entry
      context current kind) (fun query current => by
        have bound := tailFwd_bound (n := n) setup codec checks (.inr query) current kind
        cases query <;> simpa only [PqxdhServerRegistrationPublication.callKind, PqxdhServerRegistrationPublication.auxKind,
          reduceCtorEq, and_false, ite_false] using bound) _ _ _ _ _ log
  have installed : ∀ settled, (hiddenServerEffect (n := n) slot settled).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .administrative then 1 else 0) := by
    intro settled
    unfold hiddenServerEffect
    split
    · trivial
    · split
      · trivial
      · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind
  simp only [buildSplitEnv, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
  apply (isQueryBoundP_bind factored fun result _ => isQueryBoundP_bind (m := 0) (installed _)
    fun _ _ => isQueryBoundP_pure _ _ _).mono
  cases kind <;> simp

/-- The split hidden finish of a slot in capability form issues no coin, at most one BLAKE2b effect (the sequence-one opening of its finish-time receive, `PqxdhDeploymentHiddenEntry.finish_hash_bound`) and at most one administrative effect (the hidden Beacon install `installBeacon owner shell (.hidden slot)` or the abort `advanceOwner owner .aborted`); like every environment program it has no capability that reads a seed or a kernel. -/
theorem finishSplit_env_cost (material : PqxdhDeploymentHiddenLayout.Material) (slot : Slot n) (index : Nat)
    (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (pending : PqxdhPhase2DhMetadata.Prepared Response) (kind : EffectKind) :
    (finishSplitEnv setup codec material slot index control before pending).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .coin then 0 else 1) := by
  have rom : (Option.map (PqxdhDeploymentHiddenSplit.withKernel placeholderKernel) <$>
      (Prod.fst <$> PqxdhDeploymentHiddenKernels.finishErased (PqxdhDeploymentHiddenEntry.romPrim setup.source.crypto)
        (fun entry _ => pure (entry, none)) setup.source (fun response => pure (codec.application response)) codec.frameRead
        (PqxdhPhase2DhRootConsumer.cleared pending)
        (PqxdhServerAuthCtxMaterial.factor (PqxdhDeploymentHiddenLayout.joinOutput material
          PqxdhDeploymentHiddenSplit.dummySeed)))).IsTotalQueryBound 1 := by
    rw [IsTotalQueryBound, isQueryBound_map_iff]
    exact PqxdhDeploymentHiddenEntry.erased_total_le _ _ setup.source _ codec.frameRead _ _ 1
      (PqxdhDeploymentHiddenEntry.finish_hash_bound setup.source.crypto _ setup.source
        (fun response => pure (codec.application response)) (fun _ => trivial) codec.frameRead _ _)
  have forwarded : (finishSplitFwd (n := n) setup codec material pending).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .hash then 1 else 0) := by
    have bound := IsQueryBoundP.simulateQ_of_step_le_total (impl := hashFx (n := n)) (q := fun effect => effectKind effect = kind)
      (step := if kind = .hash then 1 else 0) rom (fun query => (isQueryBoundP_query_iff _ _ _).mpr fun same => by
        simp only [effectKind] at same
        simp only [← same, ite_true, Nat.one_pos])
    unfold finishSplitFwd
    simpa only [Nat.one_mul] using bound
  have installed : ∀ after : PqxdhRegistrationSchedule.Owner KemSK, (hiddenOwnerEffect (n := n) slot index before after).IsQueryBoundP
      (fun effect => effectKind effect = kind) (if kind = .administrative then 1 else 0) := by
    intro after
    unfold hiddenOwnerEffect
    split
    · trivial
    · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind
    · split
      · split
        · trivial
        · exact issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) kind
      · trivial
  unfold finishSplitEnv
  apply (isQueryBoundP_bind forwarded fun staged _ => isQueryBoundP_bind (m := 0) (installed _)
    fun _ _ => isQueryBoundP_pure _ _ _).mono
  cases kind <;> simp

end SplitWrappers

/-! ### Capability-form factoring: the native BLAKE2b cache is the world's `.hash` -/

section Factoring
variable {n : Nat}
open LazyOracleDiscard (StateLens CacheLens)

/-- The CTX reading of the environment's effects on a cache: coins are uniform draws, `.hash` is the lazy CTX oracle on the cache, and the administrative capabilities are answered by `admin` (any interpretation; the forwarded primitives issue none). -/
noncomputable def ctxEffects (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp)) :
    QueryImpl (EnvEffects n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.hash bytes) => CtxRomAuth.ctxRandomOracle ((), bytes)
  | .inr capability => admin capability

variable (admin : QueryImpl (CapabilitySpec n) (StateT CtxRomAuth.CtxRO.QueryCache ProbComp))

/-- Coin effects read back as the original coins, with the cache unchanged. -/
theorem ctxEffects_coins {α : Type} (work : ProbComp α) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (ctxEffects admin) (coins (n := n) work)).run cache = (fun value => (value, cache)) <$> work := by
  unfold coins
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind, coinFx]
      simp only [ctxEffects, StateT.run_lift, bind_assoc, pure_bind]
      refine bind_congr fun coin => ?_
      exact ih coin

/-- A forwarded step that never reads or writes the focused cache coordinate of its state, at the program level. -/
theorem frame_program {σ ι' α : Type} {spec' : OracleSpec ι'} (lens : CacheLens CtxRomAuth.CtxRO σ)
    (fwd : QueryImpl spec' (StateT σ (OracleComp (EnvEffects n))))
    (frame : ∀ query state cache, (fwd query).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (fwd query).run state)
    (work : OracleComp spec' α) (state : σ) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ fwd work).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (simulateQ fwd work).run state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, map_bind, frame, bind_map_left, ih]

/-- Generic capability-form factoring: if every native step is its forwarded step with the forwarded BLAKE2b queries answered by the lazy CTX oracle on the focused cache, and the forwarded steps never touch that coordinate, then every native program is its forwarded program read through `ctxEffects`. -/
theorem factor_program {σ ι' α : Type} {spec' : OracleSpec ι'} (lens : CacheLens CtxRomAuth.CtxRO σ)
    (native : QueryImpl spec' (StateT σ ProbComp)) (fwd : QueryImpl spec' (StateT σ (OracleComp (EnvEffects n))))
    (frame : ∀ query state cache, (fwd query).run (lens.set state cache) =
      (fun result => (result.1, lens.set result.2 cache)) <$> (fwd query).run state)
    (step : ∀ query state, (native query).run state =
      (fun result => (result.1.1, lens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((fwd query).run state)).run (lens.get state))
    (work : OracleComp spec' α) (state : σ) :
    (simulateQ native work).run state =
      (fun result => (result.1.1, lens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((simulateQ fwd work).run state)).run (lens.get state) := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, map_pure, lens.set_get]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, bind_map_left, ih, map_bind]
      refine bind_congr fun result => ?_
      rw [lens.get_set, frame_program lens fwd frame, simulateQ_map, StateT.run_map, Functor.map_map]
      congr 1
      funext final
      simp only [lens.set_set]

section Primitives
variable {Auxiliary : Type}

/-- The shared source primitives are the forwarded primitives read through `ctxEffects`, with the auxiliary state kept. -/
theorem primFwd_factor (c : Pqxdh.Crypto) (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (query : RawCtxSourceOpen.NativeSpec.Domain) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (RawCtxSharedPrimitive.nativeImpl c (RawCtxSourceHkdf.kdfImpl source) query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (primFwd (n := n) c source query)).run cache := by
  rcases query with request | (bytes | input)
  · simp only [primFwd, simulateQ_pure, StateT.run_pure, map_pure]
    exact RawCtxSourceHkdf.kdf_step source request (auxiliary, cache)
  · change (do
        let result ← (CtxRomAuth.ctxRandomOracle ((), bytes)).run cache
        pure (some result.1.toList, (auxiliary, result.2))) = _
    simp only [primFwd, simulateQ_map, request, simulateQ_spec_query, ctxEffects, StateT.run_map, Functor.map_map,
      bind_pure_comp]
  · simp only [primFwd, simulateQ_pure, StateT.run_pure, map_pure]
    rfl

/-- Generic stateless factoring: native steps on (auxiliary, cache) that are forwarded steps read through `ctxEffects` with the auxiliary state kept give the same for every program. -/
theorem factor_stateless {ι' α : Type} {spec' : OracleSpec ι'}
    (native : QueryImpl spec' (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (fwd : QueryImpl spec' (OracleComp (EnvEffects n)))
    (step : ∀ query auxiliary cache, (native query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$> (simulateQ (ctxEffects admin) (fwd query)).run cache)
    (work : OracleComp spec' α) (auxiliary : Auxiliary) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ native work).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$> (simulateQ (ctxEffects admin) (simulateQ fwd work)).run cache := by
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, step, bind_map_left, ih, map_bind]

end Primitives

section Registration
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response Auxiliary : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Every registration primitive of the Server build is its forwarded primitive read through `ctxEffects`. -/
theorem registration_factor (query : PqxdhServerRegistrationPublication.NativeSpec.Domain) (auxiliary : Auxiliary)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhRegistrationProtocolState.registrationImpl setup.source codec.frameWrite (PqxdhServerAuthExperiment.tailAux codec checks)
      query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (regFwd (n := n) setup codec checks query)).run cache := by
  rcases query with request | request
  · change ((RawCtxMixedShared.sharedImpl setup.source.crypto codec.frameWrite (RawCtxSourceHkdf.kdfImpl setup.source) ∘ₛ
        RawCtxMixedOwner.sendLift) request).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$> (simulateQ (ctxEffects admin)
        ((sharedFwd setup.source.crypto codec.frameWrite setup.source ∘ₛ RawCtxMixedOwner.sendLift) request)).run cache
    simp only [QueryImpl.apply_compose, RawCtxMixedShared.sharedImpl, sharedFwd, QueryImpl.simulateQ_compose]
    exact factor_stateless admin _ _ (fun query auxiliary cache => primFwd_factor admin setup.source.crypto setup.source
      query auxiliary cache) _ auxiliary cache
  · cases request <;> simp only [PqxdhRegistrationProtocolState.registrationImpl, PqxdhServerAuthExperiment.tailAux,
      regFwd, tailAuxFwd, simulateQ_pure, StateT.run_pure, map_pure]

/-- The Server's native response tail is its forwarded tail read through `ctxEffects`. -/
theorem nativeTail_factor (query : PqxdhServerRegistrationPublication.TailSpec.Domain) (auxiliary : Auxiliary)
    (cache : CtxRomAuth.CtxRO.QueryCache) :
    (PqxdhServerAuthExperiment.nativeTail setup codec checks query).run (auxiliary, cache) =
      (fun result => (result.1, (auxiliary, result.2))) <$>
        (simulateQ (ctxEffects admin) (nativeTailFwd (n := n) setup codec checks query)).run cache := by
  simp only [PqxdhServerAuthExperiment.nativeTail, QueryImpl.apply_compose]
  rw [show nativeTailFwd (n := n) setup codec checks query =
    simulateQ (regFwd setup codec checks) (PqxdhServerRegistrationPublication.nativeAdapter query) from rfl]
  exact factor_stateless admin _ _ (fun query auxiliary cache => registration_factor admin setup codec checks query
    auxiliary cache) _ auxiliary cache

/-- The forwarded logged tail on the seal-log coordinate of the seal state, the cache coordinate untouched. -/
def tailOnSeal : QueryImpl PqxdhServerRegistrationPublication.TailSpec
    (StateT (RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) (OracleComp (EnvEffects n))) :=
  fun query state => (fun result => (result.1, (result.2, state.2))) <$> (tailFwd setup codec checks query).run state.1

/-- One step of the seal-state lift of the forwarded tail. -/
theorem tailOnSeal_apply (query : PqxdhServerRegistrationPublication.TailSpec.Domain)
    (state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext)) :
    (tailOnSeal (n := n) setup codec checks query).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (tailFwd setup codec checks query).run state.1 := rfl

/-- Running the seal-state lift of the forwarded tail is running the forwarded tail on the log. -/
theorem tailOnSeal_run {α : Type} (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α)
    (log : List RawCtxSourceSend.SealContext) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (tailOnSeal (n := n) setup codec checks) work).run (log, cache) =
      (fun result => (result.1, (result.2, cache))) <$> (simulateQ (tailFwd setup codec checks) work).run log := by
  induction work using OracleComp.inductionOn generalizing log with
  | pure value => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, tailOnSeal_apply, bind_map_left, map_bind]
      exact bind_congr fun result => ih result.1 result.2

/-- Capability-form factoring of the Server build: the native logged response tail on (log, cache) is the forwarded tail on the log read through `ctxEffects` on the cache. -/
theorem tail_factor {α : Type} (work : OracleComp PqxdhServerRegistrationPublication.TailSpec α)
    (log : List RawCtxSourceSend.SealContext) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (simulateQ (PqxdhServerAuthExperiment.tailImpl setup codec checks) work).run (log, cache) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (ctxEffects admin) ((simulateQ (tailFwd (n := n) setup codec checks) work).run log)).run cache := by
  have factored := factor_program admin (PqxdhDeploymentHiddenEntry.sharedLens (List RawCtxSourceSend.SealContext))
    (PqxdhServerAuthExperiment.tailImpl setup codec checks) (tailOnSeal (n := n) setup codec checks)
    (fun query state cache => by
      simp only [PqxdhDeploymentHiddenEntry.sharedLens, StateLens.snd, tailOnSeal_apply, Functor.map_map])
    (fun query state => ?_) work (log, cache)
  · rw [factored, tailOnSeal_run, simulateQ_map, StateT.run_map, Functor.map_map]
    rfl
  · rcases state with ⟨log, cache⟩
    simp only [PqxdhDeploymentHiddenEntry.sharedLens, StateLens.snd, tailOnSeal_apply]
    rcases query with (request | input) | request
    · simp only [PqxdhServerAuthExperiment.tailImpl, nativeTail_factor admin setup codec checks, tailFwd,
        StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    · change StateT.run (PqxdhServerAuthExperiment.nativeTail setup codec checks (.inl (.inr input)) >>= fun sealed =>
          if sealed.isSome then (modify fun state : RawCtxSharedPrimitive.SharedState (List RawCtxSourceSend.SealContext) =>
            (state.1 ++ [input.context], state.2)) >>= fun _ => pure sealed else pure sealed) (log, cache) = _
      rw [StateT.run_bind, nativeTail_factor admin setup codec checks, bind_map_left]
      change _ = (fun result => (result.1.1, (result.1.2.1, result.2))) <$> (simulateQ (ctxEffects admin)
        ((fun result => (result.1, (result.2, cache))) <$>
          (nativeTailFwd setup codec checks (.inl (.inr input)) >>= fun sealed =>
            pure (sealed, if sealed.isSome then log ++ [input.context] else log)))).run cache
      rw [simulateQ_map, StateT.run_map, simulateQ_bind, StateT.run_bind, map_bind, map_bind]
      congr 1
      funext result
      simp only [simulateQ_pure, StateT.run_pure, map_pure]
      cases result.1.isSome <;> rfl
    · simp only [PqxdhServerAuthExperiment.tailImpl, nativeTail_factor admin setup codec checks, tailFwd,
        StateT.run_lift, bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]

end Registration

section Owner
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)

/-- The forwarded finish callbacks never read or write the CTX cache of the shared native state. -/
theorem callbacksFwd_frame
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) (cache : CtxRomAuth.CtxRO.QueryCache) :
    (callbacksFwd (n := n) setup codec query).run (PqxdhDeploymentBackend.gameCtxLens.set state cache) =
      (fun result => (result.1, PqxdhDeploymentBackend.gameCtxLens.set result.2 cache)) <$>
        (callbacksFwd setup codec query).run state := by
  rcases query with query | (query | request)
  · simp only [callbacksFwd, StateT.run_lift, map_bind, map_pure]
  · simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, map_bind, map_pure]
  · cases request with
    | root input =>
        change coins ((PqxdhServerAuthNative.sourceRoot setup.hmac input).run
          (PqxdhDeploymentBackend.gameCtxLens.set state cache)) = _ <$> coins _
        rw [PqxdhDeploymentBackend.sourceRoot_frame setup.hmac input state cache]
        unfold coins
        rw [simulateQ_map]
        rfl
    | initial request => simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, map_bind, map_pure]
    | application response =>
        simp only [callbacksFwd, PqxdhPhase2DhRootConsumer.withRoot, StateT.run_lift, map_bind, map_pure]

/-- Every native finish callback is its forwarded callback read through `ctxEffects` on the CTX cache of the shared native state. -/
theorem callbacks_step
    (query : (PqxdhBeaconPhase2Publication.NativeSpec PqxdhJointIdentity.IdentitySeed PqxdhJointGapDh.ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) PqxdhJointIdentity.IdentitySeed Response).Domain)
    (state : NativeState KemSK) :
    (PqxdhRegistrationSchedule.callbacks setup codec query).run state =
      (fun result => (result.1.1, PqxdhDeploymentBackend.gameCtxLens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((callbacksFwd (n := n) setup codec query).run state)).run
          (PqxdhDeploymentBackend.gameCtxLens.get state) := by
  rcases query with query | (query | request)
  · simp only [PqxdhRegistrationSchedule.callbacks, callbacksFwd, StateT.run_lift, simulateQ_bind, simulateQ_pure,
      StateT.run_bind, ctxEffects_coins, bind_map_left, StateT.run_pure, map_bind, map_pure]
    simp only [PqxdhServerAuthNative.nativeCoins, StateT.run, bind_pure_comp]
    rfl
  · simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
      PqxdhPhase2DhRootConsumer.withRoot, callbacksFwd, beaconFwd, PqxdhServerAuthExperiment.beaconNative,
      StateT.run_lift, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure, map_bind, map_pure]
    change (fun result => (result.1, (state.1, { state.2 with ctx := result.2.2 }))) <$>
      (RawCtxSharedPrimitive.nativeImpl setup.source.crypto (RawCtxSourceHkdf.kdfImpl setup.source) query).run
        ((), state.2.ctx) = _
    rw [primFwd_factor admin, Functor.map_map, map_eq_bind_pure_comp]
    rfl
  · cases request with
    | root input =>
        change (PqxdhServerAuthNative.sourceRoot setup.hmac input).run state =
          _ <$> (simulateQ (ctxEffects admin) (coins ((PqxdhServerAuthNative.sourceRoot setup.hmac input).run state))).run
            state.2.ctx
        rw [ctxEffects_coins, Functor.map_map]
        have framed := PqxdhDeploymentBackend.sourceRoot_frame (KemSK := KemSK) setup.hmac input state state.2.ctx
        rw [show PqxdhDeploymentBackend.gameCtxLens.set state state.2.ctx = state from rfl] at framed
        exact framed
    | initial request =>
        simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
          PqxdhPhase2DhRootConsumer.withRoot, callbacksFwd, beaconFwd,
          PqxdhServerAuthExperiment.beaconNative, StateT.run_lift, simulateQ_pure, StateT.run_pure, pure_bind, map_pure]
        rfl
    | application response =>
        simp only [PqxdhRegistrationSchedule.callbacks, PqxdhServerAuthNative.sourceBeaconTail,
          PqxdhPhase2DhRootConsumer.withRoot, callbacksFwd, beaconFwd,
          PqxdhServerAuthExperiment.beaconNative, StateT.run_lift, simulateQ_pure, StateT.run_pure, pure_bind, map_pure]
        rfl

/-- Capability-form factoring of the Beacon finish: the native owner finish on the shared native state is the forwarded finish read through `ctxEffects` on its CTX cache. -/
theorem owner_factor (raw : Pqxdh.Bytes) (owner : PqxdhRegistrationSchedule.Owner KemSK) (state : NativeState KemSK) :
    (simulateQ (PqxdhRegistrationSchedule.callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state =
      (fun result => (result.1.1, PqxdhDeploymentBackend.gameCtxLens.set result.1.2 result.2)) <$>
        (simulateQ (ctxEffects admin) ((simulateQ (callbacksFwd (n := n) setup codec)
          (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state)).run state.2.ctx :=
  factor_program admin PqxdhDeploymentBackend.gameCtxLens _ _ (callbacksFwd_frame setup codec)
    (callbacks_step admin setup codec) _ state

end Owner

end Factoring

/-! ### C2a for the real environment -/

section RealFrame
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- A registration step run by `onEnv` issues its coins as coin effects and nothing else. -/
theorem onEnv_bound {α : Type} (step : PqxdhRegistrationSchedule.Game KemSK α) (k : Nat)
    (stepBound : ∀ native, (step.run native).IsTotalQueryBound k) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((onEnv (n := n) step).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .coin then k else 0) := by
  change ((fun result => (result.1, { state with native := strip result.2 })) <$> coins (step.run state.native)).IsQueryBoundP _ _
  rw [isQueryBoundP_map_iff]
  exact coins_bound _ k (stepBound _) kind

/-- `create` stays within the real allowance of class 1. -/
theorem createStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (pin : Pqxdh.Bytes) (keyId : Std.U64) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((createStep (n := n) setup pin keyId).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (baseAllowance caps 1 kind) := by
  unfold createStep
  cases parsed : PqxdhDeploymentInterface.parsePin pin with
  | none => trivial
  | some word =>
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind]
      apply (isQueryBoundP_bind (onEnv_bound _ (64 + caps.keygenCost)
        (fun native => PqxdhRegistrationSchedule.create_uniform setup caps bounded word keyId native) state kind)
        fun _ _ => isQueryBoundP_bind (m := 0) (issue_admin _ (fun _ => by simp only [ne_eq, reduceCtorEq, not_false_eq_true])
          kind) fun _ _ => isQueryBoundP_pure _ _ _).mono
      cases kind <;> simp [baseAllowance]


/-- Publishing an owner change issues at most one administrative effect and nothing else. -/
theorem ownerChange_bound {n : Nat} (index : Nat) (before after : List (PqxdhRegistrationSchedule.Owner KemSK))
    (kind : EffectKind) :
    (ownerChange (n := n) index before after).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .administrative then 1 else 0) := by
  unfold ownerChange
  split
  · exact ownerEffect_bound _ _ _ kind
  · trivial

/-- `bundle` stays within the real allowance of class 2. -/
theorem bundleStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (owner : Nat) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((bundleStep (n := n) setup codec owner).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (baseAllowance caps 2 kind) := by
  apply (isQueryBoundP_bind (coins_bound _ 32
    (PqxdhRegistrationSchedule.bundle_uniform setup codec owner state.native) kind)
    fun result _ => isQueryBoundP_bind (m := 0) (ownerChange_bound _ _ _ kind)
      fun _ _ => isQueryBoundP_pure _ _ _).mono
  cases kind <;> simp [baseAllowance]

/-- The logged accept draws at most `96 + encaps` coins (`PqxdhRegistrationSchedule.accept_uniform`). -/
theorem acceptLogged_uniform (caps : PqxdhServerAuthSourceCosts.KemCaps)
    (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps) (seed : PqxdhJointIdentity.IdentitySeed)
    (raw : Pqxdh.Bytes) (native : PqxdhRegistrationSchedule.State KemSK) :
    ((PqxdhRegistrationSchedule.onShared
      (PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw)).run native).IsTotalQueryBound
        (96 + caps.encapsCost) := by
  have accepted := PqxdhRegistrationSchedule.accept_uniform setup codec checks caps bounded seed
    PqxdhRegistrationSchedule.observationScalar raw native.shared
  rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst] at accepted
  rw [PqxdhRegistrationSchedule.onShared_run]
  simp only [IsTotalQueryBound, isQueryBound_map_iff] at accepted ⊢
  exact accepted

/-- `accept` stays within the real allowance of class 3. -/
theorem acceptStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (raw : Pqxdh.Bytes) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((acceptStep (n := n) setup codec checks raw).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (baseAllowance caps 3 kind) := by
  change (_ <$> coins _).IsQueryBoundP _ _
  rw [isQueryBoundP_map_iff]
  apply (coins_bound _ _ (acceptLogged_uniform setup codec checks caps bounded state.created.seed raw state.native)
    kind).mono
  cases kind <;> simp [baseAllowance]

/-- `build` stays within the real allowance of class 4: no coin, the sequence-one BLAKE2b query and the peer installation. -/
theorem buildStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (session : Nat) (payload : Option Pqxdh.Bytes) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((buildStep (n := n) setup codec checks session payload).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (baseAllowance caps 4 kind) := by
  show IsQueryBoundP (buildStep setup codec checks session payload state) _ _
  unfold buildStep
  dsimp only
  split
  · trivial
  · apply (isQueryBoundP_bind (build_fwd_bound setup codec checks _ _ payload _ [] kind)
      fun result _ => isQueryBoundP_bind (m := 0) (serverEffect_bound _ kind)
        fun _ _ => isQueryBoundP_pure _ _ _).mono
    cases kind <;> simp [baseAllowance]

/-- `finish` stays within the real allowance of class 5: the decapsulation and Extract-table coins within the 69-callback bound, at most one BLAKE2b query and the installation or the abort. -/
theorem finishStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (owner : Nat) (raw : Pqxdh.Bytes) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((finishStep (n := n) setup codec owner raw).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (baseAllowance caps 5 kind) := by
  show IsQueryBoundP (finishStep setup codec owner raw state) _ _
  unfold finishStep
  split
  · trivial
  · apply (isQueryBoundP_bind (finish_fwd_bound setup codec caps bounded raw _ _ kind)
      fun result _ => isQueryBoundP_bind (m := 0) (ownerEffect_bound _ _ _ kind)
        fun _ _ => isQueryBoundP_pure _ _ _).mono
    cases kind <;> simp [baseAllowance]

/-- `hmac` stays within the real allowance of class 6. -/
theorem hmacStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes) (state : EnvState KemSK Bk)
    (kind : EffectKind) :
    ((hmacStep (n := n) setup key message).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (baseAllowance caps 6 kind) := by
  apply (onEnv_bound _ 64 (fun native => by
    have bound := PqxdhRegistrationSchedule.hmac_uniform setup state.created.seed
      PqxdhRegistrationSchedule.observationScalar key message native.shared
    rw [PqxdhRegistrationSchedule.onShared_run]
    simp only [IsTotalQueryBound, isQueryBound_map_iff] at bound ⊢
    exact bound) state kind).mono
  cases kind <;> simp [baseAllowance]

/-- Every real environment step stays within the real allowance of its command class. -/
theorem realStep_bound (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (query : EnvQuery) (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((realStep (n := n) setup codec checks query).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (baseAllowance caps (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) kind) := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId => exact createStep_bound setup caps bounded pin keyId _ kind
  | bundle owner => exact bundleStep_bound setup codec caps owner _ kind
  | accept raw => exact acceptStep_bound setup codec checks caps bounded raw _ kind
  | build session payload => exact buildStep_bound setup codec checks caps session payload _ kind
  | finish owner raw => exact finishStep_bound setup codec caps bounded owner raw _ kind
  | hmac key message => exact hmacStep_bound setup caps key message _ kind
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end RealFrame

/-! ### C2a for first-touch material wrappers -/

section Wrapped
variable {n : Nat} {Bk : Type}

/-- The environment material (key32, nonce12) of a slot from the lazily sampled material table that `table` focuses in the backend: drawn with coin effects at the slot's first touch, read back afterwards. -/
noncomputable def touch (table : LazyOracleDiscard.CacheLens (PqxdhDeploymentSeedSplit.MaterialSpec n) Bk) (slot : Slot n) :
    StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) PqxdhDeploymentHiddenLayout.Material := fun state =>
  (fun result => (result.1, { state with backend := result.2 })) <$> coins ((table.query slot).run state.backend)

/-- An environment step with first-touch material: at a command that touches a slot (`slotOf`), the slot's material is obtained by `touch` before the core step, which receives it; any other command runs the core step alone. -/
noncomputable def wrapStep (table : LazyOracleDiscard.CacheLens (PqxdhDeploymentSeedSplit.MaterialSpec n) Bk)
    (slotOf : EnvQuery → EnvState KemSK Bk → Option (Slot n))
    (core : (query : EnvQuery) → Option PqxdhDeploymentHiddenLayout.Material →
      StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (EnvSpec.Range query)) : EnvStep KemSK Bk n :=
  fun query state => match slotOf query state with
    | none => (core query none).run state
    | some slot => ((touch table slot) >>= fun material => core query (some material)).run state

/-- One lazy material lookup draws at most 44 coins (`PqxdhDeploymentHiddenLayout.material_bound`). -/
theorem materialQuery_bound (table : LazyOracleDiscard.CacheLens (PqxdhDeploymentSeedSplit.MaterialSpec n) Bk)
    (slot : Slot n) (backend : Bk) : ((table.query slot).run backend).IsTotalQueryBound 44 := by
  change ((fun r => (r.1, table.set backend r.2)) <$>
    ((PqxdhDeploymentSeedSplit.MaterialSpec n).randomOracle slot).run (table.get backend)).IsTotalQueryBound 44
  simp only [IsTotalQueryBound, isQueryBound_map_iff]
  cases cached : table.get backend slot with
  | none =>
      rw [LazyOracleDiscard.query_of_none cached, bind_pure_comp]
      simpa only [IsTotalQueryBound, isQueryBound_map_iff] using PqxdhDeploymentHiddenLayout.material_bound
  | some material =>
      rw [LazyOracleDiscard.query_of_some cached]
      trivial

/-- Touching a slot's material issues at most 44 coin effects and nothing else. -/
theorem touch_bound (table : LazyOracleDiscard.CacheLens (PqxdhDeploymentSeedSplit.MaterialSpec n) Bk) (slot : Slot n)
    (state : EnvState KemSK Bk) (kind : EffectKind) :
    ((touch table slot).run state).IsQueryBoundP (fun effect => effectKind effect = kind)
      (if kind = .coin then 44 else 0) := by
  change (_ <$> coins _).IsQueryBoundP _ _
  rw [isQueryBoundP_map_iff]
  exact coins_bound _ 44 (materialQuery_bound table slot state.backend) kind

/-- C2a for a first-touch material wrapper (plan sections 31 and 35): if the startup draws at most `startupCoins` coins, every core step stays within the core allowance of its class whatever material it receives, and the wrapper touches a slot only at first-touch classes, then the wrapped environment is framed by `allowanceG core firstTouch`. The slot is computed from the command and the pre-state before the core step; an environment whose slot is known only inside the step (for example a first-touch allocator keyed by a coordinate the finish computes) proves `PqxdhRecordLiftInterface.Frame env startupCoins (allowanceG core firstTouch)` directly instead. -/
theorem frame_wrapped (start : ProbComp (Option (PqxdhLiveServerConstruction.Created Unit × EnvState KemSK Bk)))
    (startupCoins : Nat) (startBound : start.IsTotalQueryBound startupCoins)
    (table : LazyOracleDiscard.CacheLens (PqxdhDeploymentSeedSplit.MaterialSpec n) Bk)
    (slotOf : EnvQuery → EnvState KemSK Bk → Option (Slot n))
    (core : (query : EnvQuery) → Option PqxdhDeploymentHiddenLayout.Material →
      StateT (EnvState KemSK Bk) (OracleComp (EnvEffects n)) (EnvSpec.Range query))
    (coreAllowance : Fin 14 → EffectKind → Nat) (firstTouch : Fin 14 → Bool)
    (coreBound : ∀ query material state kind, ((core query material).run state).IsQueryBoundP
      (fun effect => effectKind effect = kind) (coreAllowance (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) kind))
    (touches : ∀ query state slot, slotOf query state = some slot →
      firstTouch (PqxdhDeploymentInterface.queryClass (.inl (.inr query.val))) = true) :
    PqxdhRecordLiftInterface.Frame (⟨start, wrapStep table slotOf core⟩ : Environment n (EnvState KemSK Bk))
      startupCoins (allowanceG coreAllowance firstTouch) := by
  refine ⟨startBound, fun query state kind => ?_⟩
  change IsQueryBoundP (wrapStep table slotOf core query state) _ _
  unfold wrapStep
  split
  · exact (coreBound query none state kind).mono (Nat.le_add_right _ _)
  · rename_i slot found
    rw [StateT.run_bind]
    apply (isQueryBoundP_bind (touch_bound table slot state kind)
      fun result _ => coreBound query (some result.1) result.2 kind).mono
    have first := touches query state slot found
    by_cases coin : kind = .coin
    · simp only [coin, ite_true, allowanceG, first, and_self]
      omega
    · simp only [coin, ite_false, allowanceG, false_and, Nat.zero_add, Nat.add_zero, le_refl]

end Wrapped

/-! ### No record coordinate in the environment state (critique M6) -/

section Stripping
variable {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- `onEnv` commits a stripped registration state. -/
theorem onEnv_stripped {α : Type} (step : PqxdhRegistrationSchedule.Game KemSK α) (state : EnvState KemSK Bk) :
    ∀ result ∈ support ((onEnv (n := n) step).run state), Stripped result.2.native := by
  intro result supported
  change result ∈ support (_ <$> coins _) at supported
  rw [support_map] at supported
  obtain ⟨inner, _, rfl⟩ := supported
  exact strip_stripped _

/-- Every real environment step keeps the environment state free of record coordinates: every step commits a stripped registration state, or leaves a stripped one unchanged. -/
theorem realStep_stripped (query : EnvQuery) (state : EnvState KemSK Bk) (stripped : Stripped state.native) :
    ∀ result ∈ support ((realStep (n := n) setup codec checks query).run state), Stripped result.2.native := by
  intro result supported
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      change result ∈ support ((createStep setup pin keyId).run (snapped _ state)) at supported
      unfold createStep at supported
      cases parsed : PqxdhDeploymentInterface.parsePin pin with
      | none =>
          simp only [parsed, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst supported
          exact stripped
      | some word =>
          simp only [parsed, StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind,
            mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
          obtain ⟨first, member, _, _, rfl⟩ := supported
          exact onEnv_stripped _ _ first member
  | bundle owner =>
      change result ∈ support ((bundleStep setup codec owner).run (snapped _ state)) at supported
      change result ∈ support (_ >>= _) at supported
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
      obtain ⟨_, _, _, _, rfl⟩ := supported
      exact strip_stripped _
  | accept raw =>
      change result ∈ support (_ <$> coins _) at supported
      rw [support_map] at supported
      obtain ⟨_, _, rfl⟩ := supported
      exact strip_stripped _
  | build session payload =>
      change result ∈ support (buildStep setup codec checks session payload (snapped _ state)) at supported
      unfold buildStep at supported
      dsimp only at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact stripped
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨_, _, _, _, rfl⟩ := supported
        exact strip_stripped _
  | finish owner raw =>
      change result ∈ support (finishStep setup codec owner raw (snapped _ state)) at supported
      unfold finishStep at supported
      split at supported
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        exact stripped
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
        obtain ⟨_, _, _, _, rfl⟩ := supported
        exact strip_stripped _
  | hmac key message => exact onEnv_stripped _ _ result supported
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

end Stripping

/-- C2a for the real environment (cuttable validation, critique m12): the startup draws at most `qInit + 32` coins and every step stays within the real allowance of its class. -/
theorem frame_real {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (identityIndex : Nat) (runtime : A) :
    PqxdhRecordLiftInterface.Frame (envReal (n := n) setup codec checks ensureInit identityIndex runtime) (qInit + 32)
      (baseAllowance caps) :=
  ⟨start_bound setup ensureInit qInit initBound identityIndex runtime _,
    fun query state kind => realStep_bound setup codec checks caps bounded query state kind⟩


/-- C4 for the real environment (cuttable validation): every outcome of the record world with the real environment has its BLAKE2b routes within `qHash + S + R + qBuild + qFinish` and its record derivations within `S + 51 R`. -/
theorem c4_real {n : Nat} {ι : Type} {baseSpec : OracleSpec ι} {Reader Response A X : Type}
    (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder)
    (caps : PqxdhServerAuthSourceCosts.KemCaps) (bounded : PqxdhServerAuthSourceCosts.KemBound setup caps)
    (ensureInit : StateT A ProbComp Bool) (qInit : Nat) (initBound : ∀ state, (ensureInit.run state).IsTotalQueryBound qInit)
    (identityIndex : Nat) (runtime : A) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (B : PqxdhDeploymentInterface.Budget)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) (respects : B.Respects adversary) :
    ∀ result ∈ support (PqxdhRecordLiftWorld.run setup codec route
        (envReal (n := n) setup codec checks ensureInit identityIndex runtime) setup.serverKeyId bounds mode adversary),
      result.2.primitive.1.effects .hash + result.2.primitive.1.native .hash ≤
          B.hash + B.sends + B.receives + B.build + B.finish ∧
        result.2.primitive.1.native .kdf ≤ B.sends + 51 * B.receives :=
  c4_closed setup codec route _ (qInit + 32) (baseAllowance caps)
    (frame_real setup codec checks caps bounded ensureInit qInit initBound identityIndex runtime)
    (baseAllowance_hash caps) setup.serverKeyId bounds mode B adversary respects

end BeaconcryptCore.Computational.PqxdhDeploymentEnvironment

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripOwner_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripOwner_idem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripPeer_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripPeer_comp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripOwner_comp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.stripOwner_comp

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_idem' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_idem

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.envInitial_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.envInitial_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_created' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_created

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_initial

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.start_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.coins_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.coins_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.issue_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.issue_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.issue_admin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.issue_admin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ownerEffect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ownerEffect_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.serverEffect_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.serverEffect_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_other' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.envTotal_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.envTotal_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.capsG_sharedHash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.capsG_sharedHash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.capsG_derivations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.capsG_derivations

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.baseAllowance_hash' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.baseAllowance_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.baseAllowance_six' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.baseAllowance_six

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_six' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_six

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_hash' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.allowanceG_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_instance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_instance

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_later

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_later_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_later_closed

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTailFwd_compose' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTailFwd_compose

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailFwd_forget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailFwd_forget

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.regFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.regFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.build_fwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.build_fwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.afterRoot_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.afterRoot_hash_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tail_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tail_hash_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.owner_hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.owner_hash_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.beaconFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.beaconFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacksFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacksFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finish_fwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finish_fwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_owners_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.strip_owners_length

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_consumes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_consumes

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_idle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_idle

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_retry

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.support_simulateQ_subset' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.support_simulateQ_subset

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_terminal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_after_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_after_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_candidate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_candidate_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.generic_build_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTailFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTailFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailFwd_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailFwd_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.loggedFwd_send_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.loggedFwd_send_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildSplit_env_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildSplit_env_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishSplit_env_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishSplit_env_cost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ctxEffects_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ctxEffects_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_program

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_program

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.primFwd_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_stateless' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.factor_stateless

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.registration_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.registration_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTail_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.nativeTail_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailOnSeal_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailOnSeal_apply

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailOnSeal_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tailOnSeal_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tail_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.tail_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacksFwd_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacksFwd_frame

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacks_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.callbacks_step

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.owner_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.owner_factor

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.onEnv_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.onEnv_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.createStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.createStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ownerChange_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.ownerChange_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.bundleStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.bundleStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.acceptLogged_uniform' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.acceptLogged_uniform

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.acceptStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.acceptStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.buildStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.finishStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.hmacStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.hmacStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.realStep_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.realStep_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.materialQuery_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.materialQuery_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.touch_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.touch_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_wrapped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_wrapped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.onEnv_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.onEnv_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.realStep_stripped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.realStep_stripped

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.frame_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentEnvironment.c4_real
