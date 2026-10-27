-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRegistrationAdmission
import BeaconcryptCore.Computational.PqxdhRegistrationPending
import BeaconcryptCore.Computational.PqxdhRegistrationResponse
import BeaconcryptCore.Computational.PqxdhRegistrationBeacon

/-! An operational registration scheduler runs the existing complete Server and Beacon source programs. Owner indices are public addresses, not cryptographic identities. The single live Server and dynamically created Beacons share the original Extract and CTX tables. The root slice and CTX ROM are inherited idealizations; this module supplies no cryptographic soundness or applied-pi compiler theorem. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationSchedule
open PqxdhJointIdentity PqxdhJointGapDh PqxdhServerAuthExperiment PqxdhServerAuthNative
open PqxdhBeaconPhase2Preparation (Word32)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- Private keys occur only in the original native fields. Finishing or aborting drops the original prekey, one-time and KEM fields; this registry keeps no auxiliary copy. -/
abbrev Owner (KemSK : Type) := RawCtxBeaconLifecycle.State IdentitySeed ScalarBytes
  (PqxdhKemIndCca.MlKem768PublicKey × KemSK)

/-- Both complete primitive caches and the complete Server remain one shared state across all owners. The unused Beacon coordinate of the existing native Server interpreter is private bookkeeping only. -/
structure State (KemSK : Type) where
  shared : NativeState KemSK
  owners : List (Owner KemSK)

abbrev Game (KemSK : Type) := StateT (State KemSK) ProbComp

/-- Lift an actual complete native source operation without copying or resetting either primitive cache. -/
def onShared {Result : Type} (work : NativeGame KemSK Result) : Game KemSK Result := fun state =>
  (fun result => (result.1, { state with shared := result.2 })) <$> work state.shared

/-- All actual callback work survives this lift under an arbitrary full result/state continuation. -/
theorem shared_continuation {Result Next : Type} (work : NativeGame KemSK Result)
    (state : State KemSK) (next : Result × State KemSK → ProbComp Next) :
    (onShared work state >>= next) =
      (work state.shared >>= fun result => next (result.1, { state with shared := result.2 })) := by
  simp only [onShared, bind_map_left]

/-- Complete native preparation with actual identity, scalar and KEM fields, and the same primitive/codec contracts as the existing native interpreter. -/
noncomputable def preparation (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Preparation.Spec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) ProbComp
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind toWord32)
  | .privateConversion seed => pure (some seed)
  | .decapsulate ciphertext keys => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (Option.map PqxdhRootTableInitialization.rootArray <$>
        setup.kem.decaps keys.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))
  | .dhPair scalar point => pure ((sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity seed point => pure ((setup.joint.staticDh seed
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- Root, initializer and receive callbacks reuse the original full source tail. The same shared tables are visible to every owner and public primitive query. -/
noncomputable def callbacks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) (NativeGame KemSK)
  | .inl query => nativeCoins (preparation setup codec query)
  | .inr query => sourceBeaconTail setup codec query

/-- Public slot lookup rejects a missing owner before all preparation and receive callbacks. A present slot executes the literal complete native owner and reinstalls only its returned owner. -/
noncomputable def finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) : Game KemSK (Option Pqxdh.Bytes) := do
  let state ← get
  match state.owners[index]? with
  | none => pure none
  | some owner => do
      let result ← onShared (simulateQ (callbacks setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner))
      modify fun current => { current with owners := current.owners.set index result.2 }
      pure result.1

/-- Public projections read the source owner currently selected for Phase 1. The address is used only to route its three private signing requests. -/
def projection (setup : Setup baseSpec KemSK) (index : Nat) :
    PqxdhLivePhase1Bundle.Public IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) where
  index _ := index
  identity seed := (setup.joint.publicKeys seed).ed25519
  dh scalar := setup.dh.publicKey scalar
  kem keys := keys.1

/-- The one-time generator is called by the source bundle exactly when its current phase requests it. Inactive and retained-coin branches do not draw unused randomness. -/
def bundleCallbacks (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (seed : IdentitySeed) : QueryImpl (PqxdhLivePhase1Bundle.Spec ScalarBytes) ProbComp
  | .inl () => some <$> sampleScalar
  | .inr (.inl (.inl coin)) => (unifSpec.query coin : ProbComp _)
  | .inr (.inl (.inr .create)) => pure none
  | .inr (.inl (.inr (.service _ (.sign message)))) => pure (some (setup.joint.sign seed message))
  | .inr (.inl (.inr (.service _ (.staticDh _)))) => pure none
  | .inr (.inl (.inr (.reveal _))) => pure none
  | .inr (.inr bundle) => pure (codec.write1 bundle)

/-- Native bundle generation and all three signatures precede optional publication; the exact returned complete owner is retained even on failure. -/
def bundle (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) : Game KemSK (Option Pqxdh.Bytes) := do
  let state ← get
  match state.owners[index]? with
  | none => pure none
  | some owner => do
      let result ← StateT.lift (simulateQ (bundleCallbacks setup codec owner.beacon.identity)
        (PqxdhLivePhase1Bundle.bundle (projection setup index) owner))
      modify fun current => { current with owners := current.owners.set index result.2 }
      pure result.1

/-- The post-admission constructor body draws identity, prekey and KEM in production order at this schedule position. This typed-pin operation does not establish the preceding runtime/public-key parser admission. Phase-1 one-time material is drawn only by a later bundle call. -/
noncomputable def create (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64) :
    Game KemSK Nat := do
  let identity ← StateT.lift sampleSeed
  let prekey ← StateT.lift sampleScalar
  let keys ← StateT.lift (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let state ← get
  let owner : Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
  set { state with owners := state.owners ++ [owner] }
  pure state.owners.length

/-- The old Server analysis interface carries a prekey coordinate used only by its descriptors. Actual Server preparation and the native root address do not obtain a Beacon secret from this fixed coordinate. -/
def observationScalar : ScalarBytes := List.Vector.replicate 32 0

inductive Request where
  | create (pin : Word32) (keyId : Std.U64)
  | bundle (owner : Nat)
  | accept (raw : Pqxdh.Bytes)
  | build (session : Nat) (payload : Option Pqxdh.Bytes)
  | finish (owner : Nat) (raw : Pqxdh.Bytes)
  | hmac (key : PqxdhSecretInputKdf.HmacBlock) (message : Pqxdh.Bytes)
  | hash (bytes : Pqxdh.Bytes)
  | reveal (keyId : Std.U64)

abbrev QuerySpec : OracleSpec Request
  | .create _ _ => Nat
  | .bundle _ => Option Pqxdh.Bytes
  | .accept _ => Option Nat
  | .build _ _ => Option PqxdhServerRegistrationPublication.Response
  | .finish _ _ => Option Pqxdh.Bytes
  | .hmac _ _ => PqxdhSecretInputKdf.HmacBlock
  | .hash _ => CtxRomAuth.CtxDigest
  | .reveal _ => Option ratchet.concrete.ConcreteRatchetKernel

abbrev Spec := unifSpec + QuerySpec

/-- One shared native Server, any number of dynamically addressed Beacons, arbitrary raw inputs and public primitive queries. No admission branch consults a protocol-origin annotation. -/
noncomputable def handler (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) : QueryImpl Spec (Game KemSK)
  | .inl coin => StateT.lift (unifSpec.query coin : ProbComp _)
  | .inr (.create pin keyId) => create setup pin keyId
  | .inr (.bundle index) => bundle setup codec index
  | .inr (.accept raw) => onShared (nativeAccept setup codec checks serverSeed observationScalar raw)
  | .inr (.build index payload) => onShared (nativeBuild setup codec checks index payload)
  | .inr (.finish index raw) => finish setup codec index raw
  | .inr (.hmac key message) => onShared (nativeHmac setup serverSeed observationScalar key message)
  | .inr (.hash bytes) => onShared (nativeHash bytes)
  | .inr (.reveal keyId) => onShared (localState fun state => (revealKernel keyId state, state))

/-- A single callback may update actual primitive caches but never publishes a role or changes consumed IDs, moved tokens, counters, or another owner. -/
theorem callback_fields (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (query : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Domain)
    (state : NativeState KemSK)
    (result : (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response).Range query × NativeState KemSK)
    (supported : result ∈ support ((callbacks setup codec query).run state)) :
    result.2.2 = { state.2 with ctx := result.2.2.ctx } := by
  rcases query with query | query
  · simp only [callbacks, nativeCoins, StateT.run, support_map, Set.mem_image] at supported
    obtain ⟨value, _, rfl⟩ := supported
    rfl
  · rcases query with query | (input | request | response)
    all_goals simp only [callbacks, sourceBeaconTail, PqxdhPhase2DhRootConsumer.withRoot,
      nativeCtx, sourceRoot, StateT.run, support_map, Set.mem_image] at supported
    all_goals obtain ⟨value, _, rfl⟩ := supported
    all_goals rfl

/-- An entire native owner callback program preserves every shared protocol field. It may still perform all its original generation, decapsulation, KDF, hash and AEAD work. -/
theorem program_fields {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (program : OracleComp (PqxdhBeaconPhase2Publication.NativeSpec IdentitySeed ScalarBytes
      (PqxdhKemIndCca.MlKem768PublicKey × KemSK) IdentitySeed Response) Result)
    (state : NativeState KemSK) (result : Result × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (callbacks setup codec) program).run state)) :
    result.2.2 = { state.2 with ctx := result.2.2.ctx } := by
  apply run_rel (callbacks setup codec)
    (fun before after => after.2 = { before.2 with ctx := after.2.ctx })
    (fun _ => rfl) _ (callback_fields setup codec) program state result supported
  intro before middle after left right
  rw [right, left]

theorem onShared_run {Result : Type} (work : NativeGame KemSK Result) (state : State KemSK) :
    (onShared work).run state =
      (fun result => (result.1, { state with shared := result.2 })) <$> work state.shared := rfl

/-- Exact complete finish equation: a present owner runs the original native program once, then publishes precisely its returned owner and both complete shared caches. -/
theorem finish_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner) :
    finish setup codec index raw state =
      (fun result => (result.1.1,
        ({ shared := result.2, owners := state.owners.set index result.1.2 } : State KemSK))) <$>
      (simulateQ (callbacks setup codec)
        (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state.shared := by
  change (finish setup codec index raw).run state = _
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind, found, onShared_run,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, Functor.map_map]
  rfl

/-- An absent owner is an ordinary counted API rejection and performs no hidden preparation work. -/
theorem finish_missing (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK)
    (missing : state.owners[index]? = none) :
    (finish setup codec index raw).run state = pure (none, state) := by
  simp only [finish, StateT.run_bind, StateT.run_get, pure_bind, missing, StateT.run_pure]

/-- Successful or aborted registration is terminal for this owner's bundle/finish capabilities. Established record operations remain outside this registration scheduler. -/
def Terminal (owner : Owner KemSK) : Prop :=
  match owner.beacon.phase with
  | .established _ _ _ | .aborted _ => True
  | _ => False

/-- The original finish operation always installs one of its two actual terminal phases. -/
theorem finish_terminal (control : pqxdh.BeaconInitSent) (owner : Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) :
    Terminal (PqxdhBeaconPhase2Publication.finish control owner staged).2 := by
  cases staged <;> simp [PqxdhBeaconPhase2Publication.finish, PqxdhBeaconPhase2Publication.publish,
    PqxdhBeaconPhase2Preparation.abort, Terminal]
  split_ifs <;> trivial

/-- A terminal owner rejects every later registration finish as a pure source operation, before any primitive, parser or writer callback. -/
theorem terminal_native (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : Owner KemSK) (terminal : Terminal owner) :
    PqxdhBeaconPhase2Publication.nativeOwner (X := IdentitySeed) (Response := Response)
      decode raw owner = pure (none, owner) := by
  cases phase : owner.beacon.phase <;>
    simp_all [Terminal, PqxdhBeaconPhase2Publication.nativeOwner,
      PqxdhBeaconPhase2Publication.owner]

/-- A completed or aborted source owner cannot publish another bundle or draw/sign replacement material through the registration API. -/
theorem terminal_bundle (setup : Setup baseSpec KemSK) (index : Nat)
    (owner : Owner KemSK) (terminal : Terminal owner) :
    PqxdhLivePhase1Bundle.bundle (projection setup index) owner = pure (none, owner) := by
  cases phase : owner.beacon.phase <;> simp_all [Terminal, PqxdhLivePhase1Bundle.bundle]

/-- A later finish at a terminal public slot retains the exact entire registry and both shared caches, not merely the owner's terminal phase. -/
theorem terminal_finish (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner) (terminal : Terminal owner) :
    finish setup codec index raw state = pure (none, state) := by
  rw [finish_source setup codec index raw state owner found,
    terminal_native codec.frameRead raw owner terminal]
  simp only [simulateQ_pure, StateT.run_pure, map_pure]
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  rw [← atIndex, List.set_getElem_self bound]

/-- Every supported active source attempt ends in its actual established or aborted owner, regardless of raw input, primitive replies, or writer outcome. This assertion does not apply to a call before InitSent. -/
theorem native_attempt_terminal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (raw : Pqxdh.Bytes) (owner : Owner KemSK) (control : pqxdh.BeaconInitSent)
    (prekey oneTime : ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (active : owner.beacon.phase = .initSent control prekey oneTime kem)
    (state : NativeState KemSK) (result : (Option Pqxdh.Bytes × Owner KemSK) × NativeState KemSK)
    (supported : result ∈ support ((simulateQ (callbacks setup codec)
      (PqxdhBeaconPhase2Publication.nativeOwner codec.frameRead raw owner)).run state)) :
    Terminal result.1.2 := by
  rcases result with ⟨⟨reply, next⟩, final⟩
  cases reply with
  | some plaintext =>
      obtain ⟨staged, _, _, published⟩ := PqxdhBeaconPhase2Publication.native_success
        (callbacks setup codec) codec.frameRead raw plaintext owner next state final supported
      exact (congrArg (fun value => Terminal value.2) published).mp (by trivial)
  | none =>
      have aborted : next = PqxdhBeaconPhase2Preparation.abort control owner := by
        simpa only [active] using PqxdhBeaconPhase2Publication.native_failure
          (callbacks setup codec) codec.frameRead raw owner next state final supported
      simp only [aborted, PqxdhBeaconPhase2Preparation.abort, Terminal]

/-- An active public finish reinstalls the same reached terminal owner at its stable numeric address, including every rejection outcome. -/
theorem finish_closes (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (raw : Pqxdh.Bytes) (state : State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner) (control : pqxdh.BeaconInitSent)
    (prekey oneTime : ScalarBytes) (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (active : owner.beacon.phase = .initSent control prekey oneTime kem)
    (result : Option Pqxdh.Bytes × State KemSK)
    (supported : result ∈ support (finish setup codec index raw state)) :
    ∃ closed, result.2.owners[index]? = some closed ∧ Terminal closed := by
  rw [finish_source setup codec index raw state owner found] at supported
  simp only [support_map, Set.mem_image] at supported
  obtain ⟨reached, reach, rfl⟩ := supported
  refine ⟨reached.1.2, ?_, native_attempt_terminal setup codec raw owner control prekey oneTime kem
    active state.shared reached reach⟩
  simp only [List.getElem?_set_self', found]
  rfl

/-- Every bundle call uses the current source owner and preserves the shared Server and primitive caches. Its complete optional native reply determines the only replaced owner. -/
theorem bundle_source (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (state : State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner) :
    bundle setup codec index state =
      (fun result => (result.1, { state with owners := state.owners.set index result.2 })) <$>
      simulateQ (bundleCallbacks setup codec owner.beacon.identity)
        (PqxdhLivePhase1Bundle.bundle (projection setup index) owner) := by
  change (bundle setup codec index).run state = _
  simp only [bundle, StateT.run_bind, StateT.run_get, pure_bind, found, StateT.run_lift,
    StateT.run_map, StateT.run_modify, map_pure, bind_pure_comp, Functor.map_map]

/-- A terminal public owner slot cannot run a later Phase-1 generator, signature, or writer callback; its entire shared state and registry are retained. -/
theorem terminal_bundle_call (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (index : Nat) (state : State KemSK) (owner : Owner KemSK)
    (found : state.owners[index]? = some owner) (terminal : Terminal owner) :
    bundle setup codec index state = pure (none, state) := by
  rw [bundle_source setup codec index state owner found, terminal_bundle setup index owner terminal]
  obtain ⟨bound, atIndex⟩ := List.getElem?_eq_some_iff.mp found
  simp only [simulateQ_pure, map_pure, ← atIndex, List.set_getElem_self bound]

/-- The full post-admission constructor runs identity, prekey and KEM generation in that order, then appends the actual fresh owner. The complete prior state and every generator reply remain in the result. -/
theorem create_source (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Std.U64)
    (state : State KemSK) :
    create setup pin keyId state = (do
      let identity ← sampleSeed
      let prekey ← sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      let owner : Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
      pure (state.owners.length, { state with owners := state.owners ++ [owner] })) := by
  change (create setup pin keyId).run state = _
  simp only [create, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_map,
    StateT.run_set, bind_pure_comp, bind_map_left, map_pure, Functor.map_map]

/-- Every registration capability preserves an already terminal owner at its exact original numeric slot. Shared caches and other owners may still change through their actual source operations. -/
theorem handler_terminal (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (index : Nat) (owner : Owner KemSK) (state : State KemSK)
    (result : Spec.Range query × State KemSK)
    (found : state.owners[index]? = some owner) (terminal : Terminal owner)
    (supported : result ∈ support ((handler setup codec checks serverSeed query).run state)) :
    result.2.owners[index]? = some owner := by
  cases query with
  | inl coin =>
      simp only [handler, StateT.run_lift, bind_pure_comp, support_map, Set.mem_image] at supported
      obtain ⟨reached, _, rfl⟩ := supported
      exact found
  | inr request =>
      cases request with
      | finish selected raw =>
          by_cases same : selected = index
          · simp only [handler, StateT.run, same, terminal_finish setup codec index raw state owner found terminal,
              support_pure, Set.mem_singleton_iff] at supported
            simpa only [supported] using found
          · cases selectedFound : state.owners[selected]? with
            | none =>
                simp only [handler, finish_missing setup codec selected raw state selectedFound,
                  support_pure, Set.mem_singleton_iff] at supported
                simpa only [supported] using found
            | some selectedOwner =>
                simp only [handler, StateT.run, finish_source setup codec selected raw state selectedOwner selectedFound,
                  support_map, Set.mem_image] at supported
                obtain ⟨reached, _, rfl⟩ := supported
                simpa only [List.getElem?_set_ne same] using found
      | bundle selected =>
          by_cases same : selected = index
          · simp only [handler, StateT.run, same, terminal_bundle_call setup codec index state owner found terminal,
              support_pure, Set.mem_singleton_iff] at supported
            simpa only [supported] using found
          · cases selectedFound : state.owners[selected]? with
            | none =>
                simp only [handler, bundle, StateT.run_bind, StateT.run_get, pure_bind, selectedFound,
                  StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                simpa only [supported] using found
            | some selectedOwner =>
                simp only [handler, StateT.run, bundle_source setup codec selected state selectedOwner selectedFound,
                  support_map, Set.mem_image] at supported
                obtain ⟨reached, _, rfl⟩ := supported
                simpa only [List.getElem?_set_ne same] using found
      | create pin keyId =>
          simp only [handler, StateT.run, create_source, mem_support_bind_iff, support_pure,
            Set.mem_singleton_iff] at supported
          obtain ⟨identity, _, prekey, _, keys, _, rfl⟩ := supported
          simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1] using found
      | _ =>
          simp only [handler, onShared_run, support_map, Set.mem_image] at supported
          obtain ⟨reached, _, rfl⟩ := supported
          exact found

/-- Every finite adaptive continuation of the complete registration API retains a terminal owner at its original numeric slot, including arbitrary generation and registration interleavings. -/
theorem program_terminal {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (program : OracleComp Spec Result)
    (index : Nat) (owner : Owner KemSK) (state : State KemSK) (result : Result × State KemSK)
    (found : state.owners[index]? = some owner) (terminal : Terminal owner)
    (supported : result ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run state)) :
    result.2.owners[index]? = some owner := by
  exact run_rel (handler setup codec checks serverSeed)
    (fun before after => before.owners[index]? = some owner → after.owners[index]? = some owner)
    (fun _ present => present) (fun _ _ _ first second present => second (first present))
    (fun query before reached member present =>
      handler_terminal setup codec checks serverSeed query index owner before reached present terminal member)
    program state result supported found

/-- After any active initial-response attempt, every later adaptive registration continuation leaves both finish and Phase-1 bundle as exact pure rejections for that owner. This includes the first attempt's rejection paths and retains the complete final shared state. -/
theorem no_retry {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (index : Nat) (raw retry : Pqxdh.Bytes)
    (state : State KemSK) (owner : Owner KemSK) (found : state.owners[index]? = some owner)
    (control : pqxdh.BeaconInitSent) (prekey oneTime : ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK)
    (active : owner.beacon.phase = .initSent control prekey oneTime kem)
    (first : Option Pqxdh.Bytes × State KemSK)
    (attempted : first ∈ support (finish setup codec index raw state))
    (program : OracleComp Spec Result) (last : Result × State KemSK)
    (continued : last ∈ support ((simulateQ (handler setup codec checks serverSeed) program).run first.2)) :
    finish setup codec index retry last.2 = pure (none, last.2) ∧
      bundle setup codec index last.2 = pure (none, last.2) := by
  obtain ⟨closed, present, terminal⟩ := finish_closes setup codec index raw state owner found
    control prekey oneTime kem active first attempted
  have retained := program_terminal setup codec checks serverSeed program index closed first.2 last
    present terminal continued
  exact ⟨terminal_finish setup codec index retry last.2 closed retained terminal,
    terminal_bundle_call setup codec index last.2 closed retained terminal⟩

end BeaconcryptCore.Computational.PqxdhRegistrationSchedule

/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.shared_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.shared_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.callback_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.callback_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_fields
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.onShared_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.onShared_run
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_missing
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_terminal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_native
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_bundle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_bundle
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_finish
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.native_attempt_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.native_attempt_terminal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_closes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.finish_closes
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.bundle_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_bundle_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.terminal_bundle_call
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.create_source
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.handler_terminal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.program_terminal
/-- info: 'BeaconcryptCore.Computational.PqxdhRegistrationSchedule.no_retry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationSchedule.no_retry
