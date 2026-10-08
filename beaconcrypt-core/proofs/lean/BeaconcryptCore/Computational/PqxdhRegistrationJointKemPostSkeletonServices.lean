import BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeletonGroup
import BeaconcryptCore.Computational.PqxdhExtractRomHiddenSuffix
import BeaconcryptCore.Computational.PqxdhServerAuthEntryServices

/-!
# The services skeleton of the post-challenge phase (item 2, stage S1b, definitions)

This module defines the post-challenge phase of the grouped branch (`PqxdhRegistrationJointKemPostSkeletonGroup`) as a client of two oracles and a service record, without any table state and without the KEM candidate.

**Oracles** (`TSpec V`). The shared zero-key 192-byte Extract table is not held by the program. Every read of it is an oracle query:
- a hidden read (`ValueOracle V`) at the 128-byte coordinates of a root input whose 32-byte KEM suffix is the candidate: the Server's private resumption root (handle `.challenge`) and every grouped Beacon finish whose decapsulation handle is the challenge marker. It returns a value of type `V`;
- a direct read (`TableOracle`) at a full byte string: every other Server root (other raw accepts), every other Beacon root (known decapsulation results), the Beacon tail's root callback, and the adversary's public HMAC on the zero-key 192-byte slice.

The plan's services `serverRoot`, `beaconRoot` and `table` are these two oracles; the hops of item 2 interpret them differently (stage S1b: the one shared table of G1's `sharedGame` with the candidate as secret suffix and real Expand; stage S1c: G1's `splitGame`; stage S2: a root table).

**Services** (`Services V Response`). `rootOf v` is the root that the Server's pending token holds for a hidden Server session; `hidden v` gives the two hidden-entry services with exactly the field types of `PqxdhServerAuthEntryFactor.Services` (plan section 18): `hiddenBuild` (the response tail of the hidden Server session) and `hiddenAfter` (the Beacon continuation after a hidden root). The skeleton records the hidden Server session (the session index of the private resumption) and its value in its state (`Marks V`), dispatches the build of that session to `hiddenBuild`, and hands the continuation of every grouped Beacon finish with the challenge marker to `hiddenAfter`. `nativeServices` instantiates them with the source's native response tail and native continuation at the root `v`; `factorHidden` shows that the factored services of `PqxdhServerAuthEntryFactor.factorServices` have these types.

**Layers.** The native layer (`skelImpl`, `resumeImplT`) has state `SkelState V` (the game state, kept without analysis observers, and the marks) and sends coins and private-pool and encapsulation requests to the exposed encapsulation interface. Below it the source's interpreters run unchanged, each forwarding the table oracles (`fwd`, `fwdOption` of `PqxdhRegistrationJointKemPostSkeletonTools`): the actual encapsulator, the post-challenge router holding `placeholder`, and the CCA evaluation (`evalLayer`). `postSkel` is the whole post-challenge phase as a client over `SkelSpec V = unifSpec + TSpec V`, ending in the decision. Its arguments contain no candidate.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false
set_option maxRecDepth 100000

namespace BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton

open PqxdhKemIndCca PqxdhInitializerSecrecy PqxdhServerAuthExperiment PqxdhJointIdentity
open PqxdhRegistrationJointKemObserverFree PqxdhRegistrationJointBeaconOpaqueFinish
open PqxdhSecretInputKdf (HmacBlock RootOutput)

/-! ### Services and oracles -/

section Services

/-- The response tail of a hidden Server session (plan section 18, `PqxdhServerAuthEntryFactor.Services.hiddenBuild`). -/
abbrev HiddenBuild := PqxdhServerRelatedRootConsumer.Returned → Option Pqxdh.Bytes →
  PqxdhServerAuthEntryFactor.ServerState →
  StateT PqxdhServerAuthEntryFactor.SealState ProbComp
    (RustM (Option PqxdhServerRegistrationPublication.Response × PqxdhServerAuthEntryFactor.ServerState))

/-- The Beacon continuation after a hidden root (plan section 18, `PqxdhServerAuthEntryFactor.Services.hiddenAfter`). -/
abbrev HiddenAfter (Response : Type) := PqxdhPhase2DhMetadata.Prepared Response →
  StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp (Option PqxdhBeaconPhase2Publication.Staged)

/-- The two hidden-entry services of one hidden entry. -/
structure Hidden (Response : Type) where
  hiddenBuild : HiddenBuild
  hiddenAfter : HiddenAfter Response

/-- The services of the skeleton for hidden entries with values of type `V`. -/
structure Services (V Response : Type) where
  rootOf : V → RootOutput
  hidden : V → Hidden Response

/-- Hidden reads at 128-byte coordinates. -/
abbrev ValueOracle (V : Type) := PqxdhCorrelatedExtractFamily.Message →ₒ V

/-- The table oracles: hidden reads and direct reads. -/
abbrev TSpec (V : Type) := ValueOracle V + PqxdhExtractRomHiddenSuffix.TableOracle

/-- The client interface of the skeleton: coins and the table oracles. -/
abbrev SkelSpec (V : Type) := unifSpec + TSpec V

/-- The hidden Server session and its value. -/
abbrev Marks (V : Type) := Option (Nat × V)

/-- The state of the native layer of the skeleton. -/
abbrev SkelState (KemSK V : Type) := GameState KemSK × Marks V

/-- Native-layer programs of the skeleton. -/
abbrev NGame (KemSK V α : Type) := StateT (SkelState KemSK V) (OracleComp (SkelSpec V)) α

/-- The exposed encapsulation interface of the source. -/
abbrev Enc (KemSK : Type) := PqxdhRegistrationJointKemEncapsulation.Spec KemSK

/-- Native-layer handlers of the skeleton, on the exposed encapsulation interface with the table oracles. -/
abbrev SClient (KemSK V α : Type) := StateT (SkelState KemSK V) (OracleComp (Enc KemSK + TSpec V)) α

/-- The 128-byte coordinates of four DH outputs. -/
def message (dh1 dh2 dh3 dh4 : PqxdhBeaconPhase2Preparation.Word32) : PqxdhCorrelatedExtractFamily.Message :=
  PqxdhCorrelatedExtractFamily.coordinates (PqxdhPhase2InputBytes.coordinates dh1 dh2 dh3 dh4)

end Services

/-! ### Native-layer programs -/

section Programs

variable {KemSK V : Type}

/-- The game state without analysis observers. -/
def clean (game : GameState KemSK) : GameState KemSK := { game with ghost := Ghost.empty }

/-- A game-state computation of the source, run on the game state without analysis observers. -/
def gameStep {α : Type} (work : StateT (GameState KemSK) ProbComp α) : NGame KemSK V α :=
  fun state => (fun result => (result.1, (result.2, state.2))) <$>
    OracleComp.liftComp (work.run (clean state.1)) (SkelSpec V)

/-- A hidden read. -/
def valueRead (point : PqxdhCorrelatedExtractFamily.Message) : NGame KemSK V V :=
  fun state => (fun reply => (reply, state)) <$> ((SkelSpec V).query (.inr (.inl point)) : OracleComp (SkelSpec V) _)

/-- A direct read. -/
def tableRead (point : Pqxdh.Bytes) : NGame KemSK V HmacBlock :=
  fun state => (fun reply => (reply, state)) <$> ((SkelSpec V).query (.inr (.inr point)) : OracleComp (SkelSpec V) _)

/-- Replace the game state. -/
def setGame (game : GameState KemSK) : NGame KemSK V Unit := fun state => pure ((), (game, state.2))

/-- Change the game state. -/
def modifyGame (change : GameState KemSK → GameState KemSK) : NGame KemSK V Unit :=
  fun state => pure ((), (change state.1, state.2))

/-- Record the hidden Server session and its value. -/
def mark (index : Nat) (value : V) : NGame KemSK V Unit := fun state => pure ((), (state.1, some (index, value)))

/-- The source's consumption of a registration ID. -/
def consumeGame (rid : beaconcrypt_core.pqxdh.RegistrationId) : NGame KemSK V Unit :=
  modifyGame fun game => { game with server := { game.server with consumed := game.server.consumed ++ [absBytes rid.bytes] } }

/-- A computation on the shared commitment cache of the game state (`PqxdhServerAuthNative.nativeCtx`). -/
def ctxGame {α : Type} (work : StateT (RawCtxSharedPrimitive.SharedState Unit) ProbComp α) :
    StateT (GameState KemSK) ProbComp α :=
  fun game => (fun result => (result.1, { game with ctx := result.2.2 })) <$> work.run ((), game.ctx)

end Programs

/-! ### The native layer of the skeleton -/

section Native

open PqxdhBeaconPhase2Preparation (Word32)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response V : Type}

/-- The coin channel of the exposed encapsulation interface. -/
def coinLift : QueryImpl unifSpec (OracleComp (Enc KemSK)) :=
  fun query => (Enc KemSK).query (.inl (.inr (.inl query)))

/-- Forward a request of the exposed encapsulation interface. -/
def encLift : QueryImpl (Enc KemSK) (OracleComp (Enc KemSK + TSpec V)) :=
  fun query => (Enc KemSK + TSpec V).query (.inl query)

/-- A native-layer program on the exposed encapsulation interface: coins go to its coin channel, table oracles are forwarded. -/
def liftT {α : Type} (work : NGame KemSK V α) : SClient KemSK V α :=
  fun state => simulateQ (fwd (T := TSpec V) (coinLift (KemSK := KemSK))) (work.run state)

/-- The Beacon tail callbacks of the source backend; the root callback reads the table directly. -/
noncomputable def tailStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) :
    QueryImpl (PqxdhBeaconPhase2Publication.NativeTailSpec Response) (NGame KemSK V)
  | .inl query => gameStep (ctxGame (beaconNative setup codec (.inl query)))
  | .inr (.root input) => do
      let block ← tableRead (absBytes input.bytes)
      pure (some (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac block)))
  | .inr (.initial request) => gameStep (ctxGame (beaconNative setup codec (.inr (.initial request))))
  | .inr (.application response) => gameStep (ctxGame (beaconNative setup codec (.inr (.application response))))

/-- The Server's core acceptance and root of a raw accept (`PqxdhServerAuthNative.nativeClient`), with the root read from the table directly. -/
noncomputable def clientStep (hmac : PqxdhSecretInputKdf.HmacSha512) (control : beaconcrypt_core.pqxdh.ServerState)
    (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) :
    NGame KemSK V (RustM (Option PqxdhServerRelatedRootConsumer.Returned)) :=
  match PqxdhServerRelatedRootInput.accept control binding input with
  | .ok (.Err _) => pure (ok none)
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Ok (_, original)) => do
      let root ← PqxdhSecretInputKdf.expandRoot hmac <$> tableRead (absBytes original.root_key_input.bytes)
      consumeGame original.registration_id
      pure (ok (some ⟨root, PqxdhServerClearedRoot.cleared original⟩))

/-- The Server's accept tail (`PqxdhRegistrationJointServerAccept.tail`). -/
noncomputable def acceptTail (setup : Setup baseSpec KemSK) (publicIdentity : PublicIdentity)
    (state : GameState KemSK)
    (collected : Option (PqxdhServerRootPreparation.Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) ×
      List Pqxdh.Bytes) : NGame KemSK V (Option Nat) := do
  let index := state.sessions
  setGame { state with sessions := index + 1, server := { state.server with consumed := collected.2 } }
  match collected.1 with
  | none => pure none
  | some input => do
      let returned ← clientStep setup.hmac state.server.control
        ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, setup.serverKeyId⟩ input
      match returned with
      | .ok (some token) => do
          modifyGame fun current => { current with pending := Function.update current.pending index (some token) }
          pure (some index)
      | _ => pure none

/-- The Server's raw accept with its encapsulation exposed (`PqxdhRegistrationJointKemEncapsulation.accept`). -/
noncomputable def acceptStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (raw : Pqxdh.Bytes) : SClient KemSK V (Option Nat) := do
  let before ← (fun state => pure (clean state.1, state) : SClient KemSK V (GameState KemSK))
  let collected ← (fun state => (fun result => (result, state)) <$> simulateQ (encLift (V := V))
      ((simulateQ (PqxdhRegistrationJointKemEncapsulation.prefixImpl setup codec checks raw)
        (PqxdhRegistrationJointServerPrefix.clientPrefix identityIndex raw)).run state.1.server.consumed) :
      SClient KemSK V _)
  liftT (acceptTail setup publicIdentity before collected)

/-- The source's native response tail of a session with pending token `token`. -/
noncomputable def nativeResponse (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    HiddenBuild := fun token payload server =>
  simulateQ (tailImpl setup codec checks)
    (PqxdhServerRegistrationPublication.build setup.source token.pending token.root payload () server)

/-- The response tail of a session: the hidden session's service, every other session's native tail. -/
noncomputable def buildService (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (marks : Marks V) (session : Nat) : HiddenBuild :=
  match marks with
  | some (index, value) =>
      if index = session then (services.hidden value).hiddenBuild else nativeResponse setup codec checks
  | none => nativeResponse setup codec checks

/-- The Server build (`PqxdhServerAuthNative.nativeBuild`), with the hidden session's response tail given by its service. -/
noncomputable def buildStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (services : Services V Response) (session : Nat) (payload : Option Pqxdh.Bytes) :
    NGame KemSK V (Option PqxdhServerRegistrationPublication.Response) := fun state =>
  match state.1.pending session with
  | none => pure (none, state)
  | some token => do
      let result ← OracleComp.liftComp
        ((buildService setup codec checks services state.2 session token payload state.1.server).run ([], state.1.ctx))
        (SkelSpec V)
      let settled := settle state.1.server result.1
      pure (settled.1, ({ state.1 with
        pending := Function.update state.1.pending session none
        server := settled.2
        ctx := result.2.2 }, state.2))

/-- The adversary's public HMAC (`PqxdhRegistrationJointPublicShared.hmac`): a direct read on the zero-key 192-byte slice, the real function elsewhere. -/
noncomputable def hmacStep (setup : Setup baseSpec KemSK) (key : HmacBlock) (message : Pqxdh.Bytes) :
    NGame KemSK V HmacBlock :=
  if key = PqxdhSecretInputKdf.zeroSalt ∧ message.length = 192 then tableRead message
  else pure (setup.hmac.eval key message)

/-- The source's BLAKE2b oracle (`PqxdhServerAuthNative.nativeHash`) on the game state. -/
noncomputable def hashGame (bytes : Pqxdh.Bytes) : StateT (GameState KemSK) ProbComp CtxRomAuth.CtxDigest :=
  fun game => (fun result => (result.1, { game with ctx := result.2 })) <$> (CtxRomAuth.ctxRandomOracle ((), bytes)).run game.ctx

/-- Placeholder fields of the Beacon preparation that no service reads. -/
def zeroWord : Word32 := PqxdhRootTableInitialization.rootArray (List.Vector.replicate 32 0)

/-- The prepared state of a grouped Beacon finish in the form taken by `hiddenAfter`: its response, ciphertext, ephemeral value, metadata and the four DH outputs. The Server identity fields and the KEM field, which the services do not read (they read only `PqxdhPhase2DhRootConsumer.cleared`), are placeholders. -/
def embed (pending : Pending Response) : PqxdhPhase2DhMetadata.Prepared Response :=
  ⟨⟨pending.response, pending.ciphertext, pending.ephemeral, zeroWord, zeroWord, pending.metadata.assigned,
    .known pending.root.dh1, pending.root.dh2, .known pending.root.dh3, pending.root.dh4, zeroWord⟩, pending.metadata⟩

/-- The grouped Beacon finish: a rejected DH output stops; the challenge marker reads its hidden value and runs the hidden continuation; a known decapsulation result reads its root directly and runs the native continuation. -/
noncomputable def groupStep (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (services : Services V Response) (pending : Pending Response) :
    NGame KemSK V (Option PqxdhBeaconPhase2Publication.Staged) :=
  if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
      absBytes pending.root.dh4) then
    match pending.root.shared with
    | .challenge => do
        let value ← valueRead (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)
        gameStep (ctxGame ((services.hidden value).hiddenAfter (embed pending)))
    | .known secret => do
        let block ← tableRead (PqxdhHiddenRoot.hiddenRootIKM
          (PqxdhPhase2InputBytes.coordinates pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4) secret)
        gameStep (ctxGame (simulateQ (tailNative setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending
          (PqxdhRootTableInitialization.rootArray (PqxdhSecretInputKdf.expandRoot setup.hmac block)))))
  else pure none

/-- The native layer of the skeleton on the grouped interface. -/
noncomputable def skelImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (services : Services V Response) :
    QueryImpl (GSpec KemSK Response) (SClient KemSK V)
  | .inl (.inl (.inl query)) => fun state =>
      (fun reply => (reply, state)) <$> encLift (V := V) (.inl query)
  | .inl (.inl (.inr query)) => liftT (tailStep setup codec query)
  | .inl (.inr (.accept raw)) => acceptStep setup codec checks identityIndex publicIdentity raw
  | .inl (.inr (.build session payload)) => liftT (buildStep setup codec checks services session payload)
  | .inl (.inr (.hmac key message)) => liftT (hmacStep setup key message)
  | .inl (.inr (.hash bytes)) => liftT (gameStep (hashGame bytes))
  | .inl (.inr (.reveal keyId)) => liftT (gameStep (fun game => pure (revealKernel keyId game, game)))
  | .inr pending => liftT (groupStep setup codec services pending)

/-- The private native tail of the Server's resumption: its root request reads the hidden value of its coordinates (handle `.challenge`, marking the session) or the table directly (a known handle); the auxiliary and bookkeeping requests are the source's. -/
noncomputable def resumeTail (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (services : Services V Response) :
    QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK) (NGame KemSK V)
  | .inl (.inl input) =>
      match input.shared with
      | .challenge => do
          let value ← valueRead (PqxdhCorrelatedExtractFamily.coordinates
            (PqxdhRegistrationJointKemOpaqueClient.coordinates input))
          mark index value
          pure (services.rootOf value)
      | .known secret => do
          let block ← tableRead (PqxdhHiddenRoot.hiddenRootIKM
            (PqxdhRegistrationJointKemOpaqueClient.coordinates input) secret)
          pure (PqxdhSecretInputKdf.expandRoot hmac block)
  | .inl (.inr .eraseShared) => pure ()
  | .inl (.inr .eraseInput) => pure ()
  | .inl (.inr (.consume rid)) => consumeGame rid
  | .inr (.install game) => setGame game
  | .inr (.publish slot token) =>
      modifyGame fun current => { current with pending := Function.update current.pending slot (some token) }

/-- The native layer of the skeleton on the Server's resumption: prefix requests are forwarded, tail requests run the private native tail. -/
noncomputable def resumeImpl (hmac : PqxdhSecretInputKdf.HmacSha512) (index : Nat) (services : Services V Response) :
    QueryImpl (PqxdhRegistrationJointKemOpaqueResume.Spec Reader KemSK) (SClient KemSK V)
  | .inl query => fun state =>
      (fun reply => (reply, state)) <$> encLift (V := V) query
  | .inr query => liftT (resumeTail hmac index services query)

end Native

/-! ### The post-challenge phase of the skeleton -/

section Post

open PqxdhRegistrationJointKemCommands (SourceSpec)
open PqxdhRegistrationJointAcceptCutTag (Tag decideTag)
open PqxdhRegistrationJointAcceptKemCut (tagged)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhRegistrationJointKemRawOpaque (OpaqueContext)
open PqxdhRegistrationJointBeaconOpaqueFinishRouter (placeholder)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X R V : Type}

/-- The resumed client of the skeleton: the Server's private resumption, then the rest of the tagged client under the grouped client, on the native layer of the skeleton. -/
noncomputable def skelResume (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : Nat) (publicIdentity : PublicIdentity) (observe : X × Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes)
    (consumed : List Pqxdh.Bytes) (game : GameState KemSK) (owners : List EncodedEntry)
    (next : Option Nat → OracleComp (SourceSpec KemSK) X) (selected : Nat)
    (ciphertext : MlKem768Ciphertext) (services : Services V Response) :
    OracleComp (Enc KemSK + TSpec V) ((R × List EncodedEntry) × SkelState KemSK V) := do
  let answer ← (simulateQ (resumeImpl setup.hmac game.sessions services)
    (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray ciphertext) .challenge game consumed)).run (game, none)
  (simulateQ (skelImpl setup codec checks identityIndex publicIdentity services)
    ((simulateQ (groupedClient setup codec selected ciphertext) (tagged observe raw next answer.1)).run owners)).run
      answer.2

/-- The challenger's CCA evaluation as one interpreter (`PqxdhDynamicKemPost.evaluate`). -/
noncomputable def evalLayer (setup : Setup baseSpec KemSK) (secret : KemSK) (challenge : MlKem768Ciphertext) :
    QueryImpl (MlKemCCAOracleSpec baseSpec) ProbComp :=
  kemAmbientImpl setup.baseImpl ∘ₛ setup.kem.IND_CCA_postChallengeImpl secret challenge

/-- The decision of a post-challenge run of the skeleton: the source's Boolean result, false on a stopped run. -/
def skelDecide {S J : Type} (reached : Option ((Bool × S) × SkelState KemSK V) × J) : Bool :=
  match reached.1 with
  | some outcome => outcome.1.1
  | none => false

/-- The post-challenge phase of the skeleton as a client of the coins and the table oracles: the resumed client of the skeleton under the actual encapsulator, the post-challenge router holding `placeholder` and the CCA evaluation, each forwarding the table oracles, followed by the decision. It is given the challenger's key pair, the challenge ciphertext and the prechallenge context; it has no candidate argument. -/
noncomputable def postSkel (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (decision : X → Bool) (count : Nat) (selected : Fin (count + 1)) (services : Services V Response)
    (chosen : MlKem768PublicKey × KemSK) (challenge : MlKem768Ciphertext)
    (context : OpaqueContext Reader KemSK A X count) : OracleComp (SkelSpec V) Bool :=
  match context with
  | .ready created others (some (.pending raw value ephemeral consumed native owners next)) state _ =>
    if value.keys.pqKey = chosen.1 then
      skelDecide (KemSK := KemSK) <$> simulateQ (fwd (T := TSpec V) (evalLayer setup chosen.2 challenge))
        (((simulateQ (fwdOption (T := TSpec V) (PqxdhDynamicKemJointRouter.post setup.joint setup.kem selected.val
            (PqxdhDynamicKemRouter.selectedReservation selected chosen.1 others) challenge placeholder))
          (simulateQ (fwd (T := TSpec V) (PqxdhRegistrationJointKemEncapsulation.actual setup))
            (skelResume setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
              (decideTag decision) raw value ephemeral consumed native.2 owners next selected.val challenge
              services))).run).run (eraseJoint state))
    else pure false
  | _ => pure false

end Post

/-! ### The native and the factored services -/

section Instances

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The native services at a root: the source's response tail on the session's pending token, and the source's native continuation after the root. -/
noncomputable def nativeHidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (root : RootOutput) : Hidden Response where
  hiddenBuild := nativeResponse setup codec checks
  hiddenAfter pending := simulateQ (beaconNative setup codec)
    (PqxdhPhase2DhRootConsumer.afterRoot codec.frameRead pending (PqxdhRootTableInitialization.rootArray root))

/-- The native services: hidden values are roots, and each hidden entry runs the source's native code at its root. -/
noncomputable def nativeServices (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks) :
    Services RootOutput Response where
  rootOf root := root
  hidden := nativeHidden setup codec checks

/-- The factored services of the single-entry experiment have the skeleton's hidden-service types (plan section 18): on a hidden entry with 108-byte value `value`, stage S3b instantiates `hidden` by these fields. -/
noncomputable def factorHidden (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (context : PqxdhServerAuthEntryFactor.Context KemSK) (value : PqxdhServerAuthKeySchedule.Output) :
    Hidden Response where
  hiddenBuild := (PqxdhServerAuthEntryFactor.factorServices setup codec checks context value).hiddenBuild
  hiddenAfter := (PqxdhServerAuthEntryFactor.factorServices setup codec checks context value).hiddenAfter

end Instances

end BeaconcryptCore.Computational.PqxdhRegistrationJointKemPostSkeleton
