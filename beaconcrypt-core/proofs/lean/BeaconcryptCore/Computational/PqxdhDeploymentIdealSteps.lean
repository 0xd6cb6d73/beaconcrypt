-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealSlots
import BeaconcryptCore.Computational.PqxdhDeploymentIdealParams
import BeaconcryptCore.Computational.PqxdhRegistrationJointKemOpaqueResume
import BeaconcryptCore.Computational.PqxdhDeploymentLaterServerNative

/-!
# The ideal registration of the common deployment experiment and `CE.idealGame g` (CE-11b, unit U1)

The ideal registration of the common deployment experiment for one target (CE-11b design-v2 section 3, unit U1) and the game `CE.idealGame g` built from it. It is pointwise in the challenger's draws `p : Params KemSK count` (route R3, `PqxdhDeploymentIdealParams`) and in a target `t` (a raw-accept ordinal and a KEM creation index), and it is a slot program (`PqxdhDeploymentIdealSlots.SlotProgram`): each registration command is a stateful client of coins and of hidden reads at item 2's 128-byte DH coordinates, which `slotCore` answers through item 2's first-touch allocator in front of a slot service. Its own backend `IdealCore` holds the raw-accept counter, the flag recording that the selected accept was active, the hidden Server session with the coordinates of its hidden read, and two ghosts on which no reply and no non-ghost state depends (the hidden Server install and the hidden Beacon install; a step that may set one reads its earlier value only to keep it when it sets nothing).

- Create reads the KEM key pair of the new owner from the pool (`createPool`: `PqxdhRegistrationSchedule.create` with the KEM draw replaced by pool entry `owners.length`; beyond the pool it is the native create, `createPool_beyond`). Bundle and HMAC are the real commands (`realRegAt`, the real registration handler `PqxdhDeploymentBackend.realReg` on any backend, `realRegAt_real`; `idealProg_real`).
- The raw accept compares the pre-increment counter with the target ordinal (`acceptStep`, `acceptStep_other`, `acceptStep_accepts`). The selected accept is `acceptExposed`: when the pure verification of the Phase 1 message yields the challenger's selected PQ key, the native steps before encapsulation run; if they reach the encapsulation the accept is active, the challenge ciphertext is sent with item 2's candidate-free suffix and the challenge marker, and item 2's marker tail runs under `tailCE`, whose challenge-marked root request reads the hidden value at the root input's coordinates, marks the session with them and returns the sentinel root. On every other Phase 1 message it is the LQ-F logged accept (`acceptExposed_logged`).
- The build of the marked session with a pending token reads its hidden value (an allocator hit) and runs `buildHidden`, the native build with the session's response tail given by the hidden build service (`buildHidden_native`: with the native services at a root it is the native build); a published peer sets the Server install ghost. Every other build is real (`buildStep_real`): every build while no session is marked (`buildStep_unmarked`), and, once a session is marked, every build of another session and every build of the marked session without a pending token (`buildStep_other`).
- After an active selected accept, a finish of the selected owner in the `initSent` phase runs `finishChallenge`: the owner's grouped native finish (item 2's grouped Beacon owner at the native owner type) whose preparation answers the decapsulation of exactly the challenge ciphertext with the challenge marker (`preparationCE_challenge`) and decapsulates every other ciphertext as item 2's CCA evaluation does (`preparationCE_eval`), and whose grouped request reads the hidden value at the four DH coordinates and runs the hidden continuation on a challenge marker (`groupCE`). An establishment after a hidden read sets the Beacon install ghost. Every other finish is real (`finishStep_real`).
- `tailCE_challenge`, `groupCE_challenge` and `groupCE_known` relate the CE-native hidden steps to item 2's services skeleton under its public-table layer (`publicLocal_coins`): the challenge-marked root request and the challenge-marked grouped finish answer as `resumeTail` and `groupStep` with the factored services, with the same reply and the same game state without ghosts, and with the CE-native Extract family state (observation history and HMAC cache) and item 2's table cache both unchanged. For the root request the CE mark is item 2's mark with the coordinates in place of the value, and the whole CE-native state is unchanged; for the grouped finish the recorded coordinates become the four DH coordinates (when the DH outputs are nonzero) and item 2's marks are unchanged. A known decapsulation result is item 2's native grouped answer `groupNativeN`.

`idealCore t p svc` is the slot core of `idealProg` with the factored hidden services over any slot service, `idealReg t p` is the core over item 2's persistent lazy table, and `idealGame` (`CE.idealGame g`) draws the challenger's parameters and runs the common deployment experiment `gameWith` with `idealReg` at the target of `g`, from the initial backend `idealInit` and with identity index 0. `idealCoreErased` uses the erased hidden services `erasedHidden` (the factored build and the erased finish at the split of the value), the form after C7. Both cores are natural (`idealCore_natural`, `idealCoreErased_natural`: CE-11a's `CoreNatural`, the premise of `PqxdhDeploymentSeedSplit.represent_split`). `SplitBk` and `splitInit` are the backend of the split form.

These are definitions, program equalities and support facts. They charge nothing and make no security claim; C7, the split, the environment, the provenance facts and the second compile lemma are later units.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps
open PqxdhServerAuthExperiment (Setup Codec Checks serverAux)
open PqxdhServerAuthNative (NativeState NativeGame)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhServerRootPreparation (Verified)
open PqxdhKemIndCca (MlKem768Ciphertext MlKem768PublicKey)
open PqxdhBeaconPhase2Preparation (Word32)
open PqxdhLiveKemReservation (Pair)
open PqxdhLiveServerConstruction (Created)
open PqxdhDeploymentBackend (XState RegImpl gameWith)
open PqxdhDeploymentIdealSlots (Coord SlotSpec SlotProgram slotCore)
open PqxdhDeploymentIdealParams (Target Params drawParams)
open PqxdhRegistrationJointKemSecondEntry (Alloc emptyAlloc)
open PqxdhRegistrationJointKemPostSkeleton (Hidden)
open PqxdhRegistrationJointKemEntryFactor (Output factoredHidden)
open PqxdhRecordLiftInterface (EnvQuery EnvSpec)

/-! ### The ideal backend -/

/-- The ideal registration's own backend (design-v2 section 3.1): the number of raw accepts so far (before a raw accept, the ordinal of that accept), whether the selected accept was active (it reached its encapsulation with the challenger's selected PQ key, so the challenge ciphertext was sent), the hidden Server session with the coordinates of its hidden read, and two ghosts on which no reply and no non-ghost state depends (a step that may set one reads its earlier value only to keep it when it sets nothing): the hidden Server install (key ID of the published peer and the coordinates) and the hidden Beacon install of the selected owner (the coordinates). -/
structure IdealCore where
  accepts : ℕ
  active : Bool
  marks : Option (ℕ × Coord)
  peer : Option (Std.U64 × Coord)
  beacon : Option Coord

/-- The initial ideal backend: no raw accept, inactive, no hidden session, no hidden install. -/
def IdealCore.initial : IdealCore := ⟨0, false, none, none, none⟩

/-- The service state of the ideal registration: item 2's persistent lazy table of 108-byte outputs, with its counts. -/
abbrev TableState := PqxdhRecordLiftLazyTable.State (PqxdhDeploymentSeedSplit.OutputSpec 2)

/-- The backend of a slot core of the ideal registration: a service state, item 2's first-touch allocator and the ideal backend. -/
abbrev IdealBk (S : Type) := S × (Alloc Coord 2 × IdealCore)

/-- The initial backend of `CE.idealGame g`: the empty lazy table, the empty allocator and the initial ideal backend. -/
def idealInit (_ : Created Unit) : IdealBk TableState :=
  (PqxdhRecordLiftLazyTable.initial, (emptyAlloc, IdealCore.initial))

/-- The backend of the split form (design-v2 sections 3.1 and 5.2): the environment material cache in place of the table, the allocator and the ideal backend; the seeds live in the extended state's seed table. -/
abbrev SplitBk := (PqxdhDeploymentSeedSplit.MaterialSpec 2).QueryCache × (Alloc Coord 2 × IdealCore)

/-- The initial backend of the split form. -/
def splitInit (_ : Created Unit) : SplitBk := (∅, (emptyAlloc, IdealCore.initial))

/-! ### Registration steps as slot clients -/

/-- A probabilistic computation as a slot client (coins only). -/
abbrev liftS {α : Type} (work : ProbComp α) : OracleComp SlotSpec α := OracleComp.liftComp work SlotSpec

/-- A stateful probabilistic step as a stateful slot client that issues coins only. -/
def onSlots {σ α : Type} (step : StateT σ ProbComp α) : StateT σ (OracleComp SlotSpec) α :=
  fun state => liftS (step.run state)

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks)

/-- The real registration handler `PqxdhDeploymentBackend.realReg` on any backend and slot count: the snapshot of a finish, then the LQ-F run-phase handler on the deployment state and the log; the backend and the seed table are untouched. -/
noncomputable def realRegAt {Bk : Type} {n : ℕ} (created : Created Unit) : RegImpl KemSK Bk n :=
  fun query state =>
    let snap := PqxdhDeploymentLater.snapshotAt state.snap state.base.native.owners
      (PqxdhDeploymentLater.finishOwner (.inr query.val))
    (fun result => (result.1, { state with base := result.2.1, log := result.2.2, snap := snap })) <$>
      (PqxdhDeploymentLaterServerGame.handler setup codec checks route created.seed (.inr query.val)).run
        (state.base, state.log)

/-- At the unit backend with no slot, `realRegAt` is the real registration handler. -/
theorem realRegAt_real (created : Created Unit) :
    realRegAt (Bk := Unit) (n := 0) setup codec route checks created =
      PqxdhDeploymentBackend.realReg setup codec route checks created := rfl

end Real

/-! ### Creation from the pool -/

section Pool
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type} (setup : Setup baseSpec KemSK)

/-- The post-admission constructor body with the KEM key pair read from the pool at the new owner's index: `PqxdhRegistrationSchedule.create` with the KEM draw replaced (identity and prekey are still drawn, in production order). Beyond the pool a fresh key pair is drawn, as `create` does. -/
noncomputable def createPool (pool : List (Pair KemSK)) (pin : Word32) (keyId : Std.U64) :
    PqxdhRegistrationSchedule.Game KemSK ℕ := do
  let identity ← StateT.lift PqxdhJointIdentity.sampleSeed
  let prekey ← StateT.lift PqxdhJointGapDh.sampleScalar
  let state ← get
  let keys ← StateT.lift (match pool[state.owners.length]? with
    | some keys => pure keys
    | none => simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen)
  let owner : PqxdhRegistrationSchedule.Owner KemSK := ⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩
  set { state with owners := state.owners ++ [owner] }
  pure state.owners.length

/-- Beyond the pool, the pool create is the native create. -/
theorem createPool_beyond (pool : List (Pair KemSK)) (pin : Word32) (keyId : Std.U64)
    (state : PqxdhRegistrationSchedule.State KemSK) (beyond : pool[state.owners.length]? = none) :
    (createPool setup pool pin keyId).run state = (PqxdhRegistrationSchedule.create setup pin keyId).run state := by
  simp only [createPool, PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind,
    StateT.run_get, StateT.run_set, StateT.run_pure, beyond]

/-- The create command of the ideal registration: the native create command with the pool create. -/
noncomputable def createReg {Γ : Type} {n : ℕ} (pool : List (Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64) :
    StateT (XState KemSK Γ n) ProbComp (Option ℕ) :=
  PqxdhDeploymentBackend.onBase (match PqxdhDeploymentInterface.parsePin pin with
    | none => pure none
    | some word => some <$> PqxdhDeploymentNative.onNative (createPool setup pool word keyId))

end Pool

/-! ### The selected raw accept -/

section Accept
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The hidden-read coordinates of a prepared root input (item 2's `resumeTail`). -/
def coordsOf (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) : Coord :=
  PqxdhCorrelatedExtractFamily.coordinates (PqxdhRegistrationJointKemOpaqueClient.coordinates input)

/-- The CE-native interpreter of the Server's resumed tail (item 2's `PqxdhRegistrationJointKemPostSkeleton.resumeTail` with the factored services, natively): a root request with the challenge marker reads the hidden value at its coordinates through the allocator, marks the session with the coordinates and returns the sentinel root; a known root request is the native restricted-ROM root; auxiliary and mutation requests are the native ones. -/
noncomputable def tailCE (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) :
    QueryImpl (PqxdhRegistrationJointKemOpaqueTail.Spec Reader KemSK)
      (StateT (NativeState KemSK × Option (ℕ × Coord)) (OracleComp SlotSpec))
  | .inl (.inl input) => fun s =>
      match input.shared with
      | .challenge => do
          let _ ← (SlotSpec.query (.inr (coordsOf input)) : OracleComp SlotSpec _)
          pure (PqxdhServerAuthEntryFactor.sentinel, (s.1, some (index, coordsOf input)))
      | .known _ => (fun r => (r.1, (r.2, s.2))) <$>
          liftS ((PqxdhRegistrationJointKemOpaqueClient.romRoot KemSK hmac index (List.Vector.replicate 32 0) input).run s.1)
  | .inl (.inr query) => fun s => (fun r => (r.1, (r.2, s.2))) <$>
      liftS ((PqxdhRegistrationJointKemOpaqueClient.auxiliary KemSK query).run s.1)
  | .inr query => fun s => (fun r => (r.1, (r.2, s.2))) <$>
      liftS ((PqxdhRegistrationJointKemOpaqueTail.mutation query).run s.1)

/-- The native Server callbacks of the accept prefix. -/
noncomputable abbrev prefixNative (seed : IdentitySeed) :=
  PqxdhServerStaticDhSource.nativeImpl setup.joint seed (serverAux setup codec checks)
    (fun _ => (pure () : StateT (List Pqxdh.Bytes) ProbComp Unit))

/-- The reply of the selected raw accept: the session (if any) with the logged ephemeral scalar, and whether the accept was active with the hidden mark it set. -/
abbrev AcceptOut := (Option ℕ × Option ScalarBytes) × (Bool × Option (ℕ × Coord))

/-- The selected accept on a verified key match (design-v2 section 3.2): the native steps before encapsulation (`beforeLogged` under the native Server callbacks). A rejection there runs the native accept tail without input and is not active. Otherwise the accept is active: item 2's candidate-free suffix (`PqxdhRegistrationJointKemOpaqueSuffix.program`) with the challenge ciphertext and the challenge marker under the native callbacks, then item 2's marker tail (`PqxdhRegistrationJointKemOpaqueTail.tail`) under `tailCE`. -/
noncomputable def acceptActive (seed : IdentitySeed) (challenge : MlKem768Ciphertext) (verified : Verified Reader) :
    StateT (NativeState KemSK) (OracleComp SlotSpec) AcceptOut := fun s => do
  let pre ← liftS ((simulateQ (prefixNative setup codec checks seed)
    (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := Word32) verified)).run s.2.server.consumed)
  match pre.1.1 with
  | none => do
      let r ← liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup (setup.joint.publicKeys seed) s.2
        (none, pre.2)).run s)
      pure (((r.1, pre.1.2), (false, none)), r.2)
  | some ephemeral => do
      let prepared ← liftS ((simulateQ (prefixNative setup codec checks seed)
        (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := Word32) verified ephemeral
          (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge)).run pre.2)
      let answer ← (simulateQ (tailCE setup.hmac s.2.sessions)
        (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared)).run
          (s, none)
      pure (((answer.1, pre.1.2), (true, answer.2.2)), answer.2.1)

/-- The LQ-F logged accept as a slot client, inactive and with no mark. -/
noncomputable def acceptInactive (seed : IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (NativeState KemSK) (OracleComp SlotSpec) AcceptOut := fun s =>
  (fun r : (Option ℕ × Option ScalarBytes) × NativeState KemSK => ((r.1, (false, none)), r.2)) <$>
    liftS ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run s)

/-- The selected raw accept with its encapsulation exposed (`acceptExposed`): on a Phase 1 message whose pure verification yields the challenger's selected PQ key, `acceptActive`; on every other message, the LQ-F logged accept (`acceptInactive`). -/
noncomputable def acceptExposed (seed : IdentitySeed) (chosen : Pair KemSK) (challenge : MlKem768Ciphertext)
    (raw : Pqxdh.Bytes) : StateT (NativeState KemSK) (OracleComp SlotSpec) AcceptOut :=
  match PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
  | some verified =>
      if verified.keys.pqKey = chosen.1 then acceptActive setup codec checks seed challenge verified
      else acceptInactive setup codec checks seed raw
  | none => acceptInactive setup codec checks seed raw

/-- On a raw accept whose verification does not yield the selected PQ key, the selected accept is the LQ-F logged accept, inactive and with no mark. -/
theorem acceptExposed_logged (seed : IdentitySeed) (chosen : Pair KemSK) (challenge : MlKem768Ciphertext)
    (raw : Pqxdh.Bytes)
    (inactive : ∀ verified, PqxdhRegistrationJointRawSignatures.verified setup codec checks raw = some verified →
      verified.keys.pqKey ≠ chosen.1) (s : NativeState KemSK) :
    (acceptExposed setup codec checks seed chosen challenge raw).run s =
      (fun r : (Option ℕ × Option ScalarBytes) × NativeState KemSK => ((r.1, (false, none)), r.2)) <$>
        liftS ((PqxdhDeploymentLaterServerNative.acceptLogged setup codec checks seed raw).run s) := by
  unfold acceptExposed
  rcases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | verified
  · rfl
  · simp only [inactive verified found, ↓reduceIte]
    rfl

end Accept

/-! ### The marked build -/

section Build
variable {KemSK Response : Type}
open PqxdhServerAuthNative (nativeGet nativeSet nativeCoins)

/-- The marked Server build (design-v2 section 3.2): `PqxdhServerAuthNative.nativeBuild` with the session's response tail given by the hidden build service; the token is consumed and the seals are logged as in the native build. -/
noncomputable def buildHidden (hidden : Hidden Response) (session : ℕ) (payload : Option Pqxdh.Bytes) :
    NativeGame KemSK (Option PqxdhServerRegistrationPublication.Response) := do
  let state ← nativeGet
  match state.pending session with
  | none => pure none
  | some token => do
      let result ← nativeCoins ((hidden.hiddenBuild token payload state.server).run ([], state.ctx))
      let settled := PqxdhServerAuthExperiment.settle state.server result.1
      nativeSet { state with
        pending := Function.update state.pending session none
        server := settled.2
        ctx := result.2.2
        ghost := { state.ghost with seals := state.ghost.seals ++ result.2.1.map (fun context => (session, context)) } }
      pure settled.1

/-- With the native services at a root, the marked build is the native build. -/
theorem buildHidden_native {ι : Type} {baseSpec : OracleSpec ι} {Reader : Type} (setup : Setup baseSpec KemSK)
    (codec : Codec Reader Response) (checks : Checks) (root : PqxdhSecretInputKdf.RootOutput) (session : ℕ)
    (payload : Option Pqxdh.Bytes) :
    buildHidden (KemSK := KemSK) (PqxdhRegistrationJointKemPostSkeleton.nativeHidden setup codec checks root) session
        payload =
      PqxdhServerAuthNative.nativeBuild setup codec checks session payload := rfl

/-- The key ID of a published peer: a build response whose key ID names a peer of the settled Server (`PqxdhDeploymentEnvironment.hiddenServerEffect` installs exactly these). -/
def publishedKey (response : Option PqxdhServerRegistrationPublication.Response)
    (server : PqxdhServerRegistrationPublication.State Unit Unit (List Pqxdh.Bytes)) : Option Std.U64 :=
  match response with
  | none => none
  | some response => (server.server.peers response.keyId).map fun _ => response.keyId

end Build

/-! ### Owner k's challenge finish -/

section Finish
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
open PqxdhRegistrationJointKemPostSkeleton (Pending GroupSpec embed message)
open PqxdhPhase2DecapsulationRouting (Shared)

/-- The native Beacon preparation interface with the opaque decapsulation handle. -/
abbrev PreSpecCE (KemSK Response : Type) :=
  PqxdhBeaconPhase2Shared.Spec IdentitySeed ScalarBytes (MlKem768PublicKey × KemSK) IdentitySeed Response Shared

/-- The grouped native owner's interface: preparation requests and the grouped finish request. -/
abbrev OwnerSpecCE (KemSK Response : Type) := PreSpecCE KemSK Response + GroupSpec Response

/-- The native Beacon owner in grouped form (item 2's `PqxdhRegistrationJointKemPostSkeleton.groupedOwner` at the native owner type): the opaque-handle preparation, then the private root and the whole continuation after it as one request, then the source commit. -/
noncomputable def groupedOwnerCE (raw : Pqxdh.Bytes) (state : PqxdhRegistrationSchedule.Owner KemSK) :
    OracleComp (OwnerSpecCE KemSK Response) (Option Pqxdh.Bytes × PqxdhRegistrationSchedule.Owner KemSK) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let prepared ← simulateQ (fun query => ((OwnerSpecCE KemSK Response).query (.inl query) :
          OracleComp (OwnerSpecCE KemSK Response) _) : QueryImpl (PreSpecCE KemSK Response)
            (OracleComp (OwnerSpecCE KemSK Response)))
        (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match prepared with
      | none => pure (PqxdhBeaconPhase2Publication.finish control state none)
      | some prepared => do
          let staged ← ((OwnerSpecCE KemSK Response).query (.inr prepared) : OracleComp (OwnerSpecCE KemSK Response) _)
          pure (PqxdhBeaconPhase2Publication.finish control state staged)
  | _ => pure (none, state)

/-- The native preparation callbacks with the challenge handle: the decapsulation of exactly the challenge ciphertext answers the challenge marker without reading a key; every other ciphertext is decapsulated with the owner's secret key, as `PqxdhRegistrationSchedule.preparation` does. -/
noncomputable def preparationCE (challenge : MlKem768Ciphertext) : QueryImpl (PreSpecCE KemSK Response) ProbComp
  | .decode raw => pure (codec.read2 raw)
  | .ciphertext response => pure (codec.ciphertext response)
  | .ephemeral response => pure (codec.ephemeral response)
  | .serverIdentity response => pure (codec.serverIdentity response)
  | .publicConversion server => pure ((setup.source.crypto.xpkConv (absBytes server)).bind
      PqxdhServerAuthExperiment.toWord32)
  | .privateConversion seed => pure (some seed)
  | .decapsulate ciphertext keys =>
      if PqxdhPhase2InputBytes.ciphertext ciphertext = challenge then pure (some .challenge)
      else Option.map Shared.known <$> simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.decaps keys.2 (PqxdhPhase2InputBytes.ciphertext ciphertext))
  | .dhPair scalar point => pure ((PqxdhJointGapDh.sourceScalarDh setup.source.crypto scalar
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .dhIdentity seed point => pure ((setup.joint.staticDh seed
      (PqxdhPhase2GapDhSource.peer point)).map PqxdhRootTableInitialization.rootArray)
  | .assignedId response => pure (codec.assignedId response)
  | .eraseShared _ => pure ()

/-- The decapsulation of exactly the challenge ciphertext answers the challenge marker, whatever the key pair. -/
theorem preparationCE_challenge (challenge : MlKem768Ciphertext) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (keys : MlKem768PublicKey × KemSK) (same : PqxdhPhase2InputBytes.ciphertext ciphertext = challenge) :
    preparationCE (Response := Response) setup codec challenge (.decapsulate ciphertext keys) = pure (some .challenge) := by
  simp only [preparationCE, same, ↓reduceIte]

/-- Every other ciphertext is decapsulated as item 2's CCA evaluation (`PqxdhRegistrationJointKemPostSkeleton.evalLayer`) of the owner's secret key answers the post-challenge decapsulation query, as a known handle. -/
theorem preparationCE_eval (challenge : MlKem768Ciphertext) (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (keys : MlKem768PublicKey × KemSK) (other : PqxdhPhase2InputBytes.ciphertext ciphertext ≠ challenge) :
    preparationCE (Response := Response) setup codec challenge (.decapsulate ciphertext keys) =
      Option.map Shared.known <$> simulateQ (PqxdhRegistrationJointKemPostSkeleton.evalLayer setup keys.2 challenge)
        ((PqxdhKemIndCca.MlKemCCAOracleSpec baseSpec).query (.inr (PqxdhPhase2InputBytes.ciphertext ciphertext))) := by
  simp only [preparationCE, other, ↓reduceIte, PqxdhRegistrationJointKemPostSkeleton.evalLayer, simulateQ_spec_query,
    QueryImpl.apply_compose, KEMScheme.IND_CCA_postChallengeImpl]
  exact congrArg (fun work => Option.map Shared.known <$>
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) work) (ite_eq_right_of_eq_false _ _ (eq_false other)).symm

/-- The CE-native answer to a grouped finish request (item 2's `groupStep`, natively). With the challenge marker and nonzero DH outputs, the hidden value is read at the four DH coordinates through the allocator, the coordinates are recorded, and the hidden continuation `(hidden value).hiddenAfter` runs on the shared CTX cache; with zero DH outputs nothing happens. With a known decapsulation result, the native private root (`markedRoot`) and the native continuation after it. -/
noncomputable def groupCE (hidden : Output → Hidden Response) (pending : Pending Response) :
    StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec) (Option PqxdhBeaconPhase2Publication.Staged) :=
  fun s =>
    match pending.root.shared with
    | .challenge =>
        if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
            absBytes pending.root.dh4) then do
          let coords := message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4
          let value ← (SlotSpec.query (.inr coords) : OracleComp SlotSpec _)
          let r ← liftS ((PqxdhServerAuthNative.nativeCtx (KemSK := KemSK)
            ((hidden value).hiddenAfter (embed pending))).run s.1)
          pure (r.1, (r.2, some coords))
        else pure (none, s)
    | .known _ => (fun r => (r.1, (r.2, s.2))) <$> liftS ((do
        let root ← PqxdhRegistrationJointBeaconOpaqueFinish.markedRoot setup.hmac (List.Vector.replicate 32 0)
          pending.root
        match root with
        | none => pure none
        | some root => PqxdhServerAuthNative.nativeCtx (simulateQ (PqxdhRegistrationJointKemPostSkeleton.tailNative
            setup codec) (PqxdhBeaconPhase2Shared.afterRoot codec.frameRead pending root)) :
        NativeGame KemSK (Option PqxdhBeaconPhase2Publication.Staged)).run s.1)

/-- The interpreter of the grouped native owner: the native preparation with the challenge handle, and the CE-native grouped finish. -/
noncomputable def ownerImplCE (hidden : Output → Hidden Response) (challenge : MlKem768Ciphertext) :
    QueryImpl (OwnerSpecCE KemSK Response) (StateT (NativeState KemSK × Option Coord) (OracleComp SlotSpec))
  | .inl query => fun s => (fun reply => (reply, s)) <$> liftS (preparationCE setup codec challenge query)
  | .inr pending => groupCE setup codec hidden pending

/-- Owner k's challenge finish (design-v2 section 3.2): the addressed owner's grouped native finish under `ownerImplCE`, from the registration state and no recorded coordinates; the returned owner is reinstalled, and the coordinates of a hidden read are returned in the state. -/
noncomputable def finishChallenge (hidden : Output → Hidden Response) (challenge : MlKem768Ciphertext) (index : ℕ)
    (raw : Pqxdh.Bytes) :
    StateT (PqxdhRegistrationSchedule.State KemSK × Option Coord) (OracleComp SlotSpec) (Option Pqxdh.Bytes) :=
  fun state =>
    match state.1.owners[index]? with
    | none => pure (none, state)
    | some owner => do
        let result ← (simulateQ (ownerImplCE setup codec hidden challenge)
          (groupedOwnerCE (Response := Response) raw owner)).run (state.1.shared, state.2)
        pure (result.1.1, ({ shared := result.2.1, owners := state.1.owners.set index result.1.2 }, result.2.2))

end Finish

/-! ### Agreement of the hidden steps with item 2's skeleton steps

On the game state without ghosts and under item 2's public-table layer `PqxdhRegistrationJointKemEntryFactor.publicLocalV` (which answers the skeleton's direct reads from a lazily sampled table and forwards coins and hidden reads), the CE-native hidden steps answer as the corresponding steps of item 2's services skeleton with the factored services: the challenge-marked root request of the selected accept as `resumeTail`, and the grouped challenge finish as `groupStep`. Each statement is one equation of joint distributions that also keeps the components a later simulation relation needs: the CE-native Extract family state (the first component of the native state) and item 2's table cache are unchanged; for the root request the CE mark is item 2's mark with the coordinates in place of the value, and for the grouped finish the recorded coordinates become the four DH coordinates (when the DH outputs are nonzero) and item 2's marks are unchanged. A grouped finish with a known decapsulation result is item 2's native grouped answer `groupNativeN`, whose split against `groupStep` is item 2's `split_group`. These are the per-step facts of the post-challenge simulation (CE-11b design section 8.4). -/

section Skeleton
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhRegistrationJointKemPostSkeleton (Pending SkelSpec clean groupStep embed message)
open PqxdhRegistrationJointKemEntryFactor (EntrySpec publicLocalV factoredServices)

/-- Item 2's public-table layer passes coins through: a lifted probabilistic computation leaves the table unchanged. -/
theorem publicLocal_coins {V α : Type} (work : ProbComp α) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    (simulateQ (publicLocalV V) (OracleComp.liftComp work (SkelSpec V))).run cache =
      (fun a => (a, cache)) <$> OracleComp.liftComp work (EntrySpec V) := by
  rw [QueryImpl.simulateQ_liftComp_left_eq_of_apply (publicLocalV V)
    (fun query => StateT.mk fun cache => (fun reply => (reply, cache)) <$>
      ((EntrySpec V).query (.inl query) : OracleComp (EntrySpec V) _)) (fun _ => rfl)]
  induction work using OracleComp.inductionOn generalizing cache with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
        StateT.run_bind, OracleComp.liftComp_bind, OracleComp.liftComp_query, map_bind, StateT.run_mk, bind_map_left]
      refine bind_congr fun reply => ?_
      exact ih reply cache

/-- The challenge-marked root request of the selected accept: `tailCE` reads the hidden value at the root input's coordinates and returns the sentinel root, as item 2's `resumeTail` with the factored services does. Jointly: the replies are equal; the whole CE-native state (Extract family state and game state with its ghosts) is unchanged; item 2's game state is the CE game state without ghosts, so it is unchanged too; the CE mark records the session and the coordinates where item 2's mark records the session and the value read there; and item 2's table cache is unchanged. -/
theorem tailCE_challenge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (index : ℕ) (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader)
    (marker : input.shared = .challenge) (native : NativeState KemSK) (recorded : Option (ℕ × Coord))
    (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    (fun r => (r.1, r.2.1, clean r.2.1.2, r.2.2, cache)) <$>
        (tailCE (KemSK := KemSK) setup.hmac index (.inl (.inl input))).run (native, recorded) =
      (fun r => (r.1.1, native, r.1.2.1, (r.1.2.2).map (fun mark => (mark.1, coordsOf input)), r.2)) <$>
        (simulateQ (publicLocalV Output)
          ((PqxdhRegistrationJointKemPostSkeleton.resumeTail (KemSK := KemSK) setup.hmac index
            (factoredServices setup codec checks) (.inl (.inl input))).run (clean native.2, marks))).run cache := by
  have left : (tailCE (KemSK := KemSK) setup.hmac index (.inl (.inl input))).run (native, recorded) =
      (do
        let _ ← (SlotSpec.query (.inr (coordsOf input)) : OracleComp SlotSpec _)
        pure (PqxdhServerAuthEntryFactor.sentinel, (native, some (index, coordsOf input)))) := by
    simp only [tailCE, StateT.run, marker]
  have right : (PqxdhRegistrationJointKemPostSkeleton.resumeTail (KemSK := KemSK) setup.hmac index
      (factoredServices setup codec checks) (.inl (.inl input))).run (clean native.2, marks) =
      (do
        let value ← ((SkelSpec Output).query (.inr (.inl (coordsOf input))) : OracleComp (SkelSpec Output) _)
        pure (PqxdhServerAuthEntryFactor.sentinel, (clean native.2, some (index, value)))) := by
    simp only [PqxdhRegistrationJointKemPostSkeleton.resumeTail, marker, StateT.run]
    rfl
  rw [left, right, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  have read : (publicLocalV Output (Sum.inr (Sum.inl (coordsOf input)))).run cache =
      (fun reply => (reply, cache)) <$> ((EntrySpec Output).query (.inr (coordsOf input)) :
        OracleComp (EntrySpec Output) _) := rfl
  rw [read]
  simp only [bind_map_left, map_bind, simulateQ_pure, StateT.run_pure, map_pure]
  rfl

/-- The grouped finish with the challenge marker: the CE-native answer `groupCE` with the factored hidden services is item 2's grouped step `groupStep` with the factored services, under item 2's public-table layer. Jointly: the replies are equal; the CE-native Extract family state is unchanged; item 2's game state is the CE game state without ghosts (the CTX cache may change, equally on both sides); the CE recorded coordinates become the four DH coordinates when the DH outputs are nonzero and are unchanged otherwise; and item 2's marks and table cache are unchanged. -/
theorem groupCE_challenge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (pending : Pending Response) (marker : pending.root.shared = .challenge) (native : NativeState KemSK)
    (recorded : Option Coord) (marks : PqxdhRegistrationJointKemPostSkeleton.Marks Output)
    (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache) :
    (fun r => (r.1, r.2.1.1, clean r.2.1.2, r.2.2, marks, cache)) <$>
        (groupCE setup codec (factoredHidden setup codec checks) pending).run (native, recorded) =
      (fun r => (r.1.1, native.1, r.1.2.1,
          (if Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
              absBytes pending.root.dh4) then
            some (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)
          else recorded), r.1.2.2, r.2)) <$>
        (simulateQ (publicLocalV Output)
          ((groupStep setup codec (factoredServices setup codec checks) pending).run (clean native.2, marks))).run cache := by
  by_cases nonzero : Pqxdh.dhNonZero (absBytes pending.root.dh1, absBytes pending.root.dh2, absBytes pending.root.dh3,
      absBytes pending.root.dh4)
  · simp only [nonzero, ↓reduceIte]
    have left : (groupCE setup codec (factoredHidden setup codec checks) pending).run (native, recorded) =
        (do
          let value ← (SlotSpec.query (.inr (message pending.root.dh1 pending.root.dh2 pending.root.dh3
            pending.root.dh4)) : OracleComp SlotSpec _)
          let r ← liftS ((PqxdhServerAuthNative.nativeCtx (KemSK := KemSK)
            ((factoredHidden setup codec checks value).hiddenAfter (embed pending))).run native)
          pure (r.1, (r.2, some (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)))) := by
      simp only [groupCE, StateT.run, marker, nonzero, ↓reduceIte]
    have right : (groupStep setup codec (factoredServices setup codec checks) pending).run (clean native.2, marks) =
        (do
          let value ← ((SkelSpec Output).query (.inr (.inl (message pending.root.dh1 pending.root.dh2 pending.root.dh3
            pending.root.dh4))) : OracleComp (SkelSpec Output) _)
          (fun result => (result.1, (result.2, marks))) <$> OracleComp.liftComp
            ((PqxdhRegistrationJointKemPostSkeleton.ctxGame
              ((factoredHidden setup codec checks value).hiddenAfter (embed pending))).run (clean (clean native.2)))
            (SkelSpec Output)) := by
      simp only [groupStep, marker, nonzero, ↓reduceIte, StateT.run]
      rfl
    rw [left, right, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    have read : (publicLocalV Output (Sum.inr (Sum.inl (message pending.root.dh1 pending.root.dh2 pending.root.dh3
        pending.root.dh4)))).run cache = (fun reply => (reply, cache)) <$> ((EntrySpec Output).query
          (.inr (message pending.root.dh1 pending.root.dh2 pending.root.dh3 pending.root.dh4)) :
            OracleComp (EntrySpec Output) _) := rfl
    rw [read]
    simp only [bind_map_left, map_bind, simulateQ_map, StateT.run_map, publicLocal_coins, Functor.map_map]
    refine bind_congr fun value => ?_
    simp only [PqxdhServerAuthNative.nativeCtx, PqxdhRegistrationJointKemPostSkeleton.ctxGame, StateT.run,
      OracleComp.liftComp_map, Functor.map_map, bind_pure_comp, map_pure]
    rfl
  · simp only [nonzero, ↓reduceIte]
    have left : (groupCE setup codec (factoredHidden setup codec checks) pending).run (native, recorded) =
        pure (none, (native, recorded)) := by
      simp only [groupCE, StateT.run, marker, nonzero, ↓reduceIte]
    have right : (groupStep setup codec (factoredServices setup codec checks) pending).run (clean native.2, marks) =
        pure (none, (clean native.2, marks)) := by
      simp only [groupStep, nonzero, ↓reduceIte]
      rfl
    rw [left, right, simulateQ_pure, StateT.run_pure, map_pure, map_pure]

/-- The grouped finish with a known decapsulation result: the CE-native answer is item 2's native grouped answer `PqxdhRegistrationJointKemPostSkeleton.groupNativeN` (whose split against `groupStep` is item 2's `split_group`), lifted, with the recorded coordinates unchanged. -/
theorem groupCE_known (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (hidden : Output → Hidden Response) (pending : Pending Response) (secret : PqxdhKemIndCca.MlKemSharedSecret)
    (marker : pending.root.shared = .known secret) (native : NativeState KemSK) (recorded : Option Coord) :
    (groupCE setup codec hidden pending).run (native, recorded) =
      (fun r => (r.1, (r.2, recorded))) <$> liftS ((PqxdhRegistrationJointKemPostSkeleton.groupNativeN setup codec
        (List.Vector.replicate 32 0) pending).run native) := by
  simp only [groupCE, StateT.run, marker]
  rfl

end Skeleton

/-! ### The ideal registration -/

/-- Whether the owner at an index is in the `initSent` phase (it has sent Phase 1 and waits for Phase 2). -/
def initSentAt {KemSK : Type} (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ) : Bool :=
  match owners[index]? with
  | some owner => match owner.beacon.phase with
      | .initSent _ _ _ _ => true
      | _ => false
  | none => false

/-- Whether the owner at an index is established. -/
def establishedAt {KemSK : Type} (owners : List (PqxdhRegistrationSchedule.Owner KemSK)) (index : ℕ) : Bool :=
  match owners[index]? with
  | some owner => match owner.beacon.phase with
      | .established _ _ _ => true
      | _ => false
  | none => false

section Ideal
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ}

/-- The raw accept of the ideal registration: the pre-increment accept counter is the accept's ordinal; the selected ordinal runs `acceptExposed` (the ideal backend records whether it was active and its mark), every other ordinal the real accept. -/
noncomputable def acceptStep (t : Target count) (p : Params KemSK count) (created : Created Unit) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option ℕ) := fun x =>
  let counted : XState KemSK IdealCore 2 := { x with backend := { x.backend with accepts := x.backend.accepts + 1 } }
  if x.backend.accepts = t.accept then
    (fun r => (r.1.1.1, { counted with
        base := { counted.base with native := { counted.base.native with shared := r.2 } }
        log := counted.log ++ [r.1.1.2]
        backend := { counted.backend with active := r.1.2.1, marks := r.1.2.2 } })) <$>
      (acceptExposed setup codec checks created.seed p.chosen p.challenge raw).run x.base.native.shared
  else onSlots (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩) counted

/-- The build of the ideal registration: the marked session with a pending token reads its hidden value (an allocator hit at its coordinates) and runs `buildHidden`; a published peer sets the Server install ghost. Every other build is the real build. -/
noncomputable def buildStep (hidden : Output → Hidden Response) (created : Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option PqxdhServerRegistrationPublication.Response) :=
  fun x =>
    match x.backend.marks with
    | some (index, coords) =>
        if index = session ∧ (x.base.native.shared.2.pending session).isSome then do
          let value ← (SlotSpec.query (.inr coords) : OracleComp SlotSpec _)
          let r ← liftS ((buildHidden (KemSK := KemSK) (hidden value) session payload).run x.base.native.shared)
          pure (r.1, { x with
            base := { x.base with native := { x.base.native with shared := r.2 } }
            backend := { x.backend with
              peer := ((publishedKey r.1 r.2.2.server).map fun keyId => (keyId, coords)).or x.backend.peer } })
        else onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) x
    | none => onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩) x

/-- The finish of the ideal registration: after an active selected accept, a finish of the selected owner in the `initSent` phase takes the LQ-F snapshot and runs `finishChallenge`; when it establishes the owner after a hidden read, the Beacon install ghost records the coordinates. Every other finish is the real finish. -/
noncomputable def finishStep (t : Target count) (p : Params KemSK count) (hidden : Output → Hidden Response)
    (created : Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) :
    StateT (XState KemSK IdealCore 2) (OracleComp SlotSpec) (Option Pqxdh.Bytes) := fun x =>
  if x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true then do
    let r ← (finishChallenge setup codec hidden p.challenge owner raw).run (x.base.native, none)
    pure (r.1, { x with
      base := { x.base with native := r.2.1 }
      snap := PqxdhDeploymentLater.snapshotAt x.snap x.base.native.owners (some owner)
      backend := { x.backend with
        beacon := if establishedAt r.2.1.owners owner then r.2.2.or x.backend.beacon else x.backend.beacon } })
  else onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩) x

/-- The ideal registration as a slot program (design-v2 section 3.2): create reads the pool, bundle and HMAC are real, the selected raw accept, the marked build and the selected owner's challenge finish are the CE-native hidden steps, with the hidden services `hidden`. -/
noncomputable def idealProg (t : Target count) (p : Params KemSK count) (hidden : Output → Hidden Response)
    (created : Created Unit) : SlotProgram KemSK IdealCore 2
  | ⟨.create pin keyId, _⟩ => onSlots (createReg setup (p.pool t) pin keyId)
  | ⟨.bundle owner, _⟩ => onSlots (realRegAt setup codec route checks created ⟨.bundle owner, trivial⟩)
  | ⟨.accept raw, _⟩ => acceptStep setup codec route checks t p created raw
  | ⟨.build session payload, _⟩ => buildStep setup codec route checks hidden created session payload
  | ⟨.finish owner raw, _⟩ => finishStep setup codec route checks t p hidden created owner raw
  | ⟨.hmac key message, _⟩ => onSlots (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩)
  | ⟨.hash _, notEnv⟩ => absurd notEnv id
  | ⟨.serverSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.serverRaw _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconSend _ _, notEnv⟩ => absurd notEnv id
  | ⟨.beaconRaw _ _, notEnv⟩ => absurd notEnv id

/-- Every raw accept other than the selected ordinal is the real accept, with the accept counter advanced. -/
theorem acceptStep_other (t : Target count) (p : Params KemSK count) (created : Created Unit) (raw : Pqxdh.Bytes)
    (x : XState KemSK IdealCore 2) (other : x.backend.accepts ≠ t.accept) :
    (acceptStep setup codec route checks t p created raw).run x =
      (onSlots (realRegAt setup codec route checks created ⟨.accept raw, trivial⟩)).run
        { x with backend := { x.backend with accepts := x.backend.accepts + 1 } } := by
  change (if x.backend.accepts = t.accept then _ else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false other)]
  rfl

/-- Every raw accept advances the accept counter by one. -/
theorem acceptStep_accepts (t : Target count) (p : Params KemSK count) (created : Created Unit) (raw : Pqxdh.Bytes)
    (x : XState KemSK IdealCore 2) :
    ∀ result ∈ support ((acceptStep setup codec route checks t p created raw).run x),
      result.2.backend.accepts = x.backend.accepts + 1 := by
  intro result member
  change result ∈ support (if x.backend.accepts = t.accept then _ else _) at member
  split at member
  · rw [support_map] at member
    obtain ⟨inner, -, rfl⟩ := member
    rfl
  · change result ∈ support (liftS _) at member
    rw [support_liftComp] at member
    simp only [realRegAt, StateT.run, support_map, Set.mem_image] at member
    obtain ⟨inner, -, rfl⟩ := member
    rfl

/-- While no session is marked, every build is the real build. -/
theorem buildStep_unmarked (hidden : Output → Hidden Response) (created : Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (x : XState KemSK IdealCore 2) (unmarked : x.backend.marks = none) :
    (buildStep setup codec route checks hidden created session payload).run x =
      (onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)).run x := by
  change (match x.backend.marks with
    | some (index, coords) => _
    | none => _) = _
  rw [unmarked]
  rfl

/-- While a session is marked, a build is the real build unless it addresses the marked session and that session still has a pending token: builds of every other session, and builds of the marked session after its token is consumed. -/
theorem buildStep_other (hidden : Output → Hidden Response) (created : Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (x : XState KemSK IdealCore 2) (index : ℕ) (coords : Coord)
    (marked : x.backend.marks = some (index, coords))
    (other : ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome)) :
    (buildStep setup codec route checks hidden created session payload).run x =
      (onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)).run x := by
  change (match x.backend.marks with
    | some (index, coords) => _
    | none => _) = _
  rw [marked]
  exact ite_eq_right_of_eq_false _ _ (eq_false other)

/-- Every build is the real build except the build of the marked session while it has a pending token (`buildStep_unmarked` and `buildStep_other`). -/
theorem buildStep_real (hidden : Output → Hidden Response) (created : Created Unit) (session : ℕ)
    (payload : Option Pqxdh.Bytes) (x : XState KemSK IdealCore 2)
    (real : ∀ index coords, x.backend.marks = some (index, coords) →
      ¬ (index = session ∧ (x.base.native.shared.2.pending session).isSome)) :
    (buildStep setup codec route checks hidden created session payload).run x =
      (onSlots (realRegAt setup codec route checks created ⟨.build session payload, trivial⟩)).run x := by
  rcases marked : x.backend.marks with _ | ⟨index, coords⟩
  · exact buildStep_unmarked setup codec route checks hidden created session payload x marked
  · exact buildStep_other setup codec route checks hidden created session payload x index coords marked
      (real index coords marked)

/-- A finish is the real finish unless the selected accept was active, the finish addresses the selected owner and that owner is in the `initSent` phase. -/
theorem finishStep_real (t : Target count) (p : Params KemSK count) (hidden : Output → Hidden Response)
    (created : Created Unit) (owner : ℕ) (raw : Pqxdh.Bytes) (x : XState KemSK IdealCore 2)
    (real : ¬ (x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true)) :
    (finishStep setup codec route checks t p hidden created owner raw).run x =
      (onSlots (realRegAt setup codec route checks created ⟨.finish owner raw, trivial⟩)).run x := by
  change (if x.backend.active = true ∧ owner = t.kem.val ∧ initSentAt x.base.native.owners owner = true then _
    else _) = _
  rw [ite_eq_right_of_eq_false _ _ (eq_false real)]
  rfl

/-- Bundle and HMAC are the real commands, and create is the native create command with the pool create. -/
theorem idealProg_real (t : Target count) (p : Params KemSK count) (hidden : Output → Hidden Response)
    (created : Created Unit) :
    (∀ owner, idealProg setup codec route checks t p hidden created ⟨.bundle owner, trivial⟩ =
      onSlots (realRegAt setup codec route checks created ⟨.bundle owner, trivial⟩)) ∧
    (∀ key message, idealProg setup codec route checks t p hidden created ⟨.hmac key message, trivial⟩ =
      onSlots (realRegAt setup codec route checks created ⟨.hmac key message, trivial⟩)) ∧
    (∀ pin keyId, idealProg setup codec route checks t p hidden created ⟨.create pin keyId, trivial⟩ =
      onSlots (createReg setup (p.pool t) pin keyId)) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The ideal registration core over any slot service, with the factored hidden services. -/
noncomputable def idealCore (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : Created Unit) : RegImpl KemSK (IdealBk S) 2 :=
  slotCore (idealProg setup codec route checks t p (factoredHidden setup codec checks)) svc created

/-- The ideal registration: the ideal core over item 2's persistent lazy table. -/
noncomputable def idealReg (t : Target count) (p : Params KemSK count) :
    Created Unit → RegImpl KemSK (IdealBk TableState) 2 :=
  idealCore setup codec route checks t p PqxdhDeploymentSeedSplit.tableService

/-- The erased hidden services (C7): the factored build, and the erased finish at the split of the value into material and seed. -/
noncomputable def erasedHidden (value : Output) : Hidden Response where
  hiddenBuild := (factoredHidden setup codec checks value).hiddenBuild
  hiddenAfter := PqxdhDeploymentHiddenEntry.finishErasedSvc setup codec
    (PqxdhDeploymentHiddenLayout.splitOutput value).1 (PqxdhDeploymentHiddenLayout.splitOutput value).2

/-- The C7-erased ideal registration core over any slot service. -/
noncomputable def idealCoreErased (t : Target count) (p : Params KemSK count) {S : Type}
    (svc : PqxdhDeploymentSeedSplit.SlotService S 2) (created : Created Unit) : RegImpl KemSK (IdealBk S) 2 :=
  slotCore (idealProg setup codec route checks t p (erasedHidden setup codec checks)) svc created

/-- The ideal registration core is natural (`PqxdhDeploymentSeedSplit.CoreNatural`), the premise of `represent_split`. -/
theorem idealCore_natural (t : Target count) (p : Params KemSK count) :
    PqxdhDeploymentSeedSplit.CoreNatural (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore)
      (fun {S} svc created => idealCore setup codec route checks t p (S := S) svc created) :=
  PqxdhDeploymentIdealSlots.slotCore_natural _

/-- The C7-erased ideal registration core is natural. -/
theorem idealCoreErased_natural (t : Target count) (p : Params KemSK count) :
    PqxdhDeploymentSeedSplit.CoreNatural (KemSK := KemSK) (Γ := Alloc Coord 2 × IdealCore)
      (fun {S} svc created => idealCoreErased setup codec route checks t p (S := S) svc created) :=
  PqxdhDeploymentIdealSlots.slotCore_natural _

section Game
variable {A X : Type}
open PqxdhDeploymentInterface (Budget FreshBounds Mode ModeSpec)

/-- `CE.idealGame g` (design-v2 section 3.2): the challenger's draws for the budget's KEM creations, then the common deployment experiment with the ideal registration at the target of `g`, from the initial ideal backend, with identity index 0. -/
noncomputable def idealGame (budget : Budget) (g : Fin budget.accept × Fin budget.capacity)
    (ensureInit : StateT A ProbComp Bool) (bounds : FreshBounds) (mode : Mode)
    (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      PqxdhDeploymentSecrecy.Ledger × XState KemSK (IdealBk TableState) 2)) := fun runtime => do
  let p ← drawParams setup budget.create
  (gameWith setup codec route idealInit (idealReg setup codec route checks (Target.ofCE budget g) p) ensureInit 0
    bounds mode adversary).run runtime

end Game

end Ideal

end BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.realRegAt_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.realRegAt_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.createPool_beyond' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.createPool_beyond

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptExposed_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptExposed_logged

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildHidden_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildHidden_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.preparationCE_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.preparationCE_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.preparationCE_eval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.preparationCE_eval

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.publicLocal_coins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.publicLocal_coins

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.tailCE_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.tailCE_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.groupCE_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.groupCE_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.groupCE_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.groupCE_known

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptStep_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptStep_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptStep_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.acceptStep_accepts

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_unmarked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_unmarked

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_other

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.buildStep_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.finishStep_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.finishStep_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealProg_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealProg_real

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealCore_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealCore_natural

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealCoreErased_natural' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSteps.idealCoreErased_natural
