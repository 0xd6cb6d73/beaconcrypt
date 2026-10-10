-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCollision

/-!
# The ghost of the ciphertext-collision game (CE-12 P2b, design-v2 section 7.4)

The first half of design-v2's `ct_collision_game`: a ghost-instrumented copy of the common deployment experiment, and the bound on the ghost collision of one triple of an owner and two raw accept attempts.

- Logged collector. `collectEnc` (with `collectVerifiedEnc`) is the Server's Phase 1 collector `PqxdhServerRootPreparation.collect`, split at its encapsulation callback by `PqxdhRegistrationJointKemCollected.collect_split`, which also returns the encapsulation it reached: the PQ key of the verified candidate and the ciphertext array of the callback's reply (`Enc`). Forgetting the log gives the collector back (`collectEnc_fst`), so the logged native prefix `prefixEnc` and the logged native raw accept `acceptEnc` forget to `PqxdhServerAuthNative.nativePrefix` and `nativeAccept` (`prefixEnc_fst`, `acceptEnc_fst`, through `PqxdhRegistrationJointServerAccept.native_run`).
- Ghost. `Ghost` holds the KEM public keys of the created owners in creation order and one entry per raw accept attempt, in attempt order, with the encapsulation it reached, if any. `handlerG` is the CE handler with the ghost: a raw accept runs `acceptEnc` and appends its entry, a create appends the new owner's KEM public key (`createdKey`, read from the state after the create), and every query is answered as `PqxdhDeploymentSecrecy.handler` answers it (`handlerG_proj`). `gameG` is the experiment with `handlerG`; forgetting the ghost gives `PqxdhDeploymentSecrecy.game` (`game_ghost`, by `OracleComp.map_run_simulateQ_eq_of_query_map_eq`). No reply and no state other than the ghost depends on it.
- Fresh draws. The ciphertext a raw accept logs is a fresh draw `encC setup key` of an encapsulation to the verified key, made after every step that decides that key (`prefixEnc_expect`, `acceptEnc_expect`), and the key a create logs is a fresh draw `keyGen setup` (`create_run`, `create_expect`). Hence a potential of the ghost whose expectation does not increase over these two draws (and when an attempt reaches no encapsulation) does not increase over any query (`handlerG_expect`), nor over a whole simulation (`expected_run_le`, generic, with VCVio's `expectedValue`).
- One triple. For an owner index `k` and raw accept attempts `i < j`, the potential `phi` reads owner `k`'s key and the two attempts' encapsulations (`view`): with nothing drawn it is `pairCollision setup` (`PqxdhDeploymentHeadlineCollision`, the probability that two independent encapsulations to a fresh key collide; `pairHit_mean`), with only the key `CP(pk_k)` (`pairHit`), with only attempt `i` reached to `(pk, c)` the key's mass times `c`'s mass (`keyMass`, `hit`), with the key and attempt `i` the mass of `c` if `i` went to `pk_k`, with both attempts but no key the key's mass if `j` repeated `i`, and with all three the indicator of the collision (`GhostColl`). It does not increase in expectation over a key generation (`phi_key`), a fresh encapsulation (`phi_enc`) or an attempt without encapsulation (`phi_none`), starts at `pairCollision setup` (`phi_empty`) and is at least 1 on the collision (`phi_coll`). `triple_le`: in the instrumented experiment, the probability that owner `k`'s key exists and attempts `i` and `j` encapsulated to it with one ciphertext (`TripleColl`) is at most `pairCollision setup`.

The adversary's adaptivity costs nothing: the key of each attempt and the order of the draws are fixed before each draw, and the potential averages only over the draw itself (design-v2 section 7.4: the hit set is fixed before the draw). These are program equalities and expectation bounds; no assumption and no contract is used. The transcript event `CtCollEvent` and the union bound are in `PqxdhDeploymentHeadlineCtTrace` and `PqxdhDeploymentHeadlineCtColl`.
-/

open OracleComp OracleSpec ENNReal

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhServerRootPreparation (Inputs Verified verifyInput collectVerified collect)
open PqxdhBeaconPhase2Preparation (Ciphertext Word32)
open OracleComp.EvalDist (expectedValue)

/-- One reached encapsulation of a raw accept: the PQ key encapsulated to and the ciphertext array. -/
abbrev Enc := PqxdhKemIndCca.MlKem768PublicKey × Ciphertext

section Collector
variable {Reader E Shared : Type}

/-- The verified part of the collector with its encapsulation logged. -/
def collectVerifiedEnc (verified : Verified Reader) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Inputs Reader E Shared) × Option Enc) := do
  let ephemeral ← PqxdhRegistrationJointKemCollected.beforeEncapsulation verified
  match ephemeral with
  | none => pure (none, none)
  | some ephemeral => do
      let reply ← (PqxdhServerRootPreparation.Spec Reader E Shared).query (.encapsulate verified.keys.pqKey)
      let input ← PqxdhRegistrationJointKemCollected.afterEncapsulation verified ephemeral reply
      pure (input, reply.map fun pair => (verified.keys.pqKey, pair.1))

/-- The collector with its encapsulation logged. -/
def collectEnc (raw : Pqxdh.Bytes) :
    OracleComp (PqxdhServerRootPreparation.Spec Reader E Shared) (Option (Inputs Reader E Shared) × Option Enc) := do
  let verified ← verifyInput raw
  match verified with
  | none => pure (none, none)
  | some verified => collectVerifiedEnc verified

/-- Forgetting the log of the verified part gives the verified collector. -/
theorem collectVerifiedEnc_fst (verified : Verified Reader) :
    Prod.fst <$> collectVerifiedEnc (E := E) (Shared := Shared) verified = collectVerified verified := by
  rw [PqxdhRegistrationJointKemCollected.collect_split]
  simp only [collectVerifiedEnc, map_bind]
  refine bind_congr fun ephemeral => ?_
  cases ephemeral with
  | none => simp
  | some ephemeral => simp [map_bind]

/-- Forgetting the log gives the collector. -/
theorem collectEnc_fst (raw : Pqxdh.Bytes) :
    Prod.fst <$> collectEnc (Reader := Reader) (E := E) (Shared := Shared) raw = collect raw := by
  simp only [collectEnc, collect, map_bind]
  refine bind_congr fun verified => ?_
  cases verified with
  | none => simp
  | some verified => exact collectVerifiedEnc_fst verified

end Collector

section Native
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhServerAuthNative (NativeState nativePrefix nativeAccept)

/-- The native prefix with its encapsulation logged. -/
noncomputable def prefixEnc (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) :
    StateT (List Pqxdh.Bytes) ProbComp (Option (Inputs Reader PqxdhJointGapDh.ScalarBytes Word32) × Option Enc) :=
  simulateQ (PqxdhServerStaticDhSource.nativeImpl setup.joint seed (PqxdhServerAuthExperiment.serverAux setup codec checks)
    (fun _ => pure ())) (collectEnc raw)

/-- Forgetting the log of the logged native prefix gives the native prefix. -/
theorem prefixEnc_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes) :
    (fun result => (result.1.1, result.2)) <$> (prefixEnc setup codec checks seed raw).run consumed =
      (nativePrefix setup codec checks seed raw).run consumed := by
  rw [nativePrefix, ← collectEnc_fst, simulateQ_map, StateT.run_map, prefixEnc]

/-- The native raw accept with its encapsulation logged. -/
noncomputable def acceptEnc (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    ProbComp ((Option Nat × Option Enc) × NativeState KemSK) := do
  let collected ← (prefixEnc setup codec checks seed raw).run shared.2.server.consumed
  let answer ← (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) shared.2
    (collected.1.1, collected.2)).run shared
  pure ((answer.1, collected.1.2), answer.2)

/-- Forgetting the log of the logged native accept gives the native raw accept with its complete shared state. -/
theorem acceptEnc_fst (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK) :
    (fun result => (result.1.1, result.2)) <$> acceptEnc setup codec checks seed raw shared =
      (nativeAccept setup codec checks seed PqxdhRegistrationSchedule.observationScalar raw).run shared := by
  rw [PqxdhRegistrationJointServerAccept.native_run, ← prefixEnc_fst, bind_map_left]
  simp only [acceptEnc, map_bind, map_pure, Prod.mk.eta, bind_pure]

end Native

/-! ### Expected potentials along a simulation -/

section Potential
variable {ι' : Type} {spec : OracleSpec ι'} {σ α : Type}

/-- A potential whose expectation does not increase over any single query does not increase over a whole simulation. -/
theorem expected_run_le (impl : QueryImpl spec (StateT σ ProbComp)) (potential : σ → ℝ≥0∞)
    (step : ∀ query state, expectedValue ((impl query).run state) (fun result => potential result.2) ≤ potential state)
    (work : OracleComp spec α) (state : σ) :
    expectedValue ((simulateQ impl work).run state) (fun result => potential result.2) ≤ potential state := by
  induction work using OracleComp.inductionOn generalizing state with
  | pure value => simp
  | query_bind query next ih =>
      rw [simulateQ_query_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
      refine le_trans (OracleComp.EvalDist.expectedValue_mono ((impl query).run state) ?_) (step query state)
      intro result
      exact ih result.1 result.2

end Potential


/-! ### Expected values at the two fresh draws -/

section Draws
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}
open PqxdhServerAuthNative (NativeState)

/-- The ciphertext array of one encapsulation to `key` under the ambient interpreter of the setup. -/
noncomputable def encC (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) : ProbComp Ciphertext :=
  (fun result => PqxdhAcceptedRegistration.ciphertextArray result.1) <$>
    simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) (setup.kem.encaps key)

/-- The public key of one key generation under the ambient interpreter of the setup. -/
noncomputable def keyGen (setup : Setup baseSpec KemSK) : ProbComp PqxdhKemIndCca.MlKem768PublicKey :=
  Prod.fst <$> simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen

/-- The logged native prefix: the expected value of any function of its logged encapsulation is at most a bound that dominates the function at `none` and its expectation over one fresh encapsulation to every key. -/
theorem prefixEnc_expect (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (value : Option Enc → ℝ≥0∞) (bound : ℝ≥0∞) (noneLe : value none ≤ bound)
    (someLe : ∀ key, expectedValue (encC setup key) (fun c => value (some (key, c))) ≤ bound) :
    expectedValue ((prefixEnc setup codec checks seed raw).run consumed) (fun result => value result.1.2) ≤ bound := by
  unfold prefixEnc collectEnc
  rw [simulateQ_bind, StateT.run_bind, PqxdhRegistrationJointRawSignatures.verifyInput_source, pure_bind]
  cases PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with
  | none => simpa using noneLe
  | some verified =>
      dsimp only
      unfold collectVerifiedEnc
      rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
      refine OracleComp.EvalDist.expectedValue_le_of_le _ fun prepared => ?_
      rcases prepared with ⟨_ | ephemeral, after⟩
      · simpa using noneLe
      · dsimp only
        rw [simulateQ_bind, StateT.run_bind, simulateQ_spec_query]
        simp only [PqxdhServerStaticDhSource.nativeImpl, PqxdhServerAuthExperiment.serverAux, StateT.run_lift,
          PqxdhServerAuthExperiment.encapsulate, simulateQ_map, bind_assoc, pure_bind,
          OracleComp.EvalDist.expectedValue_bind, OracleComp.EvalDist.expectedValue_map]
        refine le_trans ?_ (someLe verified.keys.pqKey)
        unfold encC
        rw [OracleComp.EvalDist.expectedValue_map]
        refine OracleComp.EvalDist.expectedValue_mono _ fun result => ?_
        rw [simulateQ_bind, StateT.run_bind, OracleComp.EvalDist.expectedValue_bind]
        refine OracleComp.EvalDist.expectedValue_le_of_le _ fun finished => ?_
        simp

/-- The logged native accept: the same bound for the logged encapsulation of the whole accept. -/
theorem acceptEnc_expect (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (seed : PqxdhJointIdentity.IdentitySeed) (raw : Pqxdh.Bytes) (shared : NativeState KemSK)
    (value : Option Enc → ℝ≥0∞) (bound : ℝ≥0∞) (noneLe : value none ≤ bound)
    (someLe : ∀ key, expectedValue (encC setup key) (fun c => value (some (key, c))) ≤ bound) :
    expectedValue (acceptEnc setup codec checks seed raw shared) (fun result => value result.1.2) ≤ bound := by
  unfold acceptEnc
  rw [OracleComp.EvalDist.expectedValue_bind]
  refine le_trans (OracleComp.EvalDist.expectedValue_mono _ fun collected => ?_)
    (prefixEnc_expect setup codec checks seed raw shared.2.server.consumed value bound noneLe someLe)
  rw [OracleComp.EvalDist.expectedValue_bind]
  refine OracleComp.EvalDist.expectedValue_le_of_le _ fun answer => ?_
  simp

end Draws

/-! ### The ghost-instrumented experiment -/

section Handler
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhDeploymentInterface (FullSpec FreshBounds Mode ModeSpec asModeO)
open PqxdhDeploymentSecrecy (Ledger)
open PqxdhServerAuthNative (nativeAccept)

/-- The ghost of the analysis: the KEM public keys of the created owners in creation order, and one entry per raw accept attempt in attempt order with the encapsulation it reached, if any. No reply and no other state depends on it. -/
structure Ghost where
  keys : List PqxdhKemIndCca.MlKem768PublicKey
  encs : List (Option Enc)

/-- The empty ghost. -/
def Ghost.empty : Ghost := ⟨[], []⟩

/-- The KEM public key of the owner that a create reply names, read from the state after the create. -/
def createdKey (reply : Option Nat) (state : PqxdhDeploymentSecrecy.State KemSK) :
    Option PqxdhKemIndCca.MlKem768PublicKey :=
  reply.bind fun index => (state.2.native.owners[index]?).bind fun owner =>
    PqxdhDeploymentEligibility.kemPublic owner.beacon.phase

/-- The CE handler's raw accept is the native raw accept on the shared native state, recorded in the ledger. -/
theorem handler_accept (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (raw : Pqxdh.Bytes) (ledger : Ledger) (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds (.inl (.inr (.accept raw)))).run
        (ledger, state) =
      (fun result => (result.1, (ledger.record (.inl (.inr (.accept raw))) result.1,
        { state with native := { state.native with shared := result.2 } }))) <$>
        (nativeAccept setup codec checks serverSeed PqxdhRegistrationSchedule.observationScalar raw).run
          state.native.shared := by
  rw [PqxdhDeploymentEligibility.handler_run, PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, Functor.map_map]
  simp only [PqxdhDeploymentNative.handler, PqxdhDeploymentCompileStep.onNative_run, PqxdhRegistrationSchedule.handler,
    PqxdhRegistrationSchedule.onShared_run, Functor.map_map]
  rfl

/-- The ghost-instrumented CE handler: a raw accept runs the logged native accept and appends its logged encapsulation; a create appends the new owner's KEM public key; every query is answered as the CE handler answers it. -/
noncomputable def handlerG (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds) :
    QueryImpl FullSpec (StateT (PqxdhDeploymentSecrecy.State KemSK × Ghost) ProbComp)
  | .inl (.inr (.accept raw)) => fun state =>
      (fun result => (result.1.1, ((state.1.1.record (.inl (.inr (.accept raw))) result.1.1,
        { state.1.2 with native := { state.1.2.native with shared := result.2 } }),
        { state.2 with encs := state.2.encs ++ [result.1.2] }))) <$>
        acceptEnc setup codec checks serverSeed raw state.1.2.native.shared
  | .inl (.inr (.create pin keyId)) => fun state =>
      (fun result => (result.1, (result.2,
        { state.2 with keys := state.2.keys ++ (createdKey result.1 result.2).toList }))) <$>
        (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds (.inl (.inr (.create pin keyId)))).run
          state.1
  | query => fun state => (fun result => (result.1, (result.2, state.2))) <$>
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run state.1

/-- Forgetting a ghost attached to every result of a computation gives the computation back. -/
theorem map_ghost {α σ : Type} (work : ProbComp (α × σ)) (ghost : α × σ → Ghost) :
    Prod.map id Prod.fst <$> ((fun result => (result.1, (result.2, ghost result))) <$> work) = work := by
  rw [Functor.map_map]
  simp

/-- Forgetting the ghost of one step of the instrumented handler gives the CE handler's step. -/
theorem handlerG_proj (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (query : PqxdhDeploymentInterface.Query) (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) :
    Prod.map id Prod.fst <$> (handlerG setup codec checks route serverSeed bounds query).run state =
      (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds query).run state.1 := by
  rcases state with ⟨⟨ledger, native⟩, ghost⟩
  rcases query with (coin | command) | secrecy
  · exact map_ghost _ fun _ => ghost
  · cases command with
    | accept raw =>
        rw [handler_accept, ← acceptEnc_fst]
        simp only [handlerG, StateT.run, Functor.map_map]
        rfl
    | create pin keyId => exact map_ghost _ _
    | bundle => exact map_ghost _ fun _ => ghost
    | build => exact map_ghost _ fun _ => ghost
    | finish => exact map_ghost _ fun _ => ghost
    | hmac => exact map_ghost _ fun _ => ghost
    | hash => exact map_ghost _ fun _ => ghost
    | serverSend => exact map_ghost _ fun _ => ghost
    | serverRaw => exact map_ghost _ fun _ => ghost
    | beaconSend => exact map_ghost _ fun _ => ghost
    | beaconRaw => exact map_ghost _ fun _ => ghost
  · exact map_ghost _ fun _ => ghost

end Handler


/-! ### The create step and the potential over the instrumented run -/

section Steps
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhDeploymentInterface (FullSpec FreshBounds Mode ModeSpec asModeO parsePin)
open PqxdhDeploymentSecrecy (Ledger)

/-- The native create draws the identity seed, the prekey and the KEM key pair in production order and appends the owner. -/
theorem create_run (setup : Setup baseSpec KemSK) (pin : Word32) (keyId : Aeneas.Std.U64)
    (native : PqxdhRegistrationSchedule.State KemSK) :
    (PqxdhRegistrationSchedule.create setup pin keyId).run native = (do
      let identity ← PqxdhJointIdentity.sampleSeed
      let prekey ← PqxdhJointGapDh.sampleScalar
      let keys ← simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl) setup.kem.keygen
      pure (native.owners.length, { native with
        owners := native.owners ++ [⟨⟨identity, keyId, pin, .fresh ⟨⟨pin, keyId⟩⟩ prekey keys⟩, 0⟩] })) := by
  simp only [PqxdhRegistrationSchedule.create, StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set,
    StateT.run_pure, bind_assoc, pure_bind]

/-- The CE create: the expected value of any function of the created owner's KEM public key is at most a bound that dominates the function at `none` and its expectation over one key generation. -/
theorem create_expect (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (pin : Pqxdh.Bytes) (keyId : Aeneas.Std.U64) (state : PqxdhDeploymentSecrecy.State KemSK)
    (value : Option PqxdhKemIndCca.MlKem768PublicKey → ℝ≥0∞) (bound : ℝ≥0∞) (noneLe : value none ≤ bound)
    (someLe : expectedValue (keyGen setup) (fun key => value (some key)) ≤ bound) :
    expectedValue ((PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds
      (.inl (.inr (.create pin keyId)))).run state) (fun result => value (createdKey result.1 result.2)) ≤ bound := by
  rcases state with ⟨ledger, native⟩
  rw [PqxdhDeploymentEligibility.handler_run, PqxdhDeploymentSecrecy.ledgerImpl_forward, simulateQ_map,
    simulateQ_spec_query, StateT.run_map, Functor.map_map, OracleComp.EvalDist.expectedValue_map]
  simp only [PqxdhDeploymentNative.handler]
  cases parsePin pin with
  | none => simpa [createdKey] using noneLe
  | some word =>
      simp only [StateT.run_map, OracleComp.EvalDist.expectedValue_map, PqxdhDeploymentCompileStep.onNative_run,
        PqxdhRegistrationSchedule.handler, create_run]
      simp only [OracleComp.EvalDist.expectedValue_bind, OracleComp.EvalDist.expectedValue_pure]
      refine OracleComp.EvalDist.expectedValue_le_of_le _ fun identity => ?_
      refine OracleComp.EvalDist.expectedValue_le_of_le _ fun prekey => ?_
      refine le_trans (le_of_eq ?_) someLe
      unfold keyGen
      rw [OracleComp.EvalDist.expectedValue_map]
      congr 1
      funext keys
      simp [createdKey, PqxdhDeploymentEligibility.kemPublic]

/-- Appending nothing to the key list keeps the ghost. -/
theorem ghost_keys_nil (ghost : Ghost) :
    { ghost with keys := ghost.keys ++ ([] : List PqxdhKemIndCca.MlKem768PublicKey) } = ghost := by
  cases ghost
  simp

/-- One step of the instrumented handler does not increase the expectation of a potential of the ghost whose expectation does not increase over one key generation appended to the keys, over one encapsulation appended to the encapsulations, nor when `none` is appended. -/
theorem handlerG_expect (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : PqxdhJointIdentity.IdentitySeed) (bounds : FreshBounds)
    (potential : Ghost → ℝ≥0∞)
    (keyStep : ∀ ghost, expectedValue (keyGen setup) (fun key => potential { ghost with keys := ghost.keys ++ [key] }) ≤
      potential ghost)
    (encStep : ∀ ghost key, expectedValue (encC setup key)
      (fun c => potential { ghost with encs := ghost.encs ++ [some (key, c)] }) ≤ potential ghost)
    (noneStep : ∀ ghost, potential { ghost with encs := ghost.encs ++ [none] } ≤ potential ghost)
    (query : PqxdhDeploymentInterface.Query) (state : PqxdhDeploymentSecrecy.State KemSK × Ghost) :
    expectedValue ((handlerG setup codec checks route serverSeed bounds query).run state)
      (fun result => potential result.2.2) ≤ potential state.2 := by
  have other : ∀ (work : ProbComp (FullSpec.Range query × PqxdhDeploymentSecrecy.State KemSK)),
      expectedValue ((fun result => (result.1, (result.2, state.2))) <$> work) (fun result => potential result.2.2) ≤
        potential state.2 := fun work => by
    rw [OracleComp.EvalDist.expectedValue_map]
    exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl
  rcases query with (coin | command) | secrecy
  · exact other _
  · cases command with
    | accept raw =>
        change expectedValue (_ <$> acceptEnc setup codec checks serverSeed raw state.1.2.native.shared) _ ≤ _
        rw [OracleComp.EvalDist.expectedValue_map]
        exact acceptEnc_expect setup codec checks serverSeed raw state.1.2.native.shared
          (fun entry => potential { state.2 with encs := state.2.encs ++ [entry] }) (potential state.2)
          (noneStep state.2) (encStep state.2)
    | create pin keyId =>
        change expectedValue (_ <$> (PqxdhDeploymentSecrecy.handler setup codec checks route serverSeed bounds
          (.inl (.inr (.create pin keyId)))).run state.1) _ ≤ _
        rw [OracleComp.EvalDist.expectedValue_map]
        refine create_expect setup codec checks route serverSeed bounds pin keyId state.1
          (fun key => potential { state.2 with keys := state.2.keys ++ key.toList }) (potential state.2) ?_ ?_
        · simp only [Option.toList_none]
          rw [ghost_keys_nil]
        · simpa using keyStep state.2
    | bundle => exact other _
    | build => exact other _
    | finish => exact other _
    | hmac => exact other _
    | hash => exact other _
    | serverSend => exact other _
    | serverRaw => exact other _
    | beaconSend => exact other _
    | beaconRaw => exact other _
  · exact other _

/-- The common deployment experiment with the ghost-instrumented handler. -/
noncomputable def gameG (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) :
    StateT A ProbComp (Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
      (PqxdhDeploymentSecrecy.State KemSK × Ghost))) := fun runtime => do
  let born ← (PqxdhLiveServerConstruction.construct setup.joint ensureInit identityIndex setup.serverKeyId none).run runtime
  match born.1 with
  | none => pure (none, born.2)
  | some created =>
    (fun result => (some (PqxdhRegistrationJointServerBirth.encode created, result), born.2)) <$>
      (simulateQ (handlerG setup codec checks route created.seed bounds) (asModeO mode adversary)).run
        ((Ledger.empty, PqxdhDeploymentNative.initial created), Ghost.empty)

/-- Forget the ghost of an outcome of the instrumented experiment. -/
def forget (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    (PqxdhDeploymentSecrecy.State KemSK × Ghost)) × A) :
    Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X × PqxdhDeploymentSecrecy.State KemSK) × A :=
  (outcome.1.map fun result => (result.1, result.2.1, result.2.2.1), outcome.2)

/-- Forgetting the ghost of the instrumented experiment gives the common deployment experiment. -/
theorem game_ghost (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) :
    (PqxdhDeploymentSecrecy.game setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime =
      forget <$> (gameG setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime := by
  simp only [PqxdhDeploymentSecrecy.game, gameG, StateT.run, map_bind]
  refine bind_congr fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp [forget]
  · dsimp only
    have proj : Prod.map id Prod.fst <$> simulateQ (handlerG setup codec checks route created.seed bounds)
        (asModeO mode adversary) ((Ledger.empty, PqxdhDeploymentNative.initial created), Ghost.empty) =
        simulateQ (PqxdhDeploymentSecrecy.handler setup codec checks route created.seed bounds) (asModeO mode adversary)
          (Ledger.empty, PqxdhDeploymentNative.initial created) :=
      OracleComp.map_run_simulateQ_eq_of_query_map_eq (handlerG setup codec checks route created.seed bounds)
        (PqxdhDeploymentSecrecy.handler setup codec checks route created.seed bounds) Prod.fst
        (fun query state => handlerG_proj setup codec checks route created.seed bounds query state)
        (asModeO mode adversary) ((Ledger.empty, PqxdhDeploymentNative.initial created), Ghost.empty)
    rw [← proj, Functor.map_map, Functor.map_map]
    rfl

end Steps


/-! ### The ciphertext-collision potential of one triple -/

section Pair
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The indicator of one value with a weight. -/
noncomputable def pointFn {α : Type} (point : α) (value : ℝ≥0∞) : α → ℝ≥0∞ :=
  Set.indicator {point} fun _ => value

/-- The weighted indicator at its point. -/
theorem pointFn_self {α : Type} (point : α) (value : ℝ≥0∞) : pointFn point value point = value :=
  Set.indicator_of_mem (Set.mem_singleton point) _

/-- The weighted indicator away from its point. -/
theorem pointFn_ne {α : Type} (point x : α) (value : ℝ≥0∞) (other : x ≠ point) : pointFn point value x = 0 :=
  Set.indicator_of_notMem (by simpa using other) _

/-- The probability that a computation returns `point`, as the expectation of its indicator. -/
noncomputable def mass {α : Type} (work : ProbComp α) (point : α) : ℝ≥0∞ :=
  expectedValue work (pointFn point 1)

/-- `D_pk(c)`: the probability that one encapsulation to `key` gives the ciphertext array `c`. -/
noncomputable def hit (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) (c : Ciphertext) : ℝ≥0∞ :=
  mass (encC setup key) c

/-- `CP(pk)`: the probability that two independent encapsulations to `key` give equal ciphertexts. -/
noncomputable def pairHit (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) : ℝ≥0∞ :=
  expectedValue (encC setup key) (hit setup key)

/-- `KG(pk)`: the probability that one key generation gives the public key `key`. -/
noncomputable def keyMass (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) : ℝ≥0∞ :=
  mass (keyGen setup) key

/-- The ciphertext array of an ML-KEM ciphertext determines it. -/
theorem ciphertextArray_injective : Function.Injective PqxdhAcceptedRegistration.ciphertextArray := by
  intro first second same
  have bytes := congrArg PqxdhRefinement.absBytes same
  rw [PqxdhAcceptedRegistration.ciphertextArray_bytes, PqxdhAcceptedRegistration.ciphertextArray_bytes] at bytes
  exact List.Vector.toList_injective bytes

/-- A constant factor in front of the functional scales the expectation. -/
theorem expectedValue_const_mul {α : Type} (work : ProbComp α) (value : α → ℝ≥0∞) (factor : ℝ≥0∞) :
    expectedValue work (fun x => factor * value x) = factor * expectedValue work value := by
  simp only [OracleComp.EvalDist.expectedValue_def, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  ring

/-- The expectation of the zero functional. -/
theorem expectedValue_zero {α : Type} (work : ProbComp α) : expectedValue work (fun _ => (0 : ℝ≥0∞)) = 0 := by
  simp [OracleComp.EvalDist.expectedValue_def]

/-- Averaging the indicator of one value with a weight. -/
theorem expectedValue_point {α : Type} (work : ProbComp α) (point : α) (value : ℝ≥0∞) :
    expectedValue work (pointFn point value) = mass work point * value := by
  rw [mass, ← OracleComp.EvalDist.expectedValue_mul_const]
  congr 1
  funext x
  rcases Classical.em (x = point) with same | same
  · subst same
    rw [pointFn_self, pointFn_self, one_mul]
  · rw [pointFn_ne _ _ _ same, pointFn_ne _ _ _ same, zero_mul]

/-- A functional that is a weighted indicator of one value averages to the value's mass times the weight. -/
theorem point_le {α : Type} (work : ProbComp α) (f : α → ℝ≥0∞) (point : α) (value bound : ℝ≥0∞)
    (shape : ∀ x, f x = pointFn point value x) (le : mass work point * value ≤ bound) : expectedValue work f ≤ bound := by
  rw [show f = pointFn point value from funext shape, expectedValue_point]
  exact le

open Classical in
/-- `CP(pk)` as the probability that a second raw encapsulation equals a first one. -/
theorem pairHit_raw (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) :
    pairHit setup key = expectedValue (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
      (setup.kem.encaps key)) (fun first => expectedValue (simulateQ (PqxdhInitializerSecrecy.kemAmbientImpl setup.baseImpl)
        (setup.kem.encaps key)) (fun second => if second.1 = first.1 then 1 else 0)) := by
  unfold pairHit hit mass encC
  rw [OracleComp.EvalDist.expectedValue_map]
  congr 1
  funext first
  rw [OracleComp.EvalDist.expectedValue_map]
  congr 1
  funext second
  by_cases same : second.1 = first.1
  · simp [same, pointFn]
  · have different : PqxdhAcceptedRegistration.ciphertextArray second.1 ≠
        PqxdhAcceptedRegistration.ciphertextArray first.1 := fun equal => same (ciphertextArray_injective equal)
    simp [same, pointFn_ne _ _ _ different]

open Classical in
/-- `CP` averaged over key generation is `pairCollision` (`PqxdhDeploymentHeadlineCollision`): the probability that two independent encapsulations to a fresh key collide. -/
theorem pairHit_mean (setup : Setup baseSpec KemSK) :
    expectedValue (keyGen setup) (pairHit setup) = PqxdhDeploymentHeadlineCollision.pairCollision setup := by
  unfold PqxdhDeploymentHeadlineCollision.pairCollision
  rw [PqxdhDeploymentHeadlineCollision.pairDraws_eval, evalDist_apply_singleton, ← probEvent_eq_eq_probOutput,
    ← OracleComp.EvalDist.expectedValue_ite_one, OracleComp.EvalDist.expectedValue_map]
  unfold keyGen
  rw [OracleComp.EvalDist.expectedValue_map, OracleComp.EvalDist.expectedValue_bind]
  congr 1
  funext pair
  rw [pairHit_raw, OracleComp.EvalDist.expectedValue_bind]
  congr 1
  funext first
  rw [OracleComp.EvalDist.expectedValue_bind]
  congr 1
  funext second
  simp

open Classical in
/-- One key's mass times its collision probability is at most the averaged collision probability. -/
theorem keyMass_pairHit_le (setup : Setup baseSpec KemSK) (key : PqxdhKemIndCca.MlKem768PublicKey) :
    keyMass setup key * pairHit setup key ≤ PqxdhDeploymentHeadlineCollision.pairCollision setup := by
  rw [← pairHit_mean, keyMass, ← expectedValue_point]
  refine OracleComp.EvalDist.expectedValue_mono _ fun other => ?_
  by_cases same : other = key
  · subst same
    rw [pointFn_self]
  · rw [pointFn_ne _ _ _ same]
    exact zero_le

end Pair

section Triple
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK : Type}

/-- The three ghost entries a triple `(k, i, j)` reads: owner `k`'s KEM public key and the encapsulations of raw accept attempts `i` and `j`. -/
abbrev View := Option PqxdhKemIndCca.MlKem768PublicKey × Option (Option Enc) × Option (Option Enc)

/-- The view of a ghost at a triple. -/
def view (k i j : Nat) (ghost : Ghost) : View := (ghost.keys[k]?, ghost.encs[i]?, ghost.encs[j]?)

open Classical in
/-- The potential of a triple, by which of owner `k`'s key and the encapsulations of attempts `i < j` exist: with nothing drawn, `pairCollision`; with only the key, `CP(pk_k)`; with only attempt `i` reached to `(pk, c)`, `KG(pk)·D_pk(c)`; with the key and attempt `i`, `D_{pk_k}(c)` if `i` went to `pk_k`; with attempts `i` and `j` but no key, `KG(pk)` if `j` repeated `i`; with all three, the collision indicator. An attempt that reached no encapsulation gives 0. -/
noncomputable def phi (setup : Setup baseSpec KemSK) : View → ℝ≥0∞
  | (none, none, _) => PqxdhDeploymentHeadlineCollision.pairCollision setup
  | (some key, none, _) => pairHit setup key
  | (_, some none, _) => 0
  | (none, some (some (key, c)), none) => keyMass setup key * hit setup key c
  | (none, some (some _), some none) => 0
  | (none, some (some (key, c)), some (some (key', c'))) => if key' = key ∧ c' = c then keyMass setup key else 0
  | (some key, some (some (key', c)), none) => if key' = key then hit setup key c else 0
  | (some _, some (some _), some none) => 0
  | (some key, some (some (key', c)), some (some (key'', c''))) => if key' = key ∧ key'' = key ∧ c'' = c then 1 else 0

/-- The ghost event of a triple: owner `k`'s key exists and attempts `i` and `j` encapsulated to it with one ciphertext. -/
def GhostColl (k i j : Nat) (ghost : Ghost) : Prop :=
  ∃ key c, ghost.keys[k]? = some key ∧ ghost.encs[i]? = some (some (key, c)) ∧ ghost.encs[j]? = some (some (key, c))

/-- The appended element sits at the old length. -/
theorem getElem?_snoc_self {β : Type} (list : List β) (last : β) : (list ++ [last])[list.length]? = some last := by
  simp

/-- Appending keeps every other index. -/
theorem getElem?_snoc_ne {β : Type} (list : List β) (last : β) (n : Nat) (other : n ≠ list.length) :
    (list ++ [last])[n]? = list[n]? := by
  rcases Nat.lt_or_gt_of_ne other with below | above
  · rw [List.getElem?_append_left below]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

/-- With nothing drawn the potential is `pairCollision`. -/
theorem phi_empty (setup : Setup baseSpec KemSK) (k i j : Nat) :
    phi setup (view k i j Ghost.empty) = PqxdhDeploymentHeadlineCollision.pairCollision setup := by
  simp [view, Ghost.empty, phi]

/-- The collision of a triple has potential 1. -/
theorem phi_coll (setup : Setup baseSpec KemSK) (k i j : Nat) (ghost : Ghost) (coll : GhostColl k i j ghost) :
    1 ≤ phi setup (view k i j ghost) := by
  obtain ⟨key, c, keyFound, first, second⟩ := coll
  simp [view, keyFound, first, second, phi]

open Classical in
/-- A key generation appended to the keys does not increase the expected potential. -/
theorem phi_key (setup : Setup baseSpec KemSK) (k i j : Nat) (ghost : Ghost) :
    expectedValue (keyGen setup) (fun key => phi setup (view k i j { ghost with keys := ghost.keys ++ [key] })) ≤
      phi setup (view k i j ghost) := by
  by_cases atLength : k = ghost.keys.length
  · subst atLength
    have before : ghost.keys[ghost.keys.length]? = none := List.getElem?_eq_none (le_refl _)
    simp only [view, getElem?_snoc_self, before]
    rcases ghost.encs[i]? with _ | (_ | ⟨key0, c0⟩)
    · simp only [phi]
      rw [pairHit_mean]
    · simp [phi, expectedValue_zero]
    · rcases ghost.encs[j]? with _ | (_ | ⟨key1, c1⟩)
      · simp only [phi]
        refine point_le _ _ key0 (hit setup key0 c0) _ (fun key => ?_) le_rfl
        by_cases same : key = key0
        · subst same
          simp [pointFn_self]
        · simp [Ne.symm same, pointFn_ne _ _ _ same]
      · simp [phi, expectedValue_zero]
      · simp only [phi]
        refine point_le _ _ key0 (if key1 = key0 ∧ c1 = c0 then 1 else 0) _ (fun key => ?_) ?_
        · by_cases same : key = key0
          · subst same
            simp [pointFn_self]
          · simp [Ne.symm same, pointFn_ne _ _ _ same]
        · by_cases second : key1 = key0 ∧ c1 = c0
          · simp [second, keyMass]
          · simp [second]
  · have same : ∀ key, (ghost.keys ++ [key])[k]? = ghost.keys[k]? := fun key =>
      getElem?_snoc_ne ghost.keys key k atLength
    simp only [view, same]
    exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl

/-- `none` appended to the encapsulations does not increase the potential. -/
theorem phi_none (setup : Setup baseSpec KemSK) (k i j : Nat) (order : i < j) (ghost : Ghost) :
    phi setup (view k i j { ghost with encs := ghost.encs ++ [none] }) ≤ phi setup (view k i j ghost) := by
  by_cases first : i = ghost.encs.length
  · have later : j ≠ ghost.encs.length := by omega
    subst first
    simp only [view, getElem?_snoc_self, getElem?_snoc_ne ghost.encs none j later]
    rcases ghost.keys[k]? with _ | key <;> simp [phi]
  · by_cases second : j = ghost.encs.length
    · obtain ⟨entry, found⟩ : ∃ entry, ghost.encs[i]? = some entry :=
        ⟨ghost.encs[i], List.getElem?_eq_getElem (by omega)⟩
      subst second
      simp only [view, getElem?_snoc_self, getElem?_snoc_ne ghost.encs none i first, found]
      rcases ghost.keys[k]? with _ | key <;> rcases entry with _ | ⟨key0, c0⟩ <;> simp [phi]
    · simp only [view, getElem?_snoc_ne ghost.encs none i first, getElem?_snoc_ne ghost.encs none j second, le_refl]

open Classical in
/-- One encapsulation to `key` appended to the encapsulations does not increase the expected potential. -/
theorem phi_enc (setup : Setup baseSpec KemSK) (k i j : Nat) (order : i < j) (ghost : Ghost)
    (key : PqxdhKemIndCca.MlKem768PublicKey) :
    expectedValue (encC setup key) (fun c => phi setup (view k i j { ghost with encs := ghost.encs ++ [some (key, c)] })) ≤
      phi setup (view k i j ghost) := by
  by_cases first : i = ghost.encs.length
  · have later : j ≠ ghost.encs.length := by omega
    have beforeJ : ghost.encs[j]? = none := List.getElem?_eq_none (by omega)
    subst first
    have beforeI : ghost.encs[ghost.encs.length]? = none := List.getElem?_eq_none (le_refl _)
    simp only [view, getElem?_snoc_self, fun c => getElem?_snoc_ne ghost.encs (some (key, c)) j later, beforeI, beforeJ]
    rcases ghost.keys[k]? with _ | key0
    · simp only [phi]
      rw [expectedValue_const_mul]
      exact keyMass_pairHit_le setup key
    · simp only [phi]
      by_cases same : key = key0
      · subst same
        simp [pairHit]
      · simp [same, expectedValue_zero]
  · by_cases second : j = ghost.encs.length
    · obtain ⟨entry, found⟩ : ∃ entry, ghost.encs[i]? = some entry :=
        ⟨ghost.encs[i], List.getElem?_eq_getElem (by omega)⟩
      have beforeJ : ghost.encs[j]? = none := List.getElem?_eq_none (by omega)
      subst second
      simp only [view, getElem?_snoc_self, fun c => getElem?_snoc_ne ghost.encs (some (key, c)) i first, found, beforeJ]
      rcases entry with _ | ⟨key0, c0⟩
      · rcases ghost.keys[k]? with _ | key1 <;> simp [phi, expectedValue_zero]
      · rcases ghost.keys[k]? with _ | key1
        · simp only [phi]
          by_cases same : key = key0
          · subst same
            refine point_le _ _ c0 (keyMass setup key) _ (fun c => ?_) (le_of_eq (mul_comm _ _))
            by_cases same : c = c0
            · subst same
              simp [pointFn_self]
            · simp [same, pointFn_ne _ _ _ same]
          · simp [same, expectedValue_zero]
        · simp only [phi]
          by_cases same : key0 = key1 ∧ key = key1
          · obtain ⟨rfl, rfl⟩ := same
            refine point_le _ _ c0 1 _ (fun c => ?_) (by simp [hit])
            by_cases same : c = c0
            · subst same
              simp [pointFn_self]
            · simp [same, pointFn_ne _ _ _ same]
          · have zero : (fun c => if key0 = key1 ∧ key = key1 ∧ c = c0 then (1 : ℝ≥0∞) else 0) = fun _ => 0 := by
              funext c
              by_cases first' : key0 = key1
              · have different : key ≠ key1 := fun equal => same ⟨first', equal⟩
                simp [first', different]
              · simp [first']
            rw [zero, expectedValue_zero]
            exact zero_le
    · simp only [view, fun c => getElem?_snoc_ne ghost.encs (some (key, c)) i first,
        fun c => getElem?_snoc_ne ghost.encs (some (key, c)) j second]
      exact OracleComp.EvalDist.expectedValue_le_of_le _ fun _ => le_rfl

end Triple


/-! ### One triple in the instrumented experiment -/

section TripleGame
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response A X : Type}
open PqxdhDeploymentInterface (FreshBounds Mode ModeSpec asModeO)

/-- The ghost collision of a triple on an outcome of the instrumented experiment. -/
def TripleColl (k i j : Nat) (outcome : Option (PqxdhRegistrationJointServerBirth.ClientCreated Unit × X ×
    (PqxdhDeploymentSecrecy.State KemSK × Ghost)) × A) : Prop :=
  ∃ created output final, outcome.1 = some (created, output, final) ∧ GhostColl k i j final.2

/-- One triple `(k, i, j)` with `i < j`: in the instrumented experiment, the probability that owner `k`'s KEM key exists and raw accept attempts `i` and `j` encapsulated to it with one ciphertext is at most `pairCollision`, the probability that two independent encapsulations to a fresh key collide. The potential `phi` of the triple is a supermartingale along the run (`phi_key` at a key generation, `phi_enc` at a fresh encapsulation after the routing decision, `phi_none` at an attempt that reached none, unchanged at every other query), starts at `pairCollision` and is at least 1 on the collision. -/
theorem triple_le (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (ensureInit : StateT A ProbComp Bool) (identityIndex : Nat)
    (bounds : FreshBounds) (mode : Mode) (adversary : OracleComp (ModeSpec mode) X) (runtime : A) (k i j : Nat)
    (order : i < j) :
    𝒟[(fun outcome => @decide (TripleColl k i j outcome) (Classical.propDecidable _)) <$>
      (gameG setup codec checks route ensureInit identityIndex bounds mode adversary).run runtime] {true} ≤
      PqxdhDeploymentHeadlineCollision.pairCollision setup := by
  rw [evalDist_apply_singleton, ← probEvent_eq_eq_probOutput, probEvent_map]
  classical
  rw [← OracleComp.EvalDist.expectedValue_ite_one]
  simp only [gameG, StateT.run, OracleComp.EvalDist.expectedValue_bind]
  refine OracleComp.EvalDist.expectedValue_le_of_le _ fun born => ?_
  rcases born with ⟨_ | created, after⟩
  · simp [TripleColl]
  · dsimp only
    rw [OracleComp.EvalDist.expectedValue_map]
    refine le_trans (OracleComp.EvalDist.expectedValue_mono _ fun result => ?_)
      ((expected_run_le (handlerG setup codec checks route created.seed bounds)
        (fun state => phi setup (view k i j state.2))
        (handlerG_expect setup codec checks route created.seed bounds (fun ghost => phi setup (view k i j ghost))
          (phi_key setup k i j) (phi_enc setup k i j order) (phi_none setup k i j order))
        (asModeO mode adversary) ((PqxdhDeploymentSecrecy.Ledger.empty, PqxdhDeploymentNative.initial created),
          Ghost.empty)).trans (le_of_eq (phi_empty setup k i j)))
    by_cases coll : GhostColl k i j result.2.2
    · have holds : ((fun b => b = true) ∘ fun outcome => @decide (TripleColl k i j outcome) (Classical.propDecidable _))
          (some (PqxdhRegistrationJointServerBirth.encode created, result), after) := by
        simp only [Function.comp_apply, decide_eq_true_eq]
        exact ⟨_, _, _, rfl, coll⟩
      simp only [holds, ↓reduceIte]
      exact phi_coll setup k i j result.2.2 coll
    · have fails : ¬((fun b => b = true) ∘ fun outcome => @decide (TripleColl k i j outcome) (Classical.propDecidable _))
          (some (PqxdhRegistrationJointServerBirth.encode created, result), after) := by
        simp only [Function.comp_apply, decide_eq_true_eq]
        rintro ⟨_, _, _, same, holds⟩
        cases same
        exact coll holds
      simp only [fails, ↓reduceIte]
      exact zero_le

end TripleGame

end BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.collectVerifiedEnc_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.collectVerifiedEnc_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.collectEnc_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.collectEnc_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.prefixEnc_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.prefixEnc_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.acceptEnc_fst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.acceptEnc_fst

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expected_run_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expected_run_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.prefixEnc_expect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.prefixEnc_expect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.acceptEnc_expect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.acceptEnc_expect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handler_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handler_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.map_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.map_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handlerG_proj' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handlerG_proj

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.create_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.create_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.create_expect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.create_expect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.ghost_keys_nil' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.ghost_keys_nil

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handlerG_expect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.handlerG_expect

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.game_ghost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.game_ghost

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pointFn_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pointFn_self

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pointFn_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pointFn_ne

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.ciphertextArray_injective' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.ciphertextArray_injective

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_const_mul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_const_mul

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_zero

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_point' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.expectedValue_point

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.point_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.point_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pairHit_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pairHit_raw

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pairHit_mean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.pairHit_mean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.keyMass_pairHit_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.keyMass_pairHit_le

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.getElem?_snoc_self' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.getElem?_snoc_self

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.getElem?_snoc_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.getElem?_snoc_ne

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_empty

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_coll' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_coll

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_key' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_key

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_enc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.phi_enc

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.triple_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentHeadlineCtGhost.triple_le
