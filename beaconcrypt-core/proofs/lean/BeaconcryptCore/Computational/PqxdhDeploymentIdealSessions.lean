-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealEnv
import BeaconcryptCore.Computational.PqxdhDeploymentIdealKeymatch

/-!
# The Server's sessions under the ideal environment's commands (CE-11b, unit U4)

Facts about the Server's session counter, its pending tokens and the replies of the ideal environment's commands, as the provenance invariant of `PqxdhDeploymentIdealProvenance` needs them:

- Real commands: a raw accept raises the session counter by one and publishes at most one token, at the old counter (`realStep_accept`, from `PqxdhServerAuthPendingBudget.accept_pending`); a build consumes its session's token, keeps the counter and returns a response only from a pending token (`realStep_build`); the create, bundle, finish and HMAC commands keep both (`realStep_quiet`), as does the pool create (`createPool_game`); stripping keeps both (`strip_game`).
- The selected accept: under `PqxdhDeploymentIdealSteps.tailCE` the marker client keeps the session counter and the tokens (`tailCE_client_pending`); the marker tail either returns nothing and keeps the tokens of the given state or returns that state's session counter and publishes one token there (`tailCE_tail_pending`); hence the same for the selected accept on a key match (`acceptActive_pending`), for the selected accept with its encapsulation exposed when it marks a session (`acceptExposed_pending`) and for its capability form (`acceptSelected_pending`).

These are support facts; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions
open PqxdhServerAuthExperiment (Setup Codec Checks GameState)
open PqxdhDeploymentEnvironment (EnvState strip)

variable {KemSK : Type}

section Real
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response Bk : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- Stripping keeps the Server's session counter and pending tokens. -/
theorem strip_game (state : PqxdhRegistrationSchedule.State KemSK) :
    (strip state).shared.2.sessions = state.shared.2.sessions ∧ (strip state).shared.2.pending = state.shared.2.pending :=
  ⟨rfl, rfl⟩

/-- A real raw accept raises the session counter by one and may publish one pending token, at the old counter. -/
theorem realStep_accept (raw : Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks ⟨.accept raw, trivial⟩).run e),
      v.2.native.shared.2.sessions = e.native.shared.2.sessions + 1 ∧
        (v.2.native.shared.2.pending = e.native.shared.2.pending ∨ ∃ token,
          v.2.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions (some token)) := by
  intro v member
  change v ∈ support ((PqxdhDeploymentEnvironment.acceptStep (n := 2) setup codec checks raw).run
    (PqxdhDeploymentEnvironment.snapped _ e)) at member
  unfold PqxdhDeploymentEnvironment.acceptStep at member
  simp only [StateT.run, support_map, Set.mem_image] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhDeploymentLaterServerNative.acceptLogged setup
      codec checks e.created.seed raw)).run e.native) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  have native : ((x.1.1, x.2) : Option ℕ × PqxdhServerAuthNative.NativeState KemSK) ∈ support
      ((PqxdhServerAuthNative.nativeAccept setup codec checks e.created.seed PqxdhRegistrationSchedule.observationScalar
        raw).run e.native.shared) := by
    rw [← PqxdhDeploymentLaterServerNative.acceptLogged_fst, support_map]
    exact ⟨x, xMember, rfl⟩
  rw [← PqxdhServerAuthNative.accept_native] at native
  have evaluated := PqxdhServerAuthNative.evaluate_support setup e.created.seed _ _ e.native.shared _ native
  exact PqxdhServerAuthPendingBudget.accept_pending setup codec checks _ raw e.native.shared.2 _ evaluated

/-- A real build of a session consumes the session's pending token, keeps the session counter and every other token, and returns a response only from a pending token. -/
theorem realStep_build (session : ℕ) (payload : Option Pqxdh.Bytes) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks
        ⟨.build session payload, trivial⟩).run e),
      v.2.native.shared.2.sessions = e.native.shared.2.sessions ∧
        v.2.native.shared.2.pending = Function.update e.native.shared.2.pending session none ∧
        (v.1.isSome = true → (e.native.shared.2.pending session).isSome = true) := by
  intro v member
  change v ∈ support ((PqxdhDeploymentEnvironment.buildStep (n := 2) setup codec checks session payload).run
    (PqxdhDeploymentEnvironment.snapped _ e)) at member
  unfold PqxdhDeploymentEnvironment.buildStep at member
  simp only [StateT.run] at member
  split at member
  · rename_i missing
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    refine ⟨rfl, ?_, fun found => by cases found⟩
    change e.native.shared.2.pending = _
    change e.native.shared.2.pending session = none at missing
    rw [← missing, Function.update_eq_self]
  · rename_i token found
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, _, _, rfl⟩ := member
    change e.native.shared.2.pending session = some token at found
    exact ⟨rfl, rfl, fun _ => by rw [found]; rfl⟩

/-- Every real command other than a raw accept or a build keeps the Server's session counter and pending tokens. -/
theorem realStep_quiet (query : PqxdhRecordLiftInterface.EnvQuery) (notAccept : ∀ raw, query.val ≠ .accept raw)
    (notBuild : ∀ session payload, query.val ≠ .build session payload) (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.realStep (n := 2) setup codec checks query).run e),
      v.2.native.shared.2.sessions = e.native.shared.2.sessions ∧
        v.2.native.shared.2.pending = e.native.shared.2.pending := by
  rcases query with ⟨command, allowed⟩
  cases command with
  | create pin keyId =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.createStep (n := 2) setup pin keyId).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.createStep at member
      split at member
      · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl⟩
      · rename_i word _
        rw [StateT.run_bind, mem_support_bind_iff] at member
        obtain ⟨r, rMember, member⟩ := member
        simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
          support_pure, Set.mem_singleton_iff] at member
        obtain ⟨_, _, rfl⟩ := member
        simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
        obtain ⟨x, xMember, rfl⟩ := rMember
        have inner : x ∈ support ((PqxdhRegistrationSchedule.create setup word keyId).run e.native) :=
          PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
        rw [PqxdhDeploymentEnvironmentReal.create_run setup word keyId e.native] at inner
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
        obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
        exact ⟨rfl, rfl⟩
  | bundle owner =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.bundleStep (n := 2) setup codec owner).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.bundleStep at member
      simp only [StateT.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨r, rMember, _, _, rfl⟩ := member
      have inner : r ∈ support ((PqxdhRegistrationSchedule.bundle setup codec owner).run e.native) :=
        PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
      cases owned : e.native.owners[owner]? with
      | none =>
          rw [PqxdhDeploymentEnvironmentReal.bundle_run_missing setup codec owner _ owned, support_pure,
            Set.mem_singleton_iff] at inner
          subst inner
          exact ⟨rfl, rfl⟩
      | some current =>
          rw [PqxdhDeploymentEnvironmentReal.bundle_run_found setup codec owner _ current owned, support_map] at inner
          obtain ⟨b, _, rfl⟩ := inner
          exact ⟨rfl, rfl⟩
  | accept raw => exact absurd rfl (notAccept raw)
  | build session payload => exact absurd rfl (notBuild session payload)
  | finish owner raw =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.finishStep (n := 2) setup codec owner raw).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.finishStep at member
      simp only [StateT.run] at member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff] at member
        subst member
        exact ⟨rfl, rfl⟩
      · simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
        obtain ⟨result, resultMember, _, _, rfl⟩ := member
        have game := PqxdhDeploymentEnvironmentReal.finishFwd_game setup codec _ _ result resultMember
        exact ⟨congrArg (fun g => g.sessions) game, congrArg (fun g => g.pending) game⟩
  | hmac key message =>
      intro v member
      change v ∈ support ((PqxdhDeploymentEnvironment.hmacStep (n := 2) setup key message).run
        (PqxdhDeploymentEnvironment.snapped _ e)) at member
      unfold PqxdhDeploymentEnvironment.hmacStep PqxdhDeploymentEnvironment.onEnv at member
      simp only [StateT.run, support_map, Set.mem_image] at member
      obtain ⟨r, rMember, rfl⟩ := member
      have inner : r ∈ support ((PqxdhRegistrationSchedule.onShared (PqxdhServerAuthNative.nativeHmac setup e.created.seed
          PqxdhRegistrationSchedule.observationScalar key message)).run e.native) :=
        PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
      rw [PqxdhDeploymentEnvironmentReal.onShared_run, support_map] at inner
      obtain ⟨x, xMember, rfl⟩ := inner
      rw [← PqxdhServerAuthNative.hmac_native] at xMember
      have evaluated := PqxdhServerAuthNative.evaluate_support setup e.created.seed _ _ e.native.shared x xMember
      exact PqxdhDeploymentIdealEnvFacts.hmacOracle_keeps key message e.native.shared.2 _ evaluated
  | hash _ => exact absurd allowed id
  | serverSend _ _ => exact absurd allowed id
  | serverRaw _ => exact absurd allowed id
  | beaconSend _ _ => exact absurd allowed id
  | beaconRaw _ _ => exact absurd allowed id

/-- The pool create keeps the Server's session counter and pending tokens. -/
theorem createPool_game (pool : List (PqxdhLiveKemReservation.Pair KemSK)) (pin : Pqxdh.Bytes) (keyId : Std.U64)
    (e : EnvState KemSK Bk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvReal.createPoolStep (n := 2) setup pool pin keyId).run e),
      v.2.native.shared.2.sessions = e.native.shared.2.sessions ∧
        v.2.native.shared.2.pending = e.native.shared.2.pending := by
  intro v member
  unfold PqxdhDeploymentIdealEnvReal.createPoolStep at member
  split at member
  · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · rename_i word _
    rw [StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨r, rMember, member⟩ := member
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure, bind_assoc, pure_bind, mem_support_bind_iff,
      support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    simp only [PqxdhDeploymentEnvironment.onEnv, StateT.run, support_map, Set.mem_image] at rMember
    obtain ⟨x, xMember, rfl⟩ := rMember
    have inner : x ∈ support ((PqxdhDeploymentIdealSteps.createPool setup pool word keyId).run e.native) :=
      PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ xMember
    rw [PqxdhDeploymentIdealEnvReal.createPool_run setup pool word keyId e.native] at inner
    simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at inner
    obtain ⟨_, _, _, _, _, _, rfl⟩ := inner
    exact ⟨rfl, rfl⟩

end Real

/-! ### The selected accept's pending token -/

section Selected
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (tailCE acceptActive acceptInactive acceptExposed AcceptOut)
open PqxdhServerAuthNative (NativeState)
variable {Reader : Type}

/-- The marker client under `tailCE`, from any state: the Server's session counter and pending tokens are kept. -/
theorem tailCE_client_pending (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (marker : input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
      (PqxdhRegistrationJointKemOpaqueClient.client control binding input))).run s)) :
    result.2.1.2.sessions = s.1.2.sessions ∧ result.2.1.2.pending = s.1.2.pending := by
  have auxStep : ∀ (query : PqxdhServerRelatedRootConsumer.Auxiliary) (st : NativeState KemSK × Option (ℕ × Coord)),
      (match query with
        | .consume _ => False
        | _ => True) →
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr query) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st = pure ((), st) := by
    intro query st kind
    cases query <;> simp only at kind <;> rfl
  have consumeStep : ∀ (rid : beaconcrypt_core.pqxdh.RegistrationId) (st : NativeState KemSK × Option (ℕ × Coord)),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inr (.consume rid)) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        pure ((), ((st.1.1, { st.1.2 with server := { st.1.2.server with
          consumed := st.1.2.server.consumed ++ [absBytes rid.bytes] } }), st.2)) := by
    intro rid st
    rfl
  have rootStep : ∀ st : NativeState KemSK × Option (ℕ × Coord),
      (simulateQ (tailCE (KemSK := KemSK) hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
        ((PqxdhRegistrationJointKemOpaqueClient.Spec Reader).query (.inl input) :
          OracleComp (PqxdhRegistrationJointKemOpaqueClient.Spec Reader) _))).run st =
        (fun _ => (PqxdhServerAuthEntryFactor.sentinel, (st.1, some (index, PqxdhDeploymentIdealSteps.coordsOf input)))) <$>
          (SlotSpec.query (.inr (PqxdhDeploymentIdealSteps.coordsOf input)) : OracleComp SlotSpec _) := by
    intro st
    simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map,
      PqxdhRegistrationJointKemOpaqueTail.forward]
    simp only [tailCE, StateT.run, marker, map_eq_bind_pure_comp]
    rfl
  unfold PqxdhRegistrationJointKemOpaqueClient.client at member
  simp only [simulateQ_bind, StateT.run_bind, auxStep .eraseShared s trivial, pure_bind] at member
  split at member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact ⟨rfl, rfl⟩
  · simp only [simulateQ_bind, StateT.run_bind, rootStep, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [auxStep .eraseInput _ trivial, consumeStep, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, rfl, _, rfl, rfl⟩ := member
    exact ⟨rfl, rfl⟩

/-- The marker tail under `tailCE`: either it returns nothing and the pending tokens are those of the given state, or it returns the given state's session counter and publishes one token there. -/
theorem tailCE_tail_pending (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : Option ℕ × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s)) :
    (result.1 = none ∧ result.2.1.2.pending = state.pending) ∨
      ∃ token, result.1 = some state.sessions ∧
        result.2.1.2.pending = Function.update state.pending state.sessions (some token) := by
  unfold PqxdhRegistrationJointKemOpaqueTail.tail at member
  simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff] at member
  obtain ⟨installed, installedMember, member⟩ := member
  change installed ∈ support ((fun r => (r.1, (r.2, s.2))) <$> PqxdhDeploymentIdealSteps.liftS
    ((PqxdhRegistrationJointKemOpaqueTail.mutation (.install _)).run s.1)) at installedMember
  simp only [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp,
    PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeSet, PqxdhServerAuthNative.localState,
    StateT.run, support_pure, Set.image_singleton, Set.mem_singleton_iff] at installedMember
  subst installedMember
  rcases found : collected.1 with _ | input
  · simp only [found, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    exact Or.inl ⟨rfl, rfl⟩
  · simp only [found, simulateQ_bind, StateT.run_bind, mem_support_bind_iff] at member
    obtain ⟨returned, returnedMember, member⟩ := member
    have client := tailCE_client_pending hmac index state.server.control
      ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input (marker input found) _
      returned returnedMember
    rcases outcome : returned.1 with (_ | token) | _ | _ <;> simp only [outcome] at member
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, client.2⟩
    · simp only [simulateQ_bind, StateT.run_bind, simulateQ_spec_query, mem_support_bind_iff, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      obtain ⟨published, publishedMember, rfl⟩ := member
      change published ∈ support ((fun r => (r.1, (r.2, returned.2.2))) <$> PqxdhDeploymentIdealSteps.liftS
        ((PqxdhRegistrationJointKemOpaqueTail.mutation (.publish _ _)).run returned.2.1)) at publishedMember
      simp only [support_map, PqxdhDeploymentIdealSteps.liftS, support_liftComp,
        PqxdhRegistrationJointKemOpaqueTail.mutation, PqxdhServerAuthNative.nativeModify,
        PqxdhServerAuthNative.localState, StateT.run, support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at publishedMember
      subst publishedMember
      refine Or.inr ⟨token, rfl, ?_⟩
      dsimp only
      rw [client.2]
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, client.2⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, client.2⟩

variable {ι : Type} {baseSpec : OracleSpec ι} {Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The selected accept on a verified key match: either it returns nothing and keeps the pending tokens, or it returns the old session counter and publishes one token there. -/
theorem acceptActive_pending (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (s : NativeState KemSK) (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptActive setup codec checks seed challenge verified).run s)) :
    (r.1.1.1 = none ∧ r.2.2.pending = s.2.pending) ∨
      ∃ token, r.1.1.1 = some s.2.sessions ∧ r.2.2.pending = Function.update s.2.pending s.2.sessions (some token) := by
  change r ∈ support (do
    let pre ← PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed)
      (PqxdhDeploymentLaterServerSource.beforeLogged (Shared := PqxdhBeaconPhase2Preparation.Word32) verified)).run
        s.2.server.consumed)
    match pre.1.1 with
    | none => do
        let r ← PqxdhDeploymentIdealSteps.liftS ((PqxdhRegistrationJointServerAccept.tail (Reader := Reader) setup
          (setup.joint.publicKeys seed) s.2 (none, pre.2)).run s)
        pure (((r.1, pre.1.2), (false, none)), r.2)
    | some ephemeral => do
        let prepared ← PqxdhDeploymentIdealSteps.liftS ((simulateQ (PqxdhDeploymentIdealSteps.prefixNative setup codec
          checks seed) (PqxdhRegistrationJointKemOpaqueSuffix.program (Shared := PqxdhBeaconPhase2Preparation.Word32)
            verified ephemeral (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge)).run pre.2)
        let answer ← (simulateQ (tailCE setup.hmac s.2.sessions)
          (PqxdhRegistrationJointKemOpaqueTail.tail setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared)).run
            (s, none)
        pure (((answer.1, pre.1.2), (true, answer.2.2)), answer.2.1)) at member
  rw [mem_support_bind_iff] at member
  obtain ⟨pre, -, member⟩ := member
  split at member
  · rw [mem_support_bind_iff] at member
    obtain ⟨tailed, tailedMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at tailedMember
    simp only [PqxdhRegistrationJointServerAccept.tail, PqxdhServerAuthNative.nativeSet, StateT.run] at tailedMember
    subst tailedMember
    exact Or.inl ⟨rfl, rfl⟩
  · rw [mem_support_bind_iff] at member
    obtain ⟨prepared, preparedMember, member⟩ := member
    rw [mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at preparedMember
    have marker := PqxdhDeploymentIdealKeymatch.program_marker
      (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) verified _ _ _ _ prepared preparedMember
    exact tailCE_tail_pending setup.hmac s.2.sessions setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared
      marker (s, none) answer answerMember

/-- The selected accept with its encapsulation exposed: when it marks a session, either it returns nothing and keeps the pending tokens, or it returns the old session counter and publishes one token there. -/
theorem acceptExposed_pending (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (s : NativeState KemSK)
    (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptExposed setup codec checks seed chosen challenge raw).run s))
    (marked : r.1.2.2.isSome = true) :
    (r.1.1.1 = none ∧ r.2.2.pending = s.2.pending) ∨
      ∃ token, r.1.1.1 = some s.2.sessions ∧ r.2.2.pending = Function.update s.2.pending s.2.sessions (some token) := by
  have inactive : r ∈ support ((acceptInactive setup codec checks seed raw).run s) → False := fun member' => by
    have none := (PqxdhDeploymentIdealKeymatch.acceptInactive_facts setup codec checks seed raw s r member').2.1
    rw [none] at marked
    cases marked
  unfold acceptExposed at member
  rcases found : PqxdhRegistrationJointRawSignatures.verified setup codec checks raw with _ | verified
  · rw [found] at member
    exact (inactive member).elim
  · rw [found] at member
    by_cases same : verified.keys.pqKey = chosen.1
    · simp only [same, ↓reduceIte] at member
      exact acceptActive_pending setup codec checks seed challenge verified s r member
    · simp only [same, ↓reduceIte] at member
      exact (inactive member).elim

open PqxdhRegistrationJointKemSecondEntry (slotImpl) in
open PqxdhDeploymentIdealKernel (lazyDummy) in
/-- The selected accept in capability form: when it marks a session, either it returns nothing and keeps the Server's pending tokens, or it returns the old session counter and publishes one token there. -/
theorem acceptSelected_pending {count : ℕ} (p : PqxdhDeploymentIdealParams.Params KemSK count) (raw : Pqxdh.Bytes)
    (e : EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e),
      v.2.backend.2.2.marks.isSome = true →
        (v.1 = none ∧ v.2.native.shared.2.pending = e.native.shared.2.pending) ∨
          ∃ token, v.1 = some e.native.shared.2.sessions ∧
            v.2.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions
              (some token) := by
  intro v member marked
  change v ∈ support ((fun r => (r.1.1.1.1, PqxdhDeploymentIdealEnvStep.acceptedEnv e r)) <$> PqxdhDeploymentEnvironment.coins
    (n := 2) ((PqxdhDeploymentIdealEnvStep.acceptGame setup codec checks p e.created.seed raw
      (e.backend.2.1, (e.backend.1, ∅))).run e.native.shared)) at member
  rw [support_map] at member
  obtain ⟨r, rMember, rfl⟩ := member
  have inner : r ∈ support ((fun r => ((r.1.1, r.2), r.1.2)) <$> (simulateQ (slotImpl (lazyDummy (n := 2)))
      ((acceptExposed setup codec checks e.created.seed p.chosen p.challenge raw).run
        e.native.shared)).run (e.backend.2.1, (e.backend.1, ∅))) :=
    PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ rMember
  rw [support_map] at inner
  obtain ⟨x, xMember, rfl⟩ := inner
  exact acceptExposed_pending setup codec checks e.created.seed p.chosen p.challenge raw e.native.shared x.1
    (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ xMember) marked

end Selected

end BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.strip_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.strip_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_build

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_quiet' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.realStep_quiet

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.createPool_game' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.createPool_game

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.tailCE_client_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.tailCE_client_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.tailCE_tail_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.tailCE_tail_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptActive_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptActive_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptExposed_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptExposed_pending

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptSelected_pending' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealSessions.acceptSelected_pending
