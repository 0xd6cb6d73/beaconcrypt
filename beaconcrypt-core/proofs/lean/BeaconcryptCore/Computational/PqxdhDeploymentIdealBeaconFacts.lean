-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealProvenance

/-!
# Native facts for the Beacon converse of the ideal environment (CE-11b, unit U4)

The native facts that the Beacon converse of C5 (design-v2 section 7.2, L4) needs about the ideal environment's commands (`PqxdhDeploymentIdealEnv.idealStep`), each read off the extracted Rust through the existing source correspondences:

- A real Beacon finish of an owner that is not in the `initSent` phase returns nothing (`realFinish_none`; `beacon.rs`, `finish_registration`: a finish outside `InitSent` is rejected before the secret key is read). A Phase 2 finish returns bytes only when it establishes the owner (`finish_some`; `finish_none` for no staged result).
- Owner k's challenge finish on a finish input whose Phase 2 reader gives a ciphertext with the challenge ciphertext's bytes: the preparation answers that decapsulation with the challenge marker (`collect_answers`, `prepare_challenge`), and a finish that returns bytes sets the Beacon install ghost at coordinates that hold a slot (`finishChallenge_beacon`, with `commitEnv_none`).
- The selected raw accept marks a session only when it is active, and when it marks one it either returns nothing and keeps the pending tokens, or returns the old session counter and publishes there one token whose pending registration carries the challenge ciphertext: the candidate-free suffix carries the supplied ciphertext (`program_ciphertext`), the Server's accept core stores the prepared input's ciphertext (`accept_ciphertext`, through `PqxdhRegistrationJointKemOpaqueCore.accepted_original` and `PqxdhRegistrationInputs.accepted_used` on the extracted `server_accept`), and the marker client and tail publish it (`tailCE_client_token`, `tailCE_tail_token`, `acceptActive_token`, `acceptExposed_token`, `acceptSelected_token`).
- The Server build writes Phase 2 with the pending registration's KEM ciphertext: every published response of the generic build is the Phase 2 writer's output on the fields of a candidate that carries the pending registration's KEM ciphertext (`GWritten`, `afterInitialization_written`, `candidate_written`, `genericBuild_written`, through `PqxdhServerAuthNegativeControl.prepare_commit_fields`); for the environment's forwarded split build the writer is the codec's Phase 2 writer (`writeImpl`, `tailFwd_writeImpl`, `buildSplitFwd_written`), and so for the ideal environment's marked build at the session's pending token (`buildCached_written`).

These are support facts of programs; no security claim is made here.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhDeploymentEnvironment (EnvState)
open PqxdhDeploymentIdealSteps (IdealCore SplitBk initSentAt establishedAt)
open PqxdhDeploymentIdealParams (Target Params)

variable {KemSK : Type}

/-! ### Finishes -/

section Finish
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The Phase 2 finish without a staged result returns nothing. -/
theorem finish_none {I D K : Type} (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (state : PqxdhBeaconPhase2Preparation.State I D K) :
    (PqxdhBeaconPhase2Publication.finish control state none).1 = none := rfl

/-- A Phase 2 finish that returns bytes establishes the owner. -/
theorem finish_some (control : beaconcrypt_core.pqxdh.BeaconInitSent) (before : PqxdhRegistrationSchedule.Owner KemSK)
    (staged : Option PqxdhBeaconPhase2Publication.Staged) (bytes : Pqxdh.Bytes)
    (returned : (PqxdhBeaconPhase2Publication.finish control before staged).1 = some bytes) :
    ∃ control' associatedData kernel, (PqxdhBeaconPhase2Publication.finish control before staged).2.beacon.phase =
      .established control' associatedData kernel := by
  unfold PqxdhBeaconPhase2Publication.finish at returned ⊢
  rcases staged with _ | staged
  · cases returned
  · dsimp only at returned ⊢
    split_ifs at returned ⊢
    exact ⟨_, _, _, rfl⟩

/-- A real Beacon finish of an owner that is not in the `initSent` phase returns nothing (`beacon.rs`, `finish_registration`: a finish outside `InitSent` is rejected before the secret key is read). -/
theorem realFinish_none {Bk : Type} {n : ℕ} (owner : ℕ) (raw : Pqxdh.Bytes)
    (allowed : PqxdhRecordLiftInterface.IsEnvironment (.finish owner raw)) (e : EnvState KemSK Bk)
    (notInitSent : initSentAt e.native.owners owner = false) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.realStep (n := n) setup codec checks ⟨.finish owner raw, allowed⟩).run e),
      v.1 = none := by
  intro v member
  change v ∈ support (PqxdhDeploymentEnvironment.finishStep (n := n) setup codec owner raw
    (PqxdhDeploymentEnvironment.snapped ⟨.finish owner raw, allowed⟩ e)) at member
  unfold PqxdhDeploymentEnvironment.finishStep at member
  change v ∈ support (match e.native.owners[owner]? with
    | none => _
    | some before => _) at member
  rcases owned : e.native.owners[owner]? with _ | before
  · rw [owned] at member
    simp only [support_pure, Set.mem_singleton_iff] at member
    subst member
    rfl
  · rw [owned] at member
    simp only [mem_support_bind_iff] at member
    obtain ⟨result, resultMember, member⟩ := member
    simp only [support_pure, Set.mem_singleton_iff] at member
    obtain ⟨_, _, rfl⟩ := member
    have phase : ∀ control prekey oneTime kem, before.beacon.phase ≠ .initSent control prekey oneTime kem := by
      intro control prekey oneTime kem same
      simp only [initSentAt, owned, same, Bool.true_eq_false] at notInitSent
    have native : PqxdhBeaconPhase2Publication.owner (X := PqxdhJointIdentity.IdentitySeed) (Response := Response)
        codec.frameRead raw before = pure (none, before) := by
      unfold PqxdhBeaconPhase2Publication.owner
      split
      · rename_i control prekey oneTime kem same
        exact absurd same (phase control prekey oneTime kem)
      · rfl
    rw [PqxdhBeaconPhase2Publication.nativeOwner, native, simulateQ_pure, simulateQ_pure, StateT.run_pure,
      support_pure, Set.mem_singleton_iff] at resultMember
    subst resultMember
    rfl

end Finish

/-! ### The preparation of owner k's challenge finish -/

section Collect

/-- The answers behind a collected Phase 2 input: the decoded response, its ciphertext and the decapsulation handle are answers of the interpreter to the decode, ciphertext and decapsulation requests. -/
theorem collect_answers {I D K X Response Shared : Type} (impl : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) ProbComp)
    (identity : I) (prekey oneTime : D) (kem : K) (raw : Pqxdh.Bytes)
    (inputs : PqxdhBeaconPhase2Shared.Inputs Response Shared)
    (reached : some inputs ∈ support (simulateQ impl (PqxdhBeaconPhase2Shared.collect identity prekey oneTime kem raw))) :
    some inputs.response ∈ support (impl (.decode raw)) ∧
      some inputs.ciphertext ∈ support (impl (.ciphertext inputs.response)) ∧
      some inputs.secrets.shared ∈ support (impl (.decapsulate inputs.ciphertext kem)) := by
  simp only [PqxdhBeaconPhase2Shared.collect, OptionT.run_bind, OptionT.run_mk, OptionT.run_pure,
    OptionT.run_monadLift, Option.elimM, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨response, responseMember, reached⟩ := reached
  rcases response with _ | response
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨ciphertext, ciphertextMember, reached⟩ := reached
  rcases ciphertext with _ | ciphertext
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨ephemeral, ephemeralMember, reached⟩ := reached
  rcases ephemeral with _ | ephemeral
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨server, serverMember, reached⟩ := reached
  rcases server with _ | server
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨serverConverted, serverConvertedMember, reached⟩ := reached
  rcases serverConverted with _ | serverConverted
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨identityConverted, identityConvertedMember, reached⟩ := reached
  rcases identityConverted with _ | identityConverted
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨shared, sharedMember, reached⟩ := reached
  rcases shared with _ | shared
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨dh1, dh1Member, reached⟩ := reached
  rcases dh1 with _ | dh1
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨dh2, dh2Member, reached⟩ := reached
  rcases dh2 with _ | dh2
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨dh3, dh3Member, reached⟩ := reached
  rcases dh3 with _ | dh3
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at reached
  obtain ⟨dh4, dh4Member, reached⟩ := reached
  rcases dh4 with _ | dh4
  · simp at reached
  simp only [Option.elim_some, simulateQ_bind, simulateQ_map, mem_support_bind_iff, support_map, Set.mem_image] at reached
  obtain ⟨assigned, -, reached⟩ := reached
  rcases assigned with _ | assigned
  · simp at reached
  simp only [Option.elim_some, simulateQ_pure, support_pure, Set.mem_singleton_iff, Option.some.injEq] at reached
  subst reached
  exact ⟨responseMember, ciphertextMember, sharedMember⟩


end Collect

section Prepare
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : PqxdhServerAuthExperiment.Setup baseSpec KemSK) (codec : PqxdhServerAuthExperiment.Codec Reader Response)

/-- Owner k's preparation with the challenge handle on a finish input whose Phase 2 reader gives a ciphertext with the challenge ciphertext's bytes: every prepared finish carries the challenge marker as its decapsulation handle. -/
theorem prepare_challenge (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (identity : PqxdhJointIdentity.IdentitySeed) (prekey oneTime : PqxdhJointGapDh.ScalarBytes)
    (kem : PqxdhKemIndCca.MlKem768PublicKey × KemSK) (raw : Pqxdh.Bytes)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (read : (codec.read2 raw).bind codec.ciphertext = some ciphertext)
    (same : PqxdhPhase2InputBytes.ciphertext ciphertext = challenge) :
    ∀ prepared ∈ support (simulateQ (PqxdhDeploymentIdealSteps.preparationCE (Response := Response) setup codec challenge)
        (PqxdhBeaconPhase2Shared.prepare control identity prekey oneTime kem raw)),
      ∀ pending, prepared = some pending → pending.root.shared = .challenge := by
  intro prepared member pending found
  obtain ⟨response, decoded, readCiphertext⟩ := Option.bind_eq_some_iff.mp read
  simp only [PqxdhBeaconPhase2Shared.prepare, simulateQ_bind, mem_support_bind_iff] at member
  obtain ⟨inputs, inputsMember, member⟩ := member
  rcases inputs with _ | inputs
  · simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  obtain ⟨responseMember, ciphertextMember, sharedMember⟩ := collect_answers _ identity prekey oneTime kem raw inputs
    inputsMember
  simp only [PqxdhDeploymentIdealSteps.preparationCE, support_pure, Set.mem_singleton_iff, decoded,
    Option.some.injEq] at responseMember
  rw [responseMember] at ciphertextMember
  simp only [PqxdhDeploymentIdealSteps.preparationCE, support_pure, Set.mem_singleton_iff, readCiphertext,
    Option.some.injEq] at ciphertextMember
  rw [ciphertextMember, PqxdhDeploymentIdealSteps.preparationCE_challenge setup codec challenge ciphertext kem same,
    support_pure, Set.mem_singleton_iff, Option.some.injEq] at sharedMember
  simp only [PqxdhBeaconPhase2Shared.afterInputs, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at member
  obtain ⟨_, -, rfl⟩ := member
  obtain ⟨metadata, -, rfl⟩ := Option.map_eq_some_iff.mp found
  exact sharedMember

end Prepare

/-! ### Owner k's challenge finish -/

section Challenge
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) {count : ℕ}
open PqxdhDeploymentIdealEnvFinish (finishChallengeEnv commitEnv groupEnv finishedEnv hiddenBackend)

/-- The commit of a finish without a staged result returns nothing. -/
theorem commitEnv_none (e : EnvState KemSK SplitBk) (owner : ℕ) (control : beaconcrypt_core.pqxdh.BeaconInitSent)
    (before : PqxdhRegistrationSchedule.Owner KemSK) (shared : PqxdhServerAuthNative.NativeState KemSK) :
    ∀ v ∈ support (commitEnv e owner control before shared none), v.1 = none := by
  intro v member
  unfold commitEnv at member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, -, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  rfl

/-- Owner k's challenge finish on a finish input whose Phase 2 reader gives a ciphertext with the challenge ciphertext's bytes: when it returns bytes, the Beacon install ghost is set at coordinates that hold a slot. The preparation answers the decapsulation of the challenge ciphertext with the challenge marker (`prepare_challenge`), so the grouped request reads the hidden value at the four DH coordinates; a return requires an allocated slot and an established owner (`finish_some`), and the established owner sets the ghost (`PqxdhDeploymentIdealEnvFinish.hiddenBackend`). -/
theorem finishChallenge_beacon (p : Params KemSK count) (owner : ℕ) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext)
    (read : (codec.read2 raw).bind codec.ciphertext = some ciphertext)
    (same : PqxdhPhase2InputBytes.ciphertext ciphertext = p.challenge) :
    ∀ v ∈ support ((finishChallengeEnv setup codec p owner raw).run e), ∀ bytes, v.1 = some bytes →
      ∃ c j, v.2.backend.2.2.beacon = some c ∧ v.2.backend.2.1.1 c = some j := by
  intro v member bytes returned
  change v ∈ support (match e.native.owners[owner]? with
    | some before => _
    | none => _) at member
  rcases owned : e.native.owners[owner]? with _ | before
  · rw [owned] at member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    cases returned
  rw [owned] at member
  dsimp only at member
  split at member
  rotate_left
  · rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    cases returned
  rename_i control prekey oneTime kem phase
  rw [mem_support_bind_iff] at member
  obtain ⟨prepared, preparedMember, member⟩ := member
  have marker := prepare_challenge setup codec p.challenge control before.beacon.identity prekey oneTime kem raw ciphertext
    read same prepared (PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ preparedMember)
  rcases prepared with _ | pending
  · rw [commitEnv_none e owner control before _ v member] at returned
    cases returned
  dsimp only at member
  unfold groupEnv at member
  rw [marker pending rfl] at member
  dsimp only at member
  split at member
  rotate_left
  · rw [commitEnv_none e owner control before _ v member] at returned
    cases returned
  rw [mem_support_bind_iff] at member
  obtain ⟨readOut, -, member⟩ := member
  split at member
  rotate_left
  · rw [commitEnv_none e owner control before _ v member] at returned
    cases returned
  rename_i j allocated
  rw [support_map] at member
  obtain ⟨committed, committedMember, rfl⟩ := member
  unfold PqxdhDeploymentEnvironment.finishSplitEnv at committedMember
  rw [mem_support_bind_iff] at committedMember
  obtain ⟨staged, -, committedMember⟩ := committedMember
  rw [mem_support_bind_iff] at committedMember
  obtain ⟨_, -, committedMember⟩ := committedMember
  rw [support_pure, Set.mem_singleton_iff] at committedMember
  subst committedMember
  obtain ⟨control', associatedData, kernel, established⟩ := finish_some control before staged bytes returned
  have below : owner < e.native.owners.length := (List.getElem?_eq_some_iff.mp owned).1
  have opened : establishedAt (e.native.owners.set owner (PqxdhBeaconPhase2Publication.finish control before
      staged).2) owner = true := by
    simp only [establishedAt, List.getElem?_set_self below, established]
  refine ⟨_, j, ?_, allocated⟩
  simp only [finishedEnv, hiddenBackend, opened, ↓reduceIte, Option.some_or]

end Challenge

/-! ### The selected accept's token -/

section Token
open PqxdhDeploymentIdealSlots (Coord SlotSpec)
open PqxdhDeploymentIdealSteps (tailCE acceptActive acceptInactive acceptExposed AcceptOut)
open PqxdhServerAuthNative (NativeState)
variable {Reader : Type}

/-- The pending registration that the Server's accept core stores carries the prepared root input's KEM ciphertext (`server_accept` stores the encapsulation's ciphertext, `PqxdhRegistrationInputs.accepted_used`; clearing the root input keeps it). -/
theorem accept_ciphertext (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (final : beaconcrypt_core.pqxdh.ServerState)
    (pending : beaconcrypt_core.pqxdh.PendingServerRegistration)
    (accepted : PqxdhRegistrationJointKemOpaqueCore.accept control binding input = RustM.ok (.Ok (final, pending))) :
    pending.kem_ciphertext = input.ciphertext := by
  obtain ⟨original, sourced, cleared⟩ := PqxdhRegistrationJointKemOpaqueCore.accepted_original control binding input
    (List.Vector.replicate 32 0) final pending accepted
  have used := (PqxdhRegistrationInputs.accepted_used control final _ .Fresh binding _ _ original sourced).2
  have field := congrArg PqxdhRegistrationInputs.UsedInput.kem_ciphertext used
  subst cleared
  exact field

/-- The marker client under `tailCE`: a returned token's pending registration carries the prepared root input's KEM ciphertext. -/
theorem tailCE_client_token (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ)
    (control : beaconcrypt_core.pqxdh.ServerState) (binding : beaconcrypt_core.pqxdh.ServerBinding)
    (input : PqxdhRegistrationJointKemOpaqueClient.Input Reader) (marker : input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : RustM (Option PqxdhServerRelatedRootConsumer.Returned) × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index) (simulateQ PqxdhRegistrationJointKemOpaqueTail.forward
      (PqxdhRegistrationJointKemOpaqueClient.client control binding input))).run s)) :
    ∀ returned, result.1 = RustM.ok (some returned) → returned.pending.kem_ciphertext = input.ciphertext := by
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
  intro returned found
  unfold PqxdhRegistrationJointKemOpaqueClient.client at member
  simp only [simulateQ_bind, StateT.run_bind, auxStep .eraseShared s trivial, pure_bind] at member
  split at member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst member
    cases found
  · rename_i final token accepted
    simp only [simulateQ_bind, StateT.run_bind, rootStep, bind_map_left, mem_support_bind_iff] at member
    obtain ⟨_, _, member⟩ := member
    simp only [auxStep .eraseInput _ trivial, consumeStep, simulateQ_pure, StateT.run_pure, support_pure,
      Set.mem_singleton_iff] at member
    obtain ⟨_, rfl, _, rfl, rfl⟩ := member
    simp only [RustM.ok.injEq, Option.some.injEq] at found
    subst found
    exact accept_ciphertext control binding input final token accepted

/-- The marker tail under `tailCE`: either it returns nothing and the pending tokens are those of the given state, or it returns the given state's session counter and publishes there one token whose pending registration carries the prepared input's KEM ciphertext. -/
theorem tailCE_tail_token (hmac : PqxdhSecretInputKdf.HmacSha512) (index : ℕ) (serverKeyId : Std.U64)
    (publicIdentity : PqxdhJointIdentity.PublicIdentity) (state : PqxdhServerAuthExperiment.GameState KemSK)
    (collected : Option (PqxdhRegistrationJointKemOpaqueClient.Input Reader) × List Pqxdh.Bytes)
    (marker : ∀ input, collected.1 = some input → input.shared = .challenge)
    (s : NativeState KemSK × Option (ℕ × Coord))
    (result : Option ℕ × (NativeState KemSK × Option (ℕ × Coord)))
    (member : result ∈ support ((simulateQ (tailCE hmac index)
      (PqxdhRegistrationJointKemOpaqueTail.tail serverKeyId publicIdentity state collected)).run s)) :
    (result.1 = none ∧ result.2.1.2.pending = state.pending) ∨
      ∃ input token, collected.1 = some input ∧ token.pending.kem_ciphertext = input.ciphertext ∧
        result.1 = some state.sessions ∧
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
    have client := PqxdhDeploymentIdealSessions.tailCE_client_pending hmac index state.server.control
      ⟨PqxdhRootTableInitialization.rootArray publicIdentity.ed25519, serverKeyId⟩ input (marker input found) _
      returned returnedMember
    have carried := tailCE_client_token hmac index state.server.control
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
      refine Or.inr ⟨input, token, rfl, carried token outcome, rfl, ?_⟩
      dsimp only
      rw [client.2]
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, client.2⟩
    · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact Or.inl ⟨rfl, client.2⟩

/-- Item 2's candidate-free suffix returns prepared inputs carrying the supplied ciphertext, under any interpreter. -/
theorem program_ciphertext {E Shared σ ι' : Type} {spec' : OracleSpec ι'}
    (impl : QueryImpl (PqxdhServerRootPreparation.Spec Reader E Shared) (StateT σ (OracleComp spec')))
    (verified : PqxdhServerRootPreparation.Verified Reader) (ephemeral : PqxdhServerRootPreparation.Ephemeral E)
    (ciphertext : PqxdhBeaconPhase2Preparation.Ciphertext) (token : PqxdhRegistrationJointKemOpaqueSuffix.Token)
    (state : σ) (prepared : Option (PqxdhRegistrationJointKemOpaqueSuffix.Prepared Reader E Shared) × σ)
    (member : prepared ∈ support ((simulateQ impl
      (PqxdhRegistrationJointKemOpaqueSuffix.program verified ephemeral ciphertext token)).run state)) :
    ∀ input, prepared.1 = some input → input.ciphertext = ciphertext := by
  intro input found
  have free := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ member
  rw [PqxdhRegistrationJointKemOpaqueSuffix.program, support_map] at free
  obtain ⟨inner, innerMember, same⟩ := free
  rw [found] at same
  rcases inner with _ | original
  · cases same
  simp only [Option.map_some, Option.some.injEq] at same
  subst same
  obtain ⟨-, -, reply⟩ := PqxdhRegistrationJointKemCollected.after_fields verified ephemeral _ original innerMember
  simp only [Option.some.injEq, Prod.mk.injEq] at reply
  exact reply.1.symm

variable {ι : Type} {baseSpec : OracleSpec ι} {Response : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The selected accept on a verified key match: a mark comes only with the active flag, and when it marks a session, either it returns nothing and keeps the pending tokens, or it returns the old session counter and publishes there one token whose pending registration carries the challenge ciphertext. -/
theorem acceptActive_token (seed : PqxdhJointIdentity.IdentitySeed) (challenge : PqxdhKemIndCca.MlKem768Ciphertext)
    (verified : PqxdhServerRootPreparation.Verified Reader) (s : NativeState KemSK) (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptActive setup codec checks seed challenge verified).run s))
    (marked : r.1.2.2.isSome = true) :
    r.1.2.1 = true ∧ ((r.1.1.1 = none ∧ r.2.2.pending = s.2.pending) ∨
      ∃ token, token.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
        r.1.1.1 = some s.2.sessions ∧ r.2.2.pending = Function.update s.2.pending s.2.sessions (some token)) := by
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
    obtain ⟨tailed, -, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    cases marked
  · rw [mem_support_bind_iff] at member
    obtain ⟨prepared, preparedMember, member⟩ := member
    rw [mem_support_bind_iff] at member
    obtain ⟨answer, answerMember, member⟩ := member
    rw [support_pure, Set.mem_singleton_iff] at member
    subst member
    rw [PqxdhDeploymentIdealSteps.liftS, support_liftComp] at preparedMember
    have marker := PqxdhDeploymentIdealKeymatch.program_marker
      (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) verified _ _ _ _ prepared preparedMember
    have carried := program_ciphertext (PqxdhDeploymentIdealSteps.prefixNative setup codec checks seed) verified _ _ _ _
      prepared preparedMember
    refine ⟨rfl, ?_⟩
    rcases tailCE_tail_token setup.hmac s.2.sessions setup.serverKeyId (setup.joint.publicKeys seed) s.2 prepared
      marker (s, none) answer answerMember with kept | ⟨input, token, found, tokenCiphertext, returned, published⟩
    · exact Or.inl kept
    · exact Or.inr ⟨token, by rw [tokenCiphertext, carried input found], returned, published⟩

/-- The selected accept with its encapsulation exposed: a mark comes only with the active flag, and when it marks a session, either it returns nothing and keeps the pending tokens, or it returns the old session counter and publishes there one token whose pending registration carries the challenge ciphertext. -/
theorem acceptExposed_token (seed : PqxdhJointIdentity.IdentitySeed) (chosen : PqxdhLiveKemReservation.Pair KemSK)
    (challenge : PqxdhKemIndCca.MlKem768Ciphertext) (raw : Pqxdh.Bytes) (s : NativeState KemSK)
    (r : AcceptOut × NativeState KemSK)
    (member : r ∈ support ((acceptExposed setup codec checks seed chosen challenge raw).run s))
    (marked : r.1.2.2.isSome = true) :
    r.1.2.1 = true ∧ ((r.1.1.1 = none ∧ r.2.2.pending = s.2.pending) ∨
      ∃ token, token.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray challenge ∧
        r.1.1.1 = some s.2.sessions ∧ r.2.2.pending = Function.update s.2.pending s.2.sessions (some token)) := by
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
      exact acceptActive_token setup codec checks seed challenge verified s r member marked
    · simp only [same, ↓reduceIte] at member
      exact (inactive member).elim

open PqxdhRegistrationJointKemSecondEntry (slotImpl) in
open PqxdhDeploymentIdealKernel (lazyDummy) in
/-- The selected accept in capability form: a mark comes only with the active flag, and when it marks a session, either it returns nothing and keeps the Server's pending tokens, or it returns the old session counter and publishes there one token whose pending registration carries the challenge ciphertext. -/
theorem acceptSelected_token {count : ℕ} (p : Params KemSK count) (raw : Pqxdh.Bytes) (e : EnvState KemSK SplitBk) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnvStep.acceptSelectedEnv setup codec checks p raw).run e),
      v.2.backend.2.2.marks.isSome = true → v.2.backend.2.2.active = true ∧
        ((v.1 = none ∧ v.2.native.shared.2.pending = e.native.shared.2.pending) ∨
          ∃ token, token.pending.kem_ciphertext = PqxdhAcceptedRegistration.ciphertextArray p.challenge ∧
            v.1 = some e.native.shared.2.sessions ∧
            v.2.native.shared.2.pending = Function.update e.native.shared.2.pending e.native.shared.2.sessions
              (some token)) := by
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
  exact acceptExposed_token setup codec checks e.created.seed p.chosen p.challenge raw e.native.shared x.1
    (PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ xMember) marked

end Token

/-! ### The Phase 2 write of the Server build -/

section GenericWrite
open beaconcrypt_core
open PqxdhServerRegistrationPublication (AuxSpec Response ResponseFields responseFields)
variable {Kernel Metadata PeerMetadata Consumed : Type} {ι' : Type} {spec' : OracleSpec ι'}
open PqxdhInitialGenericPublication (State)

/-- A generic Server build's published response is the Phase 2 writer's output on the fields of a candidate that carries the pending registration's KEM ciphertext. -/
def GWritten (write : ResponseFields → Option Pqxdh.Bytes) (pending : pqxdh.PendingServerRegistration) :
    RustM (Option Response × State Kernel Metadata PeerMetadata Consumed) → Prop
  | .ok (some response, _) => ∃ candidate encrypted, candidate.kem_ciphertext = pending.kem_ciphertext ∧
      write (responseFields candidate encrypted) = some response.serialized
  | _ => True

/-- The generic first send and Phase 2 writing publish only the writer's output on the candidate's fields. -/
theorem afterInitialization_written (write : ResponseFields → Option Pqxdh.Bytes)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec')) (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields bytes, bytes ∈ support (aux (.write fields)) → bytes = write fields)
    (pending : pqxdh.PendingServerRegistration) (candidate : pqxdh.ServerRegistrationCandidate)
    (carried : candidate.kem_ciphertext = pending.kem_ciphertext)
    (authenticated : Pqxdh.Bytes) (kernel : Kernel) (metadata : PeerMetadata)
    (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel
      metadata state), GWritten write pending (.ok result) := by
  intro result supported
  unfold PqxdhInitialGenericPublication.afterInitialization at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨advanced, encrypted⟩, _, member⟩ := supported
  rw [mem_support_bind_iff] at member
  obtain ⟨_, _, member⟩ := member
  cases encrypted with
  | none =>
      simp only [support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
  | some encrypted =>
      dsimp only at member
      rw [mem_support_bind_iff] at member
      obtain ⟨serialized, serializedMember, member⟩ := member
      cases serialized with
      | none =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          trivial
      | some serialized =>
          simp only [support_pure, Set.mem_singleton_iff] at member
          subst member
          exact ⟨candidate, encrypted, carried, (writes _ _ serializedMember).symm⟩

/-- The generic candidate admission and first send publish only the writer's output on the candidate's fields. -/
theorem candidate_written (write : ResponseFields → Option Pqxdh.Bytes)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec')) (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields bytes, bytes ∈ support (aux (.write fields)) → bytes = write fields)
    (pending : pqxdh.PendingServerRegistration) (initial : RustM Kernel) (candidate : pqxdh.ServerRegistrationCandidate)
    (carried : candidate.kem_ciphertext = pending.kem_ciphertext)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhInitialGenericBuilder.candidate calls aux initial candidate data metadata state),
      GWritten write pending result := by
  intro result supported
  unfold PqxdhInitialGenericBuilder.candidate at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨valid, _, member⟩ := supported
  by_cases invalid : (!valid) = true
  · simp only [invalid, ite_true, support_pure, Set.mem_singleton_iff] at member
    subst member
    trivial
  · simp only [invalid, Bool.false_eq_true, ite_false, mem_support_bind_iff] at member
    obtain ⟨reserved, _, member⟩ := member
    by_cases unreserved : (!reserved) = true
    · simp only [unreserved, ite_true, support_pure, Set.mem_singleton_iff] at member
      subst member
      trivial
    · simp only [unreserved, Bool.false_eq_true, ite_false] at member
      refine PqxdhDeploymentIdealEnvBuild.continueRustG_shape _ _ _ (fun _ => trivial) trivial (fun kernel inner innerMember => ?_) result member
      split_ifs at innerMember with empty bounded
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial
      · rw [mem_support_bind_iff] at innerMember
        obtain ⟨allocated, _, innerMember⟩ := innerMember
        by_cases unallocated : (!allocated) = true
        · simp only [unallocated, ite_true, support_pure, Set.mem_singleton_iff] at innerMember
          subst innerMember
          trivial
        · simp only [unallocated, Bool.false_eq_true, ite_false] at innerMember
          refine PqxdhDeploymentIdealEnvBuild.continueRustG_shape _ _ _ (fun _ => trivial) trivial (fun binding final finalMember => ?_) inner
            innerMember
          rw [support_map] at finalMember
          obtain ⟨published, publishedMember, rfl⟩ := finalMember
          exact afterInitialization_written write calls aux writes pending candidate carried _ _ metadata state
            published publishedMember
      · simp only [support_pure, Set.mem_singleton_iff] at innerMember
        subst innerMember
        trivial

/-- Every published response of the generic Server build is the Phase 2 writer's output on the fields of a candidate that carries the pending registration's KEM ciphertext (`PqxdhServerAuthNegativeControl.prepare_commit_fields`). -/
theorem genericBuild_written (write : ResponseFields → Option Pqxdh.Bytes)
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec')) (aux : QueryImpl AuxSpec (OracleComp spec'))
    (writes : ∀ fields bytes, bytes ∈ support (aux (.write fields)) → bytes = write fields)
    (initial : RustM Kernel) (pending : pqxdh.PendingServerRegistration)
    (data : Option Pqxdh.Bytes) (metadata : PeerMetadata) (state : State Kernel Metadata PeerMetadata Consumed) :
    ∀ result ∈ support (PqxdhServerAuthSendFactor.genericBuild calls aux initial pending data metadata state),
      GWritten write pending result := by
  intro result supported
  unfold PqxdhServerAuthSendFactor.genericBuild PqxdhInitialGenericBuilder.continueRust at supported
  cases next : pqxdh.server_next_key_id state.control with
  | ok value =>
      rw [next] at supported
      rcases value with key | error
      · dsimp only at supported
        cases prepared : pqxdh.server_prepare_commit state.control pending ⟨state.server.identity, state.identityKeyId⟩
            (if (state.server.peers key).isSome then pqxdh.KeyIdAvailability.Occupied else .Available) with
        | ok value =>
            rw [prepared] at supported
            rcases value with candidate | error
            · have carried := (PqxdhServerAuthNegativeControl.prepare_commit_fields _ _ _ _ candidate prepared).2.2.2.2.1
              exact candidate_written write calls aux writes pending initial candidate carried data metadata state result
                supported
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              subst supported
              trivial
        | fail error =>
            rw [prepared] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            trivial
        | div =>
            rw [prepared] at supported
            simp only [support_pure, Set.mem_singleton_iff] at supported
            subst supported
            trivial
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst supported
        trivial
  | fail error =>
      rw [next] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial
  | div =>
      rw [next] at supported
      simp only [support_pure, Set.mem_singleton_iff] at supported
      subst supported
      trivial

end GenericWrite

section SplitWrite
variable {ι : Type} {baseSpec : OracleSpec ι} {Reader WireResponse : Type}
  (setup : Setup baseSpec KemSK) (codec : Codec Reader WireResponse) (checks : Checks)
open PqxdhServerRegistrationPublication (TailSpec ResponseFields responseFields)

/-- The Phase 2 writer as an interpreter of the Server's response tail into the free tail: a write is answered by the codec's Phase 2 writer, every other callback is forwarded as a query. -/
def writeImpl : QueryImpl TailSpec (OracleComp TailSpec) := fun query =>
  match query with
  | .inr (.write fields) => pure (codec.write2 fields)
  | query => (TailSpec.query query : OracleComp TailSpec _)

/-- The forwarded response tail answers a write with the codec's Phase 2 writer, so it factors through `writeImpl`. -/
theorem tailFwd_writeImpl {n : ℕ} {α : Type} (work : OracleComp TailSpec α) :
    simulateQ (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks) (simulateQ (writeImpl codec) work) =
      simulateQ (PqxdhDeploymentEnvironment.tailFwd (n := n) setup codec checks) work := by
  rw [← QueryImpl.simulateQ_compose]
  congr 1
  funext query
  rcases query with prim | aux
  · simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]
  · cases aux with
    | write fields => rfl
    | _ => simp only [QueryImpl.apply_compose, writeImpl, simulateQ_spec_query]

/-- Every response of the environment's forwarded split build is the Phase 2 writer's output on the fields of a candidate that carries the KEM ciphertext of the session's pending token. -/
theorem buildSplitFwd_written (material : PqxdhDeploymentHiddenLayout.Material)
    (token : PqxdhServerRelatedRootConsumer.Returned) (payload : Option Pqxdh.Bytes)
    (server : PqxdhServerAuthEntryFactor.ServerState) :
    ∀ v ∈ support ((PqxdhDeploymentEnvironment.buildSplitFwd (n := 2) setup codec checks material token payload
        server).run []), ∀ response, (PqxdhServerAuthExperiment.settle server v.1).1 = some response →
      ∃ candidate encrypted, candidate.kem_ciphertext = token.pending.kem_ciphertext ∧
        codec.write2 (responseFields candidate encrypted) = some response.serialized := by
  intro v member response settled
  rw [PqxdhDeploymentSplitFactor.buildSplitFwd_free, StateT.run_map, support_map] at member
  obtain ⟨⟨rust, log⟩, rustMember, rfl⟩ := member
  rw [← tailFwd_writeImpl setup codec checks] at rustMember
  have free := PqxdhDeploymentEnvironmentReal.run_support _ _ _ _ rustMember
  rw [← PqxdhDeploymentSplitFactor.factored_free (writeImpl codec)] at free
  unfold PqxdhServerAuthLoggedSendFactor.factored at free
  rw [support_map] at free
  obtain ⟨inner, innerMember, rfl⟩ := free
  have written := genericBuild_written codec.write2 _ (fun request => writeImpl codec (.inr request))
    (fun fields bytes found => by simpa [writeImpl] using found) _ token.pending payload () _ inner innerMember
  rcases inner with ⟨_ | built, after⟩ | error | _
  · exact absurd settled (by intro same; cases same)
  · have reply : (PqxdhServerAuthExperiment.settle server
        (PqxdhDeploymentHiddenSplit.replaceRaw PqxdhDeploymentHiddenSplit.placeholderKernel <$>
          Prod.map id (PqxdhInitialGenericPublication.native PqxdhServerAuthSendFactor.resolve) <$>
            RustM.ok (some built, after))).1 = some built := rfl
    rw [reply, Option.some.injEq] at settled
    subst settled
    exact written
  · exact absurd settled (by intro same; cases same)
  · exact absurd settled (by intro same; cases same)

/-- The ideal environment's marked build reading the cached material: every response is the Phase 2 writer's output on the fields of a candidate that carries the KEM ciphertext of the session's pending token. -/
theorem buildCached_written (session : ℕ) (payload : Option Pqxdh.Bytes) (coords : PqxdhDeploymentIdealSlots.Coord)
    (e : PqxdhDeploymentEnvironment.EnvState KemSK PqxdhDeploymentIdealSteps.SplitBk) (j : PqxdhRecordLiftInterface.Slot 2)
    (token : PqxdhServerRelatedRootConsumer.Returned) (material : PqxdhDeploymentHiddenLayout.Material)
    (allocated : e.backend.2.1.1 coords = some j) (pending : e.native.shared.2.pending session = some token)
    (cached : e.backend.1 j = some material) :
    ∀ v ∈ support ((PqxdhDeploymentIdealEnv.buildCachedEnv setup codec checks session payload coords).run e),
      ∀ response, v.1 = some response → ∃ candidate encrypted, candidate.kem_ciphertext = token.pending.kem_ciphertext ∧
        codec.write2 (responseFields candidate encrypted) = some response.serialized := by
  intro v member response replied
  rw [PqxdhDeploymentIdealProvenance.buildCached_program setup codec checks session payload coords e j token material
    allocated pending cached, mem_support_bind_iff] at member
  obtain ⟨value, valueMember, member⟩ := member
  rw [mem_support_bind_iff] at member
  obtain ⟨_, -, member⟩ := member
  rw [support_pure, Set.mem_singleton_iff] at member
  subst member
  exact buildSplitFwd_written setup codec checks material token payload _ value valueMember response replied

end SplitWrite

end BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finish_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finish_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finish_some

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.realFinish_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.realFinish_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.collect_answers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.collect_answers

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.prepare_challenge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.prepare_challenge

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.commitEnv_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.commitEnv_none

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finishChallenge_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.finishChallenge_beacon

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.accept_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.accept_ciphertext

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailCE_client_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailCE_client_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailCE_tail_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailCE_tail_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.program_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.program_ciphertext

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptActive_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptActive_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptExposed_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptExposed_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptSelected_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.acceptSelected_token

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.afterInitialization_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.afterInitialization_written

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.candidate_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.candidate_written

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.genericBuild_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.genericBuild_written

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailFwd_writeImpl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.tailFwd_writeImpl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.buildSplitFwd_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.buildSplitFwd_written

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.buildCached_written' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealBeaconFacts.buildCached_written
