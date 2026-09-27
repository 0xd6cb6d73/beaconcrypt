import BeaconcryptCore.Computational.PqxdhServerRegistrationPublication

/-!
Functional consumed-input factoring of the actual by-value registration builder. The original full pending value remains an input of every source correspondence theorem. Only four fields occur in prepare/response construction; registration_id and root_key_input have completed their source use before this tail. This is not physical erasure, an equality of shortened pending states, or a new source root.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete PqxdhRefinement
open BeaconcryptCore.Refinement.PqxdhConcreteSession
open BeaconcryptCore.Refinement.ServerTransactionRefinement
open BeaconcryptCore.Computational
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRegistrationInputs
open PqxdhServerRegistrationPublication

/-- Exactly the pending fields read by the source's consuming prepare call. -/
structure UsedInput where
  server_binding : pqxdh.ServerBinding
  beacon_identity_public_key : Std.Array Std.U8 32#usize
  ephemeral_public_key : Std.Array Std.U8 32#usize
  kem_ciphertext : Std.Array Std.U8 1088#usize

def used (pending : pqxdh.PendingServerRegistration) : UsedInput :=
  ⟨pending.server_binding, pending.beacon_identity_public_key,
    pending.ephemeral_public_key, pending.kem_ciphertext⟩

/-- The unchanged extracted body, whose result contains neither discarded pending field. -/
def prepare
  (state : pqxdh.ServerState) (pending : UsedInput)
  (current_server_binding : pqxdh.ServerBinding)
  (key_id_availability : pqxdh.KeyIdAvailability) :
  RustM (core.result.Result pqxdh.ServerRegistrationCandidate
    pqxdh.RegistrationError)
  := do
  if pending.server_binding.identity_key_id =
    current_server_binding.identity_key_id
  then
    let b ←
      core.Array.Insts.CoreCmpPartialEqArray.eq
        core.U8.Insts.CoreCmpPartialEqU8
        pending.server_binding.identity_public_key
        current_server_binding.identity_public_key
    if b
    then
      let r ← pqxdh.server_next_key_id state
      match r with
      | core.result.Result.Ok value =>
        let b1 ←
          match key_id_availability with
          | pqxdh.KeyIdAvailability.Available => ok false
          | pqxdh.KeyIdAvailability.Occupied => ok true
        if b1
        then ok (core.result.Result.Err pqxdh.RegistrationError.KeyIdCollision)
        else
          let a ←
            pqxdh.build_associated_data
              current_server_binding.identity_public_key
              pending.beacon_identity_public_key
          ok (core.result.Result.Ok
            {
              previous_state := state,
              next_state := { last_key_id := value },
              key_id := value,
              beacon_identity_public_key := pending.beacon_identity_public_key,
              server_identity_public_key :=
                current_server_binding.identity_public_key,
              server_identity_key_id := current_server_binding.identity_key_id,
              ephemeral_public_key := pending.ephemeral_public_key,
              kem_ciphertext := pending.kem_ciphertext,
              associated_data := a
            })
      | core.result.Result.Err err => ok (core.result.Result.Err err)
    else ok (core.result.Result.Err pqxdh.RegistrationError.IdentityMismatch)
  else ok (core.result.Result.Err pqxdh.RegistrationError.IdentityMismatch)


theorem prepare_exact (state : pqxdh.ServerState) (pending : pqxdh.PendingServerRegistration)
    (binding : pqxdh.ServerBinding) (available : pqxdh.KeyIdAvailability) :
    prepare state (used pending) binding available =
      pqxdh.server_prepare_commit state pending binding available := rfl


noncomputable def build {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : UsedInput)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    OracleComp TailSpec (RustM (Option Response × State Metadata PeerMetadata Consumed)) :=
  continueRust (pqxdh.server_next_key_id state.control) fun next =>
    match next with
    | .Err _ => pure (ok (none, state))
    | .Ok next =>
        let availability := if (state.server.peers next).isSome then
          pqxdh.KeyIdAvailability.Occupied else .Available
        continueRust (prepare state.control pending
          ⟨state.server.identity, state.identityKeyId⟩ availability) fun prepared =>
          match prepared with
          | .Err _ => pure (ok (none, state))
          | .Ok candidate => candidateTail source candidate root data metadata state

/-- The original full pending value remains on the source side of the exact program equality. -/
theorem build_exact {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    build source (used pending) root data metadata state =
      PqxdhServerRegistrationPublication.build source pending root data metadata state := rfl

/-- Same four read fields imply the same complete computation; unused root-input/RID bytes are not equated. -/
theorem build_used_congr {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (left right : pqxdh.PendingServerRegistration) (fields : used left = used right)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    PqxdhServerRegistrationPublication.build source left root data metadata state =
      PqxdhServerRegistrationPublication.build source right root data metadata state := by
  rw [← build_exact, ← build_exact, fields]


/-- Any actual successful acceptance establishes precisely these fields, retaining its full pending witness. -/
theorem accepted_used (state acceptedState : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (binding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : pqxdh.server_accept state registration status binding coins secrets =
      ok (.Ok (acceptedState, pending))) :
    acceptedState = state ∧ used pending =
      ⟨binding, registration.beacon_identity_public_key, coins.ephemeral_public_key, coins.kem_ciphertext⟩ := by
  obtain ⟨rootResult, registrationId, hroot, hrid, shape⟩ :=
    BeaconcryptCore.Refinement.PqxdhSurface.server_fresh_acceptance_shape state registration binding coins secrets
  cases status with
  | Consumed =>
      simp [pqxdh.server_accept, pqxdh.validate_registration_status] at accepted
  | Fresh =>
      rw [shape] at accepted
      cases rootResult <;> simp only [RustM.ok.injEq, core.result.Result.Ok.injEq,
        Prod.mk.injEq, reduceCtorEq] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩


/-- Root-input mutation during source derivation and earlier RID use do not change the consuming builder. -/
theorem used_completed_fields (pending : pqxdh.PendingServerRegistration)
    (rootInput : pqxdh.RootKeyInput) (registrationId : pqxdh.RegistrationId) :
    used { pending with root_key_input := rootInput, registration_id := registrationId } = used pending := rfl

/-- All returned values and the complete primitive state agree through any subsequent continuation. -/
theorem build_complete {Metadata PeerMetadata Consumed PrimitiveState Result ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl TailSpec (StateT PrimitiveState (OracleComp base)))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState)
    (next : (RustM (Option Response × State Metadata PeerMetadata Consumed) × PrimitiveState) →
      OracleComp base Result) :
    ((simulateQ impl (build source (used pending) root data metadata state)).run primitive >>= next) =
      ((simulateQ impl (PqxdhServerRegistrationPublication.build source pending root data metadata state)).run primitive >>=
        next) := by
  rw [build_exact]

/-- Direct source callbacks retain their entire final state after the by-value pending input is consumed. -/
theorem source_build_exact {Metadata PeerMetadata Consumed PrimitiveState : Type}
    (execute : PrimitiveState → SymmetricRatchetKdfRequest → RatchetKdfResponse × PrimitiveState)
    (sealReply : PrimitiveState → RawCtxSourceSend.SealInput → Option Bytes × PrimitiveState)
    (aux : (query : AuxQuery) → PrimitiveState → AuxSpec.Range query × PrimitiveState)
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : pqxdh.PendingServerRegistration)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed)
    (primitive : PrimitiveState) :
    sourceBuild execute sealReply aux source pending root data metadata state primitive =
      collectState ((simulateQ (functionalImpl execute sealReply aux)
        (build source (used pending) root data metadata state)).run primitive) := by
  rw [build_exact, PqxdhServerRegistrationPublication.source_build_exact]


/-- Prepare is total on the used fields directly; no fictitious pending/root input is constructed. -/
theorem prepare_ok (state : pqxdh.ServerState) (pending : UsedInput)
    (binding : pqxdh.ServerBinding) (availability : pqxdh.KeyIdAvailability) :
    ∃ result, prepare state pending binding availability = ok result :=
  (BeaconcryptCore.PanicFreedom.server_next_key_id_ok state).elim fun next hnext =>
  (BeaconcryptCore.PanicFreedom.build_associated_data_ok binding.identity_public_key
    pending.beacon_identity_public_key).elim fun _ had => by
      cases next <;> cases availability <;>
        by_cases hsender : pending.server_binding.identity_key_id = binding.identity_key_id <;>
        by_cases hidentity : absBytes pending.server_binding.identity_public_key =
          absBytes binding.identity_public_key <;>
        simp [prepare, hsender, array_eq_abs, hidentity, hnext, had]


theorem build_bound {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : UsedInput)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) (kind : CallKind) :
    (build source pending root data metadata state).IsQueryBoundP
      (fun query => callKind query = kind) 1 := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, continueRust]
  cases next with
  | Err => exact isQueryBoundP_pure _ _ _
  | Ok next =>
    obtain ⟨prepared, hprepared⟩ := prepare_ok
      state.control pending ⟨state.server.identity, state.identityKeyId⟩
      (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
    simp only [hprepared]
    cases prepared with
    | Err => exact isQueryBoundP_pure _ _ _
    | Ok candidate => exact candidate_bound source candidate root data metadata state kind


theorem native_build_bounds {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : UsedInput)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    let work := simulateQ nativeAdapter (build source pending root data metadata state)
    work.IsQueryBoundP (fun query => leftPredicate Sum.isLeft query = true) 1 ∧
      (∀ kind, work.IsQueryBoundP
        (fun query => leftPredicate (RawCtxSourceSeal.category kind) query = true) 1) ∧
      (∀ kind, work.IsQueryBoundP (fun query => auxPredicate kind query = true) 1) := by
  exact ⟨native_kdf_bound _ 1 (build_bound source pending root data metadata state .kdf),
    fun kind => native_seal_bound _ 1 (build_bound source pending root data metadata state .seal) kind,
    fun kind => native_aux_bound _ 1 kind (build_bound source pending root data metadata state kind)⟩


theorem build_normal {Metadata PeerMetadata Consumed : Type}
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (pending : UsedInput)
    (root : PqxdhSecretInputKdf.RootOutput) (data : Option Bytes)
    (metadata : PeerMetadata) (state : State Metadata PeerMetadata Consumed) :
    PqxdhServerRegistrationPublication.Normal (build source pending root data metadata state) := by
  obtain ⟨next, hnext⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok state.control
  simp only [build, hnext, continueRust]
  cases next with
  | Err => simp [PqxdhServerRegistrationPublication.Normal]
  | Ok next =>
    obtain ⟨prepared, hprepared⟩ := prepare_ok
      state.control pending ⟨state.server.identity, state.identityKeyId⟩
      (if (state.server.peers next).isSome then pqxdh.KeyIdAvailability.Occupied else .Available)
    simp only [hprepared]
    cases prepared with
    | Err => simp [PqxdhServerRegistrationPublication.Normal]
    | Ok candidate => exact candidate_normal source candidate root data metadata state



/-- The earlier consumed identifier is obtained from actual acceptance, before the pending input's last use. -/
theorem accepted_rid (state acceptedState : pqxdh.ServerState)
    (registration : pqxdh.VerifiedInitKex) (status : pqxdh.RegistrationStatus)
    (binding : pqxdh.ServerBinding) (coins : pqxdh.ServerCoins) (secrets : pqxdh.PqxdhSharedSecrets)
    (pending : pqxdh.PendingServerRegistration)
    (accepted : pqxdh.server_accept state registration status binding coins secrets =
      ok (.Ok (acceptedState, pending))) :
    absBytes pending.registration_id.bytes =
      absBytes registration.beacon_identity_public_key ++ absBytes registration.beacon_one_time_public_key := by
  obtain ⟨rootResult, hroot⟩ := BeaconcryptCore.PanicFreedom.build_root_key_input_ok secrets
  obtain ⟨rid, hrid, hbytes⟩ := registration_id_abs registration
  cases status <;> cases rootResult <;>
    simp only [pqxdh.server_accept, pqxdh.validate_registration_status, hroot, hrid,
      if_true, if_false, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq,
      Prod.mk.injEq, reduceCtorEq] at accepted
  rcases accepted with ⟨rfl, rfl⟩
  simpa only [Pqxdh.ValidInit.rid] using hbytes

end BeaconcryptCore.Computational.PqxdhRegistrationInputs

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.prepare_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.prepare_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_used_congr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_used_congr

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.accepted_used' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.accepted_used

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.used_completed_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.used_completed_fields

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_complete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_complete

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.source_build_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.source_build_exact

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.prepare_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.prepare_ok

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.native_build_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.native_build_bounds

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_normal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.build_normal

/--
info: 'BeaconcryptCore.Computational.PqxdhRegistrationInputs.accepted_rid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRegistrationInputs.accepted_rid
