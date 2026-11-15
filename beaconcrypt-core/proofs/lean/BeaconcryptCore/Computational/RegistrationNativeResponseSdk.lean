-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeResponseWorld
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual SDK build success retains the current Server pin's public identity through moved-token consumption, response sizing, occupancy, reservation, both record KDFs, mandatory signing and publication. Failed branches cannot produce a success receipt. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeResponseSdk
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem commit_success (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes))
    (before after : State n) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support ((RegistrationServerSdkSource.commit result).run before)) :
    ∃ published, result = .ok (.Ok published) ∧ published.encoded = bytes := by
  cases result with
  | fail error | div => simp [StateT.run, RegistrationServerSdkSource.commit] at supported
  | ok result => cases result with
    | Err previous => simp [StateT.run, RegistrationServerSdkSource.commit] at supported
    | Ok published =>
        simp only [StateT.run, RegistrationServerSdkSource.commit, support_pure,
          Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at supported
        exact ⟨published, rfl, supported.1.2.symm⟩

/-- A successful SDK post-root response encodes the identity of its exact admitted candidate. -/
theorem fromInitial_identity (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (before after : State n) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.fromInitial setup codec sign encode control pending).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode pending.candidate.server_identity_public_key bytes := by
  simp only [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨result, reached, continued⟩ := supported
  obtain ⟨published, actual, encoded⟩ := commit_success result.1 result.2 after keyId bytes continued
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at reached
  obtain ⟨inner, innerSupport, returned⟩ := reached
  have same : inner.1 = .ok (.Ok published) := (congrArg Prod.fst returned).trans actual
  have publicResult := RegistrationNativeResponseWorld.fromInitial_identity setup codec sign encode control pending
    published before.world inner.2 (by rw [← same]; exact innerSupport)
  rw [← encoded]
  exact publicResult

/-- Successful occupancy/reservation reaches only an initializer admitted under the actual lookup pin. -/
theorem after_identity (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (before after : State n) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode lookup.pin.binding.identity_public_key bytes := by
  unfold RegistrationServerSdkSource.afterOccupancy at supported
  cases resumed : lookup.resume occupied with
  | fail error | div => simp [resumed] at supported
  | ok result => cases result with
    | Err previous => simp [resumed] at supported
    | Ok pending =>
        rw [resumed] at supported
        dsimp only at supported
        simp only [StateT.run_bind, mem_support_bind_iff] at supported
        obtain ⟨⟨hashed, middle⟩, reached, continued⟩ := supported
        cases hashed with
        | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at continued
        | ok hashed => cases hashed with
          | Err previous => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
          | Ok initial =>
              dsimp only at continued
              split at continued
              · have selected : registration.begin_server_completion lookup.control lookup.pin
                    (if occupied then .Occupied else .Available) lookup.registration.agreement lookup.application =
                      .ok (.Ok pending) := by
                  rw [← BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_resume]
                  exact resumed
                obtain ⟨digest, completed⟩ :=
                  RegistrationServerSdkSource.adHash_receipt pending before middle initial reached
                have identity := RegistrationNativeResponseCandidate.initial_identity _ _ _ _ _ _
                  ⟨pending, digest, selected, completed⟩
                rw [← identity]
                exact fromInitial_identity setup codec sign encode control initial middle after keyId bytes continued
              · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued

/-- Actual complete-message sizing and occupancy preserve the Server identity selected by the current SDK pin. -/
theorem complete_identity (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8)
    (before after : State n) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode before.pin.binding.identity_public_key bytes := by
  obtain ⟨next, nextRun⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok before.control
  cases next with
  | Err previous =>
      simp [StateT.run, RegistrationServerSdkSource.complete, peer.begin_completion_lookup, nextRun] at supported
  | Ok allocated =>
      have looked := BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_begin_next
        before.control before.pin token application allocated nextRun
      simp only [StateT.run, RegistrationServerSdkSource.complete, looked,
        BeaconcryptCore.Refinement.PeerOwnership.completion_lookup_request] at supported
      split at supported
      · simp only [mem_support_bind_iff] at supported
        obtain ⟨occupied, _reached, continued⟩ := supported
        exact after_identity setup codec checks sign encode before.control _ occupied.1 occupied.2 after keyId bytes continued
      · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq,
          false_and] at supported

/-- Successful actual moved-token build bytes identify the original SDK Server pin, including every earlier cancellation gate. -/
theorem build_identity (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8))
    (before after : State n) (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before)) :
    RegistrationNativeResponseIdentity.EncodedFrom encode before.pin.binding.identity_public_key bytes := by
  unfold StateT.run RegistrationServerSdkSource.build RegistrationServerSdkSource.take at supported
  cases found : before.sessions[handle]? with
  | none => simp [found] at supported
  | some value => cases value with
    | none => simp [found] at supported
    | some token =>
        rw [found] at supported
        dsimp only at supported
        cases application with
        | none => simp at supported
        | some application =>
          exact complete_identity setup codec checks sign encode token application
            { before with sessions := before.sessions.set handle none } after keyId bytes supported

end BeaconcryptCore.Computational.RegistrationNativeResponseSdk
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseSdk.fromInitial_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseSdk.fromInitial_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseSdk.after_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseSdk.after_identity

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseSdk.complete_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseSdk.complete_identity
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeResponseSdk.build_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeResponseSdk.build_identity
