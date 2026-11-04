-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeCompletionReceipt
import BeaconcryptCore.Computational.RegistrationServerSdkSource

/-! Actual Server build success retains its moved registration token, current owner pin, exact initial-record capability and supported hash/sign/publication/installation stages. All gates and cuts are derived from the original SDK source bodies. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerReceipt
open PqxdhServerAuthExperiment (Setup Checks Codec)
open RegistrationServerFrontendCompiler (State)
open RegistrationSigningShared (SignReply)
variable {n : Nat} {ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}
private theorem state_pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (state : S) : (pure value : StateT S m X) state = pure (value, state) := rfl

attribute [local irreducible] RegistrationServerSdkSource.complete RegistrationServerSdkSource.fromInitial
  RegistrationWorldServerCompletion.fromInitial RegistrationWorldServerCompletion.publish
  RegistrationWorldServerCompletion.signing RegistrationWorldServerCompletion.install
  RegistrationServerSdkSource.take peer.begin_completion_lookup

/-- A returned successful build has the actual token taken before conversion and the same supported native completion from that consumed state. -/
theorem build_cut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before after : State n)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before)) :
    ∃ token current plaintext,
      RegistrationServerSdkSource.take handle before = (some token, current) ∧ application = some plaintext ∧
      (.ok (some (keyId, bytes)), after) ∈ support
        ((RegistrationServerSdkSource.complete setup codec checks sign encode token plaintext).run current) := by
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  cases taken : RegistrationServerSdkSource.take handle before with
  | mk token current =>
      cases token with
      | none =>
          simp only [taken, support_pure, Set.mem_singleton_iff] at supported
          cases supported
      | some token =>
          cases application with
          | none =>
              simp only [taken, support_pure, Set.mem_singleton_iff] at supported
              cases supported
          | some plaintext => exact ⟨token, current, plaintext, rfl, rfl, by simpa only [taken, StateT.run] using supported⟩

/-- Successful native completion has the same current-pin lookup, actual public size gate and occupancy reply, and a real initial-record capability after the peer reservation. -/
theorem complete_cut (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before after : State n)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.complete setup codec checks sign encode token application).run before)) :
    ∃ lookup requested occupied middle pending,
      peer.begin_completion_lookup before.control before.pin token application = .ok (.Ok lookup) ∧
      lookup.request = .ok requested ∧ RegistrationServerSdkSource.preflight application requested = true ∧
      (occupied, middle) ∈ support
        ((RegistrationServerSdkSource.world (RegistrationWorldServerCompletion.capability (.peerPresent requested))).run before) ∧
      lookup.resume occupied = .ok (.Ok pending) ∧ checks.reservePeer = true ∧
      (.ok (some (keyId, bytes)), after) ∈ support
        ((RegistrationServerSdkSource.fromInitial setup codec sign encode before.control pending).run middle) := by
  simp only [RegistrationServerSdkSource.complete, StateT.run] at supported
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error | div =>
      simp only [looked, support_pure, Set.mem_singleton_iff] at supported
      cases supported
  | ok result => cases result with
    | Err previous =>
        simp only [looked, support_pure, Set.mem_singleton_iff] at supported
        cases supported
    | Ok lookup =>
        simp only [looked] at supported
        cases requested : lookup.request with
        | fail error | div =>
            simp only [requested, support_pure, Set.mem_singleton_iff] at supported
            cases supported
        | ok requestedId =>
            simp only [requested] at supported
            split_ifs at supported with fits
            · rw [mem_support_bind_iff] at supported
              obtain ⟨⟨occupied, middle⟩, queried, continued⟩ := supported
              simp only [RegistrationServerSdkSource.afterOccupancy] at continued
              cases resumed : lookup.resume occupied with
              | fail error | div =>
                  simp only [resumed, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
                  cases continued
              | ok result => cases result with
                | Err previous =>
                    simp only [resumed, state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
                    cases continued
                | Ok pending =>
                    simp only [resumed] at continued
                    split_ifs at continued with reserved
                    · exact ⟨lookup, requestedId, occupied, middle, pending, rfl, requested, fits, queried, resumed, reserved, continued⟩
                    · simp only [state_pure_apply, support_pure, Set.mem_singleton_iff] at continued
                      cases continued
            · simp only [support_pure, Set.mem_singleton_iff] at supported
              cases supported

/-- SDK commit returns exactly the actual native published peer and preserves its complete reached World. -/
theorem fromInitial_cut (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) (before after : State n)
    (keyId : U64) (bytes : Pqxdh.Bytes)
    (supported : (.ok (some (keyId, bytes)), after) ∈ support
      ((RegistrationServerSdkSource.fromInitial setup codec sign encode control pending).run before)) :
    ∃ published world,
      (.ok (.Ok published), world) ∈ support
        ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before.world) ∧
      keyId = published.key_id ∧ bytes = published.encoded ∧
      after = { before with world := world, control := published.control } := by
  rw [RegistrationServerSdkSource.fromInitial, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, first, continued⟩ := supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at first
  obtain ⟨reached, queried, same⟩ := first
  subst middle
  dsimp only at continued
  rcases reached with ⟨reply, world⟩
  cases reply with
  | fail error | div =>
      simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | ok result => cases result with
    | Err previous =>
        simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff] at continued
        cases continued
    | Ok published =>
        simp only [RegistrationServerSdkSource.commit, StateT.run, support_pure, Set.mem_singleton_iff,
          Prod.mk.injEq, RustM.ok.injEq, Option.some.injEq] at continued
        exact ⟨published, world, queried, continued.1.1, continued.1.2, continued.2⟩

/-- The real native World completes the exact source initial-record capability before invoking its response hash/sign/publication controller. -/
theorem record_cut (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf)
    (before after : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (published : peer.PublishedPeer Pqxdh.Bytes)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending).run before)) :
    ∃ hashed middle,
      (.ok (.Ok hashed), middle) ∈ support
        ((simulateQ (RegistrationWorldRecords.handler setup codec)
          (RegistrationServerRecordExecutor.fromInitial pending)).run before) ∧
      (.ok (.Ok published), after) ∈ support
        ((RegistrationWorldServerCompletion.publish sign encode control hashed).run middle) := by
  rw [RegistrationWorldServerCompletion.fromInitial, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, recorded, continued⟩ := supported
  cases reply with
  | fail error =>
      change (.ok (.Ok published), after) ∈ support (pure ((.fail error : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | div =>
      change (.ok (.Ok published), after) ∈ support (pure ((.div : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | ok result => cases result with
    | Err previous =>
        change (.ok (.Ok published), after) ∈ support (pure ((.ok (.Err previous) : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
        simp only [support_pure, Set.mem_singleton_iff] at continued
        cases continued
    | Ok hashed => exact ⟨hashed, middle, recorded, continued⟩

/-- Actual successful peer publication has its real native hash/sign/encode result and the corresponding installation continuation in the same current World. -/
theorem publication_cut (sign : registration.MldsaSigningRequest → ProbComp SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerResponseHash)
    (before after : RegistrationWorldAgreement.State n RegistrationServerRoleBackend.State)
    (published : peer.PublishedPeer Pqxdh.Bytes)
    (supported : (.ok (.Ok published), after) ∈ support
      ((RegistrationWorldServerCompletion.publish sign encode control pending).run before)) :
    ∃ signed middle,
      (.ok (.Ok signed), middle) ∈ support
        ((RegistrationWorldServerCompletion.signing sign encode pending).run before) ∧
      (.ok (.Ok published), after) ∈ support
        ((RegistrationWorldServerCompletion.install control signed).run middle) := by
  rw [RegistrationWorldServerCompletion.publish, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, signed, continued⟩ := supported
  cases reply with
  | fail error =>
      change (.ok (.Ok published), after) ∈ support (pure ((.fail error : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | div =>
      change (.ok (.Ok published), after) ∈ support (pure ((.div : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
      simp only [support_pure, Set.mem_singleton_iff] at continued
      cases continued
  | ok result => cases result with
    | Err previous =>
        change (.ok (.Ok published), after) ∈ support (pure ((.ok (.Err previous) : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)), middle)) at continued
        simp only [support_pure, Set.mem_singleton_iff] at continued
        cases continued
    | Ok response => exact ⟨response, middle, signed, continued⟩

end BeaconcryptCore.Computational.RegistrationNativeServerReceipt
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerReceipt.build_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerReceipt.build_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerReceipt.complete_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerReceipt.complete_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerReceipt.fromInitial_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerReceipt.fromInitial_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerReceipt.record_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerReceipt.record_cut
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerReceipt.publication_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerReceipt.publication_cut
