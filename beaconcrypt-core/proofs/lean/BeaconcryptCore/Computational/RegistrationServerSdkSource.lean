-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerNativeSource
import BeaconcryptCore.Computational.RegistrationAuthenticationCompiler

/-! The actual SDK Server wrapper retains its outer allocator and moved-capability order. Incoming native authentication updates the shared World first; private replay lookup and registration reservation precede agreement. Building consumes the handle before conversion, pin, size, occupancy or reservation failure. Actual complete response sizing and peer occupancy precede transcript AD hashing; its actual digest completes the binding before peer reservation and the initial-record/signing/publication controller. This is a concrete source interpreter, not a cryptographic replacement of its known kernels. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerSdkSource
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

/-- Registration reservation follows authentication and actual owned replay lookup, before every conversion, KEM or DH primitive. -/
noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) ProbComp (RustM (Option Nat)) := fun before =>
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
  else if checks.reserveRegistration then do
    let completed ← (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before
    match completed.1 with
    | .fail error => pure (.fail error, completed.2)
    | .div => pure (.div, completed.2)
    | .ok (.ServerComplete accepted) => (RegistrationServerNativeSource.retain created accepted).run completed.2
    | .ok _ => pure (.ok none, completed.2)
  else pure (.ok none, before)

noncomputable def accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    StateT (State n) ProbComp (RustM (Option Nat)) := do
  let checked ← RegistrationServerNativeSource.authenticate setup codec route verify created packet
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks representation created packet authenticated
  | .ok _ => pure (.ok none)

/-- Taking the native token precedes every later build gate. -/
def take (handle : Nat) (before : State n) : Option peer.ConsumedRegistration × State n :=
  match before.sessions[handle]? with
  | none => (none, before)
  | some none => (none, before)
  | some (some token) => (some token, { before with sessions := before.sessions.set handle none })

def preflight (application : Slice U8) (keyId : U64) : Bool :=
  match transport.registration_response_len application.len keyId with
  | .ok (.Some _) => true
  | _ => false

def world (work : StateT (Local n) ProbComp Value) : StateT (State n) ProbComp Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

/-- Only native successful publication commits the advanced Server control; every reached World effect remains on failure. -/
def commit (result : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  match result with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err previous) => pure (.ok none, { before with control := previous })
  | .ok (.Ok published) => pure (.ok (some (published.key_id, published.encoded)),
      { before with control := published.control })

noncomputable def fromInitial (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) := do
  let published ← world (RegistrationWorldServerCompletion.fromInitial setup codec sign encode control pending)
  commit published

/-- The response-dependent AD hash updates the same retained World before peer reservation. -/
noncomputable def adHash (pending : registration.ServerAdHash) :
    StateT (State n) ProbComp (RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)) :=
  world (RegistrationWorldServerCompletion.adHash pending)

/-- The reached hash result supplies the digest consumed by the owned initial-record continuation. -/
theorem adHash_receipt (pending : registration.ServerAdHash) (before after : State n)
    (initial : registration.ServerInitialKdf)
    (supported : (.ok (.Ok initial), after) ∈ support ((adHash pending).run before)) :
    ∃ digest, pending.resume (.Some digest) = .ok (.Ok initial) := by
  simp only [adHash, world, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have value : inner.1 = .ok (.Ok initial) := congrArg Prod.fst same
  apply RegistrationWorldServerCompletion.adHash_receipt pending before.world inner.2 initial
  simpa only [StateT.run, ← value, Prod.mk.eta] using called

theorem adHash_history (pending : registration.ServerAdHash) (before after : State n)
    (reply : RegistrationServerAdHash.Result)
    (supported : (reply, after) ∈ support ((adHash pending).run before)) :
    after.world.world.2 = before.world.world.2 := by
  simp only [adHash, world, StateT.run, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have stateEq := congrArg (fun result => result.2.world.world.2) same
  rw [← stateEq]
  exact RegistrationWorldServerCompletion.adHash_history pending before.world inner.2 inner.1 called

noncomputable def afterOccupancy (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) :=
  match lookup.resume occupied with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok pending) => do
    let hashed ← adHash pending
    match hashed with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (.Err _) => pure (.ok none)
    | .ok (.Ok initial) =>
      if checks.reservePeer then fromInitial setup codec sign encode control initial else pure (.ok none)

/-- Complete-message preflight uses the actual key ID returned by the native lookup, before any occupancy effect. -/
noncomputable def complete (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  match peer.begin_completion_lookup before.control before.pin token application with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err _) => pure (.ok none, before)
  | .ok (.Ok lookup) => match lookup.request with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok keyId => if preflight application keyId then do
          let occupied ← (world (RegistrationWorldServerCompletion.capability (.peerPresent keyId))).run before
          (afterOccupancy setup codec checks sign encode before.control lookup occupied.1).run occupied.2
        else pure (.ok none, before)

/-- None is the explicit raw-adapter conversion cancellation, after the moved native handle has been consumed. -/
noncomputable def build (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (State n) ProbComp (RustM (Option (U64 × Pqxdh.Bytes))) := fun before =>
  match take handle before with
  | (none, current) => pure (.ok none, current)
  | (some token, current) => match application with
      | none => pure (.ok none, current)
      | some application => (complete setup codec checks sign encode token application).run current

/-- A replay rejection performs no registration reservation or agreement callback. -/
theorem replay_rejected (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (replayed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true) :
    (afterAuthentication setup checks representation created packet authenticated).run before = pure (.ok none, before) := by
  simp only [afterAuthentication, StateT.run, replayed, ite_true]

/-- A failed outer registration reservation retains the already-reached authentication World and executes no agreement. -/
theorem registration_reservation_rejected (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : State n)
    (fresh : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false)
    (refused : checks.reserveRegistration = false) :
    (afterAuthentication setup checks representation created packet authenticated).run before = pure (.ok none, before) := by
  simp only [afterAuthentication, StateT.run, fresh, refused, Bool.false_eq_true, ite_false]

/-- A live handle yields its actual consumed token and is cleared before later source operations. -/
theorem take_live (handle : Nat) (token : peer.ConsumedRegistration) (before : State n)
    (live : before.sessions[handle]? = some (some token)) :
    take handle before = (some token, { before with sessions := before.sessions.set handle none }) := by
  simp only [take, live]

/-- Raw conversion cancellation clears a live moved handle and performs no primitive, lookup or reservation. -/
theorem build_cancel (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (token : peer.ConsumedRegistration) (before : State n)
    (live : before.sessions[handle]? = some (some token)) :
    (build setup codec checks sign encode handle none).run before =
      pure (.ok none, { before with sessions := before.sessions.set handle none }) := by
  simp only [build, take_live handle token before live, StateT.run]

/-- Retrying a taken handle performs no later source operation and cannot recover its token. -/
theorem build_taken (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before : State n)
    (taken : before.sessions[handle]? = some none) :
    (build setup codec checks sign encode handle application).run before = pure (.ok none, before) := by
  simp only [build, take, taken, StateT.run]

/-- Oversized complete responses stop before occupancy, reservation and both first-record KDFs. -/
theorem complete_preflight_rejected (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State n) (lookup : peer.CompletionLookup)
    (looked : peer.begin_completion_lookup before.control before.pin token application = .ok (.Ok lookup))
    (keyId : U64) (requested : lookup.request = .ok keyId) (refused : preflight application keyId = false) :
    (complete setup codec checks sign encode token application).run before = pure (.ok none, before) := by
  simp only [complete, StateT.run, looked, requested, refused, Bool.false_eq_true, ite_false]

/-- A refused peer reservation retains the already performed AD-hash effect and its failure result. -/
theorem peer_reservation_rejected_keeps_hash (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool)
    (pending : registration.ServerAdHash) (admitted : lookup.resume occupied = .ok (.Ok pending))
    (refused : checks.reservePeer = false) :
    afterOccupancy (n := n) setup codec checks sign encode control lookup occupied = (do
      let hashed ← adHash pending
      match hashed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok _ => pure (.ok none)) := by
  simp only [afterOccupancy, admitted]
  apply bind_congr
  intro result
  cases result with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> simp only [refused, Bool.false_eq_true, ite_false]

/-- Successful complete-message admission executes exactly the actual occupancy capability and its native continuation, with the reached World preserved. -/
theorem complete_admitted (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) (before : State n) (lookup : peer.CompletionLookup)
    (looked : peer.begin_completion_lookup before.control before.pin token application = .ok (.Ok lookup))
    (keyId : U64) (requested : lookup.request = .ok keyId) (admitted : preflight application keyId = true) :
    (complete setup codec checks sign encode token application).run before = (do
      let occupied ← (world (RegistrationWorldServerCompletion.capability (.peerPresent keyId))).run before
      (afterOccupancy setup codec checks sign encode before.control lookup occupied.1).run occupied.2) := by
  simp only [complete, StateT.run, looked, requested, admitted, ite_true]


end BeaconcryptCore.Computational.RegistrationServerSdkSource

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.replay_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.replay_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.registration_reservation_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.registration_reservation_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.take_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.take_live
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.build_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.build_cancel
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.build_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.build_taken
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.complete_preflight_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.complete_preflight_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.peer_reservation_rejected_keeps_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.peer_reservation_rejected_keeps_hash
/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.complete_admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.complete_admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.adHash_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.adHash_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationServerSdkSource.adHash_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerSdkSource.adHash_history
