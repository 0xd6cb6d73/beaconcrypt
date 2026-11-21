-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerSdkSource
import BeaconcryptCore.Computational.RegistrationNativePlatformServerCompletion

/-! The logical native Server SDK retains moved-token consumption, replay rejection, complete-message preflight and occupancy, then hashes the actual AD transcript before peer reservation and first-record completion. The response writer runs inside the same Local/platform stack, whose reached effects survive failure. Pure checks and wire are compatibility cases; concrete container representation remains a separate source obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
open RegistrationServerRootCompiler (Local)
variable {n : Nat} {Value Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m]

def liftNative (coins : QueryImpl unifSpec m) (work : StateT (State n) ProbComp Value) :
    StateT (State n) m Value := fun before => simulateQ coins (work.run before)

def world (work : StateT (Local n) m Value) : StateT (State n) m Value := fun before =>
  (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world

private theorem world_run (work : StateT (Local n) m Value) (before : State n) :
    (world work).run before = (fun result => (result.1, { before with world := result.2 })) <$> work.run before.world := rfl

def commit (result : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := fun before =>
  match result with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err previous) => pure (.ok none, { before with control := previous })
  | .ok (.Ok published) => pure (.ok (some (published.key_id, published.encoded)),
      { before with control := published.control })

noncomputable def afterAuthentication (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT (State n) m Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n) m (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else do
    let admitted ← reserve
    if admitted then do
      let completed ← liftNative coins (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) => liftNative coins (RegistrationServerNativeSource.retain created accepted)
      | .ok _ => pure (.ok none)
    else pure (.ok none)

noncomputable def accept (coins : QueryImpl unifSpec m) (setup : Setup base KemSK)
    (codec : Codec Reader Response) (checks : Checks) (reserve : StateT (State n) m Bool)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    StateT (State n) m (RustM (Option Nat)) := do
  let checked ← liftNative coins (RegistrationServerNativeSource.authenticate setup codec route verify created packet)
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication coins setup checks reserve representation created packet authenticated
  | .ok _ => pure (.ok none)

noncomputable def fromInitial (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := do
  let published ← world (RegistrationNativePlatformServerCompletion.fromInitial coins setup codec sign encode control pending)
  commit published

noncomputable def adHash (coins : QueryImpl unifSpec m) (pending : registration.ServerAdHash) :
    StateT (State n) m (RustM (core.result.Result registration.ServerInitialKdf pqxdh.ServerState)) :=
  world (RegistrationNativePlatformServerCompletion.adHash coins pending)

/-- Successful native AD hashing exposes its actual core digest continuation, including the reached platform state. -/
theorem adHash_resume_receipt {Platform : Type}
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (pending : registration.ServerAdHash)
    (before after : State n) (previous next : Platform) (initial : registration.ServerInitialKdf)
    (supported : ((.ok (.Ok initial), after), next) ∈ support
      (((adHash coins pending).run before).run previous)) :
    ∃ digest, pending.resume (.Some digest) = .ok (.Ok initial) := by
  unfold adHash at supported
  rw [world_run, StateT.run_map, support_map] at supported
  obtain ⟨inner, called, same⟩ := supported
  have value : inner.1.1 = .ok (.Ok initial) := congrArg (fun result => result.1.1) same
  have reached : ((.ok (.Ok initial), inner.1.2), inner.2) ∈ support
      (((RegistrationNativePlatformServerCompletion.adHash coins pending).run before.world).run previous) := by
    simpa only [← value, Prod.mk.eta] using called
  exact RegistrationServerAdHash.state_receipt
    (fun request => do
      let digest ← RegistrationNativePlatformServerCompletion.capability coins
        (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))
      pure (.Some (RegistrationAuthenticationShared.digestArray digest)))
    pending before.world inner.1.2 previous inner.2 initial reached

noncomputable def afterOccupancy (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) :=
  match lookup.resume occupied with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.Err _) => pure (.ok none)
  | .ok (.Ok pending) => do
      let hashed ← adHash coins pending
      match hashed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.Err _) => pure (.ok none)
      | .ok (.Ok initial) => do
        let admitted ← reserve
        if admitted then fromInitial coins setup codec sign encode control initial else pure (.ok none)

noncomputable def complete (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := fun before =>
  match peer.begin_completion_lookup before.control before.pin token application with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.Err _) => pure (.ok none, before)
  | .ok (.Ok lookup) => match lookup.request with
    | .fail error => pure (.fail error, before)
    | .div => pure (.div, before)
    | .ok keyId => if RegistrationServerSdkSource.preflight application keyId then do
        let occupied ← (world (RegistrationNativePlatformServerCompletion.capability coins (.peerPresent keyId))).run before
        (afterOccupancy coins setup codec reserve sign encode before.control lookup occupied.1).run occupied.2
      else pure (.ok none, before)

noncomputable def build (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (handle : Nat) (application : Option (Slice U8)) :
    StateT (State n) m (RustM (Option (U64 × Encoded))) := fun before =>
  match RegistrationServerSdkSource.take handle before with
  | (none, current) => pure (.ok none, current)
  | (some token, current) => match application with
    | none => pure (.ok none, current)
    | some application => (complete coins setup codec reserve sign encode token application).run current

private theorem liftNative_id (work : StateT (State n) ProbComp Value) :
    liftNative (QueryImpl.id' unifSpec) work = work := by
  funext before
  exact simulateQ_id' (work.run before)

variable [LawfulMonad m]

/-- Replays skip reservation. Every failed reservation keeps its poststate, and every successful one passes that state into actual agreement and retention. -/
theorem afterAuthentication_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT (State n) m Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : State n) :
    (afterAuthentication coins setup checks reserve representation created packet authenticated).run before =
      if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, before)
      else (reserve.run before >>= fun allocated =>
        if allocated.1 then
          (simulateQ coins
            ((RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run allocated.2) >>=
            fun completed => match completed.1 with
          | .fail error => pure (.fail error, completed.2)
          | .div => pure (.div, completed.2)
          | .ok (.ServerComplete accepted) =>
              (simulateQ coins ((RegistrationServerNativeSource.retain created accepted).run completed.2))
          | .ok _ => pure (.ok none, completed.2))
        else pure (.ok none, allocated.2)) := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · rfl
  · apply bind_congr
    rintro ⟨admitted, allocated⟩
    cases admitted with
    | false => rfl
    | true =>
      apply bind_congr
      rintro ⟨result, current⟩
      cases result with
      | fail error => rfl
      | div => rfl
      | ok effect => cases effect <;> rfl

theorem afterAuthentication_pure (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    afterAuthentication (n := n) (QueryImpl.id' unifSpec) setup checks (pure checks.reserveRegistration)
      representation created packet authenticated =
      RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated := by
  funext before
  change (afterAuthentication (QueryImpl.id' unifSpec) setup checks (pure checks.reserveRegistration)
    representation created packet authenticated).run before =
      (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated).run before
  rw [afterAuthentication_run]
  simp only [StateT.run_pure, pure_bind, simulateQ_id']
  unfold RegistrationServerSdkSource.afterAuthentication StateT.run
  split
  · rfl
  · cases checks.reserveRegistration with
    | false => rfl
    | true =>
      apply bind_congr
      rintro ⟨result, current⟩
      cases result with
      | fail error => rfl
      | div => rfl
      | ok effect => cases effect <;> rfl
theorem accept_pure (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    accept (n := n) (QueryImpl.id' unifSpec) setup codec checks (pure checks.reserveRegistration)
      route verify representation created packet =
      RegistrationServerSdkSource.accept setup codec checks route verify representation created packet := by
  unfold accept RegistrationServerSdkSource.accept
  rw [liftNative_id]
  apply bind_congr
  intro checked
  cases checked with
  | fail error => rfl
  | div => rfl
  | ok result =>
    rcases result with ⟨events, verdict⟩
    cases verdict with
    | Accepted authenticated => exact afterAuthentication_pure setup checks representation created packet authenticated
    | _ => rfl

theorem fromInitial_pure (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    fromInitial (n := n) (QueryImpl.id' unifSpec) setup codec sign
      (fun view => pure (.ok (encode view))) control pending =
      RegistrationServerSdkSource.fromInitial setup codec sign encode control pending := by
  unfold fromInitial RegistrationServerSdkSource.fromInitial
  rw [RegistrationNativePlatformServerCompletion.fromInitial_pure]
  unfold world RegistrationServerSdkSource.world
  apply bind_congr
  intro published
  cases published with
  | fail error => rfl
  | div => rfl
  | ok result => cases result <;> rfl
theorem adHash_pure (pending : registration.ServerAdHash) :
    adHash (n := n) (QueryImpl.id' unifSpec) pending = RegistrationServerSdkSource.adHash pending := by
  unfold adHash RegistrationServerSdkSource.adHash
  rw [RegistrationNativePlatformServerCompletion.adHash_pure]
  rfl

omit [LawfulMonad m] in
/-- Occupancy admission hashes the actual transcript before peer allocation and retains the reached hash state on every outcome. -/
theorem afterOccupancy_run (coins : QueryImpl unifSpec m) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (reserve : StateT (State n) m Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → StateT (Local n) m (RustM (core.option.Option Encoded)))
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) (before : State n) :
    (afterOccupancy coins setup codec reserve sign encode control lookup occupied).run before =
      match lookup.resume occupied with
      | .fail error => pure (.fail error, before)
      | .div => pure (.div, before)
      | .ok (.Err _) => pure (.ok none, before)
      | .ok (.Ok pending) => ((adHash coins pending).run before >>= fun hashed =>
          match hashed.1 with
          | .fail error => pure (.fail error, hashed.2)
          | .div => pure (.div, hashed.2)
          | .ok (.Err _) => pure (.ok none, hashed.2)
          | .ok (.Ok initial) => (reserve.run hashed.2 >>= fun allocated =>
              if allocated.1 then (fromInitial coins setup codec sign encode control initial).run allocated.2
              else pure (.ok none, allocated.2))) := by
  unfold afterOccupancy
  cases lookup.resume occupied with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err previous => rfl
    | Ok pending =>
      apply bind_congr
      rintro ⟨hashed, current⟩
      cases hashed with
      | fail error => rfl
      | div => rfl
      | ok result =>
        cases result with
        | Err previous => rfl
        | Ok initial =>
          apply bind_congr
          rintro ⟨admitted, allocated⟩
          cases admitted <;> rfl
theorem afterOccupancy_pure (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    afterOccupancy (n := n) (QueryImpl.id' unifSpec) setup codec (pure checks.reservePeer) sign
      (fun view => pure (.ok (encode view))) control lookup occupied =
      RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied := by
  unfold afterOccupancy RegistrationServerSdkSource.afterOccupancy
  cases resumed : lookup.resume occupied with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err previous => rfl
    | Ok pending =>
      dsimp only
      rw [adHash_pure]
      apply bind_congr
      intro hashed
      cases hashed with
      | fail error => rfl
      | div => rfl
      | ok result =>
        cases result with
        | Err previous => rfl
        | Ok initial => simp only [pure_bind, fromInitial_pure]
theorem complete_pure (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    complete (n := n) (QueryImpl.id' unifSpec) setup codec (pure checks.reservePeer) sign
      (fun view => pure (.ok (encode view))) token application =
      RegistrationServerSdkSource.complete setup codec checks sign encode token application := by
  funext before
  unfold complete RegistrationServerSdkSource.complete
  cases looked : peer.begin_completion_lookup before.control before.pin token application with
  | fail error => rfl
  | div => rfl
  | ok result =>
    cases result with
    | Err previous => rfl
    | Ok lookup =>
      dsimp only
      cases requested : lookup.request with
      | fail error => rfl
      | div => rfl
      | ok keyId =>
        dsimp only
        cases preflight : RegistrationServerSdkSource.preflight application keyId with
        | false => rfl
        | true =>
          have nativecap :
              (RegistrationNativePlatformServerCompletion.capability (QueryImpl.id' unifSpec) (.peerPresent keyId) :
                StateT (Local n) ProbComp Bool) = RegistrationWorldServerCompletion.capability (.peerPresent keyId) :=
            RegistrationNativePlatformServerCompletion.liftNative_id _
          rw [nativecap]
          simp_rw [afterOccupancy_pure]
          unfold world RegistrationServerSdkSource.world
          rfl
theorem build_pure (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) :
    build (n := n) (QueryImpl.id' unifSpec) setup codec (pure checks.reservePeer) sign
      (fun view => pure (.ok (encode view))) handle application =
      RegistrationServerSdkSource.build setup codec checks sign encode handle application := by
  funext before
  unfold build RegistrationServerSdkSource.build
  cases moved : RegistrationServerSdkSource.take handle before with
  | mk value current =>
    cases value with
    | none => rfl
    | some token =>
      dsimp only
      cases application with
      | none => rfl
      | some application =>
        exact congrArg (fun work : StateT (State n) ProbComp _ => work.run current)
          (complete_pure setup codec checks sign encode token application)
end BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterAuthentication_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterAuthentication_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterAuthentication_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterAuthentication_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.accept_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.accept_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.fromInitial_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.fromInitial_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterOccupancy_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterOccupancy_run

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterOccupancy_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.afterOccupancy_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.complete_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.complete_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.build_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.build_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.adHash_resume_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.adHash_resume_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.adHash_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerSdk.adHash_pure
