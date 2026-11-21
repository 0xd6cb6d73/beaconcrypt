-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationWorldServerCompletion
import BeaconcryptCore.Computational.CborSizing

/-! A concrete adaptive real Server frontend owns its live control, actual current pin, persistent consumed-ID set and one-use native session capabilities. Authentication, real related-root agreement, source replay insertion, exact native response preflight, actual64/76 and signing/publication run on one retained World. Every failure keeps reached hash/sign/coin effects and a consumed registration cannot be recovered by retrying a failed build. Generated-key security is established through the separate hidden-service compiler/hybrids, rather than by relabelling this real execution's concrete kernel imports. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RegistrationWorldServerFrontend
open PqxdhServerAuthExperiment (Setup Codec)
open PqxdhRecordLiftInterface
variable {n : Nat} {Auxiliary Encoded ι KemSK Reader Response : Type} {base : OracleSpec ι}

structure State (n : Nat) (Auxiliary : Type) where
  created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)
  control : pqxdh.ServerState
  pin : session.ServerAuthenticationPin
  consumed : RegistrationReplaySchedule.State
  sessions : List (Option peer.ConsumedRegistration)
  global : RegistrationWorldServerReplay.Global n Auxiliary

def withWorld (state : State n Auxiliary) (world : PqxdhRecordLiftWorld.State n) : State n Auxiliary :=
  { state with global := (state.global.1, { state.global.2 with world := (world, state.global.2.world.2) }) }

def parameters (setup : Setup base KemSK)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) : RegistrationWorldServerReplay.Parameters Auxiliary :=
  ⟨setup.source, setup.hmac, correct, setup.joint, setup.dh, setup.serverDomain, setup.secretOfSeed,
    setup.wiring, created.seed, scalar, native⟩

/-- Core pin selection retains the exact configured Server binding and ML public key without a fingerprint query. -/
noncomputable def initializePin (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize) :
    StateT (RegistrationWorldServerReplay.Global n Auxiliary) ProbComp
      (RustM (core.option.Option session.ServerAuthenticationPin)) := fun before =>
  pure ((do let pin ← registration.begin_server_pin binding publicKey; ok (.Some pin)), before)

/-- The constructor fixes the actual static identity, control and consumed-ID set. Pin creation retains the exact configured key without a primitive callback. -/
noncomputable def start (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (publicKey : Std.Array U8 1952#usize) (auxiliary : Auxiliary) :
    StateT (PqxdhRecordLiftWorld.State n) ProbComp (RustM (core.option.Option (State n Auxiliary))) := fun world => do
  let installed ← (PqxdhRecordLiftWorld.initializeServer created).run world
  let entry : RegistrationWorldServerReplay.Global n Auxiliary :=
    (PqxdhJointDhExtractFamily.empty, ⟨auxiliary, [], [], (installed.2, [])⟩)
  let pinned ← (initializePin ⟨created.server.server.identity, created.server.server.metadata.sender⟩ publicKey).run entry
  pure ((fun option => match option with
      | .None => .None
      | .Some pin => .Some (⟨created, created.control, pin, created.consumed, [], pinned.2⟩ : State n Auxiliary)) <$> pinned.1,
    pinned.2.2.world.1)

/-- Incoming request hashing and Ed25519 checks execute against the current stored pin and update the single World cache. -/
noncomputable def authenticate (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : StateT (State n Auxiliary) ProbComp
      (RustM (List BeaconcryptCore.Refinement.RegistrationAuthenticationFlow.Event × registration.InitAuthentication)) :=
  fun before => (fun result => (result.1, withWorld before result.2)) <$>
    (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.global.2.world.1

noncomputable def agree (setup : Setup base KemSK)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT (State n Auxiliary) ProbComp (RustM agreement.AgreementEffect) := fun before =>
  (fun result => (result.1, { before with consumed := result.2.1, global := result.2.2 })) <$>
    (RegistrationWorldServerReplay.agreement (parameters setup correct scalar native before.created)
      before.control packet authenticated).run (before.consumed, before.global)

/-- Native insertion precedes returning a new handle; no registration root or private kernel is returned. -/
def retain (accepted : agreement.ServerAgreement) : StateT (State n Auxiliary) ProbComp (RustM (Option Nat)) :=
  fun before => match RegistrationReplaySchedule.consume accepted before.consumed with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (.None, history) => pure (.ok none, { before with consumed := history })
  | .ok (.Some consumed, history) =>
      pure (.ok (some before.sessions.length), { before with
        consumed := history
        sessions := before.sessions ++ [some consumed] })

/-- An authenticated packet is looked up against private consumed IDs before the real native agreement. -/
noncomputable def accept (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (packet : registration.InitPacket) : StateT (State n Auxiliary) ProbComp (RustM (Option Nat)) := do
  let checked ← authenticate setup codec route verify packet
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) =>
      let completed ← agree setup correct scalar native packet authenticated
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) => retain accepted
      | .ok _ => pure (.ok none)
  | .ok _ => pure (.ok none)

/-- Take the actual one-use capability before checking any later response gate. -/
def take (handle : Nat) : StateT (State n Auxiliary) ProbComp (Option peer.ConsumedRegistration) := fun before =>
  match before.sessions[handle]? with
  | none => pure (none, before)
  | some none => pure (none, before)
  | some (some consumed) => pure (some consumed, { before with sessions := before.sessions.set handle none })

/-- The full native CBOR response preflight is evaluated before either first-record KDF callback. -/
def responseAdmitted (control : pqxdh.ServerState) (application : Slice U8) : Bool :=
  match pqxdh.server_next_key_id control with
  | .ok (.Ok keyId) => match transport.registration_response_len application.len keyId with
      | .ok (.Some _) => true
      | _ => false
  | _ => false

noncomputable def complete (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) :
    StateT (State n Auxiliary) ProbComp (RustM (Option (Std.U64 × Encoded))) := fun before => do
  let result ← (RegistrationWorldServerCompletion.global setup codec sign encode before.control before.pin consumed application).run
    before.global
  let current := { before with global := result.2 }
  match result.1 with
  | .fail error => pure (.fail error, current)
  | .div => pure (.div, current)
  | .ok (.Err previous) => pure (.ok none, { current with control := previous })
  | .ok (.Ok published) => pure (.ok (some (published.key_id, published.encoded)),
      { current with control := published.control })

/-- Failed preflight, current-pin mismatch, optional callbacks, signing, encoding and peer insertion all leave the handle consumed. -/
noncomputable def build (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (handle : Nat) (application : Slice U8) :
    StateT (State n Auxiliary) ProbComp (RustM (Option (Std.U64 × Encoded))) := do
  let consumed ← take handle
  match consumed with
  | none => pure (.ok none)
  | some consumed => do
      let current ← get
      if responseAdmitted current.control application then complete setup codec sign encode consumed application
      else pure (.ok none)

/-- Pin selection keeps the exact configured fields and the complete native state. -/
theorem initializePin_native (binding : pqxdh.ServerBinding) (publicKey : Std.Array U8 1952#usize)
    (before : RegistrationWorldServerReplay.Global n Auxiliary) :
    (initializePin binding publicKey).run before =
      pure (.ok (.Some (⟨binding, publicKey⟩ : session.ServerAuthenticationPin)), before) := rfl

/-- Native first authentication retains exactly the actual World execution and cache. -/
theorem authenticate_native (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : State n Auxiliary) :
    (authenticate setup codec route verify packet).run before =
      (fun result => (result.1, withWorld before result.2)) <$>
        (RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.global.2.world.1 := rfl

/-- Source insertion always stores the retained native consumed capability and the canonical ID before publication work. -/
theorem retain_fresh (accepted : agreement.ServerAgreement) (before : State n Auxiliary)
    (fresh : before.consumed.contains (absBytes accepted.pending.registration_id.bytes) = false) :
    (retain accepted).run before = pure (.ok (some before.sessions.length),
      { before with
        consumed := before.consumed ++ [absBytes accepted.pending.registration_id.bytes]
        sessions := before.sessions ++ [some ⟨accepted⟩] }) := by
  simp only [retain, StateT.run, RegistrationReplaySchedule.consume_fresh accepted before.consumed fresh]

/-- Reusing an already taken handle reaches no KDF, hash, signing or encoder action. -/
theorem build_taken (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (handle : Nat) (application : Slice U8) (before : State n Auxiliary)
    (taken : before.sessions[handle]? = some none) :
    (build setup codec sign encode handle application).run before = pure (.ok none, before) := by
  have takenStep : (take handle).run before = pure (none, before) := by
    simp only [take, StateT.run, taken]
  rw [build, StateT.run_bind, takenStep]
  simp only [pure_bind, StateT.run_pure]

/-- A reached actual family/native agreement derives freshness from the owned set and retains exactly the authenticated replay identifier. -/
theorem agree_origin (setup : Setup base KemSK)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (native : QueryImpl RegistrationAgreementShared.PrimitiveSpec (StateT Auxiliary ProbComp))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before after : State n Auxiliary) (accepted : agreement.ServerAgreement)
    (supported : (.ok (.ServerComplete accepted), after) ∈ support
      ((agree setup correct scalar native packet authenticated).run before)) :
    after.consumed = before.consumed ∧
      before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false ∧
      absBytes accepted.pending.registration_id.bytes = RegistrationReplaySchedule.identifier authenticated ∧
      accepted.pending.root_key_input.bytes = Std.Array.repeat 192#usize 0#u8 := by
  simp only [agree, StateT.run, support_map] at supported
  obtain ⟨inner, reached, equal⟩ := supported
  have first : inner.1 = .ok (.ServerComplete accepted) := congrArg Prod.fst equal
  have nativeReached : (.ok (.ServerComplete accepted), inner.2) ∈ support
      ((RegistrationWorldServerReplay.agreement (parameters setup correct scalar native before.created)
        before.control packet authenticated).run (before.consumed, before.global)) := by
    simpa only [← first, Prod.mk.eta, StateT.run] using reached
  obtain ⟨history, fresh, identifier, cleared⟩ := RegistrationWorldServerReplay.agreement_origin
    (parameters setup correct scalar native before.created) before.control packet authenticated
    (before.consumed, before.global) inner.2 accepted nativeReached
  exact ⟨((congrArg (fun result => result.2.consumed) equal).symm).trans history, fresh, identifier, cleared⟩

/-- Taking a live session transfers precisely that source capability and clears only that handle. -/
theorem take_live (handle : Nat) (consumed : peer.ConsumedRegistration) (before : State n Auxiliary)
    (live : before.sessions[handle]? = some (some consumed)) :
    (take handle).run before = pure (some consumed, { before with sessions := before.sessions.set handle none }) := by
  simp only [take, StateT.run, live]

/-- Complete-response rejection consumes the session while invoking no KDF, hash, signature or encoder. -/
theorem build_preflight_rejects (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (handle : Nat) (application : Slice U8) (before : State n Auxiliary) (consumed : peer.ConsumedRegistration)
    (live : before.sessions[handle]? = some (some consumed))
    (refused : responseAdmitted before.control application = false) :
    (build setup codec sign encode handle application).run before =
      pure (.ok none, { before with sessions := before.sessions.set handle none }) := by
  rw [build, StateT.run_bind, take_live handle consumed before live]
  simp only [pure_bind]
  change (do let current ← pure ({ before with sessions := before.sessions.set handle none } : State n Auxiliary)
             (if responseAdmitted current.control application then complete setup codec sign encode consumed application
              else pure (.ok none)).run current) = _
  simp only [pure_bind, refused, Bool.false_eq_true, ite_false, StateT.run_pure]

/-- Every actual completion outcome preserves the already consumed IDs and one-use session table, including native rejection and RustM failure. -/
theorem complete_registration_state (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Encoded)
    (consumed : peer.ConsumedRegistration) (application : Slice U8) (before : State n Auxiliary)
    (result : RustM (Option (Std.U64 × Encoded)) × State n Auxiliary)
    (supported : result ∈ support ((complete setup codec sign encode consumed application).run before)) :
    result.2.created = before.created ∧ result.2.pin = before.pin ∧
      result.2.consumed = before.consumed ∧ result.2.sessions = before.sessions := by
  simp only [complete, StateT.run, mem_support_bind_iff] at supported
  obtain ⟨⟨value, afterGlobal⟩, _reached, tail⟩ := supported
  cases value with
  | fail error =>
      simp only [mem_support_pure_iff] at tail
      cases tail
      exact ⟨rfl, rfl, rfl, rfl⟩
  | div =>
      simp only [mem_support_pure_iff] at tail
      cases tail
      exact ⟨rfl, rfl, rfl, rfl⟩
  | ok value =>
      cases value <;> simp only [mem_support_pure_iff] at tail <;>
        cases tail <;> exact ⟨rfl, rfl, rfl, rfl⟩

end BeaconcryptCore.Computational.RegistrationWorldServerFrontend

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.initializePin_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.initializePin_native

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.authenticate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.authenticate_native

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.retain_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.retain_fresh

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.build_taken' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.build_taken

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.agree_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.agree_origin

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.take_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.take_live

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.build_preflight_rejects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.build_preflight_rejects

/-- info: 'BeaconcryptCore.Computational.RegistrationWorldServerFrontend.complete_registration_state' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationWorldServerFrontend.complete_registration_state
