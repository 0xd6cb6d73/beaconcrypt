-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeStatePreservation

/-! The actual SDK never rotates its configured Server authentication pin. Authentication and agreement mutate only their shared World; replay insertion and build consumption mutate owned fields; publication commits only control. This source invariant includes every refusal and failed poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeServerPinFields
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationServerFrontendCompiler (State)
variable {n : Nat} {ι KemSK Reader Response Value : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationAuthenticationCompiler.program RegistrationAgreementExecutor.server
  RegistrationWorldAgreement.agreement RegistrationWorldServerCompletion.fromInitial
  RegistrationServerNativeSource.authenticate RegistrationServerSdkSource.accept RegistrationWorldAuthentication.begin

private def Keeps (work : StateT (State n) ProbComp Value) : Prop :=
  ∀ before result, result ∈ support (work.run before) → result.2.pin = before.pin

private theorem pure_keeps (value : Value) : Keeps (n := n) (pure value : StateT (State n) ProbComp Value) := by
  intro before result supported
  simp only [StateT.run_pure, mem_support_pure_iff] at supported
  cases supported
  rfl

private theorem bind_keeps {Next : Type} (work : StateT (State n) ProbComp Value)
    (next : Value → StateT (State n) ProbComp Next) (first : Keeps work) (rest : ∀ value, Keeps (n := n) (next value)) :
    Keeps (n := n) (work >>= next) := by
  intro before result supported
  rw [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, reached, continued⟩ := supported
  exact (rest middle.1 middle.2 result continued).trans (first before middle reached)

private theorem world_keeps (work : StateT (RegistrationServerRootCompiler.Local n) ProbComp Value) :
    Keeps (n := n) (RegistrationServerSdkSource.world work) := by
  intro before result supported
  simp only [RegistrationServerSdkSource.world, StateT.run, support_map] at supported
  obtain ⟨inner, _reached, rfl⟩ := supported
  rfl

private theorem raw_world_keeps (before : State n) (work : ProbComp (Value × PqxdhRecordLiftWorld.State n))
    (result : Value × State n)
    (supported : result ∈ support ((fun current => (current.1,
      { before with world := { before.world with world := (current.2, before.world.world.2) } })) <$> work)) :
    result.2.pin = before.pin := by
  rw [support_map] at supported
  obtain ⟨current, _reached, rfl⟩ := supported
  rfl

private theorem authenticate_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    Keeps (n := n) (RegistrationServerNativeSource.authenticate setup codec route verify created packet) := by
  intro before result supported
  apply raw_world_keeps before
    ((RegistrationWorldAuthentication.begin setup codec route verify before.pin packet).run before.world.world.1) result
  simpa only [RegistrationServerNativeSource.authenticate, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.authenticate, RegistrationWorldServerFrontend.withWorld,
    RegistrationServerFrontendCompiler.restore, RegistrationServerFrontendCompiler.erase,
    StateT.run, Functor.map_map, Prod.map_def, id_eq] using supported

private theorem agree_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    Keeps (n := n) (RegistrationServerNativeSource.agree setup checks representation created packet authenticated) := by
  intro before result supported
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, _reached, rfl⟩ := supported
  rfl

private theorem retain_keeps (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement) :
    Keeps (n := n) (RegistrationServerNativeSource.retain (n := n) created accepted) := by
  intro before result supported
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [consumed, map_pure, mem_support_pure_iff] at supported
      cases supported
      rfl
  | ok retained => rcases retained with ⟨token, history⟩; cases token <;>
      simp only [consumed, map_pure, mem_support_pure_iff] at supported <;> cases supported <;> rfl

private theorem after_keeps (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) :
    Keeps (n := n) (RegistrationServerSdkSource.afterAuthentication setup checks representation created packet authenticated) := by
  intro before result supported
  simp only [RegistrationServerSdkSource.afterAuthentication, StateT.run] at supported
  split at supported
  · simp only [mem_support_pure_iff] at supported; cases supported; rfl
  · split at supported
    · rw [mem_support_bind_iff] at supported
      obtain ⟨completed, reached, continued⟩ := supported
      have first := agree_keeps setup checks representation created packet authenticated before completed reached
      cases reply : completed.1 with
      | fail error | div => simp only [reply, mem_support_pure_iff] at continued; cases continued; exact first
      | ok effect =>
          cases effect <;> simp only [reply] at continued
          all_goals first
            | exact (retain_keeps created _ completed.2 result continued).trans first
            | simp only [mem_support_pure_iff] at continued; cases continued; exact first
    · simp only [mem_support_pure_iff] at supported; cases supported; rfl

/-- Full mandatory authentication, replay reservation, native agreement and retention preserve the configured pin. -/
theorem accept_pin (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (before : State n) (result : RustM (Option Nat) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.accept setup codec checks route verify representation created packet).run before)) :
    result.2.pin = before.pin := by
  have keeps : Keeps (n := n) (RegistrationServerSdkSource.accept (n := n) setup codec checks route verify representation created packet) := by
    unfold RegistrationServerSdkSource.accept
    apply bind_keeps _ _ (authenticate_keeps setup codec route verify created packet)
    intro checked
    cases checked with
    | fail error => exact pure_keeps _
    | div => exact pure_keeps _
    | ok checked =>
        rcases checked with ⟨events, verdict⟩
        cases verdict <;> first
          | exact after_keeps setup checks representation created packet _
          | exact pure_keeps _
  exact keeps before result supported

private theorem commit_keeps (reply : RustM (RegistrationWorldServerCompletion.Result Pqxdh.Bytes)) :
    Keeps (n := n) (RegistrationServerSdkSource.commit (n := n) reply) := by
  intro before result supported
  cases reply with
  | fail error | div => simp only [RegistrationServerSdkSource.commit, StateT.run, mem_support_pure_iff] at supported; cases supported; rfl
  | ok outcome => cases outcome <;>
      simp only [RegistrationServerSdkSource.commit, StateT.run, mem_support_pure_iff] at supported <;> cases supported <;> rfl

private theorem initial_keeps (setup : Setup base KemSK) (codec : Codec Reader Response)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (pending : registration.ServerInitialKdf) :
    Keeps (n := n) (RegistrationServerSdkSource.fromInitial setup codec sign encode control pending) :=
  bind_keeps _ _ (world_keeps _) commit_keeps

private theorem occupancy_keeps (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps (n := n) (RegistrationServerSdkSource.afterOccupancy setup codec checks sign encode control lookup occupied) := by
  unfold RegistrationServerSdkSource.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps _
  | ok resumed => cases resumed with
    | Err prior => exact pure_keeps _
    | Ok pending =>
      apply bind_keeps (RegistrationServerSdkSource.adHash pending) _ (world_keeps (RegistrationWorldServerCompletion.adHash pending))
      intro hashed
      cases hashed with
      | fail error | div => exact pure_keeps _
      | ok result => cases result with
        | Err prior => exact pure_keeps _
        | Ok initial =>
          change Keeps (if checks.reservePeer then RegistrationServerSdkSource.fromInitial setup codec sign encode control initial else pure (.ok none))
          split
          · exact initial_keeps setup codec sign encode control initial
          · exact pure_keeps _

private theorem complete_keeps (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps (n := n) (RegistrationServerSdkSource.complete setup codec checks sign encode token application) := by
  intro before result supported
  simp only [RegistrationServerSdkSource.complete, StateT.run] at supported
  repeat' split at supported
  all_goals first
    | simp only [mem_support_pure_iff] at supported; cases supported; rfl
    | rw [mem_support_bind_iff] at supported
      obtain ⟨occupied, reached, continued⟩ := supported
      exact (occupancy_keeps setup codec checks sign encode before.control _ occupied.1 occupied.2 result continued).trans
        (world_keeps _ before occupied reached)

/-- Every actual build success, cancellation and failed publication retains the same configured Server pin. -/
theorem build_pin (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (encode : registration.SignedResponseView → core.option.Option Pqxdh.Bytes)
    (handle : Nat) (application : Option (Slice U8)) (before : State n)
    (result : RustM (Option (U64 × Pqxdh.Bytes)) × State n)
    (supported : result ∈ support ((RegistrationServerSdkSource.build setup codec checks sign encode handle application).run before)) :
    result.2.pin = before.pin := by
  have taken : (RegistrationServerSdkSource.take handle before).2.pin = before.pin := by
    unfold RegistrationServerSdkSource.take
    split <;> rfl
  simp only [RegistrationServerSdkSource.build, StateT.run] at supported
  cases selected : RegistrationServerSdkSource.take handle before with
  | mk token current =>
      have same : current.pin = before.pin := by simpa only [selected] using taken
      cases token with
      | none => simp only [selected, mem_support_pure_iff] at supported; cases supported; exact same
      | some token =>
          cases application with
          | none => simp only [selected, mem_support_pure_iff] at supported; cases supported; exact same
          | some application =>
              simp only [selected] at supported
              exact (complete_keeps setup codec checks sign encode token application current result supported).trans same

end BeaconcryptCore.Computational.RegistrationNativeServerPinFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinFields.accept_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinFields.accept_pin
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeServerPinFields.build_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeServerPinFields.build_pin
