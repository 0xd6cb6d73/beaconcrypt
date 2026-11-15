-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceSeal
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept

/-! The actual corrected source Server never rotates its configured authentication pin. Its world and completion lenses, stateful reservations and complete moved-token build retain that pin through every failure and external poststate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.SDK
open RegistrationNativePlatformCompletionSdk (Completion)
variable {n : Nat} {Platform Value Next Encoded State : Type}

private def serverPin (before : RegistrationServerFrontendCompiler.State n) := before.pin

private def Keeps (cache : State → session.ServerAuthenticationPin)
    (work : StateT State (StateT Platform ProbComp) Value) : Prop :=
  ∀ before previous result, result ∈ support ((work.run before).run previous) → cache result.1.2 = cache before

private theorem pure_keeps (cache : State → session.ServerAuthenticationPin) (value : Value) :
    Keeps (Platform := Platform) cache (pure value) := by
  intro before previous result supported
  simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

private theorem bind_keeps (cache : State → session.ServerAuthenticationPin)
    (work : StateT State (StateT Platform ProbComp) Value)
    (next : Value → StateT State (StateT Platform ProbComp) Next)
    (first : Keeps cache work) (rest : ∀ value, Keeps cache (next value)) : Keeps cache (work >>= next) := by
  intro before previous result supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  exact (rest middle.1.1 middle.1.2 middle.2 result continued).trans (first before previous middle called)

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) : (observe <$> work) before = Prod.map observe id <$> work before := bind_pure_comp _ _
private theorem pure_apply {S X : Type} {m : Type → Type} [Monad m]
    (value : X) (before : S) : (pure value : StateT S m X) before = pure (value, before) := rfl
private theorem bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (work : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (work >>= next) before = (do let middle ← work before; next middle.1 middle.2) := rfl
private theorem get_apply {S : Type} {m : Type → Type} [Monad m] (before : S) :
    (get : StateT S m S) before = pure (before, before) := rfl

/-- The actual SDK World lens retains the configured Server pin through arbitrary local and external effects. -/
private theorem world (work : StateT (RegistrationServerRootCompiler.Local n) (StateT Platform ProbComp) Value)
    : Keeps serverPin (RegistrationNativePlatformServerSdk.world work) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformServerSdk.world, StateT.run, map_apply, support_map] at supported
  obtain ⟨inner, _called, same⟩ := supported
  cases same
  rfl

/-- Successful and failed source publication commit retains the configured Server pin exactly. -/
private theorem commit (published : RustM (RegistrationWorldServerCompletion.Result Encoded)) :
    Keeps (Platform := Platform) (serverPin (n := n)) (RegistrationNativePlatformServerSdk.commit published) := by
  intro before previous result supported
  cases published with
  | fail error | div =>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported
    cases supported
    rfl
  | ok answer => cases answer <;>
    simp only [RegistrationNativePlatformServerSdk.commit, StateT.run, pure_apply,
      support_pure, Set.mem_singleton_iff] at supported <;>
    cases supported <;> rfl

/-- Actual source completion and commit preserve the configured Server pin. -/
private theorem fromInitial (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (initial : registration.ServerInitialKdf) :
    Keeps serverPin (RegistrationNativePlatformCompletionSdk.fromInitial finish control initial) := by
  unfold RegistrationNativePlatformCompletionSdk.fromInitial
  exact bind_keeps serverPin _ _ (world _) (commit)

variable (deriveAd : RegistrationNativePlatformCompletionSdk.AdHash n (StateT Platform ProbComp))

/-- Every occupancy, AD-hash and reservation branch preserves the configured Server pin through the actual source continuation. -/
private theorem afterOccupancy
    (derived : ∀ pending, Keeps serverPin (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverPin reserve) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (lookup : peer.CompletionLookup) (occupied : Bool) :
    Keeps serverPin (RegistrationNativePlatformCompletionSdk.afterOccupancy deriveAd reserve finish control lookup occupied) := by
  unfold RegistrationNativePlatformCompletionSdk.afterOccupancy
  cases lookup.resume occupied with
  | fail error | div => exact pure_keeps serverPin _
  | ok answer => cases answer with
    | Err prior => exact pure_keeps serverPin _
    | Ok pending =>
      apply bind_keeps serverPin _ _ (derived pending)
      intro hashed
      cases hashed with
      | fail error | div => exact pure_keeps serverPin _
      | ok answer => cases answer with
        | Err previous => exact pure_keeps serverPin _
        | Ok initial =>
          apply bind_keeps serverPin _ _ reserved
          intro admitted
          cases admitted with
          | false => exact pure_keeps serverPin _
          | true => exact fromInitial finish control initial

/-- Actual pin, lookup and preflight failures retain the configured Server pin. -/
private theorem afterPin
    (derived : ∀ pending, Keeps serverPin (deriveAd pending)) (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverPin reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverPin (present keyId))
    (finish : Completion n (StateT Platform ProbComp) Encoded)
    (control : pqxdh.ServerState) (token : peer.ConsumedRegistration) (application : Slice U8)
    (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    Keeps serverPin (RegistrationNativePlatformCompletionSdk.afterPin deriveAd reserve present finish control token application pin) := by
  unfold RegistrationNativePlatformCompletionSdk.afterPin
  cases pin with
  | fail error | div => exact pure_keeps serverPin _
  | ok optional => cases optional with
    | none => exact pure_keeps serverPin _
    | some pin =>
      dsimp only
      cases peer.begin_completion_lookup control pin token application with
      | fail error | div => exact pure_keeps serverPin _
      | ok answer => cases answer with
        | Err prior => exact pure_keeps serverPin _
        | Ok lookup =>
          dsimp only
          cases lookup.request with
          | fail error | div => exact pure_keeps serverPin _
          | ok keyId =>
            dsimp only
            split
            · exact bind_keeps serverPin _ _ (presence keyId)
                (afterOccupancy (derived := derived) (deriveAd := deriveAd) reserve reserved finish control lookup)
            · exact pure_keeps serverPin _

private theorem get_keeps : Keeps (serverPin (n := n))
    (get : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) _) := by
  intro before previous result supported
  simp only [StateT.run_get, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  rfl

/-- The complete source SDK control read and pin execution preserve the configured Server pin. -/
private theorem complete
    (derived : ∀ pending, Keeps serverPin (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverPin pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverPin reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverPin (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (token : peer.ConsumedRegistration) (application : Slice U8) :
    Keeps serverPin (RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application) := by
  unfold RegistrationNativePlatformCompletionSdk.complete
  apply bind_keeps serverPin _ _ (get_keeps)
  intro before
  exact bind_keeps serverPin _ _ pinned
    (fun selected => afterPin (derived := derived) (deriveAd := deriveAd) reserve reserved present presence finish before.control token application selected)

private def take (handle : Nat) : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (Option peer.ConsumedRegistration) :=
  fun before => pure (RegistrationServerSdkSource.take handle before)
private theorem take_keeps (handle : Nat) : Keeps (serverPin (n := n)) (take (Platform := Platform) handle) := by
  intro before previous result supported
  simp only [take, StateT.run, pure_apply, support_pure, Set.mem_singleton_iff] at supported
  cases supported
  cases found : before.sessions[handle]? with
  | none => simp only [serverPin, RegistrationServerSdkSource.take, found]
  | some stored => cases stored <;> simp only [serverPin, RegistrationServerSdkSource.take, found]

private theorem build_shape
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (finish : Completion n (StateT Platform ProbComp) Encoded) (handle : Nat) (application : Option (Slice U8)) :
    RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application = (do
      let token ← take handle
      match token, application with
      | some token, some application => RegistrationNativePlatformCompletionSdk.complete deriveAd pin reserve present finish token application
      | _, _ => pure (.ok none)) := by
  funext before previous
  simp only [RegistrationNativePlatformCompletionSdk.build, take, bind_apply, pure_apply, pure_bind, StateT.run]
  cases RegistrationServerSdkSource.take handle before with
  | mk token current => cases token <;> cases application <;> rfl

/-- All actual moved-token build branches preserve the configured Server pin through failed hash, reservation, publication and installation. -/
private theorem build
    (derived : ∀ pending, Keeps serverPin (deriveAd pending))
    (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) (RustM (core.option.Option session.ServerAuthenticationPin)))
    (pinned : Keeps serverPin pin)
    (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (reserved : Keeps serverPin reserve)
    (present : U64 → StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
    (presence : ∀ keyId, Keeps serverPin (present keyId)) (finish : Completion n (StateT Platform ProbComp) Encoded)
    (handle : Nat) (application : Option (Slice U8)) :
    Keeps serverPin (RegistrationNativePlatformCompletionSdk.build deriveAd pin reserve present finish handle application) := by
  rw [build_shape]
  apply bind_keeps serverPin _ _ (take_keeps handle)
  intro token
  cases token with
  | none => exact pure_keeps serverPin _
  | some token => cases application with
    | none => exact pure_keeps serverPin _
    | some application => exact complete (derived := derived) (deriveAd := deriveAd) pin pinned reserve reserved present presence finish token application
end BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.SDK



namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks Codec)
variable {n : Nat} {E Platform Value ι KemSK Reader Response : Type} {base : OracleSpec ι}

private theorem pin_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformSourceBuild.pin coins) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceBuild.pin, StateT.run, SDK.map_apply, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem reserve_keeps (work : StateT Platform ProbComp Value) :
    SDK.Keeps (SDK.serverPin (n := n)) (StateT.lift work) := by
  intro before previous result supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem present_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (keyId : U64) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformCompletionSdk.nativePresent coins keyId) := SDK.world _

private theorem adHash_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (pending : registration.ServerAdHash) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformCompletionSdk.nativeAdHash coins pending) := SDK.world _

/-- Complete actual source response build preserves its configured pin on every failure and success, for arbitrary actual completion and external state. -/
theorem build [primitive : AdapterSealPrimitive.Operations]
    (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (erased : commitment.CommitmentTranscript) (reservePeer : StateT Platform ProbComp Bool)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (handle : Nat) (application : Option (Slice U8)) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option (U64 × alloc.vec.Vec U8)) × RegistrationServerFrontendCompiler.State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceSeal.build coins setup codec view failure allocation erased reservePeer sign helper writer handle application).run before).run previous)) :
    result.1.2.pin = before.pin := by
  apply SDK.build _ (adHash_keeps coins) _ (pin_keeps coins) _ (reserve_keeps reservePeer) _ (present_keeps coins) _ handle application before previous result supported

private theorem native_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp Value)
    (same : ∀ before result, result ∈ support (work.run before) → result.2.pin = before.pin) :
    SDK.Keeps SDK.serverPin (fun before => simulateQ coins (work.run before)) := by
  intro before previous result supported
  have called : result.1 ∈ support (work.run before) := by
    apply OracleComp.support_simulateQ_run'_subset coins (work.run before) previous
    rw [StateT.run'_eq, support_map]
    exact ⟨result, supported, rfl⟩
  exact same before result.1 called

private theorem agree_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)) := by
  apply native_keeps
  intro before result supported
  simp only [RegistrationServerNativeSource.agree, StateT.run, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem retain_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (accepted : agreement.ServerAgreement) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.retain created accepted)) := by
  apply native_keeps
  intro before result supported
  simp only [RegistrationServerNativeSource.retain, RegistrationServerNativeSource.sourceStep,
    RegistrationWorldServerFrontend.retain, RegistrationServerFrontendCompiler.restore, StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume accepted before.consumed with
  | fail error | div =>
      simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported
      cases supported
      rfl
  | ok retained => rcases retained with ⟨token, history⟩; cases token <;>
      simp only [consumed, map_pure, support_pure, Set.mem_singleton_iff] at supported <;> cases supported <;> rfl

private theorem after_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Platform ProbComp Bool) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks (StateT.lift reserve) representation created packet authenticated) := by
  unfold RegistrationNativePlatformServerSdk.afterAuthentication
  apply SDK.bind_keeps SDK.serverPin _ _ SDK.get_keeps
  intro before
  split
  · exact SDK.pure_keeps _ _
  · apply SDK.bind_keeps _ _ _ (reserve_keeps reserve)
    intro admitted
    cases admitted with
    | false => exact SDK.pure_keeps _ _
    | true =>
      apply SDK.bind_keeps _ _ _ (agree_keeps coins setup checks representation created packet authenticated)
      intro completed
      cases completed with
      | fail error | div => exact SDK.pure_keeps _ _
      | ok effect => cases effect <;> first
          | exact SDK.pure_keeps _ _
          | exact retain_keeps coins created _

attribute [local irreducible] RegistrationWorldAuthentication.begin RegistrationWorldAuthentication.program
  RegistrationAuthenticationShared.begin

private theorem authentication_keeps (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route verify pin packet) := by
  intro before previous result supported
  simp only [RegistrationNativePlatformSourceAccept.authenticate, StateT.run, SDK.map_apply, support_map] at supported
  obtain ⟨inner, _possible, same⟩ := supported
  cases same
  rfl

private theorem after_pin (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) :
    SDK.Keeps (SDK.serverPin (n := n)) (RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks (StateT.lift reserve) route verify representation created packet pin) := by
  unfold RegistrationNativePlatformSourceAccept.afterPin
  cases pin with
  | fail error | div => exact SDK.pure_keeps _ _
  | ok optional => cases optional with
    | none => exact SDK.pure_keeps _ _
    | some pin =>
      apply SDK.bind_keeps _ _ _ (authentication_keeps coins setup codec route verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact SDK.pure_keeps _ _
      | ok answer =>
        rcases answer with ⟨events, status⟩
        cases status with
        | Accepted authenticated => exact after_keeps coins setup checks reserve representation created packet authenticated
        | _ => exact SDK.pure_keeps _ _

/-- Recomputed pin, mandatory source authentication, replay, stateful reservation and token retention never rotate the configured Server pin. -/
theorem accept (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : Setup base KemSK) (codec : Codec Reader Response)
    (checks : Checks) (reserve : StateT Platform ProbComp Bool) (route : RawCtxServerRouting.SenderDecoder) (verify : MldsaTranscriptAuth.Verify)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : RegistrationServerFrontendCompiler.State n) (previous : Platform)
    (result : (RustM (Option Nat) × RegistrationServerFrontendCompiler.State n) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformSourceAccept.accept coins setup codec checks reserve route verify representation created packet).run before).run previous)) :
    result.1.2.pin = before.pin := by
  apply SDK.bind_keeps SDK.serverPin _ _ (pin_keeps coins) (after_pin coins setup codec checks reserve route verify representation created packet) before previous result supported
end BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.build

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerPinFields.accept
