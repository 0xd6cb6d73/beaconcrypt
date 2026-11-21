-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxHashBoundsCalculus
import BeaconcryptCore.Computational.RegistrationAuthenticationHashBounds
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxAccept
import BeaconcryptCore.Computational.RegistrationNativePlatformCtxSdkHashBounds
/-! Conservative physical shared-hash accounting for actual source Init acceptance: the retained one-request pin allowance plus the retained three-hash authentication allowance (the source authentication now issues at most one hash, the remaining-field signing transcript). Replay lookup, platform reservation, agreement, KEM collection, one-use retention and parse-attempt instrumentation add no shared hash calls. Every optional/failure branch retains its reached full state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformCtxRunner (M)
open RegistrationNativePlatformCtxLeafHashBounds (Bounded)
open RegistrationNativePlatformCtxHashBoundsCalculus
variable {n : Nat} {I KemSK Platform A : Type} {base : OracleSpec I}

/-- The actual incoming authentication hash passes through the full SDK World lens once. -/
theorem hash_bound (bytes : Pqxdh.Bytes) :
    Bounded (RegistrationNativePlatformCtxAcceptAuthentication.hash (n := n) (Platform := Platform) bytes) 1 := by
  apply sdk_world_bound
  exact RegistrationNativePlatformCtxLeafHashBounds.private_work _ 1
    (RegistrationNativePlatformCtxLeafHashBounds.effects (.inr (.hash bytes)))

/-- Deterministic verifications cost no shared hash; the literal hash callback costs one. -/
theorem callback_bound (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (query : RegistrationAuthenticationExecutor.Request) :
    Bounded (RegistrationNativePlatformCtxAcceptAuthentication.callbacks (n := n) (Platform := Platform) crypto verify query)
      (if RegistrationAuthenticationHashBounds.IsHash query then 1 else 0) := by
  cases query with
  | hash request => exact bind_bound _ _ 1 0 (hash_bound _) (fun _ => pure_bound _ _)
  | mldsa request | ed25519 request => exact pure_bound _ _

attribute [local irreducible] RegistrationAuthenticationExecutor.begin
  RegistrationNativePlatformCtxAcceptAuthentication.callbacks

/-- All actual Init authentication paths have at most three shared hash calls, with no successful-authentication premise. The source now issues at most one (the remaining-field signing transcript hash); the exported cap 3 is retained as a conservative allowance. -/
theorem authenticate_bound (setup : Setup base KemSK) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    Bounded (RegistrationNativePlatformCtxAcceptAuthentication.authenticate (n := n) (Platform := Platform) setup verify pin packet) 3 := by
  unfold RegistrationNativePlatformCtxAcceptAuthentication.authenticate
  exact program_bound RegistrationAuthenticationHashBounds.IsHash
    (RegistrationNativePlatformCtxAcceptAuthentication.callbacks setup.source.crypto verify)
    (callback_bound setup.source.crypto verify) _ 3
    ((RegistrationAuthenticationHashBounds.begin_bound pin packet).mono (by decide))

attribute [local irreducible] RegistrationNativePlatformCtxAcceptAuthentication.authenticate

private theorem ordinary_bound (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A) :
    Bounded (RegistrationNativePlatformCtxAcceptFrame.ordinary (Platform := Platform) work) 0 := by
  apply RegistrationNativePlatformCtxLeafHashBounds.private_work
  intro before
  exact RegistrationNativePlatformCtxLeafHashBounds.coins _

private theorem after_authentication_bound (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Bounded (RegistrationNativePlatformCtxAcceptSdk.afterAuthentication (n := n) setup checks reserve representation created packet authenticated) 0 := by
  unfold RegistrationNativePlatformCtxAcceptSdk.afterAuthentication
  apply bind_bound _ _ 0 0 (fun _ _ => isQueryBoundP_pure _ _ _)
  intro used
  cases used with
  | true => exact pure_bound _ _
  | false =>
    apply bind_bound _ _ 0 0 (RegistrationNativePlatformCtxLeafHashBounds.public_work reserve)
    intro admitted
    cases admitted with
    | false => exact pure_bound _ _
    | true =>
      apply bind_bound _ _ 0 0 (ordinary_bound _)
      intro completed
      cases completed with
      | fail error | div => exact pure_bound _ _
      | ok effect => cases effect with
        | ServerComplete accepted => exact ordinary_bound _
        | _ => exact pure_bound _ _

attribute [local irreducible] RegistrationNativePlatformCtxAcceptSdk.afterAuthentication

private theorem after_pin_bound (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) :
    Bounded (RegistrationNativePlatformCtxAcceptSdk.afterPin (n := n) setup checks reserve verify representation created packet result) 3 := by
  cases result with
  | fail error | div => exact pure_bound _ _
  | ok result => cases result with
    | none => exact pure_bound _ _
    | some pin =>
      unfold RegistrationNativePlatformCtxAcceptSdk.afterPin
      apply bind_bound _ _ 3 0 (authenticate_bound setup verify pin packet)
      intro checked
      cases checked with
      | fail error | div => exact pure_bound _ _
      | ok pair =>
        rcases pair with ⟨events, verdict⟩
        cases verdict with
        | Accepted authenticated => exact after_authentication_bound setup checks reserve representation created packet authenticated
        | _ => exact pure_bound _ _

/-- The complete actual SDK acceptance costs one repeated pin hash plus three authentication hashes. -/
theorem sdk_bound (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    Bounded (RegistrationNativePlatformCtxAcceptSdk.accept (n := n) setup checks reserve verify representation created packet) 4 := by
  unfold RegistrationNativePlatformCtxAcceptSdk.accept
  exact bind_bound _ _ 1 3 RegistrationNativePlatformCtxSdkHashBounds.pin
    (after_pin_bound setup checks reserve verify representation created packet)

/-- The actual public accept attempt counter and complete Context/P lens preserve that four-hash bill. -/
theorem accept_bound (setup : Setup base KemSK) (checks : Checks) (reserve : StateT Platform ProbComp Bool)
    (verify : MldsaTranscriptAuth.Verify) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket) :
    RegistrationNativePlatformIdentityCtxHashBoundsCore.ContextBounded
      (RegistrationNativePlatformCtxAccept.accept (n := n) setup checks reserve verify representation created packet) 4 := by
  intro before
  exact RegistrationNativePlatformIdentityCtxHashBoundsCore.server_bound _ 4
    (sdk_bound setup checks reserve verify representation created packet) (RegistrationNativePlatformCtxAccept.increment before)
end BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.hash_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.hash_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.callback_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.callback_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.authenticate_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.authenticate_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.sdk_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.sdk_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformCtxAcceptHashBounds.accept_bound
