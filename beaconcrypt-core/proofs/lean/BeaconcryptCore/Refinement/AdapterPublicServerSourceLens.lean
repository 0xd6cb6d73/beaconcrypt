-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerReservationNative
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The literal full-Native Server lens preserves stateful reservation and native agreement/retention sequencing. It retains all outer owners, KEM pool and parsed-attempt coordinates. The actual SDK admission branch, rather than a separate agreement handler premise, determines whether those operations run. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerSourceLens
open BeaconcryptCore.Computational
variable {n : Nat} {KemSK A B : Type} {mlSource : RegistrationNativeMldsa.Source}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
local notation "ServerM" => StateT (RegistrationServerFrontendCompiler.State n) m
local notation "NativeM" => RegistrationNativePlatformExperiment.M n KemSK mlSource m

omit [LawfulMonad m] in
theorem server_run (work : ServerM A) (before : RegistrationNativeExperiment.State n KemSK mlSource) :
    (RegistrationNativePlatformExperiment.server work).run before =
      (fun result => (result.1, {before with server := result.2})) <$> work.run before.server := rfl

theorem server_pure (value : A) :
    RegistrationNativePlatformExperiment.server (n := n) (KemSK := KemSK) (source := mlSource) (pure value : ServerM A) = pure value := by
  apply StateT.ext
  intro before
  rw [server_run, StateT.run_pure, StateT.run_pure, map_pure]

theorem server_bind (work : ServerM A) (next : A → ServerM B) :
    RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := mlSource) (work >>= next) =
      (RegistrationNativePlatformExperiment.server work >>= fun value => RegistrationNativePlatformExperiment.server (next value)) := by
  apply StateT.ext
  intro before
  rw [server_run, StateT.run_bind, StateT.run_bind]
  simp only [server_run, map_bind, bind_map_left]

theorem server_lift (work : m A) :
    RegistrationNativePlatformExperiment.server (n := n) (KemSK := KemSK) (source := mlSource) (StateT.lift work) =
      (StateT.lift work : NativeM A) := by
  apply StateT.ext
  intro before
  rw [server_run, StateT.run_lift, StateT.run_lift]
  simp only [map_bind, map_pure]

theorem server_native (coins : QueryImpl unifSpec m)
    (work : StateT (RegistrationServerFrontendCompiler.State n) ProbComp A) :
    RegistrationNativePlatformExperiment.server (KemSK := KemSK) (source := mlSource)
      (RegistrationNativePlatformServerSdk.liftNative coins work) =
      RegistrationNativePlatformExperiment.liftNative coins (RegistrationNativeExperiment.server work) := by
  apply StateT.ext
  intro before
  simp only [RegistrationNativePlatformExperiment.server, RegistrationNativePlatformServerSdk.liftNative,
    RegistrationNativePlatformExperiment.liftNative, RegistrationNativeExperiment.server, StateT.run, simulateQ_map]


variable [platform : BeaconcryptCore.Refinement.PublicWrapperPlatform.Platform]
variable {I : Type} {base : OracleSpec I}


noncomputable def roleContinue (coins : QueryImpl unifSpec m) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (effect : RustM agreement.AgreementEffect) : ServerM (RustM (Option Nat)) :=
  match effect with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (.ServerComplete completed) => RegistrationNativePlatformServerSdk.liftNative coins
      (RegistrationServerNativeSource.retain created completed)
  | .ok _ => pure (.ok none)

theorem native_server (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (allocated : m AdapterPublicServerReservationNative.AllocationReply) :
    AdapterPublicServerReservationNative.native (n := n) (mlSource := mlSource) coins setup checks representation created packet authenticated allocated =
      RegistrationNativePlatformExperiment.server (do
        let result ← StateT.lift allocated
        match result.1 with
        | .Err _ => pure (.ok none)
        | .Ok _ => do
          let effect ← RegistrationNativePlatformServerSdk.liftNative coins
            (RegistrationServerNativeSource.agree setup checks representation created packet authenticated)
          roleContinue coins created effect) := by
  unfold AdapterPublicServerReservationNative.native
  rw [server_bind, server_lift]
  apply bind_congr
  intro result
  cases result.1 with
  | Err error => exact (server_pure _).symm
  | Ok allocatedUnit =>
    rw [server_bind, server_native]
    apply bind_congr
    intro effect
    unfold roleContinue
    cases effect with
    | fail error | div => exact (server_pure _).symm
    | ok effect =>
      cases effect <;> first
        | exact (server_pure _).symm
        | exact (server_native coins _).symm

def admitted (reply : AdapterPublicServerReservationNative.AllocationReply) : Bool :=
  match reply.1 with | .Err _ => false | .Ok _ => true

theorem after_authentication (coins : QueryImpl unifSpec m)
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit)
    (allocated : m AdapterPublicServerReservationNative.AllocationReply)
    (before : RegistrationNativeExperiment.State n KemSK mlSource)
    (fresh : before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false) :
    (RegistrationNativePlatformExperiment.server
      (RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks
        (StateT.lift (admitted <$> allocated)) representation created packet authenticated)).run before =
      (AdapterPublicServerReservationNative.native coins setup checks representation created packet authenticated allocated).run before := by
  rw [native_server, server_run, server_run, RegistrationNativePlatformServerSdk.afterAuthentication_run, fresh]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  simp only [StateT.run_lift, StateT.run_bind, bind_map_left, bind_assoc, pure_bind]
  apply bind_congr
  rintro ⟨allocation, history⟩
  cases allocation with
  | Err error => rfl
  | Ok allocatedUnit =>
    simp only [admitted, ↓reduceIte, StateT.run_bind]
    apply bind_congr
    rintro ⟨effect, current⟩
    cases effect with
    | fail error | div => rfl
    | ok effect => cases effect <;> rfl


end BeaconcryptCore.Refinement.AdapterPublicServerSourceLens

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_run

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_pure

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_bind

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_lift

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.server_native

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.native_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.native_server

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerSourceLens.after_authentication
