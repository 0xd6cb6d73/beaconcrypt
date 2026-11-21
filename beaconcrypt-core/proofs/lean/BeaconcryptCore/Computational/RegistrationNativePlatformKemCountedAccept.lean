-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedProgram
import BeaconcryptCore.Computational.RegistrationNativeKemCountedServerSource
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaProgram
import BeaconcryptCore.Computational.RegistrationNativePlatformSourceAccept

/-! Actual stateful Server pin recomputation, mandatory authentication and reservation precede the same counted indexed agreement program. No private KEM row is present in the executable client; all failed prefixes retain their actual native/platform poststates. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept
open PqxdhServerAuthExperiment (Setup Codec Checks)
open RegistrationNativeKemServerState (State ofNative toNative)
open RegistrationNativeKemCountedProgram (Spec)
open PqxdhLiveKemBirth (Pool)
variable {n : Nat} {ι KemSK Platform Value Reader Response : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Client" => State n source
local notation "Front" => RegistrationServerFrontendCompiler.State n
local notation "M" => RegistrationNativePlatformKemCountedProgram.M KemSK Platform
open RegistrationNativePlatformMldsaProgram (coins)

def server (work : StateT Front M Value) : StateT Client M Value := fun before =>
  (fun result => (result.1, { before with server := result.2 })) <$> work.run before.server

def ordinaryServer (work : StateT Front (StateT Platform ProbComp) Value) : StateT Client M Value :=
  server (RegistrationNativePlatformKemCountedProgram.lift work)

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (_packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : StateT Client M (RustM (Option Nat)) := do
  let before ← get
  if before.server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else do
    let admitted ← ordinaryServer reserve
    if admitted then do
      let completed ← RegistrationNativePlatformKemCountedProgram.inject
        (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated)
      match completed with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (.ServerComplete accepted) =>
          ordinaryServer (RegistrationNativePlatformServerSdk.liftNative coins (RegistrationServerNativeSource.retain created accepted))
      | .ok _ => pure (.ok none)
    else pure (.ok none)

noncomputable def afterPin (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin)) : StateT Client M (RustM (Option Nat)) :=
  match pin with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => do
      let checked ← ordinaryServer (RegistrationNativePlatformSourceAccept.authenticate coins setup codec route source.verify pin packet)
      match checked with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks reserve representation created packet authenticated
      | .ok _ => pure (.ok none)

noncomputable def accept (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) : StateT Client M (RustM (Option Nat)) := do
  let pin ← ordinaryServer (RegistrationNativePlatformSourceBuild.pin coins)
  afterPin setup codec checks reserve route representation created packet pin

private theorem agree_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) (before : Client) (pool : Pool KemSK) :
    RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
      (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated) before pool =
      (fun result => ((result.1, { before with server := result.2 }), pool)) <$>
        (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before.server := by
  have law := congrArg (fun distribution => (fun result => ((result.1, result.2.1), result.2.2)) <$> distribution)
    (RegistrationNativeKemCountedServerSource.agree_source setup checks representation created packet authenticated (toNative before pool))
  simp only [RegistrationNativeKemCountedTrusted.execute, RegistrationNativeKemCountedTrusted.project,
    RegistrationNativeKemCountedTrusted.arrange, RegistrationNativeExperiment.server, StateT.run, Functor.map_map,
    ofNative, toNative, Prod.map, id_eq] at law ⊢
  change id <$> RegistrationNativeKemCountedProgram.runState setup.baseImpl setup.kem
    (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated) before pool = _ at law
  rw [id_map] at law
  exact law

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (function : A → B) (work : StateT S m A) (before : S) :
    (function <$> work) before = Prod.map function id <$> work before := StateT.run_map function work before

private theorem server_run (setup : Setup base KemSK) (work : StateT Front M Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup (server work) before previous pool =
      (fun result => (((result.1.1.1, { before with server := result.1.1.2 }), result.1.2), result.2)) <$>
        RegistrationNativePlatformKemCountedProgram.runState setup work before.server previous pool := by
  simp only [RegistrationNativePlatformKemCountedProgram.runState, server, StateT.run, map_apply,
    RegistrationNativeKemCountedProgram.evaluate, simulateQ_map]
  rfl

private theorem ordinary_server_run (setup : Setup base KemSK) (work : StateT Front (StateT Platform ProbComp) Value)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup (ordinaryServer work) before previous pool =
      (fun result => (((result.1.1, { before with server := result.1.2 }), result.2), pool)) <$> ((work.run before.server).run previous) := by
  rw [ordinaryServer, server_run, RegistrationNativePlatformKemCountedProgram.run_lift, Functor.map_map]

private theorem injected_agree_run (setup : Setup base KemSK) (checks : Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup
      (RegistrationNativePlatformKemCountedProgram.inject (RegistrationNativeKemCountedServerPrimitive.agree setup checks representation created authenticated))
      before previous pool =
      (fun result => (((result.1, { before with server := result.2 }), previous), pool)) <$>
        (RegistrationServerNativeSource.agree setup checks representation created packet authenticated).run before.server := by
  rw [RegistrationNativePlatformKemCountedProgram.run_inject, agree_run, Functor.map_map]

private theorem run_get (setup : Setup base KemSK) (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup get before previous pool =
      pure (((before, before), previous), pool) := rfl

/-- Replay, allocation, agreement failure and token retention have exactly the original source/platform poststates; only the private indexed capability is reified. -/
theorem afterAuthentication_source (setup : Setup base KemSK) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup
      (afterAuthentication setup checks reserve representation created packet authenticated) before previous pool =
      (fun result => (((result.1.1, { before with server := result.1.2 }), result.2), pool)) <$>
        (((RegistrationNativePlatformServerSdk.afterAuthentication coins setup checks reserve representation created packet authenticated).run before.server).run previous) := by
  rw [afterAuthentication, RegistrationNativePlatformKemCountedProgram.run_bind, run_get, pure_bind,
    RegistrationNativePlatformServerSdk.afterAuthentication_run]
  split
  · rw [RegistrationNativePlatformKemCountedProgram.run_pure]
    rfl
  · rw [RegistrationNativePlatformKemCountedProgram.run_bind, ordinary_server_run]
    simp only [map_bind, bind_map_left, StateT.run_bind]
    apply bind_congr
    rintro ⟨⟨allocated, current⟩, platform⟩
    cases allocated with
    | false =>
        simp only [Bool.false_eq_true, ite_false]
        rw [RegistrationNativePlatformKemCountedProgram.run_pure]
        rfl
    | true =>
        simp only [ite_true]
        rw [RegistrationNativePlatformKemCountedProgram.run_bind, injected_agree_run setup checks representation created packet]
        simp only [map_bind, bind_map_left, RegistrationNativePlatformMldsaProgram.lift_coins, StateT.run_lift, bind_pure_comp,
          StateT.run_bind]
        apply bind_congr
        rintro ⟨result, afterAgreement⟩
        cases result with
        | fail error =>
            rw [RegistrationNativePlatformKemCountedProgram.run_pure]
            rfl
        | div =>
            rw [RegistrationNativePlatformKemCountedProgram.run_pure]
            rfl
        | ok effect =>
            cases effect <;> dsimp only <;> first
              | rw [ordinary_server_run]; simp only [RegistrationNativePlatformServerSdk.liftNative, StateT.run, RegistrationNativePlatformMldsaProgram.lift_coins]
              | rw [RegistrationNativePlatformKemCountedProgram.run_pure]; rfl

/-- Actual mandatory authentication runs after the actual recomputed pin and before the indexed agreement, including all failed authentication prefixes. -/
theorem afterPin_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (pin : RustM (core.option.Option session.ServerAuthenticationPin))
    (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup
      (afterPin setup codec checks reserve route representation created packet pin) before previous pool =
      (fun result => (((result.1.1, { before with server := result.1.2 }), result.2), pool)) <$>
        (((RegistrationNativePlatformSourceAccept.afterPin coins setup codec checks reserve route source.verify representation created packet pin).run before.server).run previous) := by
  unfold afterPin RegistrationNativePlatformSourceAccept.afterPin
  cases pin with
  | fail error =>
      rw [RegistrationNativePlatformKemCountedProgram.run_pure]
      rfl
  | div =>
      rw [RegistrationNativePlatformKemCountedProgram.run_pure]
      rfl
  | ok value =>
      cases value with
      | none =>
          rw [RegistrationNativePlatformKemCountedProgram.run_pure]
          rfl
      | some pin =>
          rw [RegistrationNativePlatformKemCountedProgram.run_bind, ordinary_server_run]
          simp only [StateT.run_bind, map_bind, bind_map_left]
          apply bind_congr
          rintro ⟨⟨checked, current⟩, platform⟩
          cases checked with
          | fail error =>
              rw [RegistrationNativePlatformKemCountedProgram.run_pure]
              rfl
          | div =>
              rw [RegistrationNativePlatformKemCountedProgram.run_pure]
              rfl
          | ok output =>
              rcases output with ⟨events, outcome⟩
              cases outcome <;> dsimp only <;> first
                | exact afterAuthentication_source setup checks reserve representation created packet _ _ _ _
                | rw [RegistrationNativePlatformKemCountedProgram.run_pure]; rfl

/-- The complete actual source acceptance controller has the same native, platform, private-row and draw-cost result. -/
theorem accept_source (setup : Setup base KemSK) (codec : Codec Reader Response) (checks : Checks)
    (reserve : StateT Front (StateT Platform ProbComp) Bool) (route : RawCtxServerRouting.SenderDecoder)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (packet : registration.InitPacket) (before : Client) (previous : Platform) (pool : Pool KemSK) :
    RegistrationNativePlatformKemCountedProgram.runState setup
      (accept setup codec checks reserve route representation created packet) before previous pool =
      (fun result => (((result.1.1, { before with server := result.1.2 }), result.2), pool)) <$>
        (((RegistrationNativePlatformSourceAccept.acceptWith (RegistrationNativePlatformSourceBuild.pin coins)
          coins setup codec checks reserve route source.verify representation created packet).run before.server).run previous) := by
  rw [accept, RegistrationNativePlatformKemCountedProgram.run_bind, ordinary_server_run,
    RegistrationNativePlatformSourceAccept.acceptWith_run]
  simp only [StateT.run_bind, map_bind, bind_map_left]
  apply bind_congr
  rintro ⟨⟨pin, current⟩, platform⟩
  exact afterPin_source setup codec checks reserve route representation created packet pin _ _ _

end BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.afterAuthentication_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.afterAuthentication_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.afterPin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.afterPin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformKemCountedAccept.accept_source
