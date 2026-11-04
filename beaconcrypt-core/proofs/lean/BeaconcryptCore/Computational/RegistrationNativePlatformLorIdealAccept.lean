-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAcceptCore
/-! The corrected OPEN controller relates separate persistent states through individual query and reservation laws, retaining authentication, replay and all failure branches. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformLorIdealAcceptCore (Leaves effects_program agreement_source)
variable {n : Nat} {I KemSK NativePrivate WordPrivate : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (native : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT NativePrivate m))
    (symbolic : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) (StateT WordPrivate m))
    (frame : WordPrivate → NativePrivate) (leaves : Leaves candidate native symbolic frame)
include leaves

private theorem hash_source (request : registration.HashRequest) (before : WordPrivate) :
    Prod.map id frame <$>
      (RegistrationNativePlatformServerReferenceAccept.hash (RegistrationNativePlatformSecretWordOpen.effects symbolic) request).run before =
      (RegistrationNativePlatformServerReferenceAccept.hash (RegistrationNativePlatformServerOpenControl.effects native) request).run (frame before) := by
  simp only [RegistrationNativePlatformServerReferenceAccept.hash,StateT.run_bind,StateT.run_pure,map_bind,map_pure]
  have sourceEq := effects_program candidate native symbolic frame leaves
    ((PqxdhRecordLiftInterface.EnvEffects n).query (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request)))) before
  simp only [simulateQ_spec_query] at sourceEq
  rw [←sourceEq,bind_map_left]
  simp only [Prod.map_def,id_eq]

theorem pin_source (pin : session.ServerAuthenticationPin) (before : WordPrivate) :
    Prod.map id frame <$>
      (RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformSecretWordOpen.effects symbolic) pin).run before =
      (RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformServerOpenControl.effects native) pin).run (frame before) := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  exact OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ frame
    (hash_source candidate native symbolic frame leaves) _ before

variable (setup : Setup base KemSK) (checks : Checks)
    (nativeReserve : StateT NativePrivate m Bool) (wordReserve : StateT WordPrivate m Bool)
    (reserve_source : ∀ before, Prod.map id frame <$> wordReserve.run before = nativeReserve.run (frame before))
include reserve_source
attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.agreement RegistrationNativePlatformServerOpenKernel.agreement

/-- Actual reservation precedes agreement and one-use retention in the same reached private state. -/
theorem after_authentication (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (server : ServerState) (env : Environment) (before : WordPrivate) :
    Prod.map (fun result => ((result.1.1,result.1.2.eval candidate),result.2)) frame <$>
      ((((RegistrationNativePlatformSecretWordOpen.afterAuthentication symbolic wordReserve setup checks packet authenticated).run server).run env).run before) =
      ((((RegistrationNativePlatformServerOpenControl.afterAuthentication native nativeReserve setup checks packet authenticated).run (server.eval candidate)).run env).run (frame before)) := by
  simp only [RegistrationNativePlatformServerOpenControl.afterAuthentication,RegistrationNativePlatformSecretWordOpen.afterAuthentication,
    StateT.run_bind,StateT.run_get,pure_bind]
  simp only [show (server.eval candidate).consumed = server.consumed from rfl]
  by_cases replayed : server.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed,ite_true,StateT.run_pure,map_pure,Prod.map_def]
  · simp only [replayed,Bool.false_eq_true,ite_false,StateT.run_bind,StateT.run_lift,
      bind_pure_comp,map_bind,bind_map_left]
    rw [←reserve_source before,bind_map_left]
    apply bind_congr
    rintro ⟨admitted,reached⟩
    simp only [Prod.map_apply,id_eq]
    cases admitted with
    | false => simp only [Bool.false_eq_true,ite_false,StateT.run_pure,map_pure,Prod.map_def]
    | true =>
      simp only [ite_true,StateT.run_bind,map_bind]
      rw [←agreement_source candidate native symbolic frame leaves setup checks packet authenticated server env reached,bind_map_left]
      apply bind_congr
      rintro ⟨⟨⟨accepted,afterServer⟩,afterEnv⟩,after⟩
      simp only [Prod.map_apply]
      cases accepted with
      | fail error | div => simp only [RegistrationNativeSecretWordServerRoot.restore,StateT.run_pure,map_pure,Prod.map_def]
      | ok reply => cases reply with
        | none => simp only [RegistrationNativeSecretWordServerRoot.restore,Option.map_none,StateT.run_pure,map_pure,Prod.map_def]
        | some ready =>
          simp only [RegistrationNativeSecretWordServerRoot.restore,Option.map_some,
            RegistrationNativePlatformServerReferenceAccept.retain,RegistrationNativePlatformSecretWordOpen.retain,StateT.run]
          have kept := RegistrationNativeSecretWordCheckedServerAccept.retain candidate ready afterServer
          cases actual : RegistrationNativeSecretWordServerMaterial.retain ready afterServer <;>
            simp only [actual,RegistrationNativeSecretWordCheckedServerAccept.retained] at kept
          all_goals rw [←kept]; simp only [StateT.monad_pure_def,StateT.pure,map_pure,Prod.map_def]

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.afterAuthentication RegistrationNativePlatformServerOpenControl.afterAuthentication

/-- Mandatory authentication forwards only its actual successful receipt and retains every rejection. -/
theorem after_pin (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply) (server : ServerState) (env : Environment) (before : WordPrivate) :
    Prod.map (fun result => ((result.1.1,result.1.2.eval candidate),result.2)) frame <$>
      ((((RegistrationNativePlatformSecretWordOpen.afterPin symbolic wordReserve setup checks verify packet current).run server).run env).run before) =
      ((((RegistrationNativePlatformServerOpenControl.afterPin native nativeReserve setup checks verify packet current).run (server.eval candidate)).run env).run (frame before)) := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin RegistrationNativePlatformSecretWordOpen.afterPin
  cases current with
  | fail error | div => simp only [StateT.run_pure,map_pure,Prod.map_def]
  | ok selected => cases selected with
    | none => simp only [StateT.run_pure,map_pure,Prod.map_def]
    | some pin =>
      simp only [StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,map_bind]
      rw [←effects_program candidate native symbolic frame leaves
        (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet) before,bind_map_left]
      apply bind_congr
      rintro ⟨checked,after⟩
      simp only [Prod.map_apply,id_eq]
      cases checked with
      | fail error | div => simp only [StateT.run_pure,map_pure,Prod.map_def]
      | ok pair =>
        rcases pair with ⟨events,authenticated⟩
        cases authenticated
        all_goals first
          | exact after_authentication candidate native symbolic frame leaves setup checks nativeReserve wordReserve reserve_source packet _ server env after
          | simp only [StateT.run_pure,map_pure,Prod.map_def]

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.afterPin RegistrationNativePlatformServerOpenControl.afterPin

/-- Complete corrected OPEN acceptance relates separate persistent states without normalizing word flags or material. -/
theorem accept_source (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (server : ServerState) (env : Environment) (before : WordPrivate) :
    Prod.map (fun result => ((result.1.1,result.1.2.eval candidate),result.2)) frame <$>
      ((((RegistrationNativePlatformSecretWordOpen.accept symbolic wordReserve setup checks verify packet).run server).run env).run before) =
      ((((RegistrationNativePlatformServerOpenControl.accept native nativeReserve setup checks verify packet).run (server.eval candidate)).run env).run (frame before)) := by
  simp only [RegistrationNativePlatformServerOpenControl.accept,RegistrationNativePlatformSecretWordOpen.accept,
    StateT.run_bind,StateT.run_get,pure_bind,StateT.run_lift,bind_pure_comp,bind_map_left,map_bind]
  simp only [show (server.eval candidate).pin = server.pin from rfl]
  rw [←pin_source candidate native symbolic frame leaves server.pin before,bind_map_left]
  apply bind_congr
  rintro ⟨current,after⟩
  simp only [Prod.map_apply,id_eq]
  exact after_pin candidate native symbolic frame leaves setup checks nativeReserve wordReserve reserve_source verify packet current server env after

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.pin_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.pin_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealAccept.accept_source
