-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordNoCreateLocal
import BeaconcryptCore.Computational.RegistrationNativeSecretWordTargetPhaseCore
/-! Before the selected parsed attempt, the actual corrected OPEN callback uses only ordinary routed getters. Its supplied-pin selection, mandatory authentication, stateful reserve and every collector failure therefore leave the selected-getter channel unused. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenPhase
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordOpen (PublicM)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)

variable {n : Nat} {I KemSK Platform X Y : Type} {base : OracleSpec I}
abbrev Selected := RegistrationNativeSecretWordTargetPhaseCore.Selected (n := n) (KemSK := KemSK)
abbrev Base (n : Nat) (KemSK Platform : Type) := RegistrationNativePlatformSecretWordFrontend.Base n KemSK Platform

private theorem local_run_free (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) X)
    (previous : Platform) :
    ((simulateQ (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false) work).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  rw [show (simulateQ (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false) work).run previous =
      (fun value => (value, previous)) <$> simulateQ (RegistrationNativeSecretWordInterface.liftLocal false) work from
    by
      induction work using OracleComp.inductionOn with
      | pure value => rfl
      | query_bind query next ih =>
        simp only [simulateQ_bind, simulateQ_spec_query, wordLocal, StateT.run_bind,
          StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
        apply bind_congr
        intro value
        exact ih value]
  rw [isQueryBoundP_map_iff]
  exact RegistrationNativeSecretWordTargetPhaseCore.ordinary_free work

private theorem environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) X) (previous : Platform) :
    ((simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false)) work).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  rw [RegistrationNativePlatformSecretWordOpen.effects, QueryImpl.simulateQ_compose]
  exact local_run_free _ previous

private theorem platform_zero (work : StateT Platform ProbComp X) (before : Platform) :
    ((RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) work).run before).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false (work.run before) 0)
  intro coin
  simp [RegistrationNativeSecretWordFrontend.effect, Selected,
    RegistrationNativeSecretWordTargetPhaseCore.Selected, isQueryBoundP_query_iff]

private theorem lift_free (work : Base n KemSK Platform X)
    (free : ∀ previous, (work.run previous).IsQueryBoundP (Selected (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((StateT.lift (StateT.lift work) : PublicM (Base n KemSK Platform) X).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using free previous

private theorem bind_free (work : PublicM (Base n KemSK Platform) X) (next : X → PublicM (Base n KemSK Platform) Y)
    (first : ∀ before env previous, (((work.run before).run env).run previous).IsQueryBoundP (Selected (n := n) (KemSK := KemSK)) 0)
    (later : ∀ value before env previous, ((((next value).run before).run env).run previous).IsQueryBoundP (Selected (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((work >>= next).run before).run env).run previous).IsQueryBoundP (Selected (n := n) (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env previous)
  rintro ⟨⟨⟨value, after⟩, nextEnv⟩, nextPlatform⟩ _
  exact later value after nextEnv nextPlatform

private theorem agreement_free (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.agreement (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  exact local_run_free _ previous

private theorem retain_free (ready : ServerReady) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.retain ready : PublicM (Base n KemSK Platform) _).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before <;> trivial

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.agreement RegistrationAuthenticationCompiler.program

private theorem afterAuthentication_free (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · apply bind_free _ _ (fun before env previous => lift_free _ (platform_zero reserve) before env previous)
    intro admitted current nextEnv nextPlatform
    cases admitted with
    | false => trivial
    | true =>
      simp only [ite_true]
      apply bind_free _ _ (fun before env previous => agreement_free setup checks packet authenticated before env previous)
      intro accepted after finalEnv finalPlatform
      cases accepted with
      | fail error | div => trivial
      | ok result => cases result with
        | none => trivial
        | some ready => exact retain_free ready after finalEnv finalPlatform

private theorem afterPin_free (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet current).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  cases current with
  | fail error | div => trivial
  | ok current => cases current with
    | none => trivial
    | some pin =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin]
      apply bind_free _ _ (fun before env previous => lift_free _ (environment_free _) before env previous)
      intro checked after nextEnv nextPlatform
      cases checked with
      | fail error | div => trivial
      | ok result =>
        rcases result with ⟨events, authenticated⟩
        cases authenticated <;> first
          | exact afterAuthentication_free reserve setup checks packet _ after nextEnv nextPlatform
          | trivial

private theorem pin_free (current : session.ServerAuthenticationPin) (previous : Platform) :
    ((RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false)) current).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  apply (isQueryBoundP_false (RegistrationNativeServerPinRecompute.program current.binding current.public_key) 0).simulateQ_run_of_step
  · intro query impossible; exact impossible.elim
  · intro request _ before
    simp only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff]
    simpa only [simulateQ_spec_query] using environment_free (n := n) (KemSK := KemSK)
      ((PqxdhRecordLiftInterface.EnvEffects n).query
        (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) before

/-- The ordinary corrected OPEN callback never asks the selected getter, including every mutable reservation outcome. -/
theorem accept_free (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.accept (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) false)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet).run before).run env).run previous).IsQueryBoundP
      (Selected (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.accept, StateT.run_bind, StateT.run_get, pure_bind]
  apply isQueryBoundP_bind (m := 0)
    (lift_free _ (pin_free before.pin) before env previous)
  rintro ⟨⟨⟨current, after⟩, nextEnv⟩, nextPlatform⟩ _
  exact afterPin_free reserve setup checks verify packet current after nextEnv nextPlatform

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenPhase


/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenPhase.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordTargetOpenPhase.accept_free
