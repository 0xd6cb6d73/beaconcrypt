-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordCapsTransport
import BeaconcryptCore.Computational.RegistrationNativeSecretWordFrontendCapsServer
/-! The corrected OPEN Word accept derives zero deferred material requests from its pure pin selection, authentication, owned replay, real shared-state reserve, ordered collector and one-use retain. All source failure paths remain literal. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordOpen (PublicM)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
open RegistrationNativePlatformSecretWordCapsTransport (local_bound platform_zero)
variable {n : Nat} {I KemSK Platform X Y : Type} {base : OracleSpec I}
abbrev IsDemand := RegistrationNativeSecretWordInterpreterCaps.IsDemand (n := n) (KemSK := KemSK)
abbrev Base (n : Nat) (KemSK Platform : Type) := RegistrationNativePlatformSecretWordFrontend.Base n KemSK Platform

private theorem local_run_bound (selected : Bool) (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) X)
    (cap : Nat) (bounded : work.IsQueryBoundP (RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (n := n) (KemSK := KemSK)) cap)
    (previous : Platform) :
    ((simulateQ (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected) work).run previous).IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted before
    simpa only [wordLocal, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound selected (((RegistrationNativeSecretWordInterface.LocalSpec n KemSK).query query) : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) _) 1
        (by simp [isQueryBoundP_query_iff, counted])
  · intro query free before
    simpa only [wordLocal, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound selected (((RegistrationNativeSecretWordInterface.LocalSpec n KemSK).query query) : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) _) 0
        (by simp [isQueryBoundP_query_iff, free])

private theorem environment_free (selected : Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) X) (previous : Platform) :
    ((simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)) work).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  rw [RegistrationNativePlatformSecretWordOpen.effects, QueryImpl.simulateQ_compose]
  exact local_run_bound selected _ 0 (RegistrationNativeSecretWordFrontendCapsLocal.effect_free work) previous

private theorem lift_free (work : Base n KemSK Platform X)
    (free : ∀ previous, (work.run previous).IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((StateT.lift (StateT.lift work) : PublicM (Base n KemSK Platform) X).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using free previous

private theorem bind_free (work : PublicM (Base n KemSK Platform) X) (next : X → PublicM (Base n KemSK Platform) Y)
    (first : ∀ before env previous, (((work.run before).run env).run previous).IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) 0)
    (later : ∀ value before env previous, ((((next value).run before).run env).run previous).IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((work >>= next).run before).run env).run previous).IsQueryBoundP (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env previous)
  rintro ⟨⟨⟨value, after⟩, nextEnv⟩, nextPlatform⟩ _
  exact later value after nextEnv nextPlatform

private theorem agreement_free (selected : Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.agreement (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  exact local_run_bound selected _ 0
    (RegistrationNativeSecretWordFrontendCapsServer.agreement_free setup checks packet authenticated before env) previous

private theorem retain_free (ready : ServerReady) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.retain ready : PublicM (Base n KemSK Platform) _).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before <;> trivial

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.agreement RegistrationAuthenticationCompiler.program

private theorem afterAuthentication_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · apply bind_free _ _ (fun before env previous => lift_free _ (platform_zero reserve) before env previous)
    intro admitted current nextEnv nextPlatform
    cases admitted with
    | false => trivial
    | true =>
      simp only [ite_true]
      apply bind_free _ _ (fun before env previous => agreement_free selected setup checks packet authenticated before env previous)
      intro accepted after finalEnv finalPlatform
      cases accepted with
      | fail error | div => trivial
      | ok result => cases result with
        | none => trivial
        | some ready => exact retain_free ready after finalEnv finalPlatform

private theorem afterPin_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet current).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  cases current with
  | fail error | div => trivial
  | ok current => cases current with
    | none => trivial
    | some pin =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin]
      apply bind_free _ _ (fun before env previous => lift_free _ (environment_free selected _) before env previous)
      intro checked after nextEnv nextPlatform
      cases checked with
      | fail error | div => trivial
      | ok result =>
        rcases result with ⟨events, authenticated⟩
        cases authenticated <;> first
          | exact afterAuthentication_free selected reserve setup checks packet _ after nextEnv nextPlatform
          | trivial

private theorem pin_free (selected : Bool) (current : session.ServerAuthenticationPin) (previous : Platform) :
    ((RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)) current).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  apply (isQueryBoundP_false (RegistrationNativeServerPinRecompute.program current.binding current.public_key) 0).simulateQ_run_of_step
  · intro query impossible; exact impossible.elim
  · intro request _ before
    simp only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff]
    simpa only [simulateQ_spec_query] using environment_free (n := n) (KemSK := KemSK) selected
      ((PqxdhRecordLiftInterface.EnvEffects n).query
        (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) before

/-- Pure pin selection, mandatory authentication, mutable reservation and actual ordered preparation consume no deferred material allowance. -/
theorem accept_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.accept (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet).run before).run env).run previous).IsQueryBoundP
      (IsDemand (n := n) (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformSecretWordOpen.accept
  apply bind_free _ _ (fun _ _ _ => by trivial)
  intro fetched afterGet nextEnv nextPlatform
  exact bind_free _ _
    (fun before env previous => lift_free _ (pin_free selected fetched.pin) before env previous)
    (fun current after nextEnv nextPlatform =>
      afterPin_free selected reserve setup checks verify packet current after nextEnv nextPlatform)
    afterGet nextEnv nextPlatform

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCaps.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptCaps.accept_free
