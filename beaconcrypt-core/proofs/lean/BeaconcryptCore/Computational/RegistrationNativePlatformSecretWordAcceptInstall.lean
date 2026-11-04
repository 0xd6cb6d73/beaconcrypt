-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordInstallTransport
import BeaconcryptCore.Computational.RegistrationNativeSecretWordAtomServerInstallCaps
/-! The actual corrected OPEN Word accept contains no installation of either role. Repeated pin, mandatory authentication, owned replay, same mutable reservation, ordered collector and one-use retention keep all source failure and platform outcomes. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptInstall
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordOpen (PublicM)
open RegistrationNativePlatformSecretWordFrontendView (wordLocal)
open RegistrationNativePlatformSecretWordInstallTransport (local_bound platform_zero)
variable (role : PqxdhRecordLiftInterface.Role)
variable {n : Nat} {I KemSK Platform X Y : Type} {base : OracleSpec I}
abbrev Install := RegistrationNativeSecretWordAtomInstallPredicate.GlobalInstall (n := n) (KemSK := KemSK) role
open RegistrationNativeSecretWordAtomInstallPredicate (LocalInstall)
open RegistrationNativeSecretWordAtomInstallCaps (InstallEnv)
abbrev Base (n : Nat) (KemSK Platform : Type) := RegistrationNativePlatformSecretWordFrontend.Base n KemSK Platform

omit role in
private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : V → W) (work : StateT S m V) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map _ _ _
omit role in
private theorem lift_apply {S V : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m V) (before : S) : (StateT.lift work : StateT S m V) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _

private theorem local_run_bound (selected : Bool) (work : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) X)
    (cap : Nat) (bounded : work.IsQueryBoundP (LocalInstall (n := n) (KemSK := KemSK) role) cap)
    (previous : Platform) :
    ((simulateQ (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected) work).run previous).IsQueryBoundP (Install role (n := n) (KemSK := KemSK)) cap := by
  apply bounded.simulateQ_run_of_step
  · intro query counted before
    simpa only [wordLocal, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound role selected (((RegistrationNativeSecretWordInterface.LocalSpec n KemSK).query query) : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) _) 1
        (by simp [isQueryBoundP_query_iff, counted])
  · intro query free before
    simpa only [wordLocal, StateT.run_lift, bind_pure_comp, isQueryBoundP_map_iff, simulateQ_spec_query] using
      local_bound role selected (((RegistrationNativeSecretWordInterface.LocalSpec n KemSK).query query) : OracleComp (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) _) 0
        (by simp [isQueryBoundP_query_iff, free])

private theorem local_environment_free (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) X)
    (bounded : work.IsQueryBoundP (InstallEnv role) 0) :
    (simulateQ (RegistrationNativeSecretWordInterface.effect (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work 0 bounded
  intro query
  by_cases charged : InstallEnv role query <;>
    simp [RegistrationNativeSecretWordInterface.effect, LocalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, charged, isQueryBoundP_query_iff]

private theorem environment_free (selected : Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) X)
    (bounded : work.IsQueryBoundP (InstallEnv role) 0) (previous : Platform) :
    ((simulateQ (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)) work).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  rw [RegistrationNativePlatformSecretWordOpen.effects, QueryImpl.simulateQ_compose]
  exact local_run_bound role selected _ 0 (local_environment_free role work bounded) previous

attribute [local irreducible] RegistrationAuthenticationExecutor.begin
private theorem authentication_free (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (pin : session.ServerAuthenticationPin) (packet : registration.InitPacket) :
    (RegistrationAuthenticationCompiler.program (n := n) crypto verify pin packet).IsQueryBoundP (InstallEnv role) 0 := by
  unfold RegistrationAuthenticationCompiler.program
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  cases query <;> simp [RegistrationAuthenticationCompiler.callbacks, InstallEnv, isQueryBoundP_query_iff]

private theorem lift_free (work : Base n KemSK Platform X)
    (free : ∀ previous, (work.run previous).IsQueryBoundP (Install role (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((StateT.lift (StateT.lift work) : PublicM (Base n KemSK Platform) X).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  simpa only [StateT.run_lift, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff] using free previous

private theorem bind_free (work : PublicM (Base n KemSK Platform) X) (next : X → PublicM (Base n KemSK Platform) Y)
    (first : ∀ before env previous, (((work.run before).run env).run previous).IsQueryBoundP (Install role (n := n) (KemSK := KemSK)) 0)
    (later : ∀ value before env previous, ((((next value).run before).run env).run previous).IsQueryBoundP (Install role (n := n) (KemSK := KemSK)) 0)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((work >>= next).run before).run env).run previous).IsQueryBoundP (Install role (n := n) (KemSK := KemSK)) 0 := by
  simp only [StateT.run_bind]
  apply isQueryBoundP_bind (m := 0) (first before env previous)
  rintro ⟨⟨⟨value, after⟩, nextEnv⟩, nextPlatform⟩ _
  exact later value after nextEnv nextPlatform

private theorem prepare_free (work : OracleComp RegistrationNativeSecretWordMessage.PrepareSpec X) :
    (simulateQ (RegistrationNativeSecretWordInterface.prepare (n := n) (KemSK := KemSK)) work).IsQueryBoundP (LocalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [RegistrationNativeSecretWordInterface.prepare, LocalInstall, isQueryBoundP_query_iff]

private theorem agreement_free (selected : Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.agreement (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  apply local_run_bound role selected _ 0 _ previous
  simp only [RegistrationNativeSecretWordServerCompiler.agreement, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind]
  apply isQueryBoundP_bind (m := 0)
    (RegistrationNativeSecretWordAtomServerInstallCaps.collect_bound role setup checks packet authenticated env)
  intro collected _
  cases collected.1 with
  | none => trivial
  | some pending =>
    simpa only [StateT.run, lift_apply, map_apply, Functor.map_map, isQueryBoundP_map_iff] using
      prepare_free (n := n) (KemSK := KemSK) role (RegistrationNativeSecretWordServerRoot.client authenticated.binding pending)

private theorem retain_free (ready : ServerReady) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.retain ready : PublicM (Base n KemSK Platform) _).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before <;> trivial

attribute [local irreducible] RegistrationNativePlatformSecretWordOpen.agreement RegistrationAuthenticationCompiler.program

private theorem afterAuthentication_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterAuthentication (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks packet authenticated).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · trivial
  · apply bind_free role _ _ (fun before env previous => lift_free role _ (platform_zero role reserve) before env previous)
    intro admitted current nextEnv nextPlatform
    cases admitted with
    | false => trivial
    | true =>
      simp only [ite_true]
      apply bind_free role _ _ (fun before env previous => agreement_free role selected setup checks packet authenticated before env previous)
      intro accepted after finalEnv finalPlatform
      cases accepted with
      | fail error | div => trivial
      | ok result => cases result with
        | none => trivial
        | some ready => exact retain_free role ready after finalEnv finalPlatform

private theorem afterPin_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply) (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.afterPin (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet current).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  cases current with
  | fail error | div => trivial
  | ok current => cases current with
    | none => trivial
    | some pin =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin]
      apply bind_free role _ _ (fun before env previous => lift_free role _ (environment_free role selected _ (authentication_free role setup.source.crypto verify pin packet)) before env previous)
      intro checked after nextEnv nextPlatform
      cases checked with
      | fail error | div => trivial
      | ok result =>
        rcases result with ⟨events, authenticated⟩
        cases authenticated <;> first
          | exact afterAuthentication_free role selected reserve setup checks packet _ after nextEnv nextPlatform
          | trivial

private theorem pin_free (selected : Bool) (current : session.ServerAuthenticationPin) (previous : Platform) :
    ((RegistrationNativePlatformServerReferenceAccept.pin (RegistrationNativePlatformSecretWordOpen.effects (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)) current).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  apply (isQueryBoundP_false (RegistrationNativeServerPinRecompute.program current.binding current.public_key) 0).simulateQ_run_of_step
  · intro query impossible; exact impossible.elim
  · intro request _ before
    simp only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, StateT.run_map, isQueryBoundP_map_iff]
    simpa only [simulateQ_spec_query] using environment_free (n := n) (KemSK := KemSK) role selected
      ((PqxdhRecordLiftInterface.EnvEffects n).query
        (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) (by simp [InstallEnv, isQueryBoundP_query_iff]) before

/-- Repeated pin hashing, mandatory authentication, mutable reservation and actual ordered preparation perform no role installation. -/
theorem accept_free (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : ServerState) (env : Environment) (previous : Platform) :
    ((((RegistrationNativePlatformSecretWordOpen.accept (wordLocal (n := n) (KemSK := KemSK) (Platform := Platform) selected)
      (RegistrationNativePlatformSecretWordOrdinary.platform (n := n) (KemSK := KemSK) reserve) setup checks verify packet).run before).run env).run previous).IsQueryBoundP
      (Install role (n := n) (KemSK := KemSK)) 0 := by
  simp only [RegistrationNativePlatformSecretWordOpen.accept, StateT.run_bind, StateT.run_get, pure_bind]
  apply bind_free role _ _ (fun before env previous => lift_free role _ (pin_free role selected _) before env previous)
  intro current after nextEnv nextPlatform
  exact afterPin_free role selected reserve setup checks verify packet current after nextEnv nextPlatform

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptInstall.accept_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordAcceptInstall.accept_free
