-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
import Cslib.Foundations.Control.Monad.IsMonadHom
/-! The corrected symbolic accept commutes with any lawful common interpreter. This permits the same platform state and external sampler to be retained when moving its literal callback tree into the checked global Word interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativePlatformSecretWordOpen (PublicM effects agreement retain afterAuthentication afterPin accept)
variable {n : Nat} {I KemSK A : Type} {base : OracleSpec I}
variable {m k : Type → Type} [Monad m] [LawfulMonad m] [Monad k] [LawfulMonad k]
    {F : ∀ {A : Type}, m A → k A} (hom : Cslib.IsMonadHom m k F)
include hom

private theorem program {J : Type} {spec : OracleSpec J} (implementation : QueryImpl spec m)
    (work : OracleComp spec A) : F (simulateQ implementation work) = simulateQ (fun query => F (implementation query)) work := by
  induction work using OracleComp.inductionOn with
  | pure value => exact hom.map_pure _
  | query_bind query next ih => simp only [simulateQ_bind, simulateQ_spec_query, hom.map_bind, ih]

variable (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks)

private theorem effect_program (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    F (simulateQ (effects implementation) work) = simulateQ (effects (fun query => F (implementation query))) work := by
  rw [program hom]
  congr 1
  funext query
  exact program hom implementation (RegistrationNativeSecretWordInterface.effect query)

private theorem pin (current : session.ServerAuthenticationPin) :
    F (RegistrationNativePlatformServerReferenceAccept.pin (effects implementation) current) =
      RegistrationNativePlatformServerReferenceAccept.pin (effects (fun query => F (implementation query))) current := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  rw [program hom]
  congr 1
  funext request
  simp only [RegistrationNativePlatformServerReferenceAccept.hash, hom.map_bind, hom.map_pure]
  have effect := effect_program hom implementation ((PqxdhRecordLiftInterface.EnvEffects n).query
    (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes request))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)
  simp only [simulateQ_spec_query] at effect
  rw [effect]

private theorem agreement (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) :
    F (((RegistrationNativePlatformSecretWordOpen.agreement implementation setup checks packet authenticated).run before).run env) =
      (((RegistrationNativePlatformSecretWordOpen.agreement (fun query => F (implementation query)) setup checks packet authenticated).run before).run env) :=
  program hom implementation _

omit [LawfulMonad m] [LawfulMonad k] in
private theorem retain (ready : ServerReady) (before : ServerState) (env : Environment) :
    F (((RegistrationNativePlatformSecretWordOpen.retain ready : PublicM m _).run before).run env) =
      (((RegistrationNativePlatformSecretWordOpen.retain ready : PublicM k _).run before).run env) := by
  simp only [RegistrationNativePlatformSecretWordOpen.retain, StateT.run]
  cases RegistrationNativeSecretWordServerMaterial.retain ready before <;> exact hom.map_pure _

private theorem afterAuthentication (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) :
    F (((RegistrationNativePlatformSecretWordOpen.afterAuthentication implementation reserve setup checks packet authenticated).run before).run env) =
      (((RegistrationNativePlatformSecretWordOpen.afterAuthentication (fun query => F (implementation query)) (F reserve) setup checks packet authenticated).run before).run env) := by
  simp only [RegistrationNativePlatformSecretWordOpen.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind]
  split
  · exact hom.map_pure _
  · simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
    rw [hom.map_bind]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => exact hom.map_pure _
    | true =>
      simp only [ite_true, StateT.run_bind]
      rw [hom.map_bind, agreement hom implementation setup checks packet authenticated before env]
      apply bind_congr
      rintro ⟨⟨accepted, after⟩, nextEnv⟩
      cases accepted with
      | fail error | div => exact hom.map_pure _
      | ok selected => cases selected with
        | none => exact hom.map_pure _
        | some ready => exact retain hom ready after nextEnv

private theorem afterPin (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply) (before : ServerState) (env : Environment) :
    F (((RegistrationNativePlatformSecretWordOpen.afterPin implementation reserve setup checks verify packet current).run before).run env) =
      (((RegistrationNativePlatformSecretWordOpen.afterPin (fun query => F (implementation query)) (F reserve) setup checks verify packet current).run before).run env) := by
  cases current with
  | fail error | div => exact hom.map_pure _
  | ok selected => cases selected with
    | none => exact hom.map_pure _
    | some current =>
      simp only [RegistrationNativePlatformSecretWordOpen.afterPin, StateT.run_bind, StateT.run_lift,
        bind_pure_comp, bind_map_left]
      rw [hom.map_bind, effect_program hom implementation]
      apply bind_congr
      intro checked
      cases checked with
      | fail error | div => exact hom.map_pure _
      | ok pair =>
        rcases pair with ⟨events, authenticated⟩
        cases authenticated
        all_goals first
          | exact afterAuthentication hom implementation reserve setup checks packet _ before env
          | exact hom.map_pure _

/-- Interpreting the corrected accept retains the same full returned symbolic state and every mutable base effect. -/
theorem accept (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : ServerState) (env : Environment) :
    F (((RegistrationNativePlatformSecretWordOpen.accept implementation reserve setup checks verify packet).run before).run env) =
      (((RegistrationNativePlatformSecretWordOpen.accept (fun query => F (implementation query)) (F reserve) setup checks verify packet).run before).run env) := by
  simp only [RegistrationNativePlatformSecretWordOpen.accept, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left]
  rw [hom.map_bind, pin hom implementation]
  apply bind_congr
  intro current
  exact afterPin hom implementation reserve setup checks verify packet current before env

/-- The actual corrected native accept has the same interpreter naturality, derived from its maintained exact free source syntax. -/
theorem native_accept (nativeImplementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) m)
    (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment) :
    F (((RegistrationNativePlatformServerOpenControl.accept nativeImplementation reserve setup checks verify packet).run before).run env) =
      (((RegistrationNativePlatformServerOpenControl.accept (fun query => F (nativeImplementation query)) (F reserve)
        setup checks verify packet).run before).run env) := by
  let requests : QueryImpl (RegistrationNativePlatformServerOpenSyntax.Spec n KemSK) m :=
    fun | .inl query => nativeImplementation query | .inr () => reserve
  have left := congrArg (fun work => ((work.run before).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source requests setup checks verify packet)
  have right := congrArg (fun work => ((work.run before).run env))
    (RegistrationNativePlatformServerOpenSyntax.accept_source (fun query => F (requests query)) setup checks verify packet)
  change simulateQ requests (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept nativeImplementation reserve setup checks verify packet).run before).run env) at left
  change simulateQ (fun query => F (requests query)) (((RegistrationNativePlatformServerOpenSyntax.accept setup checks verify packet).run before).run env) =
    (((RegistrationNativePlatformServerOpenControl.accept (fun query => F (nativeImplementation query)) (F reserve)
      setup checks verify packet).run before).run env) at right
  exact (congrArg (fun work => F work) left.symm).trans ((program hom requests _).trans right)

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap.accept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap.native_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpenMap.native_accept
