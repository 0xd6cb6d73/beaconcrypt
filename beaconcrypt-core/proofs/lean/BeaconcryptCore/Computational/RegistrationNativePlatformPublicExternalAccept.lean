-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalLocal
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalAccept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend (Base localHandler platform)
open RegistrationNativePlatformPublicExternalLocal (IsLocalExternal local_handler_zero platform_bound)
open RegistrationNativePlatformServerReferenceAccept (PublicM)
variable {n : Nat} {I KemSK Platform A B : Type} {base : OracleSpec I}
abbrev Work (A : Type) := PublicM (Base n KemSK Platform) A
private def Bounded (work : Work (n := n) (KemSK := KemSK) (Platform := Platform) A) (cap : Nat) : Prop :=
  ∀ front env before, (((work.run front).run env).run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap
private theorem pure_bound (value : A) (cap : Nat) :
    Bounded (pure value : Work (n := n) (KemSK := KemSK) (Platform := Platform) A) cap := by
  intro front env before
  simp only [StateT.run_pure]
  trivial
private theorem bind_bound (work : Work (n := n) (KemSK := KemSK) (Platform := Platform) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Platform := Platform) B)
    (firstCap laterCap : Nat) (first : Bounded work firstCap) (later : ∀ value, Bounded (next value) laterCap) :
    Bounded (work >>= next) (firstCap + laterCap) := by
  intro front env before
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (first front env before) (fun result _ => later result.1.1.1 result.1.1.2 result.1.2 result.2)
private theorem bind_zero (work : Work (n := n) (KemSK := KemSK) (Platform := Platform) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Platform := Platform) B)
    (cap : Nat) (first : Bounded work 0) (later : ∀ value, Bounded (next value) cap) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.zero_add] using bind_bound work next 0 cap first later
private theorem bind_tail_zero (work : Work (n := n) (KemSK := KemSK) (Platform := Platform) A)
    (next : A → Work (n := n) (KemSK := KemSK) (Platform := Platform) B)
    (cap : Nat) (first : Bounded work cap) (later : ∀ value, Bounded (next value) 0) :
    Bounded (work >>= next) cap := by
  simpa only [Nat.add_zero] using bind_bound work next cap 0 first later
private theorem lifted (work : Base n KemSK Platform A) (cap : Nat)
    (bounded : ∀ before, (work.run before).IsQueryBoundP (IsLocalExternal (KemSK := KemSK)) cap) :
    Bounded (StateT.lift (StateT.lift work) : Work (n := n) (KemSK := KemSK) (Platform := Platform) A) cap := by
  intro front env before
  simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map, isQueryBoundP_map_iff] using bounded before
private theorem get_zero : Bounded (get : Work (n := n) (KemSK := KemSK) (Platform := Platform) RegistrationServerMaterialFrontend.State) 0 := by
  intro front env before
  simp only [StateT.run_get, StateT.run_pure]
  trivial

private theorem effects_zero (selected : Bool) (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (before : Platform) :
    ((simulateQ (RegistrationNativePlatformServerOpenControl.effects (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected)) work).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) 0 := by
  rw [RegistrationNativePlatformServerOpenControl.effects, QueryImpl.simulateQ_compose]
  exact local_handler_zero selected _ before

private theorem pin_zero (selected : Bool) (current : session.ServerAuthenticationPin) (before : Platform) :
    ((RegistrationNativePlatformServerReferenceAccept.pin
      (RegistrationNativePlatformServerOpenControl.effects (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected)) current).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) 0 := by
  unfold RegistrationNativePlatformServerReferenceAccept.pin
  apply (isQueryBoundP_false _ 0).simulateQ_run_of_step
  · intro query impossible
    exact impossible.elim
  · intro query _ previous
    simpa only [RegistrationNativePlatformServerReferenceAccept.hash, bind_pure_comp, StateT.run_map,
      isQueryBoundP_map_iff, simulateQ_spec_query] using
      effects_zero (n := n) (KemSK := KemSK) selected (((PqxdhRecordLiftInterface.EnvEffects n).query
        (.inr (.hash (BeaconcryptCore.Refinement.RegistrationInputs.hashBytes query)))) : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _) previous

private theorem agreement_zero (selected : Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    Bounded (RegistrationNativePlatformServerOpenKernel.agreement (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected) setup checks packet authenticated) 0 := by
  intro front env before
  change ((simulateQ (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected)
    (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run front).run env)).run before).IsQueryBoundP _ 0
  exact local_handler_zero selected _ before

private theorem retain_zero (ready : RegistrationServerReferenceRoot.Ready) :
    Bounded (RegistrationNativePlatformServerReferenceAccept.retain ready : Work (n := n) (KemSK := KemSK) (Platform := Platform) _) 0 := by
  intro front env before
  dsimp only [RegistrationNativePlatformServerReferenceAccept.retain, StateT.run]
  cases current : RegistrationServerMaterialFrontend.retain ready front <;> trivial

private theorem afterAuthentication_bound (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (cap : Nat) (bounded : ∀ before, (reserve.run before).IsTotalQueryBound cap) :
    Bounded (RegistrationNativePlatformServerOpenControl.afterAuthentication (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected) (platform reserve) setup checks packet authenticated) cap := by
  unfold RegistrationNativePlatformServerOpenControl.afterAuthentication
  apply bind_zero _ _ cap get_zero
  intro front
  split
  · exact pure_bound _ cap
  · apply bind_tail_zero _ _ cap (lifted (platform reserve) cap (fun before => platform_bound reserve before cap (bounded before)))
    intro admitted
    cases admitted with
    | false => exact pure_bound _ 0
    | true =>
      simp only [ite_true]
      apply bind_zero _ _ 0 (agreement_zero selected setup checks packet authenticated)
      intro accepted
      cases accepted with
      | fail error | div => exact pure_bound _ 0
      | ok ready => cases ready with
        | none => exact pure_bound _ 0
        | some ready => exact retain_zero ready

attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem afterPin_bound (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (current : RegistrationNativeServerPinRecompute.PinReply)
    (cap : Nat) (bounded : ∀ before, (reserve.run before).IsTotalQueryBound cap) :
    Bounded (RegistrationNativePlatformServerOpenControl.afterPin (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected) (platform reserve) setup checks verify packet current) cap := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin
  cases current with
  | fail error | div => exact pure_bound _ cap
  | ok optional => cases optional with
    | none => exact pure_bound _ cap
    | some pin =>
      apply bind_zero _ _ cap (lifted _ 0 (effects_zero selected _))
      intro checked
      cases checked with
      | fail error | div => exact pure_bound _ cap
      | ok checked =>
        rcases checked with ⟨events, outcome⟩
        cases outcome with
        | Accepted authenticated => exact afterAuthentication_bound selected reserve setup checks packet authenticated cap bounded
        | _ => exact pure_bound _ cap

/-- Every actual corrected accept path uses at most its one public registration reservation's external coin allowance, with all native authentication/agreement prefixes separate. -/
theorem accept_bound (selected : Bool) (reserve : StateT Platform ProbComp Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (cap : Nat) (bounded : ∀ before, (reserve.run before).IsTotalQueryBound cap)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) (before : Platform) :
    ((((RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected) (platform reserve) setup checks verify packet).run front).run env).run before).IsQueryBoundP
      (IsLocalExternal (KemSK := KemSK)) cap := by
  have whole : Bounded (RegistrationNativePlatformServerOpenControl.accept (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) selected) (platform reserve) setup checks verify packet) cap := by
    unfold RegistrationNativePlatformServerOpenControl.accept
    apply bind_zero _ _ cap get_zero
    intro previous
    apply bind_zero _ _ cap (lifted _ 0 (pin_zero selected previous.pin))
    intro current
    exact afterPin_bound selected reserve setup checks verify packet current cap bounded
  exact whole front env before
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalAccept

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalAccept.accept_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicExternalAccept.accept_bound
