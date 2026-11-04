-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
import BeaconcryptCore.Computational.RegistrationServerOpenReferenceSessionShape
/-! The actual corrected free accept syntax keeps Server tokens unchanged or appends exactly the Ready returned at its owned insertion. Authentication, public reservation and every failure branch remain in the same query tree. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOpenSessionShape
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformServerOpenSyntax (Spec protocol reserve)
open RegistrationNativePlatformServerReferenceAccept (PublicM)
open RegistrationServerOpenReferenceSessionShape (Shape)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

private theorem lift_run (work : OracleComp (Spec n KemSK) Value)
    (front : RegistrationServerMaterialFrontend.State) (env : RegistrationServerReferenceCompiler.Environment) :
    (((StateT.lift (StateT.lift work) : PublicM (OracleComp (Spec n KemSK)) Value).run front).run env) =
      (fun value => ((value, front), env)) <$> work := by
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map]

private theorem retained (ready : RegistrationServerReferenceRoot.Ready)
    (front after : RegistrationServerMaterialFrontend.State) (env nextEnv : RegistrationServerReferenceCompiler.Environment)
    (reply : RustM (Option Nat))
    (supported : ((reply, after), nextEnv) ∈ support
      (((RegistrationNativePlatformServerReferenceAccept.retain (m := OracleComp (Spec n KemSK)) ready).run front).run env)) :
    Shape front.sessions reply after.sessions := by
  unfold RegistrationNativePlatformServerReferenceAccept.retain RegistrationServerMaterialFrontend.retain at supported
  dsimp only [StateT.run] at supported
  cases consumed : RegistrationReplaySchedule.consume (RegistrationServerReferenceRoot.atRoot ready RegistrationBoundKeySchedule.zero) front.consumed with
  | fail error | div =>
      simp only [consumed, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
  | ok result =>
      rcases result with ⟨optional, history⟩
      cases optional with
      | none =>
          simp only [consumed, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inl rfl
      | some token =>
          simp only [consumed, StateT.monad_pure_def, StateT.pure, mem_support_pure_iff] at supported
          cases supported
          exact Or.inr ⟨ready, rfl, rfl⟩

attribute [local irreducible] RegistrationNativePlatformServerOpenKernel.agreement

private theorem after_authentication (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (front after : RegistrationServerMaterialFrontend.State) (env nextEnv : RegistrationServerReferenceCompiler.Environment)
    (reply : RustM (Option Nat))
    (supported : ((reply, after), nextEnv) ∈ support
      (((RegistrationNativePlatformServerOpenControl.afterAuthentication (protocol (n := n)) reserve setup checks packet authenticated).run front).run env)) :
    Shape front.sessions reply after.sessions := by
  simp only [RegistrationNativePlatformServerOpenControl.afterAuthentication, StateT.run_bind, StateT.run_get, pure_bind] at supported
  split at supported
  · simp only [StateT.run_pure, mem_support_pure_iff] at supported
    cases supported
    exact Or.inl rfl
  · simp only [StateT.run_bind] at supported
    rw [lift_run] at supported
    simp only [bind_map_left, mem_support_bind_iff] at supported
    obtain ⟨admitted, _reserved, continued⟩ := supported
    cases admitted with
    | false =>
        simp only [Bool.false_eq_true, ite_false, StateT.run_pure, mem_support_pure_iff] at continued
        cases continued
        exact Or.inl rfl
    | true =>
        simp only [ite_true, StateT.run_bind, mem_support_bind_iff] at continued
        obtain ⟨⟨⟨accepted, current⟩, currentEnv⟩, agreed, continued⟩ := continued
        rw [RegistrationNativePlatformServerOpenKernel.agreement_factor] at agreed
        simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at agreed
        obtain ⟨⟨answer, afterEnv⟩, _actual, equal⟩ := agreed
        cases equal
        dsimp only at continued
        cases answer with
        | fail error | div =>
            simp only [StateT.run_pure, mem_support_pure_iff] at continued
            cases continued
            exact Or.inl rfl
        | ok optional => cases optional with
          | none =>
              simp only [StateT.run_pure, mem_support_pure_iff] at continued
              cases continued
              exact Or.inl rfl
          | some ready => exact retained ready front after afterEnv nextEnv reply continued


attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem after_pin (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (pin : RegistrationNativeServerPinRecompute.PinReply)
    (front after : RegistrationServerMaterialFrontend.State) (env nextEnv : RegistrationServerReferenceCompiler.Environment)
    (reply : RustM (Option Nat))
    (supported : ((reply, after), nextEnv) ∈ support
      (((RegistrationNativePlatformServerOpenControl.afterPin (protocol (n := n)) reserve setup checks verify packet pin).run front).run env)) :
    Shape front.sessions reply after.sessions := by
  cases pin with
  | fail error | div =>
      simp only [RegistrationNativePlatformServerOpenControl.afterPin, StateT.run_pure, mem_support_pure_iff] at supported
      cases supported
      exact Or.inl rfl
  | ok optional => cases optional with
    | none =>
        simp only [RegistrationNativePlatformServerOpenControl.afterPin, StateT.run_pure, mem_support_pure_iff] at supported
        cases supported
        exact Or.inl rfl
    | some pin =>
        simp only [RegistrationNativePlatformServerOpenControl.afterPin, StateT.run_bind] at supported
        rw [lift_run] at supported
        simp only [bind_map_left, mem_support_bind_iff] at supported
        obtain ⟨checked, _authenticated, continued⟩ := supported
        cases checked with
        | fail error | div =>
            simp only [StateT.run_pure, mem_support_pure_iff] at continued
            cases continued
            exact Or.inl rfl
        | ok result =>
            rcases result with ⟨events, verdict⟩
            cases verdict with
            | Accepted authenticated => exact after_authentication setup checks packet authenticated front after env nextEnv reply continued
            | Rejected | HashRequested _ | MldsaVerificationRequested _ | Ed25519VerificationRequested _ | ServerFingerprintRequested _ | BeaconFingerprintRequested _ =>
                simp only [StateT.run_pure, mem_support_pure_iff] at continued
                cases continued
                exact Or.inl rfl

/-- All actual corrected free accept outcomes keep the token list or append its one returned Ready at the returned original-length handle. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (front after : RegistrationServerMaterialFrontend.State)
    (env nextEnv : RegistrationServerReferenceCompiler.Environment) (reply : RustM (Option Nat))
    (supported : ((reply, after), nextEnv) ∈ support
      (((RegistrationNativePlatformServerOpenSyntax.accept (n := n) (KemSK := KemSK) setup checks verify packet).run front).run env)) :
    Shape front.sessions reply after.sessions := by
  simp only [RegistrationNativePlatformServerOpenSyntax.accept, RegistrationNativePlatformServerOpenControl.accept,
    StateT.run_bind, StateT.run_get, pure_bind] at supported
  rw [lift_run] at supported
  simp only [bind_map_left, mem_support_bind_iff] at supported
  obtain ⟨pin, _computed, continued⟩ := supported
  exact after_pin setup checks verify packet pin front after env nextEnv reply continued

end BeaconcryptCore.Computational.RegistrationNativePlatformOpenSessionShape

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOpenSessionShape.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOpenSessionShape.accept
