-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAgreement
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial

/-! Mandatory authentication, owned replay, reservation and actual one-use retention compose with the checked symbolic Server agreement. Authentication uses the same complete shared effect program before any root reference exists. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (Message input ServerState ServerReady)
open RegistrationNativeSecretWordChecked (Spec native implementation)
open PqxdhJointIdentity (IdentitySeed)
open PqxdhJointGapDh (ScalarBytes)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

def retained (candidate : PqxdhKemIndCca.MlKemSharedSecret) : RustM (Option Nat × ServerState) →
    RustM (Option Nat × RegistrationServerMaterialFrontend.State)
  | .fail error => .fail error
  | .div => .div
  | .ok (reply, after) => .ok (reply, after.eval candidate)

/-- Replay consumption and returned session handles depend only on the actual public agreement, not on the symbolic reference representation. -/
theorem retain (candidate : PqxdhKemIndCca.MlKemSharedSecret) (ready : ServerReady) (before : ServerState) :
    retained candidate (RegistrationNativeSecretWordServerMaterial.retain ready before) =
      RegistrationServerMaterialFrontend.retain (ready.eval candidate) (before.eval candidate) := by
  simp only [RegistrationNativeSecretWordServerMaterial.retain, RegistrationServerMaterialFrontend.retain,
    ServerReady.eval, ServerState.eval, RegistrationServerReferenceRoot.atRoot]
  split <;> simp_all only [retained, ServerState.eval, ServerReady.eval, List.map_append, List.map_cons, List.map_nil,
    Option.map_some, List.length_map]

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.agreement
  RegistrationNativeSecretWordServerCompiler.agreement RegistrationNativeSecretWordChecked.native
  RegistrationNativeSecretWordChecked.implementation

/-- Owned replay and allocation failures precede and preserve the same checked agreement and retained one-use session. -/
theorem after_authentication (setup : Setup base KemSK) (checks : Checks)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated).run (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (((RegistrationNativeSecretWordServerCompiler.afterAuthentication setup checks packet authenticated).run before).run env) := by
  simp only [RegistrationServerOpenReferenceCompiler.afterAuthentication,
    RegistrationNativeSecretWordServerCompiler.afterAuthentication, StateT.run_bind, StateT.run_get,
    pure_bind]
  simp only [show (before.eval candidate).consumed = before.consumed from rfl]
  by_cases replayed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true, StateT.run_pure, simulateQ_pure, map_pure]
  · simp only [replayed, Bool.false_eq_true, ite_false]
    cases reserved : checks.reserveRegistration with
    | false => simp only [Bool.false_eq_true, ite_false, StateT.run_pure, simulateQ_pure, map_pure]
    | true =>
      simp only [ite_true, StateT.run_bind, simulateQ_bind, map_bind]
      rw [RegistrationNativeSecretWordCheckedServerAgreement.agreement setup checks inside candidate seed scalar packet authenticated before env,
        bind_map_left]
      apply bind_congr
      intro reached
      cases accepted : reached.1.1 with
      | fail error | div => simp only [RegistrationNativeSecretWordServerRoot.restore,
          StateT.run_pure, simulateQ_pure, map_pure]
      | ok selected =>
          cases selected with
          | none => simp only [RegistrationNativeSecretWordServerRoot.restore,
              Option.map_none, StateT.run_pure, simulateQ_pure, map_pure]
          | some ready =>
              simp only [RegistrationNativeSecretWordServerRoot.restore, Option.map_some,
                RegistrationServerOpenReferenceCompiler.retain, RegistrationNativeSecretWordServerCompiler.retain,
                StateT.run]
              have kept := retain candidate ready reached.1.2
              cases actual : RegistrationNativeSecretWordServerMaterial.retain ready reached.1.2 <;>
                simp only [actual, retained] at kept
              all_goals rw [← kept]; rfl

attribute [local irreducible] RegistrationServerOpenReferenceCompiler.afterAuthentication
  RegistrationNativeSecretWordServerCompiler.afterAuthentication RegistrationAuthenticationCompiler.program

set_option maxRecDepth 4096 in
/-- Complete actual mandatory authentication composes with the checked agreement, replay and retained-session source law. -/
theorem accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : IdentitySeed) (scalar : ScalarBytes) (packet : registration.InitPacket)
    (before : ServerState) (env : Environment) :
    simulateQ (native (n := n) setup.source inside candidate (input setup.joint setup.dh seed scalar))
      (((RegistrationServerOpenReferenceCompiler.accept setup checks verify packet).run (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        simulateQ (implementation setup.source inside candidate (input setup.joint setup.dh seed scalar))
          (((RegistrationNativeSecretWordServerCompiler.accept setup checks verify packet).run before).run env) := by
  simp only [RegistrationServerOpenReferenceCompiler.accept, RegistrationNativeSecretWordServerCompiler.accept,
    StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift, bind_pure_comp, simulateQ_bind,
    bind_map_left, map_bind]
  simp only [show (before.eval candidate).pin = before.pin from rfl]
  rw [RegistrationNativeSecretWordCheckedMaterial.effects setup.source inside candidate
    (input setup.joint setup.dh seed scalar)]
  apply bind_congr
  intro checked
  cases checked with
  | fail error | div => simp only [StateT.run_pure, simulateQ_pure, map_pure]
  | ok checked =>
      rcases checked with ⟨events, stage⟩
      cases stage <;> try simp only [StateT.run_pure, simulateQ_pure, map_pure]
      exact after_authentication setup checks inside candidate seed scalar packet _ before env

end BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.retain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.retain
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.after_authentication
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept.accept
