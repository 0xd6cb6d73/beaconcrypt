-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSyntax
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedServerAccept
/-! Symbolic Server acceptance follows the corrected source controller: repeated pin hashing, mandatory authentication, owned replay, the same effectful reservation, ordered indexed agreement and one-use retention. Only the root reference representation changes. The final comparison is natural in an arbitrary checked-query interpreter and preserves its complete mutable state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeSecretWordMessage (ServerState ServerReady input)
open RegistrationServerReferenceCompiler (Environment)
variable {n : Nat} {I KemSK Value : Type} {base : OracleSpec I}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

abbrev PublicM (m : Type → Type) [Monad m] := StateT ServerState (StateT Environment m)

def effects (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m) :
    QueryImpl (PqxdhRecordLiftInterface.EnvEffects n) m :=
  implementation ∘ₛ RegistrationNativeSecretWordInterface.effect

noncomputable def agreement (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (setup : Setup base KemSK) (checks : Checks) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) : PublicM m (RustM (Option ServerReady)) :=
  fun before env => simulateQ implementation
    (((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before).run env)

def retain (ready : ServerReady) : PublicM m (RustM (Option Nat)) := fun before =>
  match RegistrationNativeSecretWordServerMaterial.retain ready before with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, after)

noncomputable def afterAuthentication (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else do
    let admitted ← StateT.lift (StateT.lift reserve)
    if admitted then do
      let accepted ← agreement implementation setup checks packet authenticated
      match accepted with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok none => pure (.ok none)
      | .ok (some ready) => retain ready
    else pure (.ok none)

noncomputable def afterPin (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (result : RegistrationNativeServerPinRecompute.PinReply) : PublicM m (RustM (Option Nat)) :=
  match result with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok .None => pure (.ok none)
  | .ok (.Some pin) => do
    let checked ← StateT.lift (StateT.lift (simulateQ (effects implementation)
      (RegistrationAuthenticationCompiler.program setup.source.crypto verify pin packet)))
    match checked with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok (_events, .Accepted authenticated) => afterAuthentication implementation reserve setup checks packet authenticated
    | .ok _ => pure (.ok none)

noncomputable def accept (implementation : QueryImpl (RegistrationNativeSecretWordInterface.LocalSpec n KemSK) m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  let current ← StateT.lift (StateT.lift
    (RegistrationNativePlatformServerReferenceAccept.pin (effects implementation) before.pin))
  afterPin implementation reserve setup checks verify packet current

variable (setup : Setup base KemSK) (checks : Checks)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (target : QueryImpl (RegistrationNativeSecretWordChecked.Spec n KemSK) m)

local notation "nativeImpl" => target ∘ₛ RegistrationNativeSecretWordChecked.native setup.source inside candidate (input setup.joint setup.dh seed scalar)
local notation "wordImpl" => target ∘ₛ RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar)

/-- The actual ordered collector and root preparation commute with arbitrary later checked-query interpretation. -/
theorem agreement_source (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : ServerState) (env : Environment) :
    (((RegistrationNativePlatformServerOpenKernel.agreement nativeImpl setup checks packet authenticated).run
      (before.eval candidate)).run env) =
      (fun result => ((RegistrationNativeSecretWordServerRoot.restore candidate result.1.1,
        result.1.2.eval candidate), result.2)) <$>
        (((agreement wordImpl setup checks packet authenticated).run before).run env) := by
  change simulateQ nativeImpl
    (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run (before.eval candidate)).run env) = _
  change simulateQ nativeImpl
    (((RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated).run (before.eval candidate)).run env) =
    (fun result => ((RegistrationNativeSecretWordServerRoot.restore candidate result.1.1, result.1.2.eval candidate), result.2)) <$>
      simulateQ wordImpl (((RegistrationNativeSecretWordServerCompiler.agreement setup checks packet authenticated).run before).run env)
  rw [QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]
  have compared := congrArg (simulateQ target)
    (RegistrationNativeSecretWordCheckedServerAgreement.agreement setup checks inside candidate seed scalar packet authenticated before env)
  simpa only [simulateQ_map] using compared

/-- Hash, random, administrative and record-marker queries retain exactly their original checked interpretation. -/
theorem effects_source :
    RegistrationNativePlatformServerOpenControl.effects nativeImpl = effects wordImpl := by
  funext query
  have compared := RegistrationNativeSecretWordCheckedMaterial.effects (n := n) (KemSK := KemSK) setup.source inside candidate
    (input setup.joint setup.dh seed scalar) ((PqxdhRecordLiftInterface.EnvEffects n).query query)
  simp only [simulateQ_spec_query] at compared
  simpa only [RegistrationNativePlatformServerOpenControl.effects, effects, QueryImpl.apply_compose,
    QueryImpl.simulateQ_compose] using congrArg (simulateQ target) compared

attribute [local irreducible] agreement RegistrationNativePlatformServerOpenKernel.agreement
  RegistrationAuthenticationCompiler.program

/-- The live shared-state reserve remains before the same actual agreement and one-use retention, including every failure branch. -/
theorem after_authentication (reserve : m Bool) (packet : registration.InitPacket)
    (authenticated : registration.AuthenticatedInit) (before : ServerState) (env : Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterAuthentication nativeImpl reserve setup checks packet authenticated).run
      (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        (((afterAuthentication wordImpl reserve setup checks packet authenticated).run before).run env) := by
  simp only [RegistrationNativePlatformServerOpenControl.afterAuthentication, afterAuthentication,
    StateT.run_bind, StateT.run_get, pure_bind]
  simp only [show (before.eval candidate).consumed = before.consumed from rfl]
  by_cases replayed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true, StateT.run_pure, map_pure]
  · simp only [replayed, Bool.false_eq_true, ite_false, StateT.run_bind, StateT.run_lift,
      bind_pure_comp, map_bind, bind_map_left]
    apply bind_congr
    intro admitted
    cases admitted with
    | false => simp only [Bool.false_eq_true, ite_false, StateT.run_pure, map_pure]
    | true =>
      simp only [ite_true, StateT.run_bind, map_bind]
      rw [agreement_source setup checks inside candidate seed scalar target packet authenticated before env,
        bind_map_left]
      apply bind_congr
      intro reached
      cases accepted : reached.1.1 with
      | fail error | div => simp only [RegistrationNativeSecretWordServerRoot.restore,
          StateT.run_pure, map_pure]
      | ok selected =>
          cases selected with
          | none => simp only [RegistrationNativeSecretWordServerRoot.restore, Option.map_none,
              StateT.run_pure, map_pure]
          | some ready =>
              simp only [RegistrationNativeSecretWordServerRoot.restore, Option.map_some,
                RegistrationNativePlatformServerReferenceAccept.retain, retain, StateT.run]
              have kept := RegistrationNativeSecretWordCheckedServerAccept.retain candidate ready reached.1.2
              cases actual : RegistrationNativeSecretWordServerMaterial.retain ready reached.1.2 <;>
                simp only [actual, RegistrationNativeSecretWordCheckedServerAccept.retained] at kept
              all_goals rw [← kept]; simp only [StateT.monad_pure_def, StateT.pure, map_pure]

attribute [local irreducible] afterAuthentication RegistrationNativePlatformServerOpenControl.afterAuthentication

/-- Mandatory authentication is unchanged and all typed failures flow into the same corrected post-authentication controller. -/
theorem after_pin (reserve : m Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (current : RegistrationNativeServerPinRecompute.PinReply)
    (before : ServerState) (env : Environment) :
    (((RegistrationNativePlatformServerOpenControl.afterPin nativeImpl reserve setup checks verify packet current).run
      (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        (((afterPin wordImpl reserve setup checks verify packet current).run before).run env) := by
  unfold RegistrationNativePlatformServerOpenControl.afterPin afterPin
  cases current with
  | fail error | div => simp only [StateT.run_pure, map_pure]
  | ok selected => cases selected with
    | none => simp only [StateT.run_pure, map_pure]
    | some pin =>
      simp only [StateT.run_bind, StateT.run_lift, bind_pure_comp,
        bind_map_left, map_bind]
      rw [effects_source setup inside candidate seed scalar target]
      apply bind_congr
      intro checked
      cases checked with
      | fail error | div => simp only [StateT.run_pure, map_pure]
      | ok pair =>
        rcases pair with ⟨events, authenticated⟩
        cases authenticated
        all_goals first
          | exact after_authentication setup checks inside candidate seed scalar target reserve packet _ before env
          | simp only [StateT.run_pure, map_pure]

attribute [local irreducible] afterPin RegistrationNativePlatformServerOpenControl.afterPin

/-- The literal corrected OPEN accept, with repeated pin hashing and an arbitrary effectful reserve, has the symbolic-word interpretation in the same mutable base monad. -/
theorem accept_source (reserve : m Bool) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) (before : ServerState) (env : Environment) :
    (((RegistrationNativePlatformServerOpenControl.accept nativeImpl reserve setup checks verify packet).run
      (before.eval candidate)).run env) =
      (fun result => ((result.1.1, result.1.2.eval candidate), result.2)) <$>
        (((accept wordImpl reserve setup checks verify packet).run before).run env) := by
  simp only [RegistrationNativePlatformServerOpenControl.accept, accept, StateT.run_bind, StateT.run_get,
    pure_bind, StateT.run_lift, bind_pure_comp, bind_map_left, map_bind]
  simp only [show (before.eval candidate).pin = before.pin from rfl]
  rw [effects_source setup inside candidate seed scalar target]
  apply bind_congr
  intro current
  exact after_pin setup checks inside candidate seed scalar target reserve verify packet current before env

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.agreement_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.agreement_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.effects_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.effects_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.after_authentication' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.after_authentication

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.after_pin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.after_pin

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.accept_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOpen.accept_source
