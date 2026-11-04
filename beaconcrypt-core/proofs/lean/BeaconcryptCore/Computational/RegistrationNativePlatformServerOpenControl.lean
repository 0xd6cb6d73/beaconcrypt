-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenSource
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! The corrected public open-indexed Server controller keeps repeated pin hashing, mandatory authentication, owned replay and the real shared-state reservation before its actual indexed collector. Executable state stores only the existing public reference capabilities. The private closing map retains the full provider pool and extra state. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationServerReferenceRoot (Ready)
open RegistrationNativeKemReferenceWorld (Private)
open RegistrationNativeKemReferenceCompiler (Spec)
open RegistrationNativePlatformServerReferenceAccept (PublicM retain)
variable {n : Nat} {ι KemSK Extra Value Next : Type} {base : OracleSpec ι}
variable {m : Type → Type} [Monad m] [LawfulMonad m]

def effects (implementation : QueryImpl (Spec n KemSK) m) : QueryImpl (EnvEffects n) m :=
  implementation ∘ₛ RegistrationBeaconReferenceCompiler.effect

noncomputable def afterAuthentication (implementation : QueryImpl (Spec n KemSK) m)
    (reserve : m Bool) (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else do
    let admitted ← StateT.lift (StateT.lift reserve)
    if admitted then do
      let accepted ← RegistrationNativePlatformServerOpenKernel.agreement implementation setup checks packet authenticated
      match accepted with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok none => pure (.ok none)
      | .ok (some ready) => retain ready
    else pure (.ok none)

noncomputable def afterPin (implementation : QueryImpl (Spec n KemSK) m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket)
    (result : RegistrationNativeServerPinRecompute.PinReply) : PublicM m (RustM (Option Nat)) :=
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

noncomputable def accept (implementation : QueryImpl (Spec n KemSK) m) (reserve : m Bool)
    (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify) (packet : registration.InitPacket) : PublicM m (RustM (Option Nat)) := do
  let before ← get
  let current ← StateT.lift (StateT.lift (RegistrationNativePlatformServerReferenceAccept.pin (effects implementation) before.pin))
  afterPin implementation reserve setup checks verify packet current

abbrev State (n : Nat) (KemSK Extra : Type) :=
  RegistrationServerMaterialFrontend.State × RegistrationNativeKemReferenceBackend.State n KemSK Extra

def sourceState (before : State n KemSK Extra) : RegistrationServerReferenceSourceRetain.State n :=
  (before.1, RegistrationNativeKemReferenceBackend.project before.2)

def project (roots : RegistrationServerReferenceRestore.Roots) (before : State n KemSK Extra) : RegistrationServerFrontendCompiler.State n :=
  RegistrationServerReferenceRestore.restore roots before.1 (RegistrationNativeKemReferenceBackend.project before.2)

def close (work : PublicM (StateT (Private n KemSK Extra) m) Value) : StateT (State n KemSK Extra) m Value := fun before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativePlatformServerOpenKernel.closeEnvironment (work.run before.1)).run before.2

theorem close_bind
    (work : PublicM (StateT (Private n KemSK Extra) m) Value)
    (next : Value → PublicM (StateT (Private n KemSK Extra) m) Next) :
    close (work >>= next) = (close work >>= fun value => close (next value)) := by
  funext before
  simp only [close, StateT.run, StateT.monad_bind_def, StateT.bind,
    RegistrationNativePlatformServerOpenKernel.closeEnvironment, map_bind, bind_map_left]

theorem close_pure (value : Value) (before : State n KemSK Extra) :
    (close (pure value : PublicM (StateT (Private n KemSK Extra) m) Value)).run before = pure (value, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (pure (((value, before.1), before.2.1), before.2.2) : m _)) = _
  simp only [map_pure]

theorem close_get (before : State n KemSK Extra) :
    (close (get : PublicM (StateT (Private n KemSK Extra) m) RegistrationServerMaterialFrontend.State)).run before =
      pure (before.1, before) := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    ((fun result => (result.1.1, (result.1.2, result.2))) <$>
      (pure (((before.1, before.1), before.2.1), before.2.2) : m _)) = _
  simp only [map_pure]

theorem close_reserve (work : m Value) (before : State n KemSK Extra) :
    (close (StateT.lift (StateT.lift (StateT.lift work)))).run before =
      (fun value => (value, before)) <$> work := by
  simp only [close, RegistrationNativePlatformServerOpenKernel.closeEnvironment, StateT.run,
    StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    bind_pure_comp, Functor.map_map]

theorem close_effect (work : StateT (Private n KemSK Extra) m Value) (before : State n KemSK Extra) :
    (close (StateT.lift (StateT.lift work))).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$> work.run before.2.2 := by
  simp only [close, RegistrationNativePlatformServerOpenKernel.closeEnvironment, StateT.run,
    StateT.lift, StateT.monad_bind_def, StateT.bind, StateT.monad_pure_def, StateT.pure,
    bind_pure_comp, Functor.map_map]

end BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_bind

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_pure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_get' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_get

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_reserve' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_reserve

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_effect' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformServerOpenControl.close_effect
