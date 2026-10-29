-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationServerMaterialFrontend
import BeaconcryptCore.Computational.RegistrationWorldAgreementProgramCompiler
import BeaconcryptCore.Computational.RegistrationAuthenticationBounds

/-! The executable Server frontend owns public one-use reference capabilities and ordinary local ephemeral state. The record World, selected identity seed, selected static DH value, prepared root32 and hidden seed64 are absent from its state. Native authentication hashes and all local primitive draws are open EnvEffects; root preparation is a message-reference service before later gated material demand. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerReferenceCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (EnvEffects)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationServerReferenceRoot (Ready PrepareSpec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev Spec (n : Nat) := PrepareSpec + RegistrationNativePairedServerService.PublicSpec n
abbrev Environment := EnvState RegistrationServerRoleBackend.State
abbrev State := RegistrationServerMaterialFrontend.State × Environment
abbrev M (n : Nat) (Value : Type) := StateT RegistrationServerMaterialFrontend.State
  (StateT Environment (OracleComp (Spec n))) Value

def effect (query : (EnvEffects n).Domain) : OracleComp (Spec n) ((EnvEffects n).Range query) :=
  (Spec n).query (.inr (.inr (.inr query)))

def prepare (query : PrepareSpec.Domain) : OracleComp (Spec n) (PrepareSpec.Range query) :=
  (Spec n).query (.inl query)

def service (query : (RegistrationNativePairedServerService.PublicSpec n).Domain) :
    OracleComp (Spec n) ((RegistrationNativePairedServerService.PublicSpec n).Range query) :=
  (Spec n).query (.inr query)

def liftEnvironment (work : StateT Environment (OracleComp (EnvEffects n)) Value) :
    StateT Environment (OracleComp (Spec n)) Value := fun before => simulateQ effect (work.run before)

noncomputable def backend (setup : Setup base KemSK) (checks : Checks) :
    QueryImpl RegistrationAgreementExecutor.Spec (StateT Environment (OracleComp (Spec n))) :=
  fun query => liftEnvironment (RegistrationWorldAgreementCompiler.compiler setup.source
    (RegistrationServerRoleBackend.localBackend setup checks) query)

def visit (point : PqxdhBeaconPhase2Preparation.Word32) : StateT Environment (OracleComp (Spec n)) Unit :=
  fun before => pure ((), { before with requests := before.requests ++ [.dh ⟨.LocalIdentity, point⟩] })

noncomputable def collect (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) :
    StateT Environment (OracleComp (Spec n))
      (Option (PqxdhServerRootPreparation.Inputs registration.InitPacket Unit PqxdhJointIdentity.PeerEncoding)) :=
  simulateQ (PqxdhServerStaticDhSource.prefixImpl setup.serverDomain
    (RegistrationAgreementInterpreter.prepImpl (backend setup checks)) visit)
    (PqxdhServerRootPreparation.collectVerified (RegistrationRootInput.verified packet authenticated))

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n (RustM (Option Ready)) := do
  let input ← StateT.lift (collect setup checks packet authenticated)
  match input with
  | none => pure (.ok none)
  | some input => StateT.lift (StateT.lift (simulateQ prepare
      (RegistrationServerReferenceRoot.client authenticated.binding input)))

def retain (ready : Ready) : M n (RustM (Option Nat)) := fun before =>
  match RegistrationServerMaterialFrontend.retain ready before with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, after)

/-- The actual private replay lookup and allocator gate are before any root preparation or material query. -/
noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n (RustM (Option Nat)) := do
  let before ← get
  if before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none)
  else if checks.reserveRegistration then do
    let accepted ← agreement setup checks packet authenticated
    match accepted with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok none => pure (.ok none)
    | .ok (some ready) => retain ready
  else pure (.ok none)

noncomputable def accept (setup : Setup base KemSK) (checks : Checks) (verify : MldsaTranscriptAuth.Verify)
    (packet : registration.InitPacket) : M n (RustM (Option Nat)) := do
  let before ← get
  let checked ← StateT.lift (StateT.lift (simulateQ effect
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet)))
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks packet authenticated
  | .ok _ => pure (.ok none)

noncomputable def build (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (handle : Nat) (application : Option (Slice U8)) : M n RegistrationServerMaterialFrontend.Result := fun before =>
  StateT.lift (simulateQ service ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before))

end BeaconcryptCore.Computational.RegistrationServerReferenceCompiler
