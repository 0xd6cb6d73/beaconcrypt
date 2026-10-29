-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeKemReferenceCompiler
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler

/-! The actual Server reference frontend forwards encapsulation through the same indexed KEM surface as owner creation and decapsulation. Authentication, owned replay and allocator ordering, native preparation, one-use handles and actual paired completion are unchanged. This additive compiler leaves the earlier closed real-KEM specialization available. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (Spec effect prepare)
open RegistrationServerReferenceRoot (Ready)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev M (n : Nat) (KemSK Value : Type) := StateT RegistrationServerMaterialFrontend.State
  (StateT Environment (OracleComp (Spec n KemSK))) Value

noncomputable def agreement (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n KemSK (RustM (Option Ready)) := do
  match ← StateT.lift (RegistrationNativeKemReferenceCompiler.collect setup checks packet authenticated) with
  | none => pure (.ok none)
  | some input => StateT.lift (StateT.lift (simulateQ prepare
      (RegistrationServerReferenceRoot.client authenticated.binding input)))

def retain (ready : Ready) : M n KemSK (RustM (Option Nat)) := fun before =>
  match RegistrationServerMaterialFrontend.retain ready before with
  | .fail error => pure (.fail error, before)
  | .div => pure (.div, before)
  | .ok (reply, after) => pure (.ok reply, after)

noncomputable def afterAuthentication (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit) : M n KemSK (RustM (Option Nat)) := do
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
    (packet : registration.InitPacket) : M n KemSK (RustM (Option Nat)) := do
  let before ← get
  let checked ← StateT.lift (StateT.lift (simulateQ effect
    (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.pin packet)))
  match checked with
  | .fail error => pure (.fail error)
  | .div => pure .div
  | .ok (_events, .Accepted authenticated) => afterAuthentication setup checks packet authenticated
  | .ok _ => pure (.ok none)

def service : QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr (.inl query))

def demand : QueryImpl
    (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
    (OracleComp (Spec n KemSK)) := fun message =>
  (Spec n KemSK).query (.inr (.inl (.inl message)))

/-- The finite material service runs on the caller's current environment, so Server and Beacon signing attempts share one chronological receipt log. -/
noncomputable def build (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (handle : Nat) (application : Option (Slice U8)) : M n KemSK RegistrationServerMaterialFrontend.Result := fun before =>
  simulateQ (RegistrationNativeCommonCompiler.service effect demand hkdf wire.frameWrite sign)
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before)

/-- Owned replay lookup remains before every ordinary callback, KEM getter, root preparation and material request. -/
theorem replay_rejected (setup : Setup base KemSK) (checks : Checks)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (before : RegistrationServerMaterialFrontend.State) (env : Environment)
    (replayed : before.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true) :
    (((afterAuthentication (n := n) setup checks packet authenticated).run before).run env) = pure ((.ok none, before), env) := by
  simp only [afterAuthentication, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, replayed, ite_true]

/-- Every actual malformed-application cancellation consumes the same moved one-use handle before performing no further native work. -/
theorem build_cancel (hkdf : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (wire : RegistrationNativeWire.Wire) (checks : Checks)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply) (handle : Nat)
    (ready : Ready) (before : RegistrationServerMaterialFrontend.State) (env : Environment)
    (live : before.sessions[handle]? = some (some ready)) :
    (((build (n := n) (KemSK := KemSK) hkdf wire checks sign handle none).run before).run env) =
      pure ((.ok none, { before with sessions := before.sessions.set handle none }), env) := by
  change (simulateQ (RegistrationNativeCommonCompiler.service effect demand hkdf wire.frameWrite sign)
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle none).run before)).run env = _
  rw [RegistrationServerMaterialFrontend.build_cancel wire checks.reservePeer handle ready before live]
  simp only [simulateQ_pure, StateT.run_pure]

end BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler

/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler.replay_rejected' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler.replay_rejected
/-- info: 'BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler.build_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationServerOpenReferenceCompiler.build_cancel
