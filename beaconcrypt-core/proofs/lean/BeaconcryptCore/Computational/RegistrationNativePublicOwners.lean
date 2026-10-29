-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeLocalMessage

/-! The executable related-root client keeps the selected owner's prekey scalar outside its state. Ordinary owners retain their local scalar and translate only their two prekey-DH coordinates to supplied native messages. Birth and outgoing publication reuse the actual local controllers with an unused dummy scalar for the selected owner and its public challenge prekey. This module defines that public view; the source sampling interchange and complete source simulation are separate theorems. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicOwners
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
open RegistrationBeaconReferenceCompiler (SelectedOwner eraseOwner restoreOwner Spec trustedLift)
open RegistrationWorldAgreementCompiler (EnvState)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

/-- Only an ordinary owner's locally owned scalar enters the executable state. -/
structure Owner (source : RegistrationNativeMldsa.Source) where
  view : SelectedOwner source
  scalar : Option ScalarBytes

abbrev State (source : RegistrationNativeMldsa.Source) := List (Owner source)
abbrev M (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) (Value : Type) :=
  StateT (State source) (StateT (EnvState Auxiliary) (OracleComp (Spec n KemSK))) Value

def dummy : ScalarBytes := List.Vector.replicate 32 0

def restore {source : RegistrationNativeMldsa.Source} (owner : Owner source) :
    RegistrationNativeBeaconFrontend.Owner source := restoreOwner (owner.scalar.getD dummy) owner.view

def pack {source : RegistrationNativeMldsa.Source} (selected : Nat) (publicPrekey : PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) : State source :=
  owners.mapIdx fun index owner =>
    if index = selected then
      ⟨eraseOwner { owner with prekeyPublic := PqxdhRootTableInitialization.rootArray publicPrekey }, none⟩
    else ⟨eraseOwner owner, some owner.prekeyScalar⟩

/-- All ordinary fields and local scalar are restored literally; no secret challenge value is required. -/
theorem restore_ordinary {source : RegistrationNativeMldsa.Source}
    (owner : RegistrationNativeBeaconFrontend.Owner source) :
    restore (⟨eraseOwner owner, some owner.prekeyScalar⟩ : Owner source) = owner := by
  exact RegistrationBeaconReferenceCompiler.restore_erase owner

/-- Changing a selected owner's private source scalar does not change its executable public view. -/
theorem erase_scalar {source : RegistrationNativeMldsa.Source}
    (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : ScalarBytes) :
    eraseOwner { owner with prekeyScalar := scalar } = eraseOwner owner := rfl

/-- Local materialization is applied only at root preparation. Returned references retain the translated literal address, and all other primitive requests are unchanged. -/
def ordinary (setup : Setup base KemSK) (scalar : ScalarBytes) :
    QueryImpl (Spec n KemSK) (OracleComp (Spec n KemSK))
  | .inl message => match RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message with
      | none => pure none
      | some message => (Spec n KemSK).query (.inl message)
  | .inr query => (Spec n KemSK).query (.inr query)

/-- Actual birth and outgoing controllers use only the selected public prekey after the private constructor scalar has been erased. -/
noncomputable def executeLocal {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : M n KemSK Auxiliary source Value :=
  fun owners env => (fun result => ((result.1.1, pack selected publicPrekey result.1.2), result.2)) <$>
    simulateQ trustedLift ((work.run (owners.map restore)).run env)

noncomputable def create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PeerEncoding) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : M n KemSK Auxiliary source (RustM (Option Nat)) :=
  executeLocal selected publicPrekey (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)

noncomputable def bundle (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (selected : Nat) (publicPrekey : PeerEncoding) (index : Nat) :
    M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  executeLocal selected publicPrekey (RegistrationNativeBeaconFrontend.bundle setup source wire index)

/-- Both selected and ordinary owners run the same terminal lifecycle and paired native first-record service. -/
noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := fun owners env =>
  match owners[index]? with
  | none => pure ((.ok none, owners), env)
  | some owner =>
      let work := ((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view).run env
      let changed := match owner.scalar with
        | none => work
        | some scalar => simulateQ (ordinary setup scalar) work
      (fun result => ((result.1.1, owners.set index { owner with view := result.1.2 }), result.2)) <$> changed

end BeaconcryptCore.Computational.RegistrationNativePublicOwners

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwners.restore_ordinary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwners.restore_ordinary
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicOwners.erase_scalar' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicOwners.erase_scalar
