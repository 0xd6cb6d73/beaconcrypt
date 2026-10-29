-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordBeaconSource
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLocalMessage

/-! The symbolic owner roster runs the actual birth and outgoing controllers and the actual terminal incoming controller. Ordinary owners translate their two locally owned DH coordinates before preparation while retaining the opaque KEM word and the exact translated returned reference. The selected owner contains no selected scalar, and this executable roster contains no candidate shared-secret value. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners
open PqxdhServerAuthExperiment (Setup)
open PqxdhJointGapDh (ScalarBytes)
open PqxdhJointIdentity (PeerEncoding)
open RegistrationNativePublicOwners (Owner State)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec)
variable {ι KemSK Auxiliary Value : Type} {base : OracleSpec ι} {n : Nat}

abbrev M (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) (Value : Type) :=
  StateT (State source) (StateT (EnvState Auxiliary) (OracleComp (LocalSpec n KemSK))) Value

def ordinary (setup : Setup base KemSK) (scalar : ScalarBytes) :
    QueryImpl (LocalSpec n KemSK) (OracleComp (LocalSpec n KemSK))
  | .inl message => match RegistrationNativeSecretWordLocalMessage.materialize setup.joint setup.dh scalar message with
      | none => pure none
      | some message => (LocalSpec n KemSK).query (.inl message)
  | .inr query => (LocalSpec n KemSK).query (.inr query)

noncomputable def executeLocal {source : RegistrationNativeMldsa.Source}
    (selected : Nat) (publicPrekey : PeerEncoding)
    (work : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value) : M n KemSK Auxiliary source Value :=
  fun owners env => simulateQ (RegistrationNativeSecretWordServerSource.realize RegistrationNativeSecretWordMessage.zero)
    (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run owners).run env)

noncomputable def create (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selected : Nat) (publicPrekey : PeerEncoding) (edPin : Std.Array U8 32#usize)
    (mlPin : Std.Array U8 1952#usize) (keyId : U64) : M n KemSK Auxiliary source (RustM (Option Nat)) :=
  executeLocal selected publicPrekey (RegistrationNativeBeaconFrontend.create setup source edPin mlPin keyId)

noncomputable def bundle (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (selected : Nat) (publicPrekey : PeerEncoding) (index : Nat) :
    M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) :=
  executeLocal selected publicPrekey (RegistrationNativeBeaconFrontend.bundle setup source wire index)

noncomputable def finish (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) :
    M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := fun owners env =>
  match owners[index]? with
  | none => pure ((.ok none, owners), env)
  | some owner =>
      let work := ((RegistrationNativeSecretWordBeaconCompiler.finish setup source packet).run owner.view).run env
      let changed := match owner.scalar with
        | none => work
        | some scalar => simulateQ (ordinary setup scalar) work
      (fun result => ((result.1.1, owners.set index { owner with view := result.1.2 }), result.2)) <$> changed

/-- An absent local owner makes no callback and changes no roster or environment field. -/
theorem finish_missing (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (index : Nat) (packet : Option registration.ResponsePacket) (owners : State source) (env : EnvState Auxiliary)
    (missing : owners[index]? = none) :
    (((finish (n := n) setup source index packet).run owners).run env) = pure ((.ok none, owners), env) := by
  simp only [finish, StateT.run, missing]

end BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners.finish_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordOwners.finish_missing
