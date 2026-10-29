-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSelectiveBeaconCompletionSource

/-! A scalar-free owner's literal public typed finish is exactly its original terminal owner controller, with the reached current environment and full thin private state. The source diagram retains the same roster position and every other frontend field. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedBeaconSource
open PqxdhServerAuthExperiment (Setup Checks)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : A → B) (work : StateT S m A) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- The same scalar-free original public owner is passed to the original actual terminal finish controller. -/
theorem selected_finish (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (index : Nat) (packet : Option registration.ResponsePacket) (frontend : RegistrationNativePublicFrontend.State source)
    (owner : RegistrationNativePublicOwners.Owner source) (found : frontend.beacons[index]? = some owner)
    (hidden : owner.scalar = none) (before : RegistrationNativeSelectiveHiddenInterpreter.State n KemSK ProviderState) :
    (simulateQ (RegistrationNativeSelectiveHiddenInterpreter.handler setup wire sign seed scalar candidate provider)
      ((RegistrationNativePublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.finish index packet))).run frontend)).run before =
      (fun result => ((result.1.1.1, { frontend with beacons := frontend.beacons.set index ({ owner with view := result.1.1.2 }), environment := result.1.2 }), result.2)) <$>
        (simulateQ (RegistrationNativeSelectiveMaterialSource.closedLocal setup wire sign seed scalar candidate provider)
          (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner.view).run frontend.environment)).run before := by
  simp only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    RegistrationNativePublicOwners.finish, found, hidden, StateT.run, simulateQ_map, map_apply,
    RegistrationNativeSelectiveMaterialSource.closedLocal, QueryImpl.simulateQ_compose, Functor.map_map,
    Prod.map_def, id_eq]

end BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedBeaconSource

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedBeaconSource.selected_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSelectiveTypedBeaconSource.selected_finish
