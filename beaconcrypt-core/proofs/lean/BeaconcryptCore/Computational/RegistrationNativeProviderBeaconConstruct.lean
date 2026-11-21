-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderNative
import BeaconcryptCore.Computational.RegistrationNativePublicCreateMask
import BeaconcryptCore.Computational.RegistrationNativePublicBundleMask
import BeaconcryptCore.Computational.RegistrationNativePublicOwnerRestore

/-! Actual Beacon birth and outgoing publication retain the same arbitrary KEM provider. The pure native selected-scalar mask equations hold before oracle interpretation, so private pool creation, current World effects and failed outgoing histories stay literal under the provider interpreter. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderCallbacks (NativeState implementation)
open RegistrationNativeProviderBeaconAgreement (trusted)
open RegistrationNativeProviderBeaconPreparation (drop)
open RegistrationNativePublicSourceState (owners)
open RegistrationWorldAgreementCompiler (EnvState)
variable {n : Nat} {ι KemSK ProviderState Value Auxiliary : Type} {base : OracleSpec ι}
variable {source : RegistrationNativeMldsa.Source}

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

def restoreResult (scalar : PqxdhJointGapDh.ScalarBytes)
    (result : (Value × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) :=
  ((result.1.1, owners scalar result.1.2), result.2)

private theorem local_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (work native : RegistrationNativeBeaconFrontend.M n KemSK source Auxiliary Value)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (before : NativeState n KemSK ProviderState)
    (equation : Prod.map (Prod.map id (fun after => owners scalar
        (RegistrationNativePublicOwners.pack selected publicPrekey after))) id <$>
      ((work.run (roster.map RegistrationNativePublicOwners.restore)).run env) =
      ((native.run (owners scalar roster)).run env)) :
    Prod.map (restoreResult scalar) drop <$>
      (simulateQ (implementation setup wire route sign seed scalar provider false)
        (((RegistrationNativePublicOwners.executeLocal selected publicPrekey work).run roster).run env)).run before =
      (simulateQ (RegistrationNativeProviderNative.handler provider)
        ((native.run (owners scalar roster)).run env)).run (drop before) := by
  have raw := congrArg (fun program => Prod.map id drop <$>
    (simulateQ (trusted setup wire route sign seed scalar provider) program).run before) equation
  have projected := RegistrationNativeProviderNative.program_project setup wire route sign seed scalar provider
    ((native.run (owners scalar roster)).run env) before
  apply Eq.trans (b := Prod.map id drop <$>
    (simulateQ (trusted setup wire route sign seed scalar provider)
      ((native.run (owners scalar roster)).run env)).run before) ?_ projected
  simpa only [RegistrationNativePublicOwners.executeLocal, StateT.run, map_apply,
    simulateQ_map, StateT.run_map, trusted, QueryImpl.simulateQ_compose,
    Functor.map_map, Prod.map_def, id_eq, restoreResult] using raw

/-- Actual native creation uses the same private pool/provider and exact current World, with no constructor-success or source-simulation premise. -/
theorem create_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Nat)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState RegistrationServerRoleBackend.State)
    (before : NativeState n KemSK ProviderState)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) roster) :
    Prod.map (restoreResult scalar) drop <$>
      (simulateQ (implementation setup wire route sign seed scalar provider false)
        (((RegistrationNativePublicOwners.create setup source selected (setup.dh.publicKey scalar) edPin mlPin keyId).run roster).run env)).run before =
      (simulateQ (RegistrationNativeProviderNative.handler provider)
        (((RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId).run
          (owners scalar roster)).run env)).run (drop before) := by
  apply local_source setup wire route sign seed scalar provider selected (setup.dh.publicKey scalar)
    _ (RegistrationNativeScalarEager.create setup source selected scalar edPin mlPin keyId) roster env before
  have equation := RegistrationNativePublicCreateMask.create_mask (n := n) setup source selected scalar edPin mlPin keyId
    (roster.map RegistrationNativePublicOwners.restore) env
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selected scalar (setup.dh.publicKey scalar) roster canonical] at equation
  simpa only [RegistrationNativePublicOwnerRestore.restore_pack] using equation

/-- Complete native outgoing publication and its failures preserve the same provider and exact returned owner/environment state. -/
theorem bundle_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected index : Nat)
    (roster : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary)
    (before : NativeState n KemSK ProviderState)
    (canonical : RegistrationNativePublicOwnerMask.Canonical selected (setup.dh.publicKey scalar) roster) :
    Prod.map (restoreResult scalar) drop <$>
      (simulateQ (implementation setup wire route sign seed scalar provider false)
        (((RegistrationNativePublicOwners.bundle setup source wire selected (setup.dh.publicKey scalar) index).run roster).run env)).run before =
      (simulateQ (RegistrationNativeProviderNative.handler provider)
        (((RegistrationNativeBeaconFrontend.bundle setup source wire index).run (owners scalar roster)).run env)).run (drop before) := by
  apply local_source setup wire route sign seed scalar provider selected (setup.dh.publicKey scalar)
    _ (RegistrationNativeBeaconFrontend.bundle setup source wire index) roster env before
  have publicKey : ∀ owner, (roster.map RegistrationNativePublicOwners.restore)[selected]? = some owner →
      owner.prekeyPublic = PqxdhRootTableInitialization.rootArray (setup.dh.publicKey scalar) := by
    intro owner found
    simp only [List.getElem?_map, Option.map_eq_some_iff] at found
    obtain ⟨exposed, present, rfl⟩ := found
    have chosen := canonical selected exposed present
    simp only [RegistrationNativePublicOwnerMask.At, ite_true] at chosen
    exact chosen.2
  have equation := RegistrationNativePublicBundleMask.bundle_mask (n := n) setup source wire index selected scalar
    (setup.dh.publicKey scalar) (roster.map RegistrationNativePublicOwners.restore) env publicKey
  rw [RegistrationNativePublicOwnerRestore.restored_dummy selected scalar (setup.dh.publicKey scalar) roster canonical] at equation
  simpa only [RegistrationNativePublicOwnerRestore.restore_pack] using equation

end BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct.create_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderBeaconConstruct.bundle_source
