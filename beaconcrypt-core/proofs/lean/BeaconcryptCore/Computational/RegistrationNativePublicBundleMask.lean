-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicBundleScalar
import BeaconcryptCore.Computational.RegistrationNativeBundlePublicFields

/-! Stored challenge public prekeys persist under the actual outgoing controller. Combining that concrete support invariant with scalar-only equivariance gives the complete public-pack/private-restore bundle equation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicBundleMask
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicScalarMap (change)
open RegistrationNativePublicOwnerRestore (mask)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

/-- Every supported outgoing result retains the selected public prekey from the actual input owner. -/
theorem bundle_public (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (valid : ∀ owner, owners[selected]? = some owner → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey)
    (result : (RustM (Option Pqxdh.Bytes) × RegistrationNativeBeaconFrontend.State source) × RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (supported : result ∈ support (((RegistrationNativeBeaconFrontend.bundle (n := n) setup source wire index).run owners).run env)) :
    ∀ owner, result.1.2[selected]? = some owner → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey := by
  have same := RegistrationNativeBundlePublicFields.bundle_metadata setup source wire index owners env result supported
  change result.1.2.map (fun owner => owner.prekeyPublic) = owners.map (fun owner => owner.prekeyPublic) at same
  intro owner found
  have entry := congrArg (fun roster => roster[selected]?) same
  simp only [List.getElem?_map, found, Option.map_some] at entry
  cases original : owners[selected]? with
  | none => simp only [original, Option.map_none] at entry; contradiction
  | some originalOwner =>
      simp only [original, Option.map_some, Option.some.injEq] at entry
      exact entry.trans (valid originalOwner original)

/-- Actual bundle execution commutes with the complete selected scalar/public-prekey mask whenever that public key is already canonical. -/
theorem bundle_mask (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (wire : RegistrationNativeWire.Wire) (index selected : Nat) (scalar : PqxdhJointGapDh.ScalarBytes)
    (publicPrekey : PqxdhJointIdentity.PeerEncoding) (owners : RegistrationNativeBeaconFrontend.State source)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (valid : ∀ owner, owners[selected]? = some owner → owner.prekeyPublic = PqxdhRootTableInitialization.rootArray publicPrekey) :
    Prod.map (Prod.map id (mask selected scalar publicPrekey)) id <$>
      ((RegistrationNativeBeaconFrontend.bundle (n := n) setup source wire index).run owners).run env =
      ((RegistrationNativeBeaconFrontend.bundle setup source wire index).run (mask selected scalar publicPrekey owners)).run env := by
  rw [RegistrationNativePublicScalarMap.mask_eq selected scalar publicPrekey owners valid]
  rw [← RegistrationNativePublicBundleScalar.bundle_scalar setup source wire index selected scalar owners env]
  simp only [map_eq_bind_pure_comp]
  apply OracleComp.bind_congr_of_forall_mem_support
  intro result supported
  simp only [Function.comp_apply, Prod.map_def, id_eq]
  rw [RegistrationNativePublicScalarMap.mask_eq selected scalar publicPrekey result.1.2
    (bundle_public setup source wire index selected publicPrekey owners env valid result supported)]

end BeaconcryptCore.Computational.RegistrationNativePublicBundleMask
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicBundleMask.bundle_public' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicBundleMask.bundle_public
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicBundleMask.bundle_mask' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicBundleMask.bundle_mask
