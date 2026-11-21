-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFrontend
import BeaconcryptCore.Computational.RegistrationNativePlatformBundleMetadata
import BeaconcryptCore.Computational.RegistrationNativeSecretWordOwnerPins
import BeaconcryptCore.Computational.RegistrationNativeOwnerFields
import BeaconcryptCore.Computational.RegistrationNativeOwnerPinBirth
import BeaconcryptCore.Computational.RegistrationNativeKemBirthCreateShape

/-! The actual selected-scalar view preserves immutable configured owner pins. Native outgoing controller metadata preserves these public bindings independently of every private root or KEM interpretation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields
open PqxdhServerAuthExperiment (Setup)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativePublicOwners (Owner State)
open RegistrationNativeBeaconFrontend (Trusted)
variable {n : Nat} {ι Q KemSK Auxiliary Platform E : Type} {base : OracleSpec ι} {target : OracleSpec Q} {source : RegistrationNativeMldsa.Source}

open RegistrationNativeSecretWordOwnerPins (key nativeKey pack_keys restore_keys)
variable {targetSpec : OracleSpec Q}
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before

/-- Actual public bundle preserves every retained configured Server pin through arbitrary stateful source writers and all failures. -/
theorem public_keys (setup : Setup base KemSK)
    (implementation : QueryImpl (Trusted n KemSK) (StateT Platform (OracleComp targetSpec)))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform (OracleComp targetSpec)))
    (selected target : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (owners : RegistrationNativePublicOwners.State source) (env : EnvState Auxiliary) (previous : Platform)
    (result : ((RustM (Option (alloc.vec.Vec U8)) × RegistrationNativePublicOwners.State source) × EnvState Auxiliary) × Platform)
    (supported : result ∈ support
      ((((RegistrationNativePlatformPublicOwners.bundle implementation writer setup source selected publicPrekey target).run owners).run env).run previous)) :
    result.1.1.2.map RegistrationNativeSecretWordOwnerPins.key = owners.map RegistrationNativeSecretWordOwnerPins.key := by
  simp only [RegistrationNativePlatformPublicOwners.bundle, RegistrationNativePlatformPublicOwners.executeLocal,
    StateT.run, map_apply, support_map] at supported
  obtain ⟨middle, reached, equal⟩ := supported
  let dictionary : QueryImpl (RegistrationNativePlatformGenericBundle.Spec E n KemSK) (StateT Platform (OracleComp targetSpec)) :=
    fun query => match query with | .inl query => implementation query | .inr query => writer query
  have translated := RegistrationNativePlatformGenericBundle.program_evaluate (Auxiliary := Auxiliary) dictionary setup source target
  have original : middle.1 ∈ support
      (((RegistrationNativePlatformGenericBundle.program (n := n) E setup source target).run (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply OracleComp.support_simulateQ_run'_subset dictionary _ previous
    rw [StateT.run'_eq, support_map]
    refine ⟨middle, ?_, rfl⟩
    change middle ∈ support ((((RegistrationNativePlatformGenericBundle.evaluate dictionary
      (RegistrationNativePlatformGenericBundle.program (n := n) E setup source target)).run (owners.map RegistrationNativePublicOwners.restore)).run env).run previous)
    rw [translated]
    exact reached
  have metadata := RegistrationNativePlatformBundleMetadata.program (n := n) setup source target
    (owners.map RegistrationNativePublicOwners.restore) env middle.1 original
  have kept : middle.1.1.2.map nativeKey = (owners.map RegistrationNativePublicOwners.restore).map nativeKey := by
    calc
      _ = (middle.1.1.2.map RegistrationNativeOwnerFields.metadata).map nativeKey := by rw [List.map_map]; rfl
      _ = ((owners.map RegistrationNativePublicOwners.restore).map RegistrationNativeOwnerFields.metadata).map nativeKey := congrArg (List.map nativeKey) metadata
      _ = _ := by rw [List.map_map]; rfl
  cases equal
  simp only [Prod.map_def, id_eq]
  rw [RegistrationNativeSecretWordOwnerPins.pack_keys, kept, RegistrationNativeSecretWordOwnerPins.restore_keys]
/-- The literal new Word bundle retains its complete configured owner-pin roster through dynamic encoding and every shared platform outcome, without a private alignment premise. -/
theorem bundle_keys (setup : Setup base KemSK) (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (target : Nat) (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (result : RustM (Option Pqxdh.Bytes) × RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) (KemSK := KemSK) setup source
      selectedOwner publicPrekey reserveFrame writer (.inr (.bundle target))).run before)) :
    result.2.1.beacons.map RegistrationNativeSecretWordOwnerPins.key =
      before.1.beacons.map RegistrationNativeSecretWordOwnerPins.key := by
  rw [RegistrationNativePlatformSecretWordOrdinary.handler, StateT.run_map, support_map] at supported
  obtain ⟨raw, possible, equal⟩ := supported
  simp only [RegistrationNativePlatformSecretWordOrdinary.beacon, StateT.run, support_map] at possible
  obtain ⟨middle, reached, same⟩ := possible
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ reached
  have kept := public_keys setup RegistrationNativePlatformPublicFrontend.trusted (RegistrationNativePlatformPublicFrontend.writer writer)
    selectedOwner target publicPrekey before.1.beacons before.1.environment before.2 middle original
  cases equal
  cases same
  exact kept

private theorem native_create_keys (setup : Setup base KemSK)
    (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : RegistrationNativeBeaconFrontend.State source) (env : RegistrationServerReferenceCompiler.Environment)
    (result : (RustM (Option Nat) × RegistrationNativeBeaconFrontend.State source) × RegistrationServerReferenceCompiler.Environment)
    (supported : result ∈ support (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run owners).run env)) :
    result.1.2.map nativeKey = match result.1.1 with
      | .ok (some _) => owners.map nativeKey ++ [(edPin,keyId)]
      | _ => owners.map nativeKey := by
  have shape := RegistrationNativeKemBirthCreateShape.create_shape setup source edPin mlPin keyId
    owners env result.1.1 result.1.2 result.2 supported
  cases actual : result.1.1 with
  | fail error | div =>
    simp only [RegistrationNativeKemBirthCreateShape.Shape,actual] at shape
    rw [shape]
  | ok reply => cases reply with
    | none =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape,actual] at shape
      rw [shape]
    | some index =>
      simp only [RegistrationNativeKemBirthCreateShape.Shape,actual] at shape
      obtain ⟨indexEq,born,roster⟩ := shape
      obtain ⟨owner,found,binding,_ml⟩ := RegistrationNativeOwnerPinBirth.create_pin setup source edPin mlPin keyId
        owners env index result.1.2 result.2 (by simpa only [←actual,Prod.mk.eta] using supported)
      rw [roster,indexEq] at found
      simp only [List.getElem?_append,Nat.lt_irrefl,ite_false,Nat.sub_self,List.getElem?_cons_zero,Option.some.injEq] at found
      have pin := (congrArg (fun owner => owner.pin.binding) found).trans binding
      simp only [roster,List.map_append,List.map_cons,List.map_nil,nativeKey]
      rw [congrArg pqxdh.ServerBinding.identity_public_key pin,congrArg pqxdh.ServerBinding.identity_key_id pin]

/-- The actual common-platform constructor appends exactly its configured pin on success and retains all prior pins on failure. -/
theorem public_create (setup : Setup base KemSK)
    (implementation : QueryImpl (RegistrationNativeBeaconFrontend.Trusted n KemSK) (StateT Platform (OracleComp target)))
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (owners : State source) (env : RegistrationServerReferenceCompiler.Environment) (previous : Platform)
    (result : ((RustM (Option Nat) × State source) × RegistrationServerReferenceCompiler.Environment) × Platform)
    (supported : result ∈ support ((((RegistrationNativePlatformPublicOwners.create implementation setup source selected publicPrekey edPin mlPin keyId).run owners).run env).run previous)) :
    result.1.1.2.map key = match result.1.1.1 with
      | .ok (some _) => owners.map key ++ [(edPin,keyId)]
      | _ => owners.map key := by
  simp only [RegistrationNativePlatformPublicOwners.create,RegistrationNativePlatformPublicOwners.executeLocal,StateT.run,map_apply,support_map] at supported
  obtain ⟨middle,called,equal⟩ := supported
  have original : middle.1 ∈ support (((RegistrationNativeBeaconFrontend.create (n := n) setup source edPin mlPin keyId).run
      (owners.map RegistrationNativePublicOwners.restore)).run env) := by
    apply OracleComp.support_simulateQ_run'_subset implementation _ previous
    rw [StateT.run'_eq,support_map]
    exact ⟨middle,by simpa only [RegistrationNativePlatformGenericBundle.liftLegacy,StateT.run] using called,rfl⟩
  have kept := native_create_keys setup edPin mlPin keyId (owners.map RegistrationNativePublicOwners.restore) env middle.1 original
  cases equal
  simp only [Prod.map_def,id_eq]
  rw [pack_keys,kept,restore_keys]

/-- The literal current Word constructor has the same configured-pin append law on every free outcome. -/
theorem word_create (setup : Setup base KemSK) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (edPin : PqxdhBeaconPhase2Preparation.Word32) (mlPin : Std.Array U8 1952#usize) (keyId : U64)
    (before : RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (result : RustM (Option Nat) × RegistrationNativePlatformSecretWordOrdinary.State source Platform)
    (supported : result ∈ support ((RegistrationNativePlatformSecretWordOrdinary.handler (n := n) setup source selected publicPrekey reserveFrame writer
      (.inr (.create edPin mlPin keyId))).run before)) :
    result.2.1.beacons.map key = match result.1 with
      | .ok (some _) => before.1.beacons.map key ++ [(edPin,keyId)]
      | _ => before.1.beacons.map key := by
  simp only [RegistrationNativePlatformSecretWordOrdinary.handler,RegistrationNativePlatformSecretWordOrdinary.beacon,StateT.run,support_map] at supported
  obtain ⟨middle,called,equal⟩ := supported
  have original := PqxdhDeploymentEnvironment.support_simulateQ_subset _ _ called
  have kept := public_create setup RegistrationNativePlatformPublicFrontend.trusted selected publicPrekey edPin mlPin keyId
    before.1.beacons before.1.environment before.2 middle original
  cases equal
  exact kept

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.public_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.public_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.bundle_keys' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.bundle_keys

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.public_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.public_create

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.word_create' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerPinFields.word_create
