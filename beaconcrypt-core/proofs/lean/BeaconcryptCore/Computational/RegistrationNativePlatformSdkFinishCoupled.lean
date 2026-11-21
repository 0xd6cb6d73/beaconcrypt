-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkStrongFinishSteps
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishAuxiliaryFrame
/-! The monitored native Finish runner supplies one joint source-object/native packet, all source normality and current material facts. Its actual original SDK physical marginal is established separately from the closed source primitive dictionary after erasing the indexed KEM observation log. No free-program decapsulation or whole source correspondence is an input to this coupling constructor. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled
open BeaconcryptCore.Refinement
open AdapterPublicFinishLifetime (packet)
open RegistrationNativePlatformExtractedSdkFinish (runner BodyResult sourceProjection nativeProjection)
variable {n : Nat} {I KemSK R P : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]

omit platform in
theorem native (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]?)
    (selected : before.beacons[index]?=some owner) (phase : owner.phase=.initSent pending scalar) (previous : P) :
    (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous =
      Prod.map (nativeProjection index owner pending before.beacons) id <$>
        (runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous := by
  have free := RegistrationNativeFinishLifetime.source_ready view setup checks representation created wire index self owner
    pending prekey oneTime kem scalar stored (packet input) before related selected phase
  have actual : (RegistrationNativeExperiment.beacon setup checks representation created
      (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before =
      nativeProjection index owner pending before.beacons <$>
        RegistrationNativeFinishLifetime.tree setup checks representation created wire pending (packet input) owner scalar before := by
    rw [RegistrationNativePlatformExtractedFinish.finish_source]
    exact free
  rw [actual,simulateQ_map,StateT.run_map]
  rfl

noncomputable def active (coins : QueryImpl unifSpec (StateT P ProbComp))
    (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (wire : RegistrationNativeWire.Wire) (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (pending : registration.BeaconPending)
    (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair) (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair)
    (stored : self.state=.InitSent pending prekey oneTime kem) (input : Slice U8)
    (owner : RegistrationNativeBeaconFrontend.Owner source) (scalar : PqxdhJointGapDh.ScalarBytes)
    (before : RegistrationNativeExperiment.State n KemSK source) (index : Nat)
    (selected : before.beacons[index]?=some owner) (phase : owner.phase=.initSent pending scalar) (previous : P)
    (objects : RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential (before,previous))
    (sourceSelected : objects.base.objects.beacons index=some self) :
    RegistrationNativePlatformExtractedSdkPublic.TotalStep
      (RegistrationNativePlatformSdkStrongCarrier.StrongCarrier (R:=R) setup view containers created credential)
      ((fun result=>(result.1.1,(result.1.2,result.2))) <$>
        (simulateQ coins ((RegistrationNativeExperiment.beacon setup checks representation created
          (RegistrationNativePlatformExtractedFinish.finish setup source wire index (packet input))).run before)).run previous) := by
  have related : AdapterPublicWrapperState.Beacon view setup.joint before.pool self owner before.server.world.world.1.owners[owner.worldOwner]? := by
    have prior:=objects.base.beacons index
    rw [selected] at prior
    obtain ⟨actual,found,material⟩:=prior
    have same:actual=self:=Option.some.inj (found.symm.trans sourceSelected)
    subst actual
    exact material
  let sample:=(runner coins setup checks representation created wire pending (packet input) owner scalar before).run previous
  let sourceReply:=fun raw : BodyResult n KemSK source × P =>(sourceProjection self pending raw.1).1
  let sourceState:=fun raw : BodyResult n KemSK source × P =>(raw.1.2,raw.2)
  let nativeReply:=fun raw : BodyResult n KemSK source × P =>
    ((nativeProjection index owner pending before.beacons raw.1).1,
      ((nativeProjection index owner pending before.beacons raw.1).2,raw.2))
  refine {
    step:={
      Packet:=BodyResult n KemSK source × P
      sample:=sample
      sourceType:=AdapterPublicFinishBody.Result
      sourceReply:=sourceReply
      sourceState:=sourceState
      sourceCall:=(fun raw=>(sourceReply raw,sourceState raw)) <$>sample
      source_exact:=rfl
      native:=nativeReply
      native_exact:=?_
      store:=?_ }
    observe:=fun value=>AdapterPublicFinishEndpoint.bytes (.ok value)
    normal:=?_
    reply:=?_ }
  · have actual:=native coins setup checks representation created wire view self pending prekey oneTime kem stored input
      owner scalar before index related selected phase previous
    rw [actual,Functor.map_map]
    rfl
  · rintro ⟨raw,next⟩ supported
    have receipt:=RegistrationNativePlatformExtractedSdkFinish.returned_material view setup checks representation created wire
      index self owner pending prekey oneTime kem scalar stored before related selected phase (packet input) raw coins previous next supported
    cases actual:sourceReply (raw,next) with
    | fail error | div => exact PUnit.unit
    | ok returned =>
        have actualNormal : AdapterPublicFinishNormalized.output
            {self with state:=.Aborted (RegistrationResponse.abortedState pending)} raw.1.1=.ok returned :=actual
        have facts : AdapterPublicFinishEndpoint.bytes (.ok returned)=RegistrationNativeFinishTerminalTree.bytes raw.1.1 ∧
            (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).beacons[index]?=
              some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1) ∧
            AdapterPublicWrapperState.Beacon view setup.joint
              (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).pool returned.2
              (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1)
              (AdapterPublicFinishLifetime.finalState index owner (RegistrationResponse.abortedState pending) before.beacons raw).server.world.world.1.owners[owner.worldOwner]? := by
          obtain ⟨word,normal,rest⟩:=receipt
          have same:word=returned:=RustM.ok.inj (normal.symm.trans actualNormal)
          subst word
          exact rest
        have found:=facts.2.1
        have material:=facts.2.2
        let baseAfter:=RegistrationNativePlatformExtractedSdkCarrierFinish.put coins setup checks representation created view containers credential wire
          (before,previous) objects.base index owner selected self sourceSelected pending prekey oneTime kem scalar stored phase
          (packet input) (raw,next) supported returned found material
        refine ⟨baseAfter,?_⟩
        change RegistrationNativePlatformSdkStrongCarrier.OtkPublic _ view
          (Function.update objects.base.objects.beacons index (some returned.2))
        apply RegistrationNativePlatformSdkStrongCarrier.update_public view _ _ objects.otkPublic index returned.2
        intro control beforeKey ot keys returnedState
        have matched:=material.phase
        cases outcome:raw.1.1 with
        | fail error | div=>simp only [AdapterPublicFinishLifetime.ownerAfter,outcome,AdapterPublicWrapperState.Phase,returnedState] at matched
        | ok completed=>cases completed with
          | none=>simp only [AdapterPublicFinishLifetime.ownerAfter,outcome,AdapterPublicWrapperState.Phase,returnedState] at matched
          | some completed=>simp only [AdapterPublicFinishLifetime.ownerAfter,outcome,AdapterPublicWrapperState.Phase,returnedState] at matched
  · intro raw supported
    exact RegistrationNativePlatformExtractedSdkAdaptiveFinish.normal view setup checks representation created wire index self owner
      pending prekey oneTime kem scalar stored before related selected phase (packet input) raw.1 coins previous raw.2 supported
  · intro raw supported returned actual
    have same:=RegistrationNativePlatformExtractedSdkAdaptiveFinish.reply self pending index owner before.beacons raw.1
    change sourceReply raw=.ok returned at actual
    change AdapterPublicFinishEndpoint.bytes (sourceReply raw)=_ at same
    rw [actual] at same
    exact same

end BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled.native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled.native

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled.active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishCoupled.active
