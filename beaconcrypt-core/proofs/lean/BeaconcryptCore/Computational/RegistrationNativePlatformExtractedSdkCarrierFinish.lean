-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkFinishFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkServerFrame
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Carrier Objects SourceSnapshot TokenTable BeaconTable)
variable {n : Nat} {I KemSK Platform R : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
private theorem phase_frame (owners : List (RegistrationNativeBeaconFrontend.Owner source)) (target : Nat)
    (phase : RegistrationNativeBeaconFrontend.Phase) (initial : RegistrationNativeHiddenAllocationOwners.NativeIndexed owners) :
    (RegistrationNativeFinishTerminal.setPhase target phase owners).length=owners.length ∧
    RegistrationNativeHiddenAllocationOwners.NativeIndexed (RegistrationNativeFinishTerminal.setPhase target phase owners) ∧
    ∀index,index≠target →(RegistrationNativeFinishTerminal.setPhase target phase owners)[index]?=owners[index]? := by
  unfold RegistrationNativeFinishTerminal.setPhase
  cases selected:owners[target]? with
  | none=>exact ⟨rfl,initial,fun _ _=>rfl⟩
  | some owner=>
      refine ⟨List.length_set,?_,fun index different=>List.getElem?_set_ne (Ne.symm different)⟩
      intro index current found
      by_cases same:index=target
      · subst index
        rw [List.getElem?_set_self (List.getElem?_eq_some_iff.mp selected).1] at found
        cases found
        exact initial target owner selected
      · rw [List.getElem?_set_ne (Ne.symm same)] at found
        exact initial index current found

private theorem projected_phase (target : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (before : Native)
    (raw : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source) :
    ∃phase,(RegistrationNativePlatformExtractedSdkFinish.nativeProjection target owner pending before.beacons raw).2.beacons=
      RegistrationNativeFinishTerminal.setPhase target phase before.beacons := by
  dsimp only [RegistrationNativePlatformExtractedSdkFinish.nativeProjection]
  cases reply:raw.1.1 with
  | fail error | div=>exact ⟨_,rfl⟩
  | ok optional=>cases optional <;>exact ⟨_,rfl⟩

private theorem projected_length (target : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (before : Native)
    (raw : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source) :
    (RegistrationNativePlatformExtractedSdkFinish.nativeProjection target owner pending before.beacons raw).2.server.world.world.1.owners.length=
      raw.2.server.world.world.1.owners.length := by
  dsimp only [RegistrationNativePlatformExtractedSdkFinish.nativeProjection]
  cases reply:raw.1.1 with
  | fail error | div=>exact List.length_set
  | ok optional=>cases optional <;>exact List.length_set

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform] [ed : AdapterInitEdPrimitive.Operations]
def update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R) (index : Nat)
    (returned : AdapterPublicFinishBody.Result) (environment : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
    (sourceAfter : Native ×Platform) : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R :=
  {before with beacons:=Function.update before.beacons index (some returned.2),snapshot:=.environment environment sourceAfter}
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup) (created : PqxdhLiveServerConstruction.Created Unit)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (containers : AdapterPublicWrapperStorage.Views)
variable (credential : RegistrationNativeMldsa.Credential source)
noncomputable def put (wire : RegistrationNativeWire.Wire) (current : Native ×Platform)
    (before : Carrier (R:=R) view containers setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons index=some self)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state=.InitSent pending prekey oneTime kem) (phase : owner.phase=.initSent pending scalar)
    (packet : Option registration.ResponsePacket) (raw : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source ×Platform)
    (supported : raw∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar current.1).run current.2))
    (returned : AdapterPublicFinishBody.Result)
    (found : (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.beacons[index]?=
      some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1.1))
    (active : AdapterPublicWrapperState.Beacon view setup.joint
      (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.pool returned.2
      (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1.1)
      (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.server.world.world.1.owners[owner.worldOwner]?) :
    Carrier (R:=R) view containers setup.joint created credential
      ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2,raw.2) := by
  let final:=(RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2
  have original : AdapterPublicWrapperState.Beacon view setup.joint current.1.pool self owner current.1.server.world.world.1.owners[owner.worldOwner]? := by
    have related:=before.beacons index
    rw [selected] at related
    obtain ⟨actual,actualStored,material⟩:=related
    have same:actual=self:=Option.some.inj (actualStored.symm.trans sourceSelected)
    subst actual
    exact material
  have ready:=AdapterPublicFinishWorld.initSent_ready view setup.joint current.1.pool self owner current.1.server.world.world.1 original pending prekey oneTime kem scalar stored phase
  have rawSupported:=RegistrationNativePlatformHashReceipt.native_support coins _ raw.1 current.2 raw.2 supported
  have rawImage:=RegistrationNativePlatformSdkServerFrame.finish_tree setup checks representation created wire pending packet owner scalar current.1 raw.1 rawSupported
  have fullImage:RegistrationNativePlatformSdkServerFrame.image final=RegistrationNativePlatformSdkServerFrame.image current.1 :=
    (RegistrationNativePlatformSdkServerFrame.finish_after index owner (RegistrationResponse.abortedState pending) raw.1.1.1 current.1.beacons raw.1.1.2 raw.1.2).trans rawImage
  have sessions:final.server.sessions=current.1.server.sessions:=congrArg RegistrationNativePlatformSdkServerFrame.ServerImage.sessions fullImage
  have worlds:=RegistrationNativeFinishBodySafety.raw_owners setup checks representation created wire pending
    (RegistrationNativePlatformExtractedSdkFinish.decodedPacket packet) owner scalar (RegistrationWorldAgreementCompiler.erase current.1.server.world) current.1 raw.1 rawSupported
  have facts:final.beacons.length=current.1.beacons.length ∧RegistrationNativeHiddenAllocationOwners.NativeIndexed final.beacons ∧
      ∀otherIndex,otherIndex≠index →final.beacons[otherIndex]?=current.1.beacons[otherIndex]? := by
    obtain ⟨finalPhase,roster⟩:=projected_phase index owner pending current.1 raw.1
    dsimp only [final]
    rw [roster]
    exact phase_frame current.1.beacons index finalPhase before.indexed
  have length:=facts.1
  refine {
    objects:=update before.objects index returned raw.1.1.2 (raw.1.2,raw.2)
    server:=RegistrationNativePlatformSdkServerFrame.server_material (created:=created) view containers credential before.objects.server current.1 final before.server fullImage
    beacons:=?_
    tokens:=by change TokenTable before.objects.tokens final.server.sessions;rw [sessions];exact before.tokens
    sessionCount:=by change before.objects.nextSession=final.server.sessions.length;rw [sessions];exact before.sessionCount
    ownerCount:=before.ownerCount.trans length.symm
    allocated:=?_
    indexed:=facts.2.1
    backend:=RegistrationNativePlatformExtractedSdkCarrier.finish_snapshot index owner pending current.1.beacons raw }
  · intro otherIndex
    by_cases same:otherIndex=index
    · subst otherIndex
      rw [found]
      refine ⟨returned.2,Function.update_self _ _ _,?_⟩
      have address:(AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1.1).worldOwner=owner.worldOwner := by
        cases raw.1.1.1 with
        | fail error | div=>rfl
        | ok optional=>cases optional <;>rfl
      rw [address]
      exact active
    · have otherLookup:final.beacons[otherIndex]?=current.1.beacons[otherIndex]? := facts.2.2 otherIndex same
      rw [otherLookup]
      cases prior:current.1.beacons[otherIndex]? with
      | none=>simpa only [update,Function.update_of_ne same,prior] using before.beacons otherIndex
      | some other=>
          have old:=before.beacons otherIndex
          simp only [prior] at old
          obtain ⟨oldSelf,oldStored,oldMaterial⟩:=old
          have otherMaterial:=RegistrationNativePlatformSdkFinishFrame.other_platform setup checks representation created coins view wire index otherIndex same owner other pending scalar packet oldSelf current.1
            selected phase ready prior before.indexed oldMaterial current.2 raw supported
          exact ⟨oldSelf,(Function.update_of_ne same _ _).trans oldStored,otherMaterial.2⟩
  · have ownerLength:raw.1.2.server.world.world.1.owners.length=current.1.server.world.world.1.owners.length:=congrArg List.length worlds
    rw [projected_length,ownerLength,before.allocated]
    exact length.symm
theorem put_objects (wire : RegistrationNativeWire.Wire) (current : Native ×Platform)
    (before : Carrier (R:=R) view containers setup.joint created credential current)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source) (selected : current.1.beacons[index]?=some owner)
    (self : beaconcrypt_public_wrapper.beacon.Beacon) (sourceSelected : before.objects.beacons index=some self)
    (pending : registration.BeaconPending) (prekey oneTime : beaconcrypt_crypto.crypto_kx.KeyPair)
    (kem : beaconcrypt_crypto.crypto_kem.mlkem768.KeyPair) (scalar : PqxdhJointGapDh.ScalarBytes)
    (stored : self.state=.InitSent pending prekey oneTime kem) (phase : owner.phase=.initSent pending scalar)
    (packet : Option registration.ResponsePacket) (raw : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source ×Platform)
    (supported : raw∈support ((RegistrationNativePlatformExtractedSdkFinish.runner coins setup checks representation created wire pending packet owner scalar current.1).run current.2))
    (returned : AdapterPublicFinishBody.Result)
    (found : (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.beacons[index]?=
      some (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1.1))
    (active : AdapterPublicWrapperState.Beacon view setup.joint
      (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.pool returned.2
      (AdapterPublicFinishLifetime.ownerAfter owner (RegistrationResponse.abortedState pending) raw.1.1.1)
      (RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending current.1.beacons raw.1).2.server.world.world.1.owners[owner.worldOwner]?) :
    (put coins setup checks representation created view containers credential wire current before index owner selected self sourceSelected pending prekey oneTime kem scalar stored phase packet raw supported returned found active).objects=
      update before.objects index returned raw.1.1.2 (raw.1.2,raw.2) := rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish.put_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierFinish.put_objects
