-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkCreateFrame
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCreateSupported
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier (Objects BeaconTable Carrier SourceSnapshot)
variable {n : Nat} {KemSK Platform R : Type} {source : RegistrationNativeMldsa.Source}
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
local notation "Native"=>RegistrationNativeExperiment.State n KemSK source

def update (before : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (outcome : AdapterBeaconConstructorBody.Outcome R) (snapshot : SourceSnapshot n KemSK Platform source) :
    Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R :=
  { before with
    rng := outcome.2
    snapshot := snapshot
    beacons := match outcome.1 with | .Err _=>before.beacons | .Ok self=>Function.update before.beacons before.nextOwner (some self)
    nextOwner := match outcome.1 with | .Err _=>before.nextOwner | .Ok _=>before.nextOwner+1 }

private theorem table (view : AdapterPublicWrapperState.MaterialView source KemSK) (joint : PqxdhJointIdentity.Primitives)
    (before after : Native) (objects : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (prior : BeaconTable view joint objects.beacons before) (count : objects.nextOwner=before.beacons.length)
    (allocated : before.server.world.world.1.owners.length=before.beacons.length)
    (indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed before.beacons)
    (reply : RustM (Option Nat)) (outcome : AdapterBeaconConstructorBody.Outcome R)
    (frame : RegistrationNativePlatformSdkCreateFrame.Frame before after)
    (shape : RegistrationNativePlatformSdkCreateFrame.Roster before.beacons reply after.beacons)
    (observed : RegistrationNativePlatformExtractedSdkCreateCommit.observe before.beacons.length outcome=reply)
    (born : ∀self nextRng,outcome=(.Ok self,nextRng) → ∃owner,after.beacons[before.beacons.length]?=some owner ∧
      AdapterPublicWrapperState.Beacon view joint after.pool self owner after.server.world.world.1.owners[owner.worldOwner]?)
    (snapshot : SourceSnapshot n KemSK Platform source) : BeaconTable view joint (update objects outcome snapshot).beacons after := by
  have originalShape:=shape
  rw [←observed] at shape
  rcases outcome with ⟨result,nextRng⟩
  cases result with
  | Err error=>
    change after.beacons=before.beacons at shape
    intro index
    cases found:before.beacons[index]? with
    | none=>
      rw [shape,found]
      simpa only [update,found] using prior index
    | some owner=>
      have old:=prior index
      simp only [found] at old
      obtain ⟨self,sourceAt,related⟩:=old
      have kept:=RegistrationNativePlatformSdkCreateFrame.old_material view joint before after reply frame originalShape allocated indexed index owner found self related
      rw [kept.1]
      exact ⟨self,sourceAt,kept.2⟩
  | Ok self=>
    change before.beacons.length=before.beacons.length ∧∃owner,after.beacons=before.beacons++[owner] at shape
    obtain ⟨_same,newOwner,rows⟩:=shape
    intro index
    by_cases selected:index=before.beacons.length
    · subst index
      obtain ⟨owner,found,related⟩:=born self nextRng rfl
      rw [found]
      refine ⟨self,?_,related⟩
      change Function.update objects.beacons objects.nextOwner (some self) before.beacons.length=some self
      rw [count,Function.update_self]
    · have different:index≠objects.nextOwner:=by simpa only [count] using selected
      cases found:before.beacons[index]? with
      | none=>
        have beyond:before.beacons.length + 1 ≤ index:=by
          have lower:=List.getElem?_eq_none_iff.mp found
          omega
        have missing:after.beacons[index]?=none := by
          rw [rows,List.getElem?_eq_none_iff.mpr (by simpa only [List.length_append,List.length_singleton] using beyond)]
        rw [missing]
        change Function.update objects.beacons objects.nextOwner (some self) index=none
        rw [Function.update_of_ne different]
        simpa only [found] using prior index
      | some owner=>
        have old:=prior index
        simp only [found] at old
        obtain ⟨oldSelf,sourceAt,related⟩:=old
        have kept:=RegistrationNativePlatformSdkCreateFrame.old_material view joint before after reply frame originalShape allocated indexed index owner found oldSelf related
        rw [kept.1]
        refine ⟨oldSelf,?_,kept.2⟩
        exact (Function.update_of_ne different _ _).trans sourceAt

private theorem owner_count (before after : Native)
    (objects : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R)
    (count : objects.nextOwner=before.beacons.length) (reply : RustM (Option Nat))
    (outcome : AdapterBeaconConstructorBody.Outcome R)
    (shape : RegistrationNativePlatformSdkCreateFrame.Roster before.beacons reply after.beacons)
    (observed : RegistrationNativePlatformExtractedSdkCreateCommit.observe before.beacons.length outcome=reply)
    (snapshot : SourceSnapshot n KemSK Platform source) : (update objects outcome snapshot).nextOwner=after.beacons.length := by
  rw [←observed] at shape
  rcases outcome with ⟨result,nextRng⟩
  cases result with
  | Err error=>
    change after.beacons=before.beacons at shape
    change objects.nextOwner=after.beacons.length
    rw [shape]
    exact count
  | Ok self=>
    change before.beacons.length=before.beacons.length ∧∃owner,after.beacons=before.beacons++[owner] at shape
    obtain ⟨_same,owner,rows⟩:=shape
    change objects.nextOwner+1=after.beacons.length
    simp only [rows,List.length_append,List.length_singleton,count]

variable {I Error : Type} {base : OracleSpec I}
variable [generators : AdapterBeaconConstructorRequestMonad.Operations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable [crypto : AdapterPublicWrapperRequestMonad.CryptoOperations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable [children : AdapterPublicWrapperRequestMonad.ChildOperations
  (AdapterPublicWrapperRustT.RustT (RegistrationNativePlatformExtractedSdkCreateReceipt.SourceM n KemSK source Platform))]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp)) (setup : PqxdhServerAuthExperiment.Setup base KemSK)
variable (checks : PqxdhServerAuthExperiment.Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (generator : rand_core.TryCryptoRng R Error)
variable (view : AdapterPublicWrapperState.MaterialView source KemSK) (kem : AdapterBeaconConstructorKem.Representation view R)
variable (leaves : AdapterBeaconConstructorNative.Leaves (n:=n) (Auxiliary:=RegistrationServerRoleBackend.State)
  coins setup checks representation created generator view kem)
variable (containers : AdapterPublicWrapperStorage.Views) (credential : RegistrationNativeMldsa.Credential source)

noncomputable def put (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential (before,previous))
    (packet : RegistrationNativePlatformExtractedSdkCreateReceipt.Result n KemSK R source) (next : Platform)
    (supported : (packet,next)∈support ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created
      generator view kem leaves keyId serverId mlPin objects.objects.rng before).run previous)) :
    RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential
      ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2,next) := by
  let after:=(RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet).2
  have called:=RegistrationNativePlatformExtractedSdkCreateSupported.native coins setup checks representation created generator view kem leaves
    keyId serverId mlPin objects.objects.rng before previous next packet supported
  have frame:=RegistrationNativePlatformSdkCreateFrame.platform coins setup checks representation created (view.edPublic serverId) mlPin keyId
    before previous objects.allocated objects.indexed _ called
  have same:=frame.1.1
  have sessions:after.server.sessions=before.server.sessions:=congrArg RegistrationNativePlatformSdkServerFrame.ServerImage.sessions same
  have publicEq:=RegistrationNativePlatformExtractedSdkCreateSupported.reply coins setup checks representation created generator view kem leaves
    keyId serverId mlPin objects.objects.rng before previous next packet supported
  let snapshot:SourceSnapshot n KemSK Platform source:=.direct (packet.1.1.1.sourceAfter,next)
  refine { objects := update objects.objects packet.1.1.1.outcome snapshot
           server := RegistrationNativePlatformSdkServerFrame.server_material (created:=created) view containers credential objects.objects.server before after objects.server same
           beacons := ?_
           tokens := ?_
           sessionCount := ?_
           ownerCount := owner_count before after objects.objects objects.ownerCount packet.1.1.1.reply packet.1.1.1.outcome frame.2.1 publicEq snapshot
           allocated := frame.2.2.1
           indexed := frame.2.2.2
           backend := ?_ }
  · apply table view setup.joint before after objects.objects objects.beacons objects.ownerCount objects.allocated objects.indexed
      packet.1.1.1.reply packet.1.1.1.outcome frame.1 frame.2.1 publicEq
    intro self nextRng outcome
    have replyEq:packet.1.1.1.reply=.ok (some before.beacons.length) := by
      rw [outcome] at publicEq
      exact publicEq.symm
    exact RegistrationNativePlatformExtractedSdkCreateSupported.created_material coins setup checks representation created generator view kem leaves
      keyId serverId mlPin objects.objects.rng nextRng before previous next packet supported before.beacons.length self replyEq outcome
  · change RegistrationNativePlatformExtractedSdkCarrier.TokenTable objects.objects.tokens after.server.sessions
    rw [sessions]
    exact objects.tokens
  · change objects.objects.nextSession=after.server.sessions.length
    rw [sessions]
    exact objects.sessionCount
  · exact (RegistrationNativePlatformExtractedSdkCreateSupported.backend coins setup checks representation created generator view kem leaves
      keyId serverId mlPin objects.objects.rng before previous next packet supported).symm

theorem put_objects (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential (before,previous))
    (packet : RegistrationNativePlatformExtractedSdkCreateReceipt.Result n KemSK R source) (next : Platform)
    (supported : (packet,next)∈support ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created
      generator view kem leaves keyId serverId mlPin objects.objects.rng before).run previous)) :
    (put coins setup checks representation created generator view kem leaves containers credential keyId serverId mlPin before previous objects packet next supported).objects=
      update objects.objects packet.1.1.1.outcome (.direct (packet.1.1.1.sourceAfter,next)) := rfl

noncomputable def putPacket (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential (before,previous))
    (packet : RegistrationNativePlatformExtractedSdkCreateReceipt.Result n KemSK R source×Platform)
    (supported : packet∈support ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created
      generator view kem leaves keyId serverId mlPin objects.objects.rng before).run previous)) :
    RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential
      ((RegistrationNativePlatformExtractedSdkCreateCommon.nativeProjection packet.1).2,packet.2) := by
  rcases packet with ⟨result,next⟩
  exact put coins setup checks representation created generator view kem leaves containers credential keyId serverId mlPin before previous objects result next supported

theorem putPacket_objects (keyId : U64) (serverId : beaconcrypt_crypto.crypto_sign.PublicKey)
    (mlPin : Std.Array U8 1952#usize) (before : Native) (previous : Platform)
    (objects : RegistrationNativePlatformExtractedSdkCarrier.Carrier (R:=R) view containers setup.joint created credential (before,previous))
    (packet : RegistrationNativePlatformExtractedSdkCreateReceipt.Result n KemSK R source×Platform)
    (supported : packet∈support ((RegistrationNativePlatformExtractedSdkCreateCommon.runner coins setup checks representation created
      generator view kem leaves keyId serverId mlPin objects.objects.rng before).run previous)) :
    (putPacket coins setup checks representation created generator view kem leaves containers credential keyId serverId mlPin before previous objects packet supported).objects=
      update objects.objects packet.1.1.1.1.outcome (.direct (packet.1.1.1.1.sourceAfter,packet.2)) := by
  rcases packet with ⟨result,next⟩
  rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.put' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.put

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.put_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.put_objects

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrierCreate.putPacket_objects
