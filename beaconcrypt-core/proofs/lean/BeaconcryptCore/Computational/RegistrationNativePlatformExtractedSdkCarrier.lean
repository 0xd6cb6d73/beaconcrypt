-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkAdaptive
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkReification
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkBundle
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkFinish
import BeaconcryptCore.Computational.RegistrationNativeHiddenAllocationOwners
import BeaconcryptCore.Refinement.AdapterPublicServerBuildOwnership
import BeaconcryptCore.Refinement.AdapterPublicWrapperState
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
/-! A registration boundary retains the actual source objects, caller RNG and opaque one-use tokens separately from the native analysis representation. Finish snapshots retain their returned environment before reification; no raw poststate equality is imposed. Token movement consumes the exact associated native slot before the next build stage. -/
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
open BeaconcryptCore.Refinement
variable {n : Nat} {KemSK Platform R : Type} {source : RegistrationNativeMldsa.Source}
/-- Returned finish environments are source results and remain part of the stored receipt. -/
inductive SourceSnapshot (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) where
  | direct (raw : RegistrationNativeExperiment.State n KemSK source ×Platform)
  | environment (returned : RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State)
      (raw : RegistrationNativeExperiment.State n KemSK source ×Platform)
  | server (environment : Option (RegistrationWorldAgreementCompiler.EnvState RegistrationServerRoleBackend.State))
      (records : PqxdhRecordLiftWorld.Server)
      (raw : RegistrationNativeExperiment.State n KemSK source ×Platform)
def SourceSnapshot.raw : SourceSnapshot n KemSK Platform source →RegistrationNativeExperiment.State n KemSK source ×Platform
  | .direct raw | .environment _ raw | .server _ _ raw=>raw
def SourceSnapshot.committed : SourceSnapshot n KemSK Platform source →RegistrationNativeExperiment.State n KemSK source ×Platform
  | .direct raw=>raw
  | .environment returned raw=>(RegistrationNativePlatformSdkReification.commitEnvironment returned raw.1,raw.2)
  | .server captured records raw=>
      let sourceState := {raw.1 with server := {raw.1.server with world := {raw.1.server.world with world :=
        ({raw.1.server.world.world.1 with server := some records},raw.1.server.world.world.2)}}}
      (match captured with
       | none=>sourceState
       | some returned=>RegistrationNativePlatformSdkReification.commitEnvironment returned sourceState,raw.2)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
structure Objects (R : Type) where
  server : beaconcrypt_public_wrapper.server.Server
  beacons : Nat →Option beaconcrypt_public_wrapper.beacon.Beacon
  tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput
  rng : R
  nextSession : Nat
  nextOwner : Nat
  snapshot : SourceSnapshot n KemSK Platform source

def TokenTable (tokens : Nat →Option beaconcrypt_public_wrapper.server.RegistrationOutput)
    (sessions : List (Option peer.ConsumedRegistration)) : Prop :=
  ∀index,match sessions[index]? with
  | some (some consumed)=>∃token,tokens index=some token ∧AdapterPublicWrapperState.Token token consumed
  | _=>tokens index=none

def BeaconTable (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (joint : PqxdhJointIdentity.Primitives) (objects : Nat →Option beaconcrypt_public_wrapper.beacon.Beacon)
    (native : RegistrationNativeExperiment.State n KemSK source) : Prop :=
  ∀index,match native.beacons[index]? with
  | none=>objects index=none
  | some owner=>∃self,objects index=some self ∧AdapterPublicWrapperState.Beacon view joint native.pool self owner
      native.server.world.world.1.owners[owner.worldOwner]?

structure Carrier (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (current : RegistrationNativeExperiment.State n KemSK source ×Platform) where
  objects : Objects (n:=n) (KemSK:=KemSK) (Platform:=Platform) (source:=source) R
  server : AdapterPublicWrapperState.Server view containers created credential objects.server current.1.server
  beacons : BeaconTable view joint objects.beacons current.1
  tokens : TokenTable objects.tokens current.1.server.sessions
  sessionCount : objects.nextSession=current.1.server.sessions.length
  ownerCount : objects.nextOwner=current.1.beacons.length
  allocated : current.1.server.world.world.1.owners.length=current.1.beacons.length
  indexed : RegistrationNativeHiddenAllocationOwners.NativeIndexed current.1.beacons
  backend : RegistrationNativePlatformSdkReification.persistent objects.snapshot.committed=
    RegistrationNativePlatformSdkReification.persistent current

variable (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (current : RegistrationNativeExperiment.State n KemSK source ×Platform) (before : Carrier (R:=R) view containers joint created credential current)

theorem token (handle : Nat) (consumed : peer.ConsumedRegistration)
    (live : current.1.server.sessions[handle]?=some (some consumed)) :
    ∃token,before.objects.tokens handle=some token ∧AdapterPublicWrapperState.Token token consumed := by
  have found:=before.tokens handle
  simpa only [TokenTable,live] using found

noncomputable def move (handle : Nat) :
    Carrier (R:=R) view containers joint created credential
      (AdapterPublicServerBuildOwnership.moved handle current.1,current.2) := {
  objects := {before.objects with tokens:=Function.update before.objects.tokens handle none}
  server := AdapterPublicServerBuildOwnership.material_retained view containers created credential before.objects.server current.1 before.server handle
  beacons := before.beacons
  tokens := by
    intro index
    change match (current.1.server.sessions.set handle none)[index]? with
      | some (some consumed)=>∃token,Function.update before.objects.tokens handle none index=some token ∧AdapterPublicWrapperState.Token token consumed
      | _=>Function.update before.objects.tokens handle none index=none
    by_cases same:index=handle
    · subst index
      rw [List.getElem?_set_self']
      cases current.1.server.sessions[handle]? <;> simp
    · rw [List.getElem?_set_ne (Ne.symm same)]
      have old:=before.tokens index
      cases value:current.1.server.sessions[index]? with
      | none=>simpa only [value,Function.update_of_ne same] using old
      | some stored=>cases stored <;> simpa only [value,Function.update_of_ne same] using old
  sessionCount := by simpa only [AdapterPublicServerBuildOwnership.moved,List.length_set] using before.sessionCount
  ownerCount := before.ownerCount
  allocated := before.allocated
  indexed := before.indexed
  backend := before.backend }

theorem move_source (handle : Nat) :
    (move view containers joint created credential current before handle).objects.server=before.objects.server ∧
    (move view containers joint created credential current before handle).objects.beacons=before.objects.beacons ∧
    (move view containers joint created credential current before handle).objects.rng=before.objects.rng ∧
    (move view containers joint created credential current before handle).objects.snapshot=before.objects.snapshot := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem move_token (handle : Nat) :
    (move view containers joint created credential current before handle).objects.tokens handle=none :=
  by simp only [move,Function.update_self]

theorem take (handle : Nat) (consumed : peer.ConsumedRegistration)
    (live : current.1.server.sessions[handle]?=some (some consumed)) :
    ∃token,before.objects.tokens handle=some token ∧AdapterPublicWrapperState.Token token consumed ∧
      RegistrationServerSdkSource.take handle current.1.server=
        (some token.registration,(AdapterPublicServerBuildOwnership.moved handle current.1).server) := by
  obtain ⟨token,stored,related⟩ := token view containers joint created credential current before handle consumed live
  exact ⟨token,stored,related,(AdapterPublicServerBuildOwnership.move token consumed current.1 handle related live).1⟩
theorem source_token (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) :
    ∃consumed,current.1.server.sessions[handle]?=some (some consumed) ∧AdapterPublicWrapperState.Token token consumed := by
  have table:=before.tokens handle
  cases found:current.1.server.sessions[handle]? with
  | none=>simp only [found,stored,Option.some_ne_none] at table
  | some optional=>cases optional with
    | none=>simp only [found,stored,Option.some_ne_none] at table
    | some consumed=>
        simp only [found] at table
        obtain ⟨actual,actualStored,related⟩ := table
        have same:actual=token:=Option.some.inj (actualStored.symm.trans stored)
        subst actual
        exact ⟨consumed,rfl,related⟩

variable (pin : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp)
    (RustM (core.option.Option session.ServerAuthenticationPin)))
variable (reserve : StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (present : U64 →StateT (RegistrationServerFrontendCompiler.State n) (StateT Platform ProbComp) Bool)
variable (finish : RegistrationNativePlatformCompletionSdk.Completion n (StateT Platform ProbComp) (alloc.vec.Vec U8))
theorem build_live (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) (application : Slice U8) :
    (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle (some application)).run current.1.server=
      (RegistrationNativePlatformCompletionSdk.complete pin reserve present finish token.registration application).run
        (AdapterPublicServerBuildOwnership.moved handle current.1).server := by
  obtain ⟨consumed,live,related⟩ := source_token view containers joint created credential current before handle token stored
  exact AdapterPublicServerBuildOwnership.build_live pin reserve present finish token consumed current.1 handle related live application

theorem build_cancel (handle : Nat) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (stored : before.objects.tokens handle=some token) :
    (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle none).run current.1.server=
      pure (.ok none,(AdapterPublicServerBuildOwnership.moved handle current.1).server) := by
  obtain ⟨consumed,live,related⟩ := source_token view containers joint created credential current before handle token stored
  unfold RegistrationNativePlatformCompletionSdk.build
  simp only [StateT.run]
  rw [(AdapterPublicServerBuildOwnership.move token consumed current.1 handle related live).1]

 theorem build_missing (handle : Nat) (missing : before.objects.tokens handle=none)
    (application : Option (Slice U8)) :
    (RegistrationNativePlatformCompletionSdk.build pin reserve present finish handle application).run current.1.server=
      pure (.ok none,current.1.server) := by
  have table:=before.tokens handle
  cases found:current.1.server.sessions[handle]? with
  | none=>simp only [RegistrationNativePlatformCompletionSdk.build,StateT.run,RegistrationServerSdkSource.take,found]
  | some optional=>cases optional with
    | none=>simp only [RegistrationNativePlatformCompletionSdk.build,StateT.run,RegistrationServerSdkSource.take,found]
    | some consumed=>
        simp only [found] at table
        obtain ⟨token,stored,_⟩ := table
        rw [missing] at stored
        cases stored

omit material platform ed in
theorem bundle_snapshot (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (scalar : PqxdhJointGapDh.ScalarBytes)
    (raw : (RegistrationNativePlatformExtractedSdkBundle.Publication ×RegistrationNativeExperiment.State n KemSK source) ×Platform) :
    RegistrationNativePlatformSdkReification.persistent
      (SourceSnapshot.direct (raw.1.2,raw.2) : SourceSnapshot n KemSK Platform source).committed=
      RegistrationNativePlatformSdkReification.persistent
        (RegistrationNativePlatformExtractedSdkAdaptive.pack
          (RegistrationNativePlatformExtractedSdkBundle.withCoinsNative index owner scalar raw)).2 := by
  change (RegistrationNativePlatformSdkReification.backend raw.1.2,raw.2)=
    (RegistrationNativePlatformSdkReification.backend
      (RegistrationNativeBundleLifecycle.after index owner scalar raw.1.1 raw.1.2),raw.2)
  rw [RegistrationNativePlatformSdkReification.publication_backend]

omit material platform ed in
theorem finish_snapshot (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (owners : List (RegistrationNativeBeaconFrontend.Owner source))
    (raw : RegistrationNativePlatformExtractedSdkFinish.BodyResult n KemSK source ×Platform) :
    RegistrationNativePlatformSdkReification.persistent
      (SourceSnapshot.environment raw.1.1.2 (raw.1.2,raw.2)).committed=
      RegistrationNativePlatformSdkReification.persistent
        ((RegistrationNativePlatformExtractedSdkFinish.nativeProjection index owner pending owners raw.1).2,raw.2) := by
  change (RegistrationNativePlatformSdkReification.backend
      (RegistrationNativePlatformSdkReification.commitEnvironment raw.1.1.2 raw.1.2),raw.2)=
    (RegistrationNativePlatformSdkReification.backend
      (RegistrationNativeFinishTerminalTree.after index owner (RegistrationResponse.abortedState pending) raw.1.1.1
        (RegistrationNativeFinishTerminalTree.assemble owners raw.1.1.2 raw.1.2)),raw.2)
  rw [RegistrationNativePlatformSdkReification.finish_backend]
end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.token

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.move_token

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.take' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.take

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.source_token' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.source_token

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_live

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_cancel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_cancel

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_missing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.build_missing

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.bundle_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.bundle_snapshot

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.finish_snapshot' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier.finish_snapshot
