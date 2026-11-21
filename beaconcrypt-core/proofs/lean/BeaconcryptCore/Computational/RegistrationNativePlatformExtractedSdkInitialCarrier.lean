-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkCarrier
import BeaconcryptCore.Refinement.AdapterServerConstructorInitialized
/-! Assemble the empty source object/token store from the actual returned initialization receipt. The initializer proves the Server material and exact empty lists; this constructor adds no sampling, source object or correspondence assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
namespace BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier
open BeaconcryptCore.Refinement
open RegistrationNativePlatformExtractedSdkCarrier
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform : Type} {source : RegistrationNativeMldsa.Source}

def empty (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (stored : beaconcrypt_public_wrapper.server.Server) (rng : R)
    (initial : RegistrationNativeExperiment.Initial n KemSK source) (previous : Platform)
    (serverMaterial : AdapterPublicWrapperState.Server view containers initial.created initial.credential stored initial.state.server)
    (owners : initial.state.beacons=[]) (sessions : initial.state.server.sessions=[])
    (slots : initial.state.server.world.world.1.owners=[]) :
    Carrier (R := R) view containers joint initial.created initial.credential (initial.state,previous) where
  objects := {server := stored,beacons := (fun _ =>none),tokens := (fun _ =>none),rng := rng,nextSession := 0,nextOwner := 0,snapshot := .direct (initial.state,previous)}
  server := serverMaterial
  beacons := by
    intro index
    simp only [owners,List.getElem?_nil]
  tokens := by
    intro index
    simp only [sessions,List.getElem?_nil]
  sessionCount := by simp only [sessions,List.length_nil]
  ownerCount := by simp only [owners,List.length_nil]
  allocated := by simp only [slots,owners,List.length_nil]
  indexed := by
    intro index owner found
    simp only [owners,List.getElem?_nil,reduceCtorEq] at found
  backend := rfl

def ready (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (returned : AdapterServerConstructorInitialized.Ready n KemSK R source) (previous : Platform)
    (serverMaterial : AdapterPublicWrapperState.Server view containers returned.initial.created returned.initial.credential returned.stored returned.initial.state.server)
    (owners : returned.initial.state.beacons=[]) (sessions : returned.initial.state.server.sessions=[])
    (slots : returned.initial.state.server.world.world.1.owners=[]) :
    Carrier (R := R) view containers joint returned.initial.created returned.initial.credential (returned.initial.state,previous) :=
  empty view containers joint returned.stored returned.rng returned.initial previous serverMaterial owners sessions slots

theorem ready_objects (view : AdapterPublicWrapperState.MaterialView source KemSK)
    (containers : AdapterPublicWrapperStorage.Views) (joint : PqxdhJointIdentity.Primitives)
    (returned : AdapterServerConstructorInitialized.Ready n KemSK R source) (previous : Platform)
    (serverMaterial : AdapterPublicWrapperState.Server view containers returned.initial.created returned.initial.credential returned.stored returned.initial.state.server)
    (owners : returned.initial.state.beacons=[]) (sessions : returned.initial.state.server.sessions=[])
    (slots : returned.initial.state.server.world.world.1.owners=[]) :
    (ready view containers joint returned previous serverMaterial owners sessions slots).objects=
      {server := returned.stored,beacons := (fun _ =>none),tokens := (fun _ =>none),rng := returned.rng,nextSession := 0,nextOwner := 0,snapshot := .direct (returned.initial.state,previous)} := by rfl

end BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.empty
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.ready' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.ready
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.ready_objects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformExtractedSdkInitialCarrier.ready_objects
