-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceRuntime
import BeaconcryptCore.Computational.RegistrationNativePlatformSdkOrdinaryBeaconSelected
/-! Adaptive erasure into literal RustT source execution uses the physical source law of each locally constructed call. The source interpreter retains enclosing failure/divergence and has no access to the monitored native owners, signing receipts, or selected common packet. -/
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution
open BeaconcryptCore.Refinement
open RegistrationNativePlatformPublicAdapterStore (Store)
open RegistrationNativePlatformExtractedSdkPublic (TotalStep)
open RegistrationNativePlatformPublicAdapterSourceRuntime (M run embed)
variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations]
variable {n : Nat} {KemSK R Platform N I A : Type} {spec : OracleSpec I}
variable (Private : N→Type) (model : QueryImpl spec (StateT N ProbComp))
variable (calls : ∀query current,Private current→TotalStep Private ((model query).run current))
variable (physical : ∀current,Private current→Store n KemSK R Platform)

abbrev Raw (n : Nat) (KemSK R Platform Value : Type) :=
  Store n KemSK R Platform→ProbComp (RustM (Value×Store n KemSK R Platform)×(RegistrationNativePlatformSdkReification.Backend n KemSK×Platform))

noncomputable def source (operations : ∀query,Raw n KemSK R Platform (spec.Range query)) :
    QueryImpl spec (M n KemSK R Platform) :=fun selected=>RegistrationNativePlatformPublicAdapterSourceRuntime.raw (operations selected)

def physicalState (before : RegistrationNativePlatformExtractedSdkPublic.State Private) : Store n KemSK R Platform :=physical before.1 before.2

theorem query (operations : ∀query,Raw n KemSK R Platform (spec.Range query))
    (localSource : ∀selected before,
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (calls selected before.1 before.2)=
        operations selected (physicalState Private physical before))
    (selected : spec.Domain) (before : RegistrationNativePlatformExtractedSdkPublic.State Private) :
    (fun result=>embed (result.1,physicalState Private physical result.2)) <$>
      ((RegistrationNativePlatformExtractedSdkPublic.handler Private model calls selected).run before)=
    run (source operations selected) (physicalState Private physical before) := by
  rw [source,RegistrationNativePlatformPublicAdapterSourceRuntime.run_raw,←localSource selected before]
  simp only [StateT.run,RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw,
    RegistrationNativePlatformExtractedSdkPublic.handler,Functor.map_map]
  rfl

theorem program (operations : ∀query,Raw n KemSK R Platform (spec.Range query))
    (localSource : ∀selected before,
      RegistrationNativePlatformSdkOrdinaryBeaconSelected.raw physical (calls selected before.1 before.2)=
        operations selected (physicalState Private physical before))
    (work : OracleComp spec A) (before : RegistrationNativePlatformExtractedSdkPublic.State Private) :
    (fun result=>embed (result.1,physicalState Private physical result.2)) <$>
      (simulateQ (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) work).run before=
    run (simulateQ (source operations) work) (physicalState Private physical before) :=
  RegistrationNativePlatformPublicAdapterSourceRuntime.program
    (RegistrationNativePlatformExtractedSdkPublic.handler Private model calls) (source operations)
    (physicalState Private physical) (query Private model calls physical operations localSource) work before

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution.query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution.query
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution.program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicAdapterSourceExecution.program
