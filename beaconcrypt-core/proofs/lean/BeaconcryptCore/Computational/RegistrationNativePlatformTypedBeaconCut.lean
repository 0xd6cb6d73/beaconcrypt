-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconFinishCut
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicFrontend
import BeaconcryptCore.Computational.RegistrationNativeTypedBeaconAllController
/-! The actual shared-platform owner callback exposes its same translated preparation and corrected material completion under every runtime interpretation. Source platform state is retained literally. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativeTypedBeaconAllController (translated)
open RegistrationNativeBeaconFinishController (lower)
variable {n : Nat} {I KemSK Platform Runtime Value : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

private theorem local_run (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (before : Platform) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work).run before =
      (fun value => (value,before)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind,simulateQ_spec_query,RegistrationNativePlatformPublicFrontend.localHandler,
      StateT.run_bind,StateT.run_lift,bind_pure_comp,bind_map_left,map_bind,ih]

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := StateT.run_map observe work before

private theorem local_apply (work : OracleComp (RegistrationBeaconReferenceCompiler.Spec n KemSK) Value) (before : Platform) :
    (simulateQ (RegistrationNativePlatformPublicFrontend.localHandler false) work) before =
      (fun value => (value,before)) <$> simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false) work :=
  local_run work before

noncomputable def interpreter
    (implementation : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (scalar : Option PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK) (StateT Runtime ProbComp) :=
  match scalar with
  | none => (implementation ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal) ∘ₛ RegistrationNativePlatformPublicFrontend.localQuery false
  | some scalar => ((implementation ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal) ∘ₛ RegistrationNativePlatformPublicFrontend.localQuery false) ∘ₛ
      RegistrationNativePublicOwners.ordinary setup scalar

/-- The literal owner callback changes only its returned frontend projection around the same actual local source tree. -/
theorem finish_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : before.1.beacons[index]? = some owner) :
    ((RegistrationNativePlatformPublicFrontend.executeLocal
      (RegistrationNativePlatformPublicFrontend.beacon (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run before) =
      (fun result => (result.1.1,({before.1 with beacons := before.1.beacons.set index {owner with view := result.1.2},environment := result.2},before.2))) <$>
        simulateQ RegistrationNativePlatformPublicFrontend.embedLocal
          (simulateQ (RegistrationNativePlatformPublicFrontend.localQuery false)
            (translated setup owner.scalar
              (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner.view).run before.1.environment))) := by
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal,RegistrationNativePlatformPublicFrontend.beacon,
    RegistrationNativePlatformPublicFrontend.finish,found,StateT.run,map_apply,local_apply,simulateQ_map,Functor.map_map,translated]
  rfl

/-- Every successful literal owner callback exposes its same local finish with the complete reached runtime. -/
theorem closed
    (implementation : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (beforeFront afterFront : RegistrationNativePlatformPublicFrontend.State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : beforeFront.1.beacons[index]? = some owner)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application),afterFront),after) ∈ support ((simulateQ implementation
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.beacon (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run beforeFront)).run before)) :
    ∃ afterOwner afterEnv,
      ((.ok (some application),afterOwner),(afterEnv,after)) ∈ support
        ((lower (interpreter implementation setup owner.scalar)
          ((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner.view)).run (beforeFront.1.environment,before)) := by
  rw [finish_source setup wire index packet beforeFront owner found] at supported
  simp only [simulateQ_map,StateT.run_map,support_map] at supported
  obtain ⟨finished,called,equal⟩ := supported
  have successful : finished.1.1.1 = .ok (some application) := congrArg (fun result => result.1.1) equal
  have runtime : finished.2 = after := congrArg Prod.snd equal
  refine ⟨finished.1.1.2,finished.1.2,?_⟩
  simp only [lower,StateT.run,support_map]
  refine ⟨finished,?_,?_⟩
  · cases scalarEq : owner.scalar <;>
      simpa only [interpreter,translated,scalarEq,QueryImpl.simulateQ_compose,StateT.run] using called
  · exact Prod.ext (Prod.ext successful rfl) (Prod.ext rfl runtime)

/-- The actual terminal material stage is independent of the already-consumed optional scalar preparation translation. -/
theorem complete_source
    (implementation : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (scalar : Option PqxdhJointGapDh.ScalarBytes)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) :
    lower (interpreter implementation setup scalar)
      ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current) =
    lower (Auxiliary := RegistrationServerRoleBackend.State) (interpreter implementation setup none)
      ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current) := by
  apply StateT.ext
  intro before
  unfold lower
  change (fun result => (result.1.1,(result.1.2,result.2))) <$>
      (simulateQ (interpreter implementation setup scalar)
        (((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
          RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run before.1)).run before.2 = _
  cases scalar with
  | none => rfl
  | some scalar =>
    simp only [interpreter,QueryImpl.simulateQ_compose,RegistrationNativePlatformBeaconFinishCut.ordinary_complete]
    rfl

/-- A successful actual shared-platform finish supplies its own prepared Ready and the same corrected completion at the exact final runtime. -/
theorem finish
    (implementation : QueryImpl (RegistrationNativePlatformPublicFrontend.Spec n KemSK) (StateT Runtime ProbComp))
    (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (index : Nat) (packet : Option registration.ResponsePacket)
    (beforeFront afterFront : RegistrationNativePlatformPublicFrontend.State source Platform)
    (owner : RegistrationNativePublicOwners.Owner source) (found : beforeFront.1.beacons[index]? = some owner)
    (before after : Runtime) (application : Pqxdh.Bytes)
    (supported : ((.ok (some application),afterFront),after) ∈ support ((simulateQ implementation
      ((RegistrationNativePlatformPublicFrontend.executeLocal
        (RegistrationNativePlatformPublicFrontend.beacon (RegistrationNativePlatformPublicFrontend.finish setup wire source index packet))).run beforeFront)).run before)) :
    ∃ ready : RegistrationBeaconReferenceRoot.Ready, ∃ current : SelectedOwner source,
    ∃ middle afterOwner afterEnv,
      ((.ok (some ready),current),middle) ∈ support
        ((lower (interpreter implementation setup owner.scalar)
          ((RegistrationBeaconReferenceCompiler.finishPreparation setup source packet).run owner.view)).run (beforeFront.1.environment,before)) ∧
      ((.ok (some application),afterOwner),(afterEnv,after)) ∈ support
        ((lower (interpreter implementation setup none)
          ((RegistrationNativePlatformBeaconMaterialFrontend.complete setup.source wire.frameWrite RegistrationBeaconReferenceCompiler.effect
            RegistrationNativePlatformBeaconMaterialInterpreter.demand owner.view ready).run current)).run middle) := by
  obtain ⟨afterOwner,afterEnv,actual⟩ := closed implementation setup wire index packet beforeFront afterFront owner found before after application supported
  obtain ⟨ready,current,middle,prepared,finished⟩ := RegistrationNativePlatformBeaconFinishCut.finish
    (interpreter implementation setup owner.scalar) setup wire source packet owner.view afterOwner application
    (beforeFront.1.environment,before) (afterEnv,after) actual
  rw [complete_source] at finished
  exact ⟨ready,current,middle,afterOwner,afterEnv,prepared,finished⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.finish_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.closed

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformTypedBeaconCut.finish
