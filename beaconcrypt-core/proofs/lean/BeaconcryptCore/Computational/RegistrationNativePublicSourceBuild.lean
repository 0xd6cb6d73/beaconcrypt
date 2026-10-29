-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial

/-! Actual native Server material completion closes the optional-memo gap using the derived live-token query receipt. This composes the real current-environment compiler, source108 completion and SDK build rather than assuming a whole-build simulation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePublicSourceEffects (Extra Private)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationNativeRetainedRoots (Memo)
open RegistrationServerReferenceRestore (Roots)
variable {n : Nat} {ι KemSK Value Index : Type} {base : OracleSpec ι} {spec : OracleSpec Index}

private theorem lower_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (interpreter : QueryImpl spec (StateT RegistrationServerReferenceCompiler.Environment
      (OracleComp (RegistrationNativeKemReferenceCompiler.Spec n KemSK))))
    (work : OracleComp spec Value) : RegistrationNativeKemReferencePrefix.lower setup callbacks (simulateQ interpreter work) =
      simulateQ (fun query => RegistrationNativeKemReferencePrefix.lower setup callbacks (interpreter query)) work := by
  have same : (fun query => RegistrationNativeKemReferencePrefix.lower setup callbacks (interpreter query)) =
      ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT := rfl
  rw [same]
  funext before
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation setup callbacks) ((simulateQ interpreter work).run before.1)).run before.2 =
      (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  change id <$> (simulateQ ((implementation setup callbacks).mapStateTBase interpreter).flattenStateT work).run before = _
  exact id_map _

private theorem build_program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (callbacks : Callbacks n KemSK Extra) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerOpenMaterialSource.State n KemSK Extra) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (RegistrationNativeKemReferencePrefix.lower setup callbacks
        ((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run before.1)).run before.2 =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (fun query => RegistrationNativeKemReferencePrefix.lower setup callbacks
          (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
            RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign query))
          ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.1)).run before.2 := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup callbacks (simulateQ
      (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
        RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign)
      ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.1))).run before.2 = _
  rw [lower_program]

/-- Every actual live Server build has exactly its total private-source material interpretation, including cancellation and all failed native states. -/
theorem memo_total (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerOpenMaterialSource.State n KemSK Extra)
    (live : RegistrationServerMaterialRoots.Live before.1 before.2.2.extra.1)
    (consistent : ∀ message root, before.2.2.extra.1 message = some root → roots message = root) :
    (RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
      (services setup wire route sign seed scalar)
      (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      (RegistrationServerOpenMaterialSource.close setup roots (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup (RegistrationNativePublicSourceMaterial.actualCallbacks setup wire route sign seed scalar)
      ((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run before.1)).run before.2 = _
  rw [build_program]
  have equal := RegistrationNativePublicSourceMaterial.program_equal setup wire route sign seed scalar before.2.2.extra.1 roots
    ((RegistrationServerMaterialFrontend.build wire checks.reservePeer handle application).run before.1)
    (RegistrationNativePublicSourceBuildQueries.build_prepared before.2.2.extra.1 roots wire checks.reservePeer handle application before.1 live consistent)
    before.2 rfl
  change (simulateQ (fun query => RegistrationNativeKemReferencePrefix.lower setup
    (RegistrationNativePublicSourceMaterial.actualCallbacks setup wire route sign seed scalar)
    (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign query)) _).run before.2 = _ at equal
  rw [equal]
  change _ = (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup
      (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
      ((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run before.1)).run before.2
  rw [build_program]
  rfl

/-- The complete live native Server build has its literal SDK source controller under the explicitly named native/coin/log source view. -/
theorem build_source (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerOpenMaterialSource.State n KemSK Extra)
    (live : RegistrationServerMaterialRoots.Live before.1 before.2.2.extra.1)
    (consistent : ∀ message root, before.2.2.extra.1 message = some root → roots message = root) :
    Prod.map id (fun current => RegistrationServerMaterialSourceState.project roots
      (RegistrationServerOpenMaterialSource.project current)) <$>
      (RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before =
      Prod.map id RegistrationServerMaterialSourceState.nativeView <$>
        (RegistrationServerSdkSource.build setup (RegistrationNativeWire.ledgerCodec wire) checks sign wire.encodeResponse handle application).run
          (RegistrationServerMaterialSourceState.restore roots (RegistrationServerOpenMaterialSource.project before)) := by
  rw [memo_total setup wire checks route sign seed scalar roots handle application before live consistent]
  exact RegistrationServerOpenMaterialSource.native setup checks wire sign roots (services setup wire route sign seed scalar) handle application before

/-- The complete actual source build retains its prepared memo and opaque owner-key pool through all current-environment material work. -/
theorem build_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (checks : Checks) (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (handle : Nat) (application : Option (Slice U8))
    (before : RegistrationServerOpenMaterialSource.State n KemSK Extra)
    (result : RegistrationServerMaterialFrontend.Result × RegistrationServerOpenMaterialSource.State n KemSK Extra)
    (live : RegistrationServerMaterialRoots.Live before.1 before.2.2.extra.1)
    (consistent : ∀ message root, before.2.2.extra.1 message = some root → roots message = root)
    (supported : result ∈ support
      ((RegistrationServerOpenReferenceSourceAccept.close setup seed scalar remember
        (services setup wire route sign seed scalar)
        (RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application)).run before)) :
    result.2.2.2.extra = before.2.2.extra ∧ result.2.2.2.pool = before.2.2.pool := by
  rw [memo_total setup wire checks route sign seed scalar roots handle application before live consistent] at supported
  change result ∈ support ((fun output => (output.1.1, (output.1.2, output.2))) <$>
    (RegistrationNativeKemReferencePrefix.lower setup
      (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
      ((RegistrationServerOpenReferenceCompiler.build setup.source wire checks sign handle application).run before.1)).run before.2) at supported
  rw [build_program, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  exact RegistrationNativePublicSourceMaterial.program_frame setup wire route sign seed scalar roots _ before.2 inner reached

end BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.memo_total' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.memo_total
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.build_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.build_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.build_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceBuild.build_frame
