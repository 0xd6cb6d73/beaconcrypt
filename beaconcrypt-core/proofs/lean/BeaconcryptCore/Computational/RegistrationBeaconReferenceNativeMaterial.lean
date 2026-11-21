-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeEffects
import BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeTail

/-! The scalar-free Beacon material continuation is interpreted through its actual raw opening and existing World effects. No signing branch is fabricated, no local environment is restored over reached receipts, and the native consumed kernel remains the one installed by the service. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationBeaconReferenceNativeInterpreter (State implementation onNative)
open RegistrationBeaconReferenceCompiler (Spec)
variable {ι KemSK Value : Type} {base : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

def rawLift : QueryImpl RegistrationRawSealBridge.Spec (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr (.inl (.inr (.inl (.inl query)))))

def commonLift : QueryImpl (RegistrationNativePairedServerService.Common n) (OracleComp (Spec n KemSK)) :=
  fun query => (Spec n KemSK).query (.inr (.inl (.inr query)))

private theorem raw_component (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationRawSealBridge.Spec.Domain) :
    RegistrationNativeCommonCompiler.common (Auxiliary := RegistrationServerRoleBackend.State)
      (RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK)) source writer sign
      (.inl (.inl query)) = StateT.lift (simulateQ RegistrationBeaconReferenceNativeRecord.environment
        (RegistrationBoundSourceCompiler.rawCompiler source writer query)) := by
  simpa only [RegistrationNativePairedBeaconService.rawLift, simulateQ_spec_query] using
    (RegistrationBeaconReferenceCompletion.raw_program (Auxiliary := RegistrationServerRoleBackend.State)
      RegistrationBeaconReferenceNativeRecord.environment source writer sign
      (RegistrationRawSealBridge.Spec.query query : OracleComp RegistrationRawSealBridge.Spec _))

private theorem framed (work : RegistrationNativeExperiment.M n KemSK mlSource Value)
    (memo : RegistrationNativeReferenceInterpreter.State)
    (before : RegistrationBeaconReferenceNativeInterpreter.Inner n KemSK mlSource) :
    (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (((fun reply => (reply, memo)) <$> onNative work).run before) =
      (fun result => (result.1, (memo, (before.1, result.2)))) <$> work.run before.2 := by
  rw [StateT.run_map]
  simp only [onNative, StateT.run, Functor.map_map]

/-- Each actual raw opening primitive lowers to its explicit existing World-effect program on the reached native state. -/
theorem raw_query (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (query : RegistrationRawSealBridge.Spec.Domain) (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential) (rawLift query)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created)
          (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite query)).run before.2.2 := by
  simp only [rawLift, simulateQ_spec_query]
  rw [implementation, QueryImpl.flattenStateT_mapStateTBase_apply_run]
  simp only [RegistrationNativeReferenceInterpreter.compilerWith, RegistrationNativeReferenceInterpreter.compiler,
    RegistrationNativeReferenceInterpreter.targetLift, simulateQ_map, simulateQ_spec_query,
    StateT.run, RegistrationBeaconReferenceNativeInterpreter.target, raw_component]
  rw [RegistrationBeaconReferenceNativeEffects.beacon_program]
  exact framed _ before.1 before.2

/-- The complete actual opening AST preserves the private root memo/family and uses precisely the native World and callback effects. -/
theorem raw_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp RegistrationRawSealBridge.Spec Value) (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (simulateQ rawLift work)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created)
          (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite) work)).run before.2.2 := by
  rw [← QueryImpl.simulateQ_compose, ← QueryImpl.simulateQ_compose]
  let embed : RegistrationNativeExperiment.State n KemSK mlSource → State n KemSK mlSource :=
    fun current => (before.1, (before.2.1, current))
  have step (query : RegistrationRawSealBridge.Spec.Domain)
      (current : RegistrationNativeExperiment.State n KemSK mlSource) :
      Prod.map id embed <$>
        ((RegistrationBeaconReferenceNativeEffects.native setup checks representation created ∘ₛ
          RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite) query).run current =
      ((implementation setup checks wire representation created scalar credential ∘ₛ rawLift) query).run (embed current) := by
    simpa only [QueryImpl.apply_compose, embed, Prod.map_def, id_eq] using
      (raw_query setup checks wire representation created scalar credential query (embed current)).symm
  simpa only [embed, Prod.map_def, id_eq] using
    (OracleComp.map_run_simulateQ_eq_of_query_map_eq _ _ embed step work before.2.2).symm

/-- Explicit World effects in the material continuation use the same actual source interpreter and preserve the private preparation state. -/
theorem effects_program (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        (simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created) work).run before.2.2 := by
  have lifted : RegistrationBeaconReferenceCompiler.trustedLift ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      RegistrationBeaconReferenceCompiler.effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, RegistrationBeaconReferenceCompiler.trustedLift]
  have native : RegistrationNativeExperiment.trusted setup checks representation created mlSource ∘ₛ
      RegistrationBeaconReferenceNativeRecord.environment (n := n) (KemSK := KemSK) =
      RegistrationBeaconReferenceNativeEffects.native setup checks representation created := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationBeaconReferenceNativeRecord.environment,
      simulateQ_spec_query, RegistrationBeaconReferenceNativeEffects.native]
  have actual := RegistrationBeaconReferenceNativeInterpreter.trusted_program setup checks wire representation created scalar credential
    (simulateQ RegistrationBeaconReferenceNativeRecord.environment work) before
  simpa only [← QueryImpl.simulateQ_compose, lifted, native] using actual

/-- The known-output branch is the actual raw sequence-one opening followed by its existing World installation effect. -/
theorem known_program (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (commonLift (n := n) (KemSK := KemSK))
      (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output) = (do
        let result ← simulateQ rawLift (RegistrationNativePairedBeaconService.program source descriptor output)
        simulateQ RegistrationBeaconReferenceCompiler.effect
          (RegistrationNativePairedBeaconService.after owner sender (fun completed => .known completed.kernel) result)) := by
  have raw : commonLift (n := n) (KemSK := KemSK) ∘ₛ RegistrationNativePairedBeaconService.rawLift = rawLift := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePairedBeaconService.rawLift,
      simulateQ_spec_query, commonLift, rawLift]
  have effect : commonLift (n := n) (KemSK := KemSK) ∘ₛ RegistrationHiddenInstall.effectLift =
      RegistrationBeaconReferenceCompiler.effect := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationHiddenInstall.effectLift,
      simulateQ_spec_query, commonLift, RegistrationBeaconReferenceCompiler.effect]
  simp only [RegistrationNativePairedBeaconService.knownStage, simulateQ_bind,
    ← QueryImpl.simulateQ_compose, raw, effect]

/-- Interpreting the whole known continuation retains the complete actual native state and all optional opening/install outcomes. -/
theorem known_source (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) (before : State n KemSK mlSource) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (simulateQ commonLift (RegistrationNativePairedBeaconService.knownStage setup.source owner sender descriptor output))).run before =
      (fun result => (result.1, (before.1, (before.2.1, result.2)))) <$>
        ((do
          let result ← simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created)
            (simulateQ (RegistrationBoundSourceCompiler.rawCompiler setup.source wire.frameWrite)
              (RegistrationNativePairedBeaconService.program setup.source descriptor output))
          simulateQ (RegistrationBeaconReferenceNativeEffects.native setup checks representation created)
            (RegistrationNativePairedBeaconService.after owner sender (fun completed => .known completed.kernel) result)).run before.2.2) := by
  rw [known_program]
  simp only [simulateQ_bind, StateT.run_bind, map_bind]
  rw [raw_program]
  simp only [bind_map_left]
  apply bind_congr
  rintro ⟨result, after⟩
  exact effects_program setup checks wire representation created scalar credential _ (before.1, (before.2.1, after))

/-- Actual successful preparation forces the deferred source branch to use its returned root; no independent material or root assumption is inserted. -/
theorem admitted_known (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (scalar : PqxdhJointGapDh.ScalarBytes)
    (credential : RegistrationNativeMldsa.Credential mlSource)
    (owner : Nat) (sender : U64) (ready : RegistrationBeaconReferenceRoot.Ready)
    (root : PqxdhSecretInputKdf.RootOutput) (before : State n KemSK mlSource)
    (prepared : before.1 ready.reference = some root) :
    (simulateQ (implementation setup checks wire representation created scalar credential)
      (simulateQ RegistrationBeaconReferenceFinish.service
        (RegistrationNativePairedBeaconService.admitted setup.source owner sender ready.descriptor ready.reference))).run before =
      (simulateQ (implementation setup checks wire representation created scalar credential)
        (simulateQ commonLift (RegistrationNativePairedBeaconService.knownStage setup.source owner sender ready.descriptor
          (PqxdhServerAuthKeySchedule.fromRoot setup.source root)))).run before := by
  have common : RegistrationBeaconReferenceFinish.service (n := n) (KemSK := KemSK) ∘ₛ
      RegistrationNativePairedServerService.publicCommon = commonLift := by
    funext query
    simp only [QueryImpl.apply_compose, RegistrationNativePairedServerService.publicCommon,
      simulateQ_spec_query, RegistrationBeaconReferenceFinish.service, commonLift]
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind, simulateQ_spec_query,
    RegistrationBeaconReferenceFinish.service, StateT.run_bind]
  rw [RegistrationBeaconReferenceNativeInterpreter.demand_known setup checks wire representation created scalar credential
    ready.reference before root prepared]
  simp only [pure_bind, RegistrationNativePairedBeaconService.publicBranch]
  have joined := congrArg (fun handler => simulateQ handler
    (RegistrationNativePairedBeaconService.knownStage setup.source owner sender ready.descriptor
      (PqxdhServerAuthKeySchedule.fromRoot setup.source root))) common
  rw [QueryImpl.simulateQ_compose] at joined
  rw [joined]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.raw_query' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.raw_query
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.raw_program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.effects_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.effects_program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.known_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.known_program
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.known_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.known_source
/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.admitted_known' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceNativeMaterial.admitted_known
