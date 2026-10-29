-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePublicSourceBuildQueries
import BeaconcryptCore.Computational.RegistrationServerOpenMaterialSource

/-! The actual optional source memo and the total private source-root material service agree on every demand reached by a live native Server capability. Common raw/sign/install work runs on the current environment and preserves the private memo/pool frame. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativePublicSourceEffects (Extra Private)
open RegistrationNativePublicSourceCallbacks (services remember)
open RegistrationNativeKemReferenceEffects (Callbacks implementation)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationNativeRelatedFamily (Message)
open RegistrationNativeRetainedRoots (Memo)
open RegistrationServerReferenceRestore (Roots)
open RegistrationNativePublicSourceBuildQueries (Prepared)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}

abbrev Local (n : Nat) (KemSK : Type) := Environment × Private n KemSK

noncomputable def actualCallbacks (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) : Callbacks n KemSK Extra :=
  RegistrationServerOpenReferenceSourceStage.callbacks setup seed scalar remember (services setup wire route sign seed scalar)

noncomputable def memoService (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes) :
    QueryImpl (RegistrationNativePairedServerService.PublicSpec n) (StateT (Local n KemSK) ProbComp) := fun query =>
  RegistrationNativeKemReferencePrefix.lower setup (actualCallbacks setup wire route sign seed scalar)
    (RegistrationNativeCommonCompiler.service RegistrationBeaconReferenceCompiler.effect
      RegistrationServerOpenReferenceCompiler.demand setup.source wire.frameWrite sign query)

private theorem effect_program (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) Value) (before : Private n KemSK) :
    (simulateQ (implementation setup callbacks)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work)).run before =
      (fun result => (result.1, { before with world := result.2 })) <$>
        (simulateQ PqxdhRecordLiftWorld.effects work).run before.world := by
  rw [← QueryImpl.simulateQ_compose]
  have same : implementation setup callbacks ∘ₛ RegistrationBeaconReferenceCompiler.effect =
      RegistrationNativeKemReferenceWorld.effect := by
    funext query
    simp only [QueryImpl.compose, RegistrationBeaconReferenceCompiler.effect,
      simulateQ_spec_query, implementation, RegistrationNativeKemReferenceWorld.handler]
  rw [same]
  exact RegistrationNativeKemReferenceWorld.world_program PqxdhRecordLiftWorld.effects work before

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (before : S) :
    (observe <$> work) before = Prod.map observe id <$> work before := by
  change (work before >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Native common components keep the entire private memo, receipt frame and owner KEM pool while sharing the actual environment World. -/
theorem common_source (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (wire : RegistrationNativeWire.Wire)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : (RegistrationNativePairedServerService.Common n).Domain) (before : Local n KemSK) :
    (RegistrationNativeKemReferencePrefix.lower setup callbacks
      (RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect
        setup.source wire.frameWrite sign query)).run before =
      (fun result => (result.1.1, (result.1.2, { before.2 with world := result.2 }))) <$>
        (simulateQ PqxdhRecordLiftWorld.effects
          ((RegistrationNativeCommonCompiler.common (QueryImpl.id' (PqxdhRecordLiftInterface.EnvEffects n))
            setup.source wire.frameWrite sign query).run before.1)).run before.2.world := by
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
    (simulateQ (implementation setup callbacks)
      ((RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect
        setup.source wire.frameWrite sign query).run before.1)).run before.2 = _
  rw [RegistrationNativeCommonCompiler.common_map, effect_program, Functor.map_map]

private theorem actual_demand (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (message : Message) (before : Private n KemSK) :
    ((actualCallbacks setup wire route sign seed scalar).demand message).run before =
      pure ((before.extra.1 message).map (fun root => RegistrationNativePairedChoice.Choice.known
        (PqxdhServerAuthKeySchedule.fromRoot setup.source root)), before) := by
  rfl

private theorem demand_run (setup : Setup base KemSK) (callbacks : Callbacks n KemSK Extra)
    (message : Message) (before : Local n KemSK) :
    (RegistrationNativeKemReferencePrefix.lower setup callbacks
      (StateT.lift (RegistrationServerOpenReferenceCompiler.demand message))).run before =
      (fun result => (result.1, (before.1, result.2))) <$> (callbacks.demand message).run before.2 := by
  simp only [RegistrationNativeKemReferencePrefix.lower, StateT.run, StateT.lift,
    bind_pure_comp, simulateQ_map, RegistrationServerOpenReferenceCompiler.demand,
    simulateQ_spec_query, implementation, RegistrationNativeKemReferenceWorld.handler,
    state_map_apply, Functor.map_map, Prod.map_def, id_eq]

/-- A source demand reached by a live capability has the same reply and full state as the total private source-root service. -/
theorem query_equal (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (memo : Memo) (roots : Roots) (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (prepared : Prepared memo roots query) (before : Local n KemSK) (fixed : before.2.extra.1 = memo) :
    (memoService setup wire route sign seed scalar query).run before =
      (RegistrationServerOpenMaterialInterface.source setup wire.frameWrite sign roots
        (services setup wire route sign seed scalar) query).run before := by
  cases query with
  | inl message =>
      change (RegistrationNativeKemReferencePrefix.lower setup (actualCallbacks setup wire route sign seed scalar)
        (StateT.lift (RegistrationServerOpenReferenceCompiler.demand message))).run before = _
      rw [demand_run, actual_demand]
      simp only [fixed, Prepared] at prepared ⊢
      rw [prepared]
      simp only [Option.map_some, map_pure]
      change _ = (RegistrationNativeKemReferencePrefix.lower setup
        (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
        (StateT.lift (RegistrationServerOpenReferenceCompiler.demand message))).run before
      rw [demand_run]
      simp only [RegistrationServerOpenMaterialInterface.callbacks, StateT.run_pure, map_pure]
  | inr query =>
      change (RegistrationNativeKemReferencePrefix.lower setup (actualCallbacks setup wire route sign seed scalar)
        (RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect setup.source wire.frameWrite sign query)).run before =
        (RegistrationNativeKemReferencePrefix.lower setup
          (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
          (RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect setup.source wire.frameWrite sign query)).run before
      rw [common_source, common_source]

/-- Every total-source material component preserves the full private bookkeeping alongside the current environment. -/
theorem total_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (query : (RegistrationNativePairedServerService.PublicSpec n).Domain)
    (before : Local n KemSK) (result : (RegistrationNativePairedServerService.PublicSpec n).Range query × Local n KemSK)
    (supported : result ∈ support ((RegistrationServerOpenMaterialInterface.source setup wire.frameWrite sign roots
      (services setup wire route sign seed scalar) query).run before)) :
    result.2.2.extra = before.2.extra ∧ result.2.2.pool = before.2.pool := by
  cases query with
  | inl message =>
      change result ∈ support ((RegistrationNativeKemReferencePrefix.lower setup
        (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
        (StateT.lift (RegistrationServerOpenReferenceCompiler.demand message))).run before) at supported
      rw [demand_run] at supported
      simp only [RegistrationServerOpenMaterialInterface.callbacks, StateT.run_pure, map_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | inr query =>
      change result ∈ support ((RegistrationNativeKemReferencePrefix.lower setup
        (RegistrationServerOpenMaterialInterface.callbacks setup.source roots (services setup wire route sign seed scalar))
        (RegistrationNativeCommonCompiler.common RegistrationBeaconReferenceCompiler.effect setup.source wire.frameWrite sign query)).run before) at supported
      rw [common_source, support_map] at supported
      obtain ⟨inner, _possible, rfl⟩ := supported
      exact ⟨rfl, rfl⟩

/-- A complete material program whose demands are backed by live-root receipts equals the actual total source program, with full optional replies and private state. -/
theorem program_equal (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (memo : Memo) (roots : Roots) (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (prepared : work.AllQueriesSatisfy (Prepared memo roots)) (before : Local n KemSK) (fixed : before.2.extra.1 = memo) :
    (simulateQ (memoService setup wire route sign seed scalar) work).run before =
      (simulateQ (RegistrationServerOpenMaterialInterface.source setup wire.frameWrite sign roots
        (services setup wire route sign seed scalar)) work).run before := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure output => rfl
  | query_bind query next ih =>
      rw [allQueriesSatisfy_query_bind_iff] at prepared
      rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query,
        StateT.run_bind, StateT.run_bind, query_equal setup wire route sign seed scalar memo roots query prepared.1 before fixed]
      apply bind_congr_of_forall_mem_support
      intro step supported
      have frame := total_frame setup wire route sign seed scalar roots query before step supported
      exact ih step.1 (prepared.2 step.1) step.2 ((congrArg Prod.fst frame.1).trans fixed)

/-- Complete source material continuations keep the entire private memo and pool frame, including all signing and installation failures. -/
theorem program_frame (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (roots : Roots) (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value)
    (before : Local n KemSK) (result : Value × Local n KemSK)
    (supported : result ∈ support ((simulateQ (RegistrationServerOpenMaterialInterface.source setup wire.frameWrite sign roots
      (services setup wire route sign seed scalar)) work).run before)) :
    result.2.2.extra = before.2.extra ∧ result.2.2.pool = before.2.pool := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure output =>
      rw [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact ⟨rfl, rfl⟩
  | query_bind query next ih =>
      rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, reached, tail⟩ := supported
      obtain ⟨extraFirst, poolFirst⟩ := total_frame setup wire route sign seed scalar roots query before step reached
      obtain ⟨extraLast, poolLast⟩ := ih step.1 step.2 result tail
      exact ⟨extraLast.trans extraFirst, poolLast.trans poolFirst⟩

end BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.common_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.common_source
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.query_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.query_equal
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.total_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.total_frame
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.program_equal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.program_equal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.program_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePublicSourceMaterial.program_frame
