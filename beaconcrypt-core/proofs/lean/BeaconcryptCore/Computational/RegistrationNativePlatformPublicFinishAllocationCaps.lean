-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeHiddenBeaconFinishAllocationCaps
import BeaconcryptCore.Computational.RegistrationNativeOpenKeyKemBeacon
import BeaconcryptCore.Computational.RegistrationNativePlatformPairedBeaconRawFree
/-! The literal corrected public finish has no physical owner append, private KEM birth or secret reveal. Its exact source preparation helper and actual assigned-ID material/open/install continuation retain all failures and prior journal entries. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps
open PqxdhServerAuthExperiment (Setup)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec effect)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeHiddenServerAllocationCaps (EffectAllowed LocalAllowed)
open RegistrationNativeHiddenAllocationCore (simulation mapped)
variable {n : Nat} {I KemSK Auxiliary A B : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

def Safe (kind : RegistrationNativeKemBeaconFootprint.Kind) (query : (Spec n KemSK).Domain) : Prop :=
  LocalAllowed query ∧ ¬ RegistrationNativeOpenKeyKemBeacon.IsPrivate kind query

private theorem every {J V : Type} {spec : OracleSpec J} (work : OracleComp spec V) : work.AllQueriesSatisfy (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩

private theorem and_safe {J A : Type} {spec : OracleSpec J} (work : OracleComp spec A) (p q : J → Prop)
    (left : work.AllQueriesSatisfy p) (right : work.AllQueriesSatisfy q) : work.AllQueriesSatisfy (fun query => p query ∧ q query) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨⟨left.1, right.1⟩, fun reply => ih reply (left.2 reply) (right.2 reply)⟩

private theorem raw_safe (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawSealBridge.Spec.Domain) :
    (RegistrationBoundSourceCompiler.rawCompiler (n := n) crypto writer query).AllQueriesSatisfy EffectAllowed := by
  have actual := RegistrationNativeHiddenAllocationService.publication (n := n) crypto writer (fun _ => pure none) (.inl query) []
  simpa only [RegistrationBoundSourceCompiler.compiler, StateT.run, AllQueriesSatisfy, isQueryBound_map_iff, RegistrationNativeHiddenAllocationService.EffectAllowed, EffectAllowed] using actual

private theorem read_safe (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (query : RegistrationRawReceiveBridge.Spec.Domain) (before : EnvState Auxiliary) :
    ((RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n)))
      crypto writer query).run before).AllQueriesSatisfy EffectAllowed := by
  simp only [RegistrationBeaconMaterialRead.read, RegistrationBeaconMaterialRead.charge,
    StateT.run_bind, StateT.run_modify, pure_bind, StateT.run_lift, bind_pure_comp,
    simulateQ_ofLift_eq_self, AllQueriesSatisfy, isQueryBound_map_iff]
  unfold RegistrationBeaconRecordSourceProgram.read QueryImpl.compose
  apply simulation _ (fun _ => True) EffectAllowed _ _ (every _)
  intro request _
  exact raw_safe crypto writer request

private theorem run_safe {J S V : Type} {spec : OracleSpec J}
    (impl : QueryImpl spec (StateT S (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))))
    (step : ∀ query before, AllQueriesSatisfy ((impl query).run before) EffectAllowed)
    (work : OracleComp spec V) (before : S) :
    AllQueriesSatisfy ((simulateQ impl work).run before) EffectAllowed := by
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => trivial
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    exact allQueriesSatisfy_bind (step query before) (fun reached => ih reached.1 reached.2)

private theorem raw_program_safe (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (work : OracleComp RawCtxWholeOwner.PrimitiveSpec A) (before : EnvState Auxiliary) :
    ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) crypto writer)) work).run before).AllQueriesSatisfy EffectAllowed := by
  apply run_safe _ _ work before
  intro query current
  unfold RegistrationBeaconChargedSource.primitive QueryImpl.compose
  exact run_safe _ (fun query state => read_safe crypto writer query state) _ current

private theorem installed_safe (owner : Nat) (kernel : registration.CompletedBeacon → PqxdhRecordLiftInterface.KernelRef n)
    (result : RustM RegistrationBeaconRecordExecutor.Result) (before : EnvState Auxiliary) :
    AllQueriesSatisfy ((RegistrationNativePlatformPairedBeaconService.after
      (fun query => StateT.lift ((PqxdhRecordLiftInterface.EnvEffects n).query query : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)) owner kernel result).run before) EffectAllowed := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err error => trivial
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, bind_pure_comp]
      exact allQueriesSatisfy_bind ((allQueriesSatisfy_query_iff _ _).mpr rfl) (fun _ => trivial)

private theorem branch_safe (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : Nat) (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (choice : RegistrationNativePairedChoice.Choice n)
    (before : EnvState Auxiliary) :
    ((RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
      (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) crypto writer))
      (fun query => StateT.lift ((PqxdhRecordLiftInterface.EnvEffects n).query query : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _))
      owner descriptor choice).run before).AllQueriesSatisfy EffectAllowed := by
  cases choice with
  | known output =>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch, RegistrationNativePlatformPairedBeaconOwner.knownStage, StateT.run_bind]
    exact allQueriesSatisfy_bind (raw_program_safe crypto writer _ before) (fun reached => installed_safe owner _ reached.1 reached.2)
  | hidden reference =>
    simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch, RegistrationNativePlatformPairedBeaconOwner.publicHidden,
      RegistrationNativePlatformPairedBeaconOwner.hiddenStage, StateT.run_bind]
    exact allQueriesSatisfy_bind (raw_program_safe crypto writer _ before) (fun reached => installed_safe owner _ reached.1 reached.2)

private theorem after_safe (owner current : SelectedOwner source) (result : RustM RegistrationNativePairedBeaconService.Result)
    (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (PqxdhRecordLiftInterface.EnvEffects n) (OracleComp (PqxdhRecordLiftInterface.EnvEffects n))) owner result).run current).run before).AllQueriesSatisfy EffectAllowed := by
  cases result with
  | fail error | div =>
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
      seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift]
    exact mapped _ _ EffectAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
  | ok result => cases result with
    | Err error =>
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, RegistrationNativePlatformBeaconMaterialFrontend.abort,
        seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, QueryImpl.ofLift]
      exact mapped _ _ EffectAllowed ((allQueriesSatisfy_query_iff _ _).mpr rfl)
    | Ok completed => trivial

private theorem material_safe (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready) (choice : RegistrationNativePairedChoice.Choice n)
    (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run before).AllQueriesSatisfy EffectAllowed := by
  by_cases valid : RawCtxReceive.ValidFrame ready.descriptor.candidate.server_binding.identity_key_id
    (PqxdhRefinement.absBytes ready.descriptor.binding.associated_data) (RegistrationBeaconBoundSource.frame ready.descriptor)
  all_goals
    simp only [RegistrationNativePlatformBeaconMaterialFrontend.program, valid, ite_true, ite_false,
      StateT.run_bind, StateT.run_lift, RegistrationBeaconMaterialRead.charge,
      StateT.run_modify, pure_bind, bind_pure_comp, bind_map_left]
    exact allQueriesSatisfy_bind (branch_safe crypto writer owner.worldOwner ready.descriptor choice _)
      (fun reached => after_safe owner current reached.1 reached.2)

private theorem effect_safe (kind : RegistrationNativeKemBeaconFootprint.Kind)
    (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) (safe : work.AllQueriesSatisfy EffectAllowed) :
    (simulateQ (effect (KemSK := KemSK)) work).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK) kind) := by
  apply simulation _ EffectAllowed (Safe (n := n) (KemSK := KemSK) kind) _ work safe
  intro query allowed
  exact (allQueriesSatisfy_query_iff _ _).mpr ⟨allowed, by cases query <;> simp [RegistrationNativeOpenKeyKemBeacon.IsPrivate]⟩

private theorem abort_safe (kind : RegistrationNativeKemBeaconFootprint.Kind) (owner current : SelectedOwner source)
    (before : EnvState Auxiliary) (value : A) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.abort (effect (n := n) (KemSK := KemSK)) owner *> pure value :
      RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := Auxiliary) source A).run current).run before).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK) kind) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, seqRight_eq_bind, StateT.run_lift, StateT.run_map, bind_pure_comp]
  exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr ⟨rfl, by simp [RegistrationNativeOpenKeyKemBeacon.IsPrivate]⟩)

private theorem prepared_safe (kind : RegistrationNativeKemBeaconFootprint.Kind)
    (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready)) (before : EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconContinuation.afterPrepared (n := n) (KemSK := KemSK) crypto writer owner result).run current).run before).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK) kind) := by
  cases result with
  | fail error | div =>
    simpa only [RegistrationNativePlatformBeaconContinuation.afterPrepared] using abort_safe kind owner current before _
  | ok result => cases result with
    | none => simpa only [RegistrationNativePlatformBeaconContinuation.afterPrepared] using abort_safe kind owner current before _
    | some ready =>
      simp only [RegistrationNativePlatformBeaconContinuation.afterPrepared, RegistrationNativePlatformBeaconMaterialFrontend.complete,
        StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left, RegistrationNativePlatformBeaconMaterialInterpreter.demand]
      refine (allQueriesSatisfy_query_bind_iff _ _ _).mpr ⟨⟨trivial, by simp [RegistrationNativeOpenKeyKemBeacon.IsPrivate]⟩, ?_⟩
      intro choice
      cases choice with
      | none => exact abort_safe kind owner current before _
      | some choice => exact effect_safe kind _ (material_safe crypto writer owner current ready choice before)

noncomputable def program (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket) :
    RegistrationBeaconReferenceCompletion.M (target := Spec n KemSK) (Auxiliary := RegistrationServerRoleBackend.State) source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending _ => match pending.aborted_state with
      | .fail error => pure (.fail error)
      | .div => pure .div
      | .ok _ => do
          let ready ← RegistrationBeaconReferenceCompiler.finishPreparation setup source packet
          RegistrationNativePlatformBeaconContinuation.afterPrepared setup.source wire.frameWrite owner ready
  | _ => pure (.ok none)

/-- The actual corrected public finish factors through its unchanged literal preparation helper and actual assigned-ID material continuation. -/
theorem source_eq (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (source : RegistrationNativeMldsa.Source) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run before) =
      (((program setup wire source packet).run owner).run before) := by
  simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, program, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => rfl
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved]
    | ok aborted =>
      simp only [RegistrationBeaconReferenceCompiler.finishPreparation, StateT.run_bind, StateT.run_get, pure_bind,
        phase, moved, StateT.run_set, StateT.run_modify, StateT.run_lift, bind_pure_comp, bind_map_left, bind_assoc]
      apply bind_congr
      intro authenticated
      cases authenticated with
      | fail error | div => simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformBeaconContinuation.afterPrepared]
      | ok value => cases value with
        | Err previous => simp only [StateT.run_pure, pure_bind, RegistrationNativePlatformBeaconContinuation.afterPrepared]
        | Ok authenticated => simp only [RegistrationNativePlatformBeaconPhase.phase, StateT.run_bind, StateT.run_lift,
            StateT.run_map, bind_pure_comp, bind_map_left]

attribute [local irreducible] RegistrationBeaconReferenceCompiler.finishPreparation

private theorem finish_all (kind : RegistrationNativeKemBeaconFootprint.Kind) (setup : Setup base KemSK)
    (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run before).AllQueriesSatisfy (Safe (n := n) (KemSK := KemSK) kind) := by
  classical
  rw [source_eq]
  simp only [program, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase
  all_goals try trivial
  case initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => trivial
    | ok aborted =>
      apply allQueriesSatisfy_bind
      · apply and_safe
        · exact RegistrationNativeHiddenBeaconFinishAllocationCaps.preparation_safe setup source packet owner before
        · exact (isQueryBoundP_zero_iff _ _).mp (by
            simpa only [not_not, StateT.run] using (RegistrationNativeOpenKeyKemBeacon.preparation_free (kind := kind) setup source packet owner before))
      · intro reached
        exact prepared_safe kind setup.source wire.frameWrite owner reached.1.2 reached.1.1 reached.2

/-- The complete actual corrected finish contains no physical append capability on any reply or failure branch. -/
theorem finish_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (packet : Option registration.ResponsePacket)
    (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run before).AllQueriesSatisfy (LocalAllowed (KemSK := KemSK)) :=
  (finish_all (n := n) .create setup wire packet owner before).mono (fun _ allowed => allowed.1)

/-- The same actual corrected finish creates and reveals no private KEM row, retaining every indexed decapsulation and failure. -/
theorem finish_free (kind : RegistrationNativeKemBeaconFootprint.Kind) (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : EnvState RegistrationServerRoleBackend.State) :
    (((RegistrationNativePlatformBeaconReferenceFinish.finish (n := n) setup wire source packet).run owner).run before).IsQueryBoundP
      (RegistrationNativeOpenKeyKemBeacon.IsPrivate (KemSK := KemSK) kind) 0 := by
  classical
  have kept := (finish_all (n := n) kind setup wire packet owner before).mono (fun _ allowed => allowed.2)
  have bound := (isQueryBoundP_zero_iff _ _).mpr kept
  simpa only [not_not] using bound

end BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.source_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.source_eq

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.finish_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.finish_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.finish_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicFinishAllocationCaps.finish_free
