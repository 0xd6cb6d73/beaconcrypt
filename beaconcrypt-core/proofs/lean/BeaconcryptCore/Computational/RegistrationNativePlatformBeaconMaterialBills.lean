-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialFrontend
import BeaconcryptCore.Computational.RegistrationNativeFinishCosts
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialInterpreter
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconOpeningBills
/-! Corrected assigned-ID Beacon material use retains native record markers, first opening, final installation and abort. The small opening bill is composed in the same environment; public callback resource closure is separate. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills
open PqxdhRecordLiftInterface (EnvEffects EffectKind effectKind KernelRef)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativePublicationCosts (hashCost)
open RegistrationNativeCreateCosts (administrativeCost)
variable {n : Nat} {Auxiliary A B : Type} {source : RegistrationNativeMldsa.Source}

private abbrev EnvM (A : Type) := StateT (EnvState Auxiliary) (OracleComp (EnvEffects n)) A
private abbrev Work (A : Type) := StateT (SelectedOwner source) (EnvM (n := n) (Auxiliary := Auxiliary)) A
private def Bounded (kind : EffectKind) (work : Work (n := n) (Auxiliary := Auxiliary) (source := source) A) (cap : Nat) : Prop :=
  ∀ owner env, ((work.run owner).run env).IsQueryBoundP (fun query => effectKind query = kind) cap
private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (before : S) :
    (StateT.lift work : StateT S m X) before = (fun value => (value, before)) <$> work := bind_pure_comp _ _
private theorem pure_bound (kind : EffectKind) (value : A) (cap : Nat) :
    Bounded kind (pure value : Work (n := n) (Auxiliary := Auxiliary) (source := source) A) cap := by
  intro owner env
  simp only [StateT.run_pure]
  trivial
private theorem bind_bound (kind : EffectKind)
    (work : Work (n := n) (Auxiliary := Auxiliary) (source := source) A)
    (next : A → Work (n := n) (Auxiliary := Auxiliary) (source := source) B)
    (firstCap laterCap : Nat) (first : Bounded kind work firstCap) (later : ∀ value, Bounded kind (next value) laterCap) :
    Bounded kind (work >>= next) (firstCap + laterCap) := by
  intro owner env
  simp only [StateT.run_bind]
  exact isQueryBoundP_bind (first owner env) (fun result _ => later result.1.1 result.1.2 result.2)
private theorem bind_zero (kind : EffectKind)
    (work : Work (n := n) (Auxiliary := Auxiliary) (source := source) A)
    (next : A → Work (n := n) (Auxiliary := Auxiliary) (source := source) B)
    (cap : Nat) (first : Bounded kind work 0) (later : ∀ value, Bounded kind (next value) cap) :
    Bounded kind (work >>= next) cap := by
  simpa only [Nat.zero_add] using bind_bound kind work next 0 cap first later
private theorem lifted_bound (kind : EffectKind) (work : EnvM (n := n) (Auxiliary := Auxiliary) A) (cap : Nat)
    (bounded : ∀ env, (work.run env).IsQueryBoundP (fun query => effectKind query = kind) cap) :
    Bounded kind (StateT.lift work : Work (n := n) (Auxiliary := Auxiliary) (source := source) A) cap := by
  intro owner env
  simpa only [StateT.run_lift, StateT.run_map, bind_pure_comp, Functor.map_map, isQueryBoundP_map_iff] using bounded env
private theorem charge_zero (kind : EffectKind) (call : RegistrationWorldAgreement.RecordCall) :
    Bounded kind (StateT.lift (RegistrationBeaconMaterialRead.charge call) : Work (n := n) (Auxiliary := Auxiliary) (source := source) Unit) 0 := by
  intro owner env
  simp only [StateT.run_lift, RegistrationBeaconMaterialRead.charge]
  trivial

private def effects : QueryImpl (EnvEffects n) (EnvM (n := n) (Auxiliary := Auxiliary)) :=
  fun query => StateT.lift ((EnvEffects n).query query)

private theorem install_bound (kind : EffectKind) (owner : Nat)
    (kernel : registration.CompletedBeacon → KernelRef n) (result : RustM RegistrationBeaconRecordExecutor.Result) (env : EnvState Auxiliary) :
    ((RegistrationNativePlatformPairedBeaconService.after effects owner kernel result).run env).IsQueryBoundP
      (fun query => effectKind query = kind) (administrativeCost kind) := by
  cases result with
  | fail error | div => trivial
  | ok result => cases result with
    | Err aborted => trivial
    | Ok completed =>
      simp only [RegistrationNativePlatformPairedBeaconService.after, effects,
        StateT.run_lift, bind_pure_comp, StateT.run_map, Functor.map_map, isQueryBoundP_map_iff]
      cases kind <;> simp [isQueryBoundP_query_iff, effectKind, administrativeCost]

private theorem abort_bound (kind : EffectKind) (owner : SelectedOwner source) :
    Bounded kind (RegistrationNativePlatformBeaconMaterialFrontend.abort
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner : Work (n := n) (Auxiliary := Auxiliary) (source := source) Unit)
      (administrativeCost kind) := by
  intro current env
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, StateT.run_map,
    bind_pure_comp, Functor.map_map, QueryImpl.ofLift, isQueryBoundP_map_iff]
  cases kind <;> simp [isQueryBoundP_query_iff, effectKind, administrativeCost]

private theorem after_bound (kind : EffectKind) (owner : SelectedOwner source)
    (result : RustM RegistrationNativePairedBeaconService.Result) :
    Bounded kind (RegistrationNativePlatformBeaconMaterialFrontend.after
      (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) owner result : Work (n := n) (Auxiliary := Auxiliary) (source := source) _)
      (administrativeCost kind) := by
  cases result with
  | fail error | div =>
    simpa only [RegistrationNativePlatformBeaconMaterialFrontend.after, seqRight_eq_bind, Nat.add_zero] using
      bind_bound kind _ _ (administrativeCost kind) 0 (abort_bound kind owner) (fun _ => pure_bound kind _ 0)
  | ok result => cases result with
    | Err aborted =>
      simpa only [RegistrationNativePlatformBeaconMaterialFrontend.after, seqRight_eq_bind, Nat.add_zero] using
        bind_bound kind _ _ (administrativeCost kind) 0 (abort_bound kind owner) (fun _ => pure_bound kind _ 0)
    | Ok completed =>
      intro current env
      simp only [RegistrationNativePlatformBeaconMaterialFrontend.after, StateT.run_bind, StateT.run_modify, StateT.run_pure, pure_bind]
      trivial

private theorem branch_bound (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (descriptor : RegistrationBeaconBoundSource.PublicAgreement) (owner : Nat)
    (choice : RegistrationNativePairedChoice.Choice n) (kind : EffectKind)
    (opening : ∀ output (env : EnvState Auxiliary), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (RegistrationBeaconSeed.program crypto descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) (env : EnvState Auxiliary) :
    ((RegistrationNativePlatformPairedBeaconOwner.publicBranch crypto
      (RegistrationBeaconChargedSource.primitive (RegistrationBeaconMaterialRead.read
        (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer)) effects owner descriptor choice).run env).IsQueryBoundP
      (fun query => effectKind query = kind) (2 * hashCost kind + administrativeCost kind) := by
  cases choice with
  | known output | hidden reference =>
    all_goals simp only [RegistrationNativePlatformPairedBeaconOwner.publicBranch,
      RegistrationNativePlatformPairedBeaconOwner.knownStage, RegistrationNativePlatformPairedBeaconOwner.publicHidden,
      RegistrationNativePlatformPairedBeaconOwner.hiddenStage, StateT.run_bind]
    all_goals exact isQueryBoundP_bind (opening _ env) (fun result _ => install_bound kind owner _ result.1 result.2)

private theorem program_from_opening (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (kind : EffectKind)
    (opening : ∀ output (env : EnvState Auxiliary), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (RegistrationBeaconSeed.program crypto ready.descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Bounded (Auxiliary := Auxiliary) kind (RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice)
      (2 * hashCost kind + administrativeCost kind + administrativeCost kind) := by
  have tail := bind_bound kind _ _ (2 * hashCost kind + administrativeCost kind) (administrativeCost kind)
    (lifted_bound (source := source) kind _ _ (branch_bound crypto writer ready.descriptor owner.worldOwner choice kind opening))
    (after_bound kind owner)
  unfold RegistrationNativePlatformBeaconMaterialFrontend.program
  dsimp only
  apply bind_zero kind _ _ _ (charge_zero kind .initialKdf)
  intro _
  split
  · exact bind_zero kind _ _ _ (charge_zero kind .ratchetKdf) (fun _ => tail)
  · exact tail
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_simulate weighted_indicator weighted_bind weighted_mono)
open RegistrationNativeWeightedContext (query_bound map_bound)
variable {KemSK : Type}
def recordBill (kind : EffectKind) := 2 * hashCost kind + administrativeCost kind + administrativeCost kind
def completeBill (kind : EffectKind) := RegistrationNativePrimitiveCosts.coinCost 108 kind + recordBill kind

private theorem chosen_from_opening (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (env : EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind)
    (opening : ∀ output (env : EnvState Auxiliary), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (RegistrationBeaconSeed.program crypto ready.descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationBeaconReferenceCompiler.effect owner ready choice).run current).run env)
      (recordBill kind) := by
  change Weighted _ (simulateQ RegistrationBeaconReferenceCompiler.effect
    (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run env)) _
  apply weighted_simulate (fun query => if effectKind query = kind then 1 else 0) _ _ _ _
  · simpa only [Nat.one_mul, recordBill] using weighted_indicator (fun query => effectKind query = kind) 1 _ _
      (program_from_opening crypto writer owner ready choice kind opening current env)
  · intro query
    simp [Weighted, RegistrationBeaconReferenceCompiler.effect, RegistrationNativeReferenceCosts.bill, isQueryBound_query_iff]

private theorem reference_abort (owner current : SelectedOwner source) (env : EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner).run current).run env)
      (administrativeCost kind) := RegistrationNativeFinishCosts.abort_bound owner current env qSign qKem kind

private theorem complete_from_opening (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind)
    (opening : ∀ output (env : EnvState Auxiliary), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (RegistrationBeaconSeed.program crypto ready.descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env)
      (completeBill kind) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, completeBill]
  apply weighted_bind _ _ _ (RegistrationNativePrimitiveCosts.coinCost 108 kind) (recordBill kind)
  · simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, Weighted, isQueryBound_map_iff,
      RegistrationNativePlatformBeaconMaterialInterpreter.demand]
    exact query_bound (source := RegistrationBeaconReferenceCompiler.Spec n KemSK)
      (fun query => RegistrationNativeReferenceCosts.bill qSign qKem query kind) (.inr (.inl (.inl ready.reference)))
  · intro selected
    rcases selected with ⟨⟨selected, reached⟩, reachedEnv⟩
    cases selected with
    | none =>
      apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold recordBill; omega)
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, Weighted, isQueryBound_map_iff] using
        reference_abort (KemSK := KemSK) owner reached reachedEnv qSign qKem kind
    | some choice => exact chosen_from_opening crypto writer owner reached ready choice reachedEnv qSign qKem kind opening
variable {I : Type} {base : OracleSpec I}

def finishBill (qKem : Nat) (kind : EffectKind) := hashCost kind * 2 +
  (RegistrationNativePrimitiveCosts.coinCost qKem kind * 12 + completeBill kind)

private theorem afterPrepared_from_opening (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (result : RustM (Option RegistrationBeaconReferenceRoot.Ready))
    (env : EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind)
    (opening : ∀ descriptor output (env : EnvState Auxiliary), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) crypto writer))
        (RegistrationBeaconSeed.program crypto descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconContinuation.afterPrepared crypto writer owner result).run current).run env)
      (completeBill kind) := by
  cases result with
  | fail error | div =>
    apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill recordBill; omega)
    simpa only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind,
      StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, Weighted, isQueryBound_map_iff] using
        reference_abort (KemSK := KemSK) owner current env qSign qKem kind
  | ok result => cases result with
    | none =>
      apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill recordBill; omega)
      simpa only [RegistrationNativePlatformBeaconContinuation.afterPrepared, seqRight_eq_bind,
        StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, Weighted, isQueryBound_map_iff] using
          reference_abort (KemSK := KemSK) owner current env qSign qKem kind
    | some ready => exact complete_from_opening crypto writer owner current ready env qSign qKem kind (opening ready.descriptor)

private theorem phase_from_opening (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner current : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : EnvState RegistrationServerRoleBackend.State) (qSign qKem : Nat) (kind : EffectKind)
    (opening : ∀ descriptor output (env : EnvState RegistrationServerRoleBackend.State), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) setup.source wire.frameWrite))
        (RegistrationBeaconSeed.program setup.source descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconPhase.phase setup wire owner oneTime authenticated).run current).run env)
      (RegistrationNativePrimitiveCosts.coinCost qKem kind * 12 + completeBill kind) := by
  simp only [RegistrationNativePlatformBeaconPhase.phase, StateT.run_bind, StateT.run_lift, bind_pure_comp]
  apply weighted_bind _ _ _ (RegistrationNativePrimitiveCosts.coinCost qKem kind * 12) (completeBill kind)
  · simpa only [StateT.run_map, Weighted, isQueryBound_map_iff] using
      RegistrationNativeBeaconPreparationCosts.agreement_bound setup owner oneTime authenticated qSign qKem kind env
  · rintro ⟨⟨result, afterOwner⟩, afterEnv⟩
    exact afterPrepared_from_opening setup.source wire.frameWrite owner afterOwner result afterEnv qSign qKem kind opening

private theorem finish_from_opening (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) (qSign qKem : Nat) (kind : EffectKind)
    (opening : ∀ descriptor output (env : EnvState RegistrationServerRoleBackend.State), ((simulateQ (RegistrationBeaconChargedSource.primitive
      (RegistrationBeaconMaterialRead.read (QueryImpl.ofLift (EnvEffects n) (OracleComp (EnvEffects n))) setup.source wire.frameWrite))
        (RegistrationBeaconSeed.program setup.source descriptor output)).run env).IsQueryBoundP
        (fun query => effectKind query = kind) (2 * hashCost kind)) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)
      (finishBill qKem kind) := by
  simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases phase : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted previous => trivial
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => trivial
    | ok aborted =>
      simp only [finishBill]
      rw [← Nat.zero_add (hashCost kind * 2 + (RegistrationNativePrimitiveCosts.coinCost qKem kind * 12 + completeBill kind))]
      apply weighted_bind _ _ _ 0 _ (by trivial)
      rintro ⟨⟨_, current⟩, currentEnv⟩
      apply weighted_bind _ _ _ (hashCost kind * 2) _
      · simpa only [lift_apply, map_apply, Weighted, isQueryBound_map_iff] using
          RegistrationNativeResponseCosts.compiled_bound setup.source.crypto source.verify pending _ qSign qKem kind
      · rintro ⟨⟨authenticated, afterOwner⟩, afterEnv⟩
        cases authenticated with
        | fail error | div =>
          apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill recordBill; omega)
          have aborting := reference_abort (n := n) (KemSK := KemSK) owner afterOwner afterEnv qSign qKem kind
          simp only [StateT.run] at aborting
          simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, Weighted, isQueryBound_map_iff] using aborting
        | ok result => cases result with
          | Err error =>
            apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill recordBill; omega)
            have aborting := reference_abort (n := n) (KemSK := KemSK) owner afterOwner afterEnv qSign qKem kind
            simp only [StateT.run] at aborting
            simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map, map_apply, Weighted, isQueryBound_map_iff] using aborting
          | Ok authenticated => exact phase_from_opening setup wire owner afterOwner oneTime authenticated afterEnv qSign qKem kind opening
/-- The actual chosen-source opening, assigned installation and abort have their derived Env bill. -/
theorem program_bound (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (choice : RegistrationNativePairedChoice.Choice n) (env : EnvState Auxiliary) (kind : EffectKind) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner ready choice).run current).run env).IsQueryBoundP
      (fun query => effectKind query = kind) (recordBill kind) :=
  program_from_opening crypto writer owner ready choice kind
    (fun output current => RegistrationNativePlatformBeaconOpeningBills.opening_bound crypto writer ready.descriptor output current kind) current env

/-- Actual reference demand and corrected sequence-one use retain the native weighted material bill on every failure path. -/
theorem complete_bound (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : RegistrationBeaconReferenceRoot.Ready)
    (env : EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner ready).run current).run env)
      (completeBill kind) :=
  complete_from_opening crypto writer owner current ready env qSign qKem kind
    (fun output current => RegistrationNativePlatformBeaconOpeningBills.opening_bound crypto writer ready.descriptor output current kind)

/-- The complete corrected assigned-ID finish has a derived source bill; no source callback or Frame allowance is supplied. -/
theorem finish_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeReferenceCosts.bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env)
      (finishBill qKem kind) :=
  finish_from_opening setup wire packet owner env qSign qKem kind
    (fun descriptor output current => RegistrationNativePlatformBeaconOpeningBills.opening_bound setup.source wire.frameWrite descriptor output current kind)
end BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.complete_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformBeaconMaterialBills.finish_bound
