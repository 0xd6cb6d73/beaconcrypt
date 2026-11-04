-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedOrdinaryAgreement
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedBeaconAgreement
import BeaconcryptCore.Computational.RegistrationNativeSecretWordCheckedMaterial
/-! The symbolic corrected Beacon finish retains terminal-before-authentication order and the actual assigned-ID first-record/install program. Only preparation and material addresses carry an opaque word. The chosen material program uses solely its public descriptor, so its concrete source effects are retained unchanged. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (BeaconReady input zero)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open RegistrationNativeSecretWordInterface (LocalSpec effect)
variable {n : Nat} {I KemSK Auxiliary : Type} {base : OracleSpec I}
variable {source : RegistrationNativeMldsa.Source}

abbrev M (n : Nat) (KemSK Auxiliary : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp (LocalSpec n KemSK)))

noncomputable def complete (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) (ready : BeaconReady) : M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  match ← StateT.lift (StateT.lift (RegistrationNativeSecretWordInterface.demand ready.reference)) with
  | none => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.ok none)
  | some choice => RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effect owner (ready.eval zero) choice

noncomputable def afterPrepared (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner : SelectedOwner source) : RustM (Option BeaconReady) → M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes))
  | .fail error => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.fail error)
  | .div => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure .div
  | .ok none => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.ok none)
  | .ok (some ready) => complete crypto writer owner ready

noncomputable def phase (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse) :
    M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let result ← StateT.lift (RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated)
  afterPrepared setup.source wire.frameWrite owner result

noncomputable def finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) : M n KemSK Auxiliary source (RustM (Option Pqxdh.Bytes)) := do
  let owner ← get
  match owner.phase with
  | .initSent pending oneTime => match pending.aborted_state with
    | .fail error => pure (.fail error)
    | .div => pure .div
    | .ok aborted => do
        modify fun current => { current with phase := .aborted aborted }
        let authenticated ← StateT.lift (StateT.lift (simulateQ effect
          (simulateQ (RegistrationAuthenticationCompiler.callbacks setup.source.crypto source.verify)
            (RegistrationResponseExecutor.begin pending (match packet with | none => .None | some value => .Some value)))))
        match authenticated with
        | .fail error => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.fail error)
        | .div => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure .div
        | .ok (.Err _) => RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure (.ok none)
        | .ok (.Ok accepted) => phase setup wire owner oneTime accepted
  | _ => pure (.ok none)

variable (setup : Setup base KemSK) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (seed : PqxdhJointIdentity.IdentitySeed)
    (scalar : PqxdhJointGapDh.ScalarBytes) (localScalar : Option PqxdhJointGapDh.ScalarBytes)

noncomputable def nativeImpl : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (OracleComp (RegistrationNativeSecretWordChecked.Spec n KemSK)) :=
  match localScalar with
  | none => RegistrationNativeSecretWordChecked.native setup.source inside candidate (input setup.joint setup.dh seed scalar)
  | some localScalar => RegistrationNativeSecretWordCheckedOrdinary.original setup localScalar inside candidate seed scalar

noncomputable def wordImpl : QueryImpl (LocalSpec n KemSK)
    (OracleComp (RegistrationNativeSecretWordChecked.Spec n KemSK)) :=
  match localScalar with
  | none => RegistrationNativeSecretWordChecked.implementation setup.source inside candidate (input setup.joint setup.dh seed scalar)
  | some localScalar => RegistrationNativeSecretWordCheckedOrdinary.symbolic setup localScalar inside candidate seed scalar

private theorem effects_source {A : Type} (work : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) A) :
    simulateQ (nativeImpl setup inside candidate seed scalar localScalar)
      (simulateQ RegistrationBeaconReferenceCompiler.effect work) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar) (simulateQ effect work) := by
  cases localScalar with
  | none => exact RegistrationNativeSecretWordCheckedMaterial.effects setup.source inside candidate (input setup.joint setup.dh seed scalar) work
  | some localScalar => exact RegistrationNativeSecretWordCheckedOrdinary.effects setup localScalar inside seed scalar candidate work

/-- The actual source-selected first-record program ignores only the private reference field, retaining every public descriptor, record marker and assigned-ID install. -/
theorem chosen_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (choice : RegistrationNativePairedChoice.Choice n)
    (env : EnvState Auxiliary) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer RegistrationBeaconReferenceCompiler.effect owner (ready.eval candidate) choice).run current).run env) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar)
        (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer effect owner (ready.eval zero) choice).run current).run env) := by
  change simulateQ (nativeImpl setup inside candidate seed scalar localScalar)
    (simulateQ RegistrationBeaconReferenceCompiler.effect
      (((RegistrationNativePlatformBeaconMaterialFrontend.program crypto writer owner (ready.eval candidate) choice).run current).run env)) = _
  rw [effects_source]
  rfl

private theorem demand_source (reference : RegistrationNativeSecretWordMessage.Message) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (RegistrationNativePlatformBeaconMaterialInterpreter.demand (RegistrationNativeSecretWordMessage.eval candidate reference)) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar) (RegistrationNativeSecretWordInterface.demand reference) := by
  have same := RegistrationNativeSecretWordCheckedInput.material_literal_eval (n := n) (KemSK := KemSK)
    setup.source inside setup.joint setup.dh seed scalar candidate reference
  cases localScalar with
  | none =>
    simpa only [nativeImpl, wordImpl, RegistrationNativePlatformBeaconMaterialInterpreter.demand,
      RegistrationNativeSecretWordChecked.native, QueryImpl.apply_compose, RegistrationNativeSecretWordServerSource.realize,
      RegistrationNativeSecretWordInterface.demand, simulateQ_spec_query, RegistrationNativeSecretWordChecked.implementation] using same
  | some localScalar =>
    simpa only [nativeImpl, wordImpl, RegistrationNativeSecretWordCheckedOrdinary.original,
      RegistrationNativeSecretWordCheckedOrdinary.symbolic, QueryImpl.apply_compose,
      RegistrationNativePlatformBeaconMaterialInterpreter.demand, RegistrationNativePublicOwners.ordinary,
      RegistrationNativeSecretWordOwners.ordinary, simulateQ_spec_query, RegistrationNativeSecretWordChecked.native,
      RegistrationNativeSecretWordServerSource.realize, RegistrationNativeSecretWordInterface.demand,
      RegistrationNativeSecretWordChecked.implementation] using same

private theorem effect_query_source (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar) (RegistrationBeaconReferenceCompiler.effect query) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar) (effect query) := by
  simpa only [simulateQ_spec_query] using effects_source setup inside candidate seed scalar localScalar
    ((PqxdhRecordLiftInterface.EnvEffects n).query query : OracleComp (PqxdhRecordLiftInterface.EnvEffects n) _)

/-- The source abort preserves every reached owner/environment field and the same actual World update. -/
theorem abort_source (owner current : SelectedOwner source) (env : EnvState Auxiliary) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.abort RegistrationBeaconReferenceCompiler.effect owner).run current).run env) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar)
        (((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.abort, StateT.run_lift, bind_pure_comp,
    StateT.run_map, simulateQ_map]
  rw [effect_query_source]

/-- The actual corrected first-record continuation changes only the symbolic material address, preserving all optional failures and assigned identifiers. -/
theorem complete_source (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (owner current : SelectedOwner source) (ready : BeaconReady) (env : EnvState Auxiliary) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (((RegistrationNativePlatformBeaconMaterialFrontend.complete crypto writer RegistrationBeaconReferenceCompiler.effect
        RegistrationNativePlatformBeaconMaterialInterpreter.demand owner (ready.eval candidate)).run current).run env) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar)
        (((complete crypto writer owner ready).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.complete, complete, StateT.run_bind,
    StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, BeaconReady.eval]
  rw [demand_source]
  apply bind_congr
  intro choice
  cases choice with
  | none =>
    simp only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
    rw [abort_source setup inside candidate seed scalar localScalar owner current env]
  | some choice => exact chosen_source setup inside candidate seed scalar localScalar crypto writer owner current ready choice env

private theorem agreement_source (owner : SelectedOwner source) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (authenticated : registration.AuthenticatedResponse) (env : EnvState Auxiliary) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      ((RegistrationBeaconReferenceCompiler.agreement setup owner oneTime authenticated).run env) =
      Prod.map (RegistrationNativeSecretWordBeaconRoot.restore candidate) id <$>
        simulateQ (wordImpl setup inside candidate seed scalar localScalar)
          ((RegistrationNativeSecretWordBeaconCompiler.agreement setup owner oneTime authenticated).run env) := by
  cases localScalar with
  | none => exact RegistrationNativeSecretWordCheckedBeaconAgreement.agreement setup inside candidate seed scalar owner oneTime authenticated env
  | some localScalar => exact RegistrationNativeSecretWordCheckedOrdinaryAgreement.agreement setup localScalar inside candidate seed scalar owner oneTime authenticated env

attribute [local irreducible] RegistrationBeaconReferenceCompiler.agreement
  RegistrationNativeSecretWordBeaconCompiler.agreement RegistrationNativePlatformBeaconMaterialFrontend.complete complete

/-- The source agreement and corrected continuation compose with the same captured owner, full local environment and symbolic readiness receipt. -/
theorem phase_source (wire : RegistrationNativeWire.Wire) (owner current : SelectedOwner source)
    (oneTime : PqxdhJointGapDh.ScalarBytes) (authenticated : registration.AuthenticatedResponse)
    (env : EnvState RegistrationServerRoleBackend.State) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (((RegistrationNativePlatformBeaconPhase.phase setup wire owner oneTime authenticated).run current).run env) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar)
        (((phase setup wire owner oneTime authenticated).run current).run env) := by
  simp only [RegistrationNativePlatformBeaconPhase.phase, phase, StateT.run_bind, StateT.run_lift,
    bind_pure_comp, simulateQ_bind, bind_map_left]
  rw [agreement_source setup inside candidate seed scalar localScalar owner oneTime authenticated env, bind_map_left]
  apply bind_congr
  intro reached
  simp only [Prod.map, id_eq]
  cases accepted : reached.1 with
  | fail error | div =>
    simp only [RegistrationNativeSecretWordBeaconRoot.restore, RegistrationNativePlatformBeaconContinuation.afterPrepared,
      afterPrepared, seqRight_eq_bind, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
    rw [abort_source setup inside candidate seed scalar localScalar owner current reached.2]
  | ok selected => cases selected with
    | none =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore, Option.map_none,
        RegistrationNativePlatformBeaconContinuation.afterPrepared, afterPrepared, seqRight_eq_bind,
        StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
      rw [abort_source setup inside candidate seed scalar localScalar owner current reached.2]
    | some ready =>
      simp only [RegistrationNativeSecretWordBeaconRoot.restore, Option.map_some,
        RegistrationNativePlatformBeaconContinuation.afterPrepared, afterPrepared]
      exact complete_source setup inside candidate seed scalar localScalar setup.source wire.frameWrite owner current ready reached.2

attribute [local irreducible] RegistrationNativePlatformBeaconPhase.phase phase
  RegistrationAuthenticationCompiler.callbacks RegistrationResponseExecutor.begin

/-- The whole corrected finish, including terminal movement before authentication and every failed callback prefix, has its candidate-independent symbolic source. -/
theorem finish_source (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source)
    (env : EnvState RegistrationServerRoleBackend.State) :
    simulateQ (nativeImpl (n := n) setup inside candidate seed scalar localScalar)
      (((RegistrationNativePlatformBeaconReferenceFinish.finish setup wire source packet).run owner).run env) =
      simulateQ (wordImpl setup inside candidate seed scalar localScalar)
        (((finish setup wire source packet).run owner).run env) := by
  simp only [RegistrationNativePlatformBeaconReferenceFinish.finish, finish, StateT.run_bind,
    StateT.run_get, pure_bind]
  cases phaseShape : owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted control => rfl
  | initSent pending oneTime =>
    cases moved : pending.aborted_state with
    | fail error | div => simp only [moved, StateT.run_pure, simulateQ_pure]
    | ok aborted =>
      simp only [moved, StateT.run_modify, pure_bind, StateT.run_bind, StateT.run_lift,
        bind_pure_comp, simulateQ_bind, bind_map_left]
      rw [effects_source setup inside candidate seed scalar localScalar]
      apply bind_congr
      intro authenticated
      cases authenticated with
      | fail error | div =>
        simp only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
        rw [abort_source setup inside candidate seed scalar localScalar owner _ env]
      | ok accepted => cases accepted with
        | Err previous =>
          simp only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, simulateQ_bind, simulateQ_pure]
          rw [abort_source setup inside candidate seed scalar localScalar owner _ env]
        | Ok accepted => exact phase_source setup inside candidate seed scalar localScalar wire owner _ oneTime accepted env

end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.chosen_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.chosen_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.abort_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.abort_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.complete_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.complete_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.phase_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.phase_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.finish_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish.finish_source
