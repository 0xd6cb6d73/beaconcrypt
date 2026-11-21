-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBeaconPreparationCosts
import BeaconcryptCore.Computational.RegistrationNativeBeaconInstallCosts

/-! The actual native terminal finish callback pays response authentication, the twelve-slot local prefix, one admitted material/first-record/installation program and every possible native abort. Ordinary-owner message materialization changes no resource bill. All source owner, optional failure, receipt and environment states are retained. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
namespace BeaconcryptCore.Computational.RegistrationNativeFinishCosts
open PqxdhRecordLiftInterface (EffectKind)
open RegistrationNativeCreateCosts (administrativeCost)
open RegistrationNativeBeaconInstallCosts (admittedBill publicCost)
open RegistrationNativeBeaconPreparationCosts (preparationBill)
open PqxdhRecordLiftCtxProgramBounds (Weighted weighted_bind weighted_simulate weighted_mono)
open RegistrationNativeWeightedContext (query_bound map_bound)
open RegistrationNativeReferenceCosts (bill)
open RegistrationBeaconReferenceCompiler (SelectedOwner Spec)
variable {n : Nat} {ι KemSK Auxiliary : Type} {base : OracleSpec ι}

def completeBill (kind : EffectKind) := admittedBill kind + administrativeCost kind

def finishBill (qKem : Nat) (kind : EffectKind) := preparationBill qKem kind + completeBill kind

private theorem map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : X → Y) (work : StateT S m X) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := by
  change (work before >>= fun result => pure (f result.1, result.2)) = _
  simp only [bind_pure_comp]
  rfl

private theorem service_bound {Value : Type} (qSign qKem : Nat) (kind : EffectKind)
    (work : OracleComp (RegistrationNativePairedServerService.PublicSpec n) Value) (count : Nat)
    (bounded : Weighted (publicCost qSign kind) work count) :
    Weighted (fun query => bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (simulateQ (RegistrationBeaconReferenceFinish.service (KemSK := KemSK)) work) count := by
  apply weighted_simulate (publicCost qSign kind) _ _ _ _ bounded
  intro query
  cases query with
  | inl message => exact query_bound _ _
  | inr common => cases common <;> exact query_bound _ _

/-- The real abort is one administrative request with the original owner address. -/
theorem abort_bound {source : RegistrationNativeMldsa.Source} (owner current : SelectedOwner source)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationBeaconReferenceFinish.abort (KemSK := KemSK) owner).run current).run before) (administrativeCost kind) := by
  simp only [RegistrationBeaconReferenceFinish.abort, StateT.run_lift,
    StateT.run_map, bind_pure_comp, Functor.map_map,
    RegistrationBeaconReferenceCompiler.effect]
  exact map_bound _ _ _ _ (by cases kind <;> exact query_bound _ _)

/-- The source completion includes optional material failure, original first-record work, installation refusal and subsequent abort. -/
theorem complete_bound (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    {mlSource : RegistrationNativeMldsa.Source} (owner current : SelectedOwner mlSource)
    (ready : RegistrationBeaconReferenceRoot.Ready) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationBeaconReferenceFinish.complete (n := n) (KemSK := KemSK) source owner ready).run current).run before) (completeBill kind) := by
  simp only [RegistrationBeaconReferenceFinish.complete, StateT.run_bind, StateT.run_lift,
    bind_map_left, bind_pure_comp]
  apply weighted_bind _ _ _ _ _ (service_bound qSign qKem kind _ _
    (RegistrationNativeBeaconInstallCosts.admitted_bound source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference qSign kind))
  intro completed
  cases completed with
  | fail error =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
        map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current before qSign qKem kind
  | div =>
      simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
        map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current before qSign qKem kind
  | ok completed => cases completed with
    | Err aborted =>
        simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
          map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current before qSign qKem kind
    | Ok completed => trivial

/-- Every actual terminal finish branch obeys its literal source bill, without a caller-supplied callback-frame premise. -/
theorem finish_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationBeaconReferenceFinish.finish setup source packet).run owner).run before) (finishBill qKem kind) := by
  simp only [RegistrationBeaconReferenceFinish.finish, StateT.run_bind, StateT.run_get, pure_bind]
  cases owner.phase with
  | fresh | freshWithCoins oneTime | established completed | aborted aborted => trivial
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error => simp only [moved, StateT.run_pure]; trivial
      | div => simp only [moved, StateT.run_pure]; trivial
      | ok aborted =>
          simp only []
          apply weighted_bind _ _ _ _ _ (RegistrationNativeBeaconPreparationCosts.preparation_bound setup source packet owner before qSign qKem kind)
          intro prepared
          rcases prepared with ⟨⟨prepared, current⟩, env⟩
          cases prepared with
          | fail error =>
              apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill; omega)
              simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
                map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current env qSign qKem kind
          | div =>
              apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill; omega)
              simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
                map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current env qSign qKem kind
          | ok prepared => cases prepared with
            | none =>
                apply weighted_mono _ _ (administrativeCost kind) _ ?_ (by unfold completeBill; omega)
                simpa only [seqRight_eq_bind, StateT.run_bind, StateT.run_pure, bind_pure_comp, StateT.run_map,
                  map_apply, StateT.run, Weighted, isQueryBound_map_iff] using abort_bound owner current env qSign qKem kind
            | some ready => exact complete_bound setup.source owner current ready env qSign qKem kind

private theorem ordinary_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK)
    (scalar : PqxdhJointGapDh.ScalarBytes) (qSign qKem : Nat) (kind : EffectKind)
    {Value : Type} (work : OracleComp (Spec n KemSK) Value) (count : Nat)
    (bounded : Weighted (fun query => bill qSign qKem query kind) work count) :
    Weighted (fun query => bill qSign qKem query kind) (simulateQ (RegistrationNativePublicOwners.ordinary setup scalar) work) count := by
  apply weighted_simulate _ _ _ _ _ bounded
  intro query
  cases query with
  | inl message =>
      simp only [RegistrationNativePublicOwners.ordinary]
      cases RegistrationNativeLocalMessage.materialize setup.joint setup.dh scalar message
      · trivial
      · exact query_bound _ _
  | inr query => exact query_bound _ _

/-- The actual public-owner finish retains both absent-handle rejection and ordinary-owner materialization under the same source bill. -/
theorem owners_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (index : Nat) (owners : RegistrationNativePublicOwners.State source)
    (before : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => bill (n := n) (KemSK := KemSK) qSign qKem query kind)
      (((RegistrationNativePublicOwners.finish (n := n) setup source index packet).run owners).run before) (finishBill qKem kind) := by
  simp only [RegistrationNativePublicOwners.finish, StateT.run]
  cases owners[index]? with
  | none => trivial
  | some owner =>
      simp only []
      cases stored : owner.scalar with
      | none =>
          simp only []
          exact map_bound _ _ _ _ (finish_bound setup source packet owner.view before qSign qKem kind)
      | some scalar =>
          simp only []
          exact map_bound _ _ _ _ (ordinary_bound setup scalar qSign qKem kind _ _
            (finish_bound setup source packet owner.view before qSign qKem kind))

/-- Every typed native finish callback has its source-derived cost before the original raw parser/lifecycle transport. -/
theorem frontend_bound (setup : PqxdhServerAuthExperiment.Setup base KemSK) (checks : PqxdhServerAuthExperiment.Checks)
    (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (packet : Option registration.ResponsePacket) (index : Nat) (before : RegistrationNativePublicFrontend.State source)
    (qSign qKem : Nat) (kind : EffectKind) :
    Weighted (fun query => RegistrationNativeRestrictedCosts.bill qSign qKem query kind)
      ((RegistrationNativePublicFrontend.handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey
        (.inr (.finish index packet))).run before) (finishBill qKem kind) := by
  have actual := RegistrationNativeReferenceCosts.lifted_program (n := n) qSign qKem false _ kind _
    (owners_bound (n := n) setup source packet index before.beacons before.environment qSign qKem kind)
  simpa only [RegistrationNativePublicFrontend.handler, RegistrationNativePublicFrontend.beacon,
    StateT.run, Weighted, isQueryBound_map_iff] using actual

end BeaconcryptCore.Computational.RegistrationNativeFinishCosts

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishCosts.abort_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishCosts.abort_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishCosts.complete_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishCosts.complete_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishCosts.finish_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishCosts.finish_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishCosts.owners_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishCosts.owners_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeFinishCosts.frontend_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeFinishCosts.frontend_bound
