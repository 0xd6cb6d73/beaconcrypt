-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAgreement

/-! The exact same-provider agreement law composes through the actual SDK replay, reservation and one-use retention branches. Only the private root memo is projected; failed native callbacks retain every reached World, cache, pool and provider state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptRun (State close)
open RegistrationNativeProviderAcceptAgreement (project nativeProject restore)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}

def referenceNext (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
    (completed : RustM (Option RegistrationServerReferenceRoot.Ready) × State n KemSK ProviderState) :
    ProbComp (RustM (Option Nat) × State n KemSK ProviderState) :=
  match completed.1 with
  | .fail error => pure (.fail error, completed.2)
  | .div => pure (.div, completed.2)
  | .ok none => pure (.ok none, completed.2)
  | .ok (some ready) => (close implementation (RegistrationServerOpenReferenceCompiler.retain ready)).run completed.2

def nativeNext (completed : RustM agreement.AgreementEffect × RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState) :
    ProbComp (RustM (Option Nat) × RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState) :=
  match completed.1 with
  | .fail error => pure (.fail error, completed.2)
  | .div => pure (.div, completed.2)
  | .ok (.ServerComplete accepted) => (RegistrationNativeProviderAcceptSdk.retain accepted).run completed.2
  | .ok _ => pure (.ok none, completed.2)

theorem next_project (implementation : QueryImpl (RegistrationBeaconReferenceCompiler.Spec n KemSK)
    (StateT (RegistrationNativeProviderInterpreter.State n KemSK ProviderState) ProbComp))
    (roots : RegistrationServerReferenceRestore.Roots) (memo : RegistrationNativeReferenceInterpreter.State)
    (completed : RustM (Option RegistrationServerReferenceRoot.Ready) × State n KemSK ProviderState) :
    Prod.map id (project roots memo) <$> referenceNext implementation completed =
      nativeNext (RegistrationServerReferenceSourceClient.restore roots completed.1, project roots memo completed.2) := by
  rcases completed with ⟨completed, current⟩
  cases completed with
  | fail error => simp only [referenceNext, nativeNext, RegistrationServerReferenceSourceClient.restore, map_pure, Prod.map_def, id_eq]
  | div => simp only [referenceNext, nativeNext, RegistrationServerReferenceSourceClient.restore, map_pure, Prod.map_def, id_eq]
  | ok completed => cases completed with
    | none => simp only [referenceNext, nativeNext, RegistrationServerReferenceSourceClient.restore, map_pure, Prod.map_def, id_eq]
    | some ready =>
        simp only [referenceNext, RegistrationServerReferenceSourceClient.restore, nativeNext]
        rw [RegistrationNativeProviderAcceptRun.retain_run]
        simp only [RegistrationNativeProviderAcceptSdk.retain, StateT.run]
        change _ = (match RegistrationNativeProviderAcceptFields.retain
          (RegistrationServerReferenceRoot.atRoot ready (roots ready.reference))
          (RegistrationNativeProviderAcceptFields.restore roots current.1) with
          | .fail error => pure (.fail error, project roots memo current)
          | .div => pure (.div, project roots memo current)
          | .ok (reply, after) => pure (.ok reply, (after, RegistrationNativeProviderAcceptStage.resetAux memo current.2)) : ProbComp (RustM (Option Nat) × RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState))
        rw [← RegistrationNativeProviderAcceptFields.retain_restore]
        cases retained : RegistrationServerMaterialFrontend.retain ready current.1 <;>
          simp only [map_pure, project]
        all_goals rfl

theorem native_next_project (memo : RegistrationNativeReferenceInterpreter.State)
    (completed : RustM agreement.AgreementEffect × RegistrationNativeProviderAcceptSdk.State n KemSK ProviderState) :
    Prod.map id (nativeProject memo) <$> nativeNext completed =
      nativeNext (completed.1, nativeProject memo completed.2) := by
  rcases completed with ⟨completed, current⟩
  cases completed with
  | fail error => simp only [nativeNext, map_pure, Prod.map_def, id_eq]
  | div => simp only [nativeNext, map_pure, Prod.map_def, id_eq]
  | ok completed =>
      cases completed <;> simp only [nativeNext, map_pure, Prod.map_def, id_eq]
      case ServerComplete accepted =>
        simp only [RegistrationNativeProviderAcceptSdk.retain, StateT.run, nativeProject]
        cases retained : RegistrationNativeProviderAcceptFields.retain accepted current.1 <;> simp only [map_pure]

/-- Actual replay and reservation precede the complete native agreement; consumed-token retention follows only its successful result under the identical arbitrary provider. -/
theorem after_native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (packet : registration.InitPacket) (authenticated : registration.AuthenticatedInit)
    (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) memo) <$>
      (close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.afterAuthentication setup checks packet authenticated)).run before =
      Prod.map id (nativeProject memo) <$>
        (RegistrationNativeProviderAcceptSdk.afterAuthentication setup checks wire route sign seed scalar provider selected authenticated).run
          (restore (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar
  rw [RegistrationNativeProviderAcceptRun.after_run]
  change _ = Prod.map id (nativeProject memo) <$>
    (if before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) then pure (.ok none, restore roots before)
    else if checks.reserveRegistration then do
      let completed ← (RegistrationNativeProviderAcceptSdk.agree setup checks wire route sign seed scalar provider selected authenticated).run (restore roots before)
      nativeNext completed
    else pure (.ok none, restore roots before))
  by_cases replayed : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = true
  · simp only [replayed, ite_true, map_pure]; rfl
  · have fresh : before.1.consumed.contains (RegistrationReplaySchedule.identifier authenticated) = false := Bool.eq_false_iff.mpr replayed
    simp only [fresh, Bool.false_eq_true, ite_false]
    by_cases reserved : checks.reserveRegistration = true
    · simp only [reserved, ite_true, map_bind]
      change (do
        let completed ← (close (localImpl setup wire route sign seed scalar provider selected)
          (RegistrationServerOpenReferenceCompiler.agreement setup checks packet authenticated)).run before
        Prod.map id (project roots memo) <$> referenceNext (localImpl setup wire route sign seed scalar provider selected) completed) = _
      simp_rw [next_project]
      rw [← bind_map_left]
      have agreed := RegistrationNativeProviderAcceptAgreement.agreement_native setup checks wire route sign seed scalar provider selected correct packet authenticated memo before
      simp only [Prod.map_def, id_eq] at agreed
      rw [agreed]
      rw [bind_map_left]
      apply bind_congr
      intro completed
      exact (native_next_project memo completed).symm
    · have refused : checks.reserveRegistration = false := Bool.eq_false_iff.mpr reserved
      simp only [refused, Bool.false_eq_true, ite_false, map_pure]; rfl

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.next_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.next_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.native_next_project' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.native_next_project
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.after_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter.after_native
