-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeProviderAcceptAfter

/-! Mandatory native ML/Ed verification precedes actual replay, reservation and same-provider agreement. The complete accept source equation retains all failed poststates and the real World cache; its sole additional observation erases the private prepared-root memo. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeProviderInterpreter (Provider)
open RegistrationNativeProviderSource (localImpl)
open RegistrationNativeProviderAcceptRun (State close close_bind close_get close_pure)
open RegistrationNativeProviderAcceptAgreement (project nativeProject restore)
variable {n : Nat} {ι KemSK ProviderState : Type} {base : OracleSpec ι}
attribute [local irreducible] RegistrationAuthenticationCompiler.program

private theorem state_lift_apply {S X : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (work : m X) (state : S) : (StateT.lift work) state = (fun value => (value, state)) <$> work := by
  change (work >>= fun value => pure (value, state)) = _
  rw [bind_pure_comp]

private theorem state_map_apply {S X Y : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (observe : X → Y) (work : StateT S m X) (state : S) : (observe <$> work) state = Prod.map observe id <$> work state := by
  change (work state >>= fun result => pure (observe result.1, result.2)) = _
  rw [bind_pure_comp]
  rfl

/-- Both the reference and native SDK paths execute the literal same mandatory authentication controller at the current native pin. -/
theorem authenticate_native (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (verify : MldsaTranscriptAuth.Verify)
    (roots : RegistrationServerReferenceRestore.Roots) (packet : registration.InitPacket) (before : State n KemSK ProviderState) :
    Prod.map id (restore roots) <$>
      (close (localImpl setup wire route sign seed scalar provider selected) (StateT.lift (StateT.lift
        (simulateQ RegistrationBeaconReferenceCompiler.effect
          (RegistrationAuthenticationCompiler.program setup.source.crypto verify before.1.pin packet))))).run before =
      (RegistrationNativeProviderAcceptSdk.authenticate setup wire route sign seed scalar provider selected verify packet).run (restore roots before) := by
  simp only [close, RegistrationNativeProviderLocal.lower, RegistrationNativeProviderAcceptSdk.authenticate,
    StateT.run, state_lift_apply, state_map_apply, simulateQ_map, Functor.map_map,
    restore, RegistrationNativeProviderAcceptFields.restore, Prod.map_def, id_eq]

/-- Actual native acceptance, including authentication rejection and every failed agreement, is derived under the identical arbitrary total KEM provider. -/
theorem accept_native (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (provider : Provider KemSK ProviderState) (selected : Bool) (verify : MldsaTranscriptAuth.Verify)
    (correct : PqxdhSecretInputKdf.SourceRootCorrect setup.source setup.hmac)
    (packet : registration.InitPacket) (memo : RegistrationNativeReferenceInterpreter.State) (before : State n KemSK ProviderState) :
    Prod.map id (project (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) memo) <$>
      (close (localImpl setup wire route sign seed scalar provider selected)
        (RegistrationServerOpenReferenceCompiler.accept setup checks verify packet)).run before =
      Prod.map id (nativeProject memo) <$>
        (RegistrationNativeProviderAcceptSdk.accept setup checks wire route sign seed scalar provider selected verify packet).run
          (restore (RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar) before) := by
  let roots := RegistrationServerReferenceSourceClient.roots setup.source setup.joint setup.dh seed scalar
  rw [RegistrationServerOpenReferenceCompiler.accept, close_bind, close_get, pure_bind]
  simp only [RegistrationNativeProviderAcceptSdk.accept, StateT.run_bind, map_bind]
  rw [← authenticate_native setup wire route sign seed scalar provider selected verify roots packet before, bind_map_left]
  rw [close_bind, map_bind]
  apply bind_congr
  rintro ⟨checked, current⟩
  cases checked with
  | fail error => simp only [close_pure, map_pure]; rfl
  | div => simp only [close_pure, map_pure]; rfl
  | ok checked =>
      rcases checked with ⟨events, verdict⟩
      cases verdict with
      | Accepted authenticated => exact RegistrationNativeProviderAcceptAfter.after_native setup checks wire route sign seed scalar provider selected correct packet authenticated memo current
      | Rejected => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl
      | HashRequested request => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl
      | MldsaVerificationRequested request => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl
      | Ed25519VerificationRequested request => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl
      | ServerFingerprintRequested request => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl
      | BeaconFingerprintRequested request => simp only [Prod.map_def, id_eq, close_pure, StateT.run_pure, map_pure]; rfl

end BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry.authenticate_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry.authenticate_native
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry.accept_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeProviderAcceptEntry.accept_native
