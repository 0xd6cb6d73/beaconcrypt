-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationBeaconReferenceFinish
import BeaconcryptCore.Computational.RegistrationNativeCommonCompiler

/-! The pure paired Beacon service is interpreted on the current environment before the outer owner phase changes. This retains actual shared hash effects and chronological receipts; it does not flatten a captured mutable environment into itself. Material demand is the explicit phase query made after successful root preparation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationWorldAgreementCompiler (EnvState)
open PqxdhRecordLiftInterface (EnvEffects)
variable {ι Auxiliary : Type} {target : OracleSpec ι} {n : Nat}
variable {mlSource : RegistrationNativeMldsa.Source}

abbrev M (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (StateT (EnvState Auxiliary) (OracleComp target))

def abort (environment : QueryImpl (EnvEffects n) (OracleComp target)) (owner : SelectedOwner mlSource) : M (target := target) (Auxiliary := Auxiliary) mlSource Unit := do
  let _ ← StateT.lift (StateT.lift (environment (.inr (.advanceOwner owner.worldOwner .aborted))))
  pure ()

def after (environment : QueryImpl (EnvEffects n) (OracleComp target)) (owner : SelectedOwner mlSource) :
    RustM RegistrationNativePairedBeaconService.Result → M (target := target) (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes))
  | .fail error => abort environment owner *> pure (.fail error)
  | .div => abort environment owner *> pure .div
  | .ok (.Err _) => abort environment owner *> pure (.ok none)
  | .ok (.Ok completed) => do
      modify fun current => { current with phase := .established completed }
      pure (.ok (some (TranscriptAuthParts.absSlice completed.application)))

/-- Interpret the actual finite service on the reached environment, then settle the owner using its complete returned state. -/
noncomputable def complete (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : SelectedOwner mlSource) (ready : RegistrationBeaconReferenceRoot.Ready) : M (target := target) (Auxiliary := Auxiliary) mlSource (RustM (Option Pqxdh.Bytes)) := do
  let completed ← StateT.lift (simulateQ (RegistrationNativeCommonCompiler.service (Auxiliary := Auxiliary) environment demand source writer sign)
    (RegistrationNativePairedBeaconService.admitted source owner.worldOwner owner.pin.binding.identity_key_id ready.descriptor ready.reference))
  after environment owner completed

/-- The actual demand precedes opening and installation; no captured environment is restored after the concrete service runs. -/
theorem admitted (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (demand : QueryImpl (RegistrationNativeRelatedFamily.Message →ₒ Option (RegistrationNativePairedChoice.Choice n))
      (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (ready : RegistrationBeaconReferenceRoot.Ready) :
    simulateQ (RegistrationNativeCommonCompiler.service (Auxiliary := Auxiliary) environment demand source writer sign)
      (RegistrationNativePairedBeaconService.admitted source owner sender ready.descriptor ready.reference) = (do
        let chosen ← StateT.lift (demand ready.reference)
        match chosen with
        | none => pure (.ok (.Err ⟨sender⟩))
        | some choice =>
            simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign)
              (RegistrationNativePairedBeaconService.publicBranch source owner sender ready.descriptor choice)) := by
  simp only [RegistrationNativePairedBeaconService.admitted, simulateQ_bind, simulateQ_spec_query,
    RegistrationNativeCommonCompiler.service]
  apply bind_congr
  intro chosen
  cases chosen with
  | none => exact simulateQ_pure _ _
  | some choice =>
      rw [← QueryImpl.simulateQ_compose]
      congr 1
      funext query
      simp only [QueryImpl.compose, RegistrationNativePairedServerService.publicCommon,
        simulateQ_spec_query, RegistrationNativeCommonCompiler.service]

private theorem raw_query (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (query : RegistrationRawSealBridge.Spec.Domain) :
    RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign
        (.inl (.inl query)) =
      StateT.lift (simulateQ environment (RegistrationBoundSourceCompiler.rawCompiler source writer query)) := by
  apply StateT.ext
  intro before
  change (fun result => (result.1, { before with receipts := result.2 })) <$>
      simulateQ environment ((fun reply => (reply, before.receipts)) <$>
        RegistrationBoundSourceCompiler.rawCompiler source writer query) =
    (simulateQ environment (RegistrationBoundSourceCompiler.rawCompiler source writer query) >>=
      fun reply => pure (reply, before))
  simp only [simulateQ_map, Functor.map_map, bind_pure_comp]

/-- Beacon opening components preserve the current environment and all explicit World effects without appending fictitious ML signing receipts. -/
theorem raw_program {Result : Type} (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp RegistrationRawSealBridge.Spec Result) :
    simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign)
      (simulateQ RegistrationNativePairedBeaconService.rawLift work) =
      StateT.lift (simulateQ environment (simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer) work)) := by
  rw [← QueryImpl.simulateQ_compose]
  have step : RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign ∘ₛ
      RegistrationNativePairedBeaconService.rawLift =
      (environment ∘ₛ RegistrationBoundSourceCompiler.rawCompiler source writer).liftTarget
        (StateT (EnvState Auxiliary) (OracleComp target)) := by
    funext query
    rw [QueryImpl.apply_compose, RegistrationNativePairedBeaconService.rawLift, simulateQ_spec_query,
      QueryImpl.liftTarget_apply, QueryImpl.apply_compose]
    exact raw_query environment source writer sign query
  rw [step, simulateQ_liftTarget, QueryImpl.simulateQ_compose]
  rfl

private theorem effect_program {Result : Type} (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (work : OracleComp (EnvEffects n) Result) :
    simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign)
      (simulateQ RegistrationHiddenInstall.effectLift work) = StateT.lift (simulateQ environment work) := by
  rw [← QueryImpl.simulateQ_compose]
  have step : RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign ∘ₛ
      RegistrationHiddenInstall.effectLift = environment.liftTarget (StateT (EnvState Auxiliary) (OracleComp target)) := by
    funext query
    rw [QueryImpl.apply_compose, RegistrationHiddenInstall.effectLift, simulateQ_spec_query, QueryImpl.liftTarget_apply]
    rfl
  rw [step, simulateQ_liftTarget]
  rfl

/-- The actual known-output branch first executes the real opening and then inserts its entire consumed native kernel. -/
theorem known_stage (environment : QueryImpl (EnvEffects n) (OracleComp target))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (owner : Nat) (sender : U64) (descriptor : RegistrationBeaconBoundSource.PublicAgreement)
    (output : PqxdhServerAuthKeySchedule.Output) :
    simulateQ (RegistrationNativeCommonCompiler.common (Auxiliary := Auxiliary) environment source writer sign)
      (RegistrationNativePairedBeaconService.knownStage source owner sender descriptor output) = (do
        let result ← StateT.lift (simulateQ environment
          (simulateQ (RegistrationBoundSourceCompiler.rawCompiler source writer)
            (RegistrationNativePairedBeaconService.program source descriptor output)))
        StateT.lift (simulateQ environment
          (RegistrationNativePairedBeaconService.after owner sender (fun completed => .known completed.kernel) result))) := by
  simp only [RegistrationNativePairedBeaconService.knownStage, simulateQ_bind, raw_program, effect_program]

end BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.admitted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.admitted

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.raw_program' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.raw_program

/-- info: 'BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.known_stage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationBeaconReferenceCompletion.known_stage
