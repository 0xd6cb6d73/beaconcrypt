-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordFinish
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBeacon
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message BeaconReady)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec effect)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
open RegistrationNativeSecretWordLiveCaps (Bad BadLocal)
open RegistrationNativeSecretWordLiveBeaconPreparation (routing)
open RegistrationNativeSecretWordLiveBeaconSafety (close)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
open RegistrationNativePlatformSecretWordFinish (complete afterPrepared phase finish)
variable {n : Nat} {I KemSK Auxiliary Value Next : Type} {base : OracleSpec I}

private theorem routing_bound (flags : Message → Bool) (setup : Setup base KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (work : OracleComp (LocalSpec n KemSK) Value)
    (bounded : work.IsQueryBoundP (BadLocal (KemSK := KemSK) flags) 0) :
    (simulateQ (routing setup ownScalar) work).IsQueryBoundP (Bad (KemSK := KemSK) flags) 0 := by
  cases ownScalar with
  | none => exact RegistrationNativeSecretWordLiveCaps.local_bound flags false work bounded
  | some scalar =>
      rw [routing, QueryImpl.simulateQ_compose]
      exact RegistrationNativeSecretWordLiveCaps.local_bound flags false _
        (RegistrationNativeSecretWordLiveBeaconCaps.ordinary_bound flags setup scalar work bounded)

private theorem pure_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (value : Value) (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) (pure value) before :=
  RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid (by trivial)

private theorem chosen_free (flags : Message → Bool) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (ready : BeaconReady) (choice : RegistrationNativePairedChoice.Choice n)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) :
    (((RegistrationNativePlatformBeaconMaterialFrontend.chosen crypto writer (effect (KemSK := KemSK)) owner (ready.eval RegistrationNativeSecretWordMessage.zero) choice).run current).run env).IsQueryBoundP
      (BadLocal (KemSK := KemSK) flags) 0 := by
  simp only [RegistrationNativePlatformBeaconMaterialFrontend.chosen, StateT.run]
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro query
  simp [effect, BadLocal, isQueryBoundP_query_iff]

private theorem abort_free (flags : Message → Bool) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (value : Value) :
    ((((RegistrationNativePlatformBeaconMaterialFrontend.abort effect owner *> pure value :
      RegistrationNativePlatformSecretWordFinish.M n KemSK Auxiliary source Value).run current).run env)).IsQueryBoundP
      (BadLocal (KemSK := KemSK) flags) 0 := by
  simp [RegistrationNativePlatformBeaconMaterialFrontend.abort, effect, seqRight_eq_bind,
    StateT.run_lift, bind_pure_comp, BadLocal, isQueryBoundP_map_iff, isQueryBoundP_query_iff]

private theorem complete_free (flags : Message → Bool) (crypto : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (writer : RawCtxMixedShared.Writer) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (ready : BeaconReady)
    (env : RegistrationWorldAgreementCompiler.EnvState Auxiliary) (prepared : flags ready.reference = true) :
    (((complete crypto writer owner ready : RegistrationNativePlatformSecretWordFinish.M n KemSK Auxiliary source _).run current).run env).IsQueryBoundP
      (BadLocal (KemSK := KemSK) flags) 0 := by
  simp only [complete, StateT.run_bind, StateT.run_lift, bind_pure_comp, bind_map_left]
  apply isQueryBoundP_bind (n := 0) (m := 0)
  · simp [RegistrationNativeSecretWordInterface.demand, BadLocal, prepared, isQueryBoundP_query_iff]
  · intro chosen _
    cases chosen with
    | none => exact abort_free flags owner current env _
    | some choice => exact chosen_free flags crypto writer owner current ready choice env

private theorem after_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (env : Environment) (result : RustM (Option BeaconReady))
    (before : State n KemSK) (valid : Valid input before)
    (prepared : ∀ ready, result = .ok (some ready) → before.flags ready.reference = true) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (close setup ownScalar (afterPrepared setup.source wire.frameWrite owner result) current env) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply routing_bound before.flags setup ownScalar
  cases result with
  | fail error | div => exact abort_free before.flags owner current env _
  | ok reply => cases reply with
    | none => exact abort_free before.flags owner current env _
    | some ready => exact complete_free before.flags setup.source wire.frameWrite owner current ready env (prepared ready rfl)

private theorem state_bind_apply {S X Y : Type} {m : Type → Type} [Monad m]
    (first : StateT S m X) (next : X → StateT S m Y) (before : S) :
    (first >>= next) before = (first before >>= fun reached => next reached.1 reached.2) := rfl

private theorem finish_close (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : Environment) :
    close (n := n) setup ownScalar (finish setup wire source packet) owner env =
      match owner.phase with
      | .initSent pending _ => match pending.aborted_state with
        | .fail error => pure ((.fail error, owner), env)
        | .div => pure ((.div, owner), env)
        | .ok _ => do
            let reached ← close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env
            close setup ownScalar (afterPrepared setup.source wire.frameWrite owner reached.1.1) reached.1.2 reached.2
      | _ => pure ((.ok none, owner), env) := by
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [close, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, StateT.run_pure, simulateQ_pure]
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [close, finish, StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_pure, simulateQ_pure]
      | ok aborted =>
          simp only [close, finish, RegistrationNativeSecretWordBeaconCompiler.finishPreparation,
            StateT.run_bind, StateT.run_get, pure_bind, ownerPhase, moved, StateT.run_modify, StateT.run_set,
            StateT.run_lift, bind_pure_comp, bind_map_left, simulateQ_bind, bind_assoc]
          apply bind_congr
          intro accepted
          cases accepted with
          | fail error | div => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
          | ok response => cases response with
            | Err _ => simp only [StateT.run_pure, simulateQ_pure, pure_bind, afterPrepared]
            | Ok authenticated =>
                simp only [phase, StateT.run_bind, StateT.run_lift, StateT.run_map, bind_pure_comp, bind_map_left, simulateQ_bind, simulateQ_map]

/-- The literal corrected selected/ordinary finish demands only its actual successful prepared reference, with terminal movement and assigned-ID opening preserved. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : Environment)
    (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (close setup ownScalar (finish setup wire source packet) owner env) before := by
  rw [finish_close]
  cases ownerPhase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ => exact pure_safe setup wire route sign input inside provider _ before valid
  | initSent pending oneTime =>
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [moved]
          exact pure_safe setup wire route sign input inside provider _ before valid
      | ok aborted =>
          simp only [moved]
          apply RegistrationNativeSecretWordLivePrefix.bind input (handlerChecked setup wire route sign input inside provider)
            _ _ before (RegistrationNativeSecretWordLiveBeaconSafety.preparation setup wire route sign input inside provider ownScalar source packet owner env before valid)
          rintro ⟨⟨⟨prepared, current⟩, currentEnv⟩, context⟩ supported
          have validAfter := (RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider
            (close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env)
            before valid _ supported).1
          apply after_safe setup wire route sign input inside provider ownScalar owner current currentEnv prepared context validAfter
          intro ready equal
          subst prepared
          exact RegistrationNativeSecretWordLiveBeaconPreparation.finish setup wire route sign input inside provider
            ownScalar source packet owner current ready env currentEnv before context supported
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBeacon

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBeacon.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordLiveBeacon.finish
