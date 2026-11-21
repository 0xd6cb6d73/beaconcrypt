-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconCaps
import BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconPreparation

/-! The complete selected and ordinary incoming controller is preparation-safe under its actual checked execution. Authentication and collection have the derived zero-demand footprint; a successful preparation supplies precisely the returned reference used by completion. The roster wrapper preserves that source equation for missing owners and all reached owner/environment states. No whole-frontend preparation certificate is a caller premise. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety
open PqxdhServerAuthExperiment (Setup)
open RegistrationNativeSecretWordMessage (Message)
open RegistrationNativeSecretWord (Key)
open RegistrationNativeSecretWordInterface (Spec LocalSpec)
open RegistrationNativeSecretWordInterpreter (State Provider)
open RegistrationNativeSecretWordInterpreterChecked (handlerChecked AllPrepared)
open RegistrationNativeSecretWordLiveFlags (Valid)
open RegistrationNativeSecretWordLiveCaps (Bad BadLocal)
open RegistrationNativeSecretWordLiveBeaconPreparation (routing)
open RegistrationServerReferenceCompiler (Environment)
open RegistrationBeaconReferenceCompiler (SelectedOwner)
variable {n : Nat} {ι KemSK Value Next : Type} {base : OracleSpec ι}

abbrev OwnerM (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) :=
  StateT (SelectedOwner source) (RegistrationNativeSecretWordBeaconCompiler.M n KemSK RegistrationServerRoleBackend.State)

def close (setup : Setup base KemSK) (ownScalar : Option PqxdhJointGapDh.ScalarBytes)
    {source : RegistrationNativeMldsa.Source} (work : OwnerM n KemSK source Value)
    (owner : SelectedOwner source) (env : Environment) : OracleComp (Spec n KemSK) ((Value × SelectedOwner source) × Environment) :=
  simulateQ (routing setup ownScalar) ((work.run owner).run env)

private theorem state_bind_apply {S A B : Type} {m : Type → Type} [Monad m]
    (first : StateT S m A) (next : A → StateT S m B) (before : S) :
    (first >>= next) before = (first before >>= fun reached => next reached.1 reached.2) := rfl

private theorem close_bind (setup : Setup base KemSK) (ownScalar : Option PqxdhJointGapDh.ScalarBytes)
    {source : RegistrationNativeMldsa.Source} (work : OwnerM n KemSK source Value)
    (next : Value → OwnerM n KemSK source Next) (owner : SelectedOwner source) (env : Environment) :
    close setup ownScalar (work >>= next) owner env =
      (close setup ownScalar work owner env >>= fun reached => close setup ownScalar (next reached.1.1) reached.1.2 reached.2) := by
  simp only [close, StateT.run, state_bind_apply, simulateQ_bind]

private theorem close_pure (setup : Setup base KemSK) (ownScalar : Option PqxdhJointGapDh.ScalarBytes)
    {source : RegistrationNativeMldsa.Source} (value : Value) (owner : SelectedOwner source) (env : Environment) :
    close (n := n) setup ownScalar (pure value) owner env = pure ((value, owner), env) := by
  simp only [close, StateT.run_pure, simulateQ_pure]

private theorem close_get (setup : Setup base KemSK) (ownScalar : Option PqxdhJointGapDh.ScalarBytes)
    {source : RegistrationNativeMldsa.Source} (owner : SelectedOwner source) (env : Environment) :
    close (n := n) setup ownScalar get owner env = pure ((owner, owner), env) := by
  simp only [close, StateT.run_get, StateT.run_pure, simulateQ_pure]

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

private theorem demand_imp (flags : Message → Bool) (query : (LocalSpec n KemSK).Domain)
    (bad : BadLocal (KemSK := KemSK) flags query) : RegistrationNativeSecretWordFrontendCapsLocal.IsDemand (KemSK := KemSK) query := by
  rcases query with message | (message | common) | kem
  · exact bad.elim
  · trivial
  · exact bad.elim
  · exact bad.elim

private theorem pure_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (value : Value) (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) (pure value) before :=
  RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid (by trivial)

/-- Actual mandatory response authentication and preparation are safe before any material request, for selected and supplied ordinary references. -/
theorem preparation (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : Environment)
    (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply routing_bound before.flags setup ownScalar
  exact IsQueryBoundP.of_imp (demand_imp before.flags)
    (RegistrationNativeSecretWordFrontendCapsBeacon.preparation_free setup source packet owner env)

private theorem abort_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) {source : RegistrationNativeMldsa.Source}
    (owner current : SelectedOwner source) (env : Environment) (value : Value)
    (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.abort owner *> pure value) current env) before := by
  apply RegistrationNativeSecretWordLiveCaps.of_bound setup wire route sign input inside provider _ before valid
  apply routing_bound before.flags setup ownScalar
  simp [RegistrationNativeSecretWordBeaconCompiler.abort, RegistrationNativeSecretWordInterface.effect,
    StateT.run_lift, StateT.run_pure, bind_pure_comp, BadLocal,
    isQueryBoundP_map_iff, isQueryBoundP_query_iff]

/-- The literal whole incoming controller derives its exact returned-name preparation receipt before each material demand, retaining every selected/ordinary terminal failure path. -/
theorem finish (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (ownScalar : Option PqxdhJointGapDh.ScalarBytes) (source : RegistrationNativeMldsa.Source)
    (packet : Option registration.ResponsePacket) (owner : SelectedOwner source) (env : Environment)
    (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finish setup source packet) owner env) before := by
  rw [RegistrationNativeSecretWordBeaconCompiler.finish, close_bind, close_get, pure_bind]
  simp only []
  cases phase : owner.phase with
  | fresh | freshWithCoins _ | established _ | aborted _ =>
      simp only [close_pure]
      exact pure_safe setup wire route sign input inside provider _ before valid
  | initSent pending oneTime =>
      simp only []
      cases moved : pending.aborted_state with
      | fail error | div =>
          simp only [close_pure]
          exact pure_safe setup wire route sign input inside provider _ before valid
      | ok aborted =>
          simp only []
          rw [close_bind]
          apply RegistrationNativeSecretWordLivePrefix.bind input
            (handlerChecked setup wire route sign input inside provider) _ _ before
            (preparation setup wire route sign input inside provider ownScalar source packet owner env before valid)
          rintro ⟨⟨⟨prepared, current⟩, currentEnv⟩, context⟩ supported
          have validAfter := (RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider
            (close setup ownScalar (RegistrationNativeSecretWordBeaconCompiler.finishPreparation setup source packet) owner env)
            before valid _ supported).1
          cases prepared with
          | fail error => exact abort_safe setup wire route sign input inside provider ownScalar owner current currentEnv (RustM.fail error : RustM (Option Pqxdh.Bytes)) context validAfter
          | div => exact abort_safe setup wire route sign input inside provider ownScalar owner current currentEnv (RustM.div : RustM (Option Pqxdh.Bytes)) context validAfter
          | ok reply => cases reply with
            | none => exact abort_safe setup wire route sign input inside provider ownScalar owner current currentEnv (RustM.ok (none : Option Pqxdh.Bytes)) context validAfter
            | some ready =>
                have receipt := RegistrationNativeSecretWordLiveBeaconPreparation.finish setup wire route sign input inside provider
                  ownScalar source packet owner current ready env currentEnv before context supported
                have completed := RegistrationNativeSecretWordLiveBeaconCaps.complete setup wire route sign input inside provider
                  ownScalar owner current ready currentEnv context validAfter receipt
                cases ownScalar <;>
                  simpa only [close, routing, QueryImpl.simulateQ_compose] using completed

private theorem map_safe (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (work : OracleComp (Spec n KemSK) Value) (map : Value → Next) (before : State n KemSK) (valid : Valid input before)
    (safe : AllPrepared input (handlerChecked setup wire route sign input inside provider) work before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider) (map <$> work) before := by
  rw [map_eq_bind_pure_comp]
  apply RegistrationNativeSecretWordLivePrefix.bind input _ work _ before safe
  intro reached supported
  exact pure_safe setup wire route sign input inside provider _ reached.2
    (RegistrationNativeSecretWordLiveFlags.program_receipts setup wire route sign input inside provider work before valid reached supported).1

/-- The actual mixed owner roster retains preparation safety for missing, selected and ordinary owners without identifying local indices with opaque handles. -/
theorem owners (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (input : Message → Option Key) (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (provider : Provider KemSK)
    (source : RegistrationNativeMldsa.Source) (index : Nat) (packet : Option registration.ResponsePacket)
    (roster : RegistrationNativePublicOwners.State source) (env : Environment)
    (before : State n KemSK) (valid : Valid input before) :
    AllPrepared input (handlerChecked setup wire route sign input inside provider)
      (simulateQ (RegistrationNativeSecretWordInterface.liftLocal false)
        (((RegistrationNativeSecretWordOwners.finish setup source index packet).run roster).run env)) before := by
  cases found : roster[index]? with
  | none =>
      rw [RegistrationNativeSecretWordOwners.finish_missing setup source index packet roster env found, simulateQ_pure]
      exact pure_safe setup wire route sign input inside provider _ before valid
  | some owner =>
      have safe := finish setup wire route sign input inside provider owner.scalar source packet owner.view env before valid
      have mapped := map_safe setup wire route sign input inside provider _
        (fun result => ((result.1.1, roster.set index { owner with view := result.1.2 }), result.2)) before valid safe
      cases scalar : owner.scalar <;>
        simpa only [RegistrationNativeSecretWordOwners.finish, StateT.run, found, scalar,
          close, routing, simulateQ_map, QueryImpl.simulateQ_compose] using mapped

end BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.preparation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.preparation
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.finish
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.owners' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeSecretWordLiveBeaconSafety.owners
