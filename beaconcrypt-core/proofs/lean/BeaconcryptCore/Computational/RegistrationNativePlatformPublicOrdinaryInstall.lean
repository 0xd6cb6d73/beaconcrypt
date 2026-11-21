-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicInstallLocal
/-! Every actual public callback other than build and finish has zero Server and Beacon installation requests. This is a source-syntax property including external allocation coins and failed publication paths, not an old callback equality or a safety assumption. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall
open PqxdhServerAuthExperiment (Setup Checks)
open PqxdhRecordLiftInterface (Role)
open RegistrationNativePlatformPublicFrontend
variable {n : Nat} {E Platform ι KemSK Value : Type} {base : OracleSpec ι}
def Install (role : Role) : (Spec n KemSK).Domain → Prop
  | .inl query => RegistrationNativePairedSafe.GlobalInstall (KemSK := KemSK) role query
  | .inr _ => False
instance (role : Role) : DecidablePred (Install (n := n) (KemSK := KemSK) role) := fun query => by
  cases query <;> dsimp [Install] <;> infer_instance
private theorem map_apply {S A B : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (change : A → B) (work : StateT S m A) (before : S) :
    (change <$> work) before = Prod.map change id <$> work before := StateT.run_map change work before
private theorem embed_bound (role : Role) (work : OracleComp (LocalSpec n KemSK) Value) (count : Nat)
    (bounded : work.IsQueryBoundP (RegistrationNativePlatformPublicInstallLocal.LocalInstall (KemSK := KemSK) role) count) :
    (simulateQ embedLocal work).IsQueryBoundP (Install (KemSK := KemSK) role) count := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ work count bounded
  intro query
  cases query with
  | inl query =>
    simp only [embedLocal, isQueryBoundP_query_iff, Install, RegistrationNativePlatformPublicInstallLocal.LocalInstall]
    intro installed
    simp only [installed, ite_true]
    decide
  | inr coin => simp [embedLocal, publicCoin, Install, RegistrationNativePlatformPublicInstallLocal.LocalInstall, isQueryBoundP_query_iff]
private theorem coins_free (role : Role) (work : ProbComp Value) :
    (simulateQ (publicCoin (n := n) (KemSK := KemSK)) work).IsQueryBoundP (Install (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ (fun _ => False) _ _ 0 (isQueryBoundP_false _ 0)
  intro coin
  simp [publicCoin, Install, isQueryBoundP_query_iff]

private theorem gate_free {A : Type} (role : Role) (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).IsQueryBoundP
      (Install (KemSK := KemSK) role) 0 := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply isQueryBoundP_bind (n := 0) (m := 0) (coins_free role _)
    rintro ⟨result, after⟩ _
    cases result <;> trivial

private theorem effect_free {source : RegistrationNativeMldsa.Source}
    (role : Role) (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (free : ∀ actual, ¬ RegistrationNativeSecretWordAtomInstallCaps.InstallEnv actual query) (before : State source Platform) :
    ((executeLocal (StateT.lift (effect (KemSK := KemSK) query))).run before).IsQueryBoundP
      (Install (KemSK := KemSK) role) 0 := by
  change (simulateQ embedLocal ((StateT.lift (effect query) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP _ 0
  simp only [StateT.run_lift, bind_pure_comp, simulateQ_map, isQueryBoundP_map_iff]
  simp [effect, localQuery, embedLocal, Install,
    RegistrationNativePairedSafe.GlobalInstall, RegistrationNativeSecretWordAtomInstallCaps.Install, isQueryBoundP_query_iff]
  exact free role

private theorem record_free {source : RegistrationNativeMldsa.Source} (role : Role)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).IsQueryBoundP (Install (KemSK := KemSK) role) 0 := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run, old]
    rw [isQueryBoundP_query_bind_iff]
    refine ⟨by simp [Install, RegistrationNativePairedSafe.GlobalInstall], ?_⟩
    intro output
    simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, Install, RegistrationNativePairedSafe.GlobalInstall, ite_false] using gate_free role reserve _ output before.2
  · simp [record, StateT.run, old, isQueryBoundP_map_iff,
      Install, RegistrationNativePairedSafe.GlobalInstall, isQueryBoundP_query_iff]
  · simp only [record, StateT.run]
    split
    · trivial
    · simp only [old]
      rw [isQueryBoundP_query_bind_iff]
      refine ⟨by simp [Install, RegistrationNativePairedSafe.GlobalInstall], ?_⟩
      intro output
      simpa only [StateT.run, bind_pure_comp, isQueryBoundP_map_iff, Install, RegistrationNativePairedSafe.GlobalInstall, ite_false] using gate_free role reserve _ output before.2
  · simp only [record, StateT.run]
    split
    · trivial
    · simp [old, isQueryBoundP_map_iff, Install, RegistrationNativePairedSafe.GlobalInstall, isQueryBoundP_query_iff]


variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))


attribute [local irreducible] RegistrationNativePlatformServerOpenControl.accept

private theorem handler_zero (role : Role) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial query) (before : State source Platform) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper implementation query).run before).IsQueryBoundP
      (Install (KemSK := KemSK) role) 0 := by
  cases query with
  | inl coin => exact effect_free role (.inl coin) (by intro actual; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]) before
  | inr query => cases query with
    | create edPin mlPin keyId =>
      apply embed_bound role
      simp only [beacon, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicInstallLocal.create_zero role setup source selectedOwner publicPrekey edPin mlPin keyId _ _ _
    | bundle index =>
      change (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)).IsQueryBoundP _ 0
      apply embed_bound role
      simp only [beacon, StateT.run, map_apply, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicInstallLocal.bundle_zero role setup source implementation selectedOwner publicPrekey index _ _ _
    | accept packet =>
      change (simulateQ embedLocal ((do
        let previous ← get
        modify fun current => ({current.1 with parsedAccepts := current.1.parsedAccepts + 1}, current.2)
        serverOpen (RegistrationNativePlatformServerOpenControl.accept
          (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) (decide (previous.1.parsedAccepts = selectedAccept)))
          (platform reserveRegistration) setup checks source.verify packet) : LocalM n KemSK Platform source _).run before)).IsQueryBoundP _ 0
      apply embed_bound role
      simp only [StateT.run_bind, StateT.run_get, StateT.run_modify, pure_bind]
      simp only [serverOpen, StateT.run, isQueryBoundP_map_iff]
      exact RegistrationNativePlatformPublicInstallLocal.accept_zero role (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet before.1.server before.1.environment before.2
    | build handle application => exact (ordinary trivial).elim
    | finish index packet => exact (ordinary trivial).elim
    | hmac key bytes => trivial
    | hash bytes => exact effect_free role (.inr (.hash bytes)) (by intro actual; simp [RegistrationNativeSecretWordAtomInstallCaps.InstallEnv]) before
    | serverSend keyId plaintext => exact record_free role reserveFrame (.inl (.inl (plaintext,keyId))) before
    | serverRaw raw => exact record_free role reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free role reserveFrame (.inr (index,.inl plaintext)) before
    | beaconRaw index raw => exact record_free role reserveFrame (.inr (index,.inr raw)) before

/-- Every literal non-build/finish callback has zero installation bill after the exact external-coin embedding. -/
theorem handler_free (role : Role) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial query) (before : State source Platform) :
    (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)).IsQueryBoundP
      (RegistrationNativePairedSafe.GlobalInstall (KemSK := KemSK) role) 0 := by
  apply RawCtxSourceOpen.simulate_bound _ _ _ _ 0
    (handler_zero setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation role query ordinary before)
  intro request
  cases request with
  | inl request =>
    simp only [RegistrationNativePlatformPublicCoinEmbedding.embed, isQueryBoundP_query_iff, Install]
    intro installed
    simp only [installed, ite_true]
    decide
  | inr coin =>
    simp [RegistrationNativePlatformPublicCoinEmbedding.embed, RegistrationNativePublicFrontend.effect,
      RegistrationNativePublicFrontend.liftLocal, Install, RegistrationNativePairedSafe.GlobalInstall,
      RegistrationNativeSecretWordAtomInstallCaps.Install, RegistrationNativeSecretWordAtomInstallCaps.InstallEnv, isQueryBoundP_query_iff]

/-- Ordinary corrected callbacks preserve the actual paired monitor for arbitrary source/private state and all failure replies. -/
theorem handler_safe (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (ordinary : ¬ RegistrationNativePublicCaps.IsMaterial query) (before : State source Platform) :
    RegistrationNativePairedTrace.Safe (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
      ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper implementation query).run before)) := by
  exact RegistrationNativePairedSafe.free _ (fun role => handler_free setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation role query ordinary before)
end BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall.handler_free' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall.handler_free

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall.handler_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformPublicOrdinaryInstall.handler_safe
