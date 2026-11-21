-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! Free realization of the actual ordinary callbacks preserves opaque Server references, dynamic Init publication and terminal-gated record behavior in the same platform state. These equations precede the checked interpreter and allow arbitrary stateful material replies in the enclosing client. Accept, build and finish are handled separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordMessage (zero)
open PqxdhRecordLiftInterface (RecordQuery)
variable {n : Nat} {I KemSK Platform E A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

open RegistrationNativePlatformSecretWordOrdinary (State M evaluate beacon platform record handler Ordinary)
private theorem local_embedding (candidate : PqxdhKemIndCca.MlKemSharedSecret) :
    RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate ∘ₛ
      (RegistrationNativePlatformPublicCoinEmbedding.embed ∘ₛ RegistrationNativePlatformPublicFrontend.embedLocal) =
      RegistrationNativePlatformSecretWordOwnerRealization.base candidate := by
  funext query
  cases query <;> simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.embedLocal,
    RegistrationNativePlatformPublicCoinEmbedding.embed, simulateQ_spec_query,
    RegistrationNativePlatformSecretWordOwnerRealization.base, RegistrationNativePlatformPublicFrontend.publicCoin]
  rfl

private theorem beacon_realized (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A)
    (before : State source Platform)
    (independent : simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base candidate)
        (((work.run before.1.beacons).run before.1.environment).run before.2) =
      simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
        (((work.run before.1.beacons).run before.1.environment).run before.2)) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon work)).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$> (beacon work).run before := by
  simp only [StateT.run] at independent
  simp only [RegistrationNativePlatformPublicFrontend.executeLocal, RegistrationNativePlatformPublicFrontend.beacon,
    beacon, evaluate, Prod.map_def, id_eq, RegistrationNativeSecretWordMessage.State.eval, StateT.run,
    simulateQ_map, ← QueryImpl.simulateQ_compose, local_embedding]
  rw [independent]
  simp only [Functor.map_map]
private theorem platform_realized (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (work : StateT Platform ProbComp A) (previous : Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed)
      ((RegistrationNativePlatformPublicFrontend.platformFull work).run previous) = (platform work).run previous := by
  simp only [RegistrationNativePlatformPublicFrontend.platformFull, platform, StateT.run,
    ← QueryImpl.simulateQ_compose]
  apply congrArg (fun handler => simulateQ handler (work.run previous))
  funext coin
  simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.publicCoin,
    simulateQ_spec_query, RegistrationNativePlatformPublicCoinEmbedding.embed]
  rfl

private theorem gate_realized (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : A → Nat) (output : Option A) (previous : Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed)
      ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => RegistrationNativePlatformPublicFrontend.platformFull (reserve amount)) size output).run previous) =
      (RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (reserve amount)) size output).run previous := by
  cases output with
  | none => rfl
  | some value =>
      simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run_bind, simulateQ_bind]
      rw [platform_realized]
      congr 1
      funext result
      cases result.1 <;> rfl

private theorem record_query_realized (candidate : PqxdhKemIndCca.MlKemSharedSecret) (query : RecordQuery) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed)
      (RegistrationNativePlatformPublicFrontend.old (.inr query)) = (Spec n KemSK).query (.inr query) := by
  simp only [QueryImpl.compose, RegistrationNativePlatformPublicFrontend.old, simulateQ_spec_query,
    RegistrationNativePlatformPublicCoinEmbedding.embed]
  rfl

private theorem record_realized (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery)
    (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate ∘ₛ
      RegistrationNativePlatformPublicCoinEmbedding.embed)
      ((RegistrationNativePlatformPublicFrontend.record reserve query).run (evaluate candidate before)) =
    Prod.map id (evaluate candidate) <$> (record reserve query).run before := by
  rcases query with (send | raw) | ⟨index, plaintext | raw⟩
  · simp only [RegistrationNativePlatformPublicFrontend.record, record, StateT.run, evaluate,
      Prod.map_def, id_eq, simulateQ_bind, record_query_realized, map_bind]
    apply bind_congr
    intro output
    have same := gate_realized (n := n) (KemSK := KemSK) candidate reserve
      (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) output before.2
    simp only [StateT.run] at same
    rw [same]
    simp only [simulateQ_pure, map_pure]
  · simp only [RegistrationNativePlatformPublicFrontend.record, record, StateT.run, evaluate,
      Prod.map_def, id_eq, simulateQ_map]
    rw [record_query_realized (n := n) (KemSK := KemSK) candidate (.inl (.inr raw))]
    simp only [Functor.map_map]
  · simp only [RegistrationNativePlatformPublicFrontend.record, record, StateT.run, evaluate,
      Prod.map_def, id_eq, RegistrationNativeSecretWordMessage.State.eval]
    cases found : before.1.beacons[index]? with
    | none => rfl
    | some owner =>
        simp only [simulateQ_bind, record_query_realized, map_bind]
        apply bind_congr
        intro output
        have same := gate_realized (n := n) (KemSK := KemSK) candidate reserve
          (fun value : RawCtxSourceSend.Encrypted => value.ciphertext.length) output before.2
        simp only [StateT.run] at same
        rw [same]
        simp only [simulateQ_pure, map_pure]
  · simp only [RegistrationNativePlatformPublicFrontend.record, record, StateT.run, evaluate,
      Prod.map_def, id_eq, RegistrationNativeSecretWordMessage.State.eval]
    cases found : before.1.beacons[index]? with
    | none => rfl
    | some owner =>
        simp only [simulateQ_map]
        rw [record_query_realized (n := n) (KemSK := KemSK) candidate (.inr (owner.view.worldOwner, .inr raw))]
        simp only [Functor.map_map]
private theorem execute_map (observe : A → B)
    (work : RegistrationNativePlatformPublicFrontend.LocalM n KemSK Platform source A)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    (RegistrationNativePlatformPublicFrontend.executeLocal (observe <$> work)).run before =
      Prod.map observe id <$> (RegistrationNativePlatformPublicFrontend.executeLocal work).run before := by
  change simulateQ RegistrationNativePlatformPublicFrontend.embedLocal ((observe <$> work).run before) =
    Prod.map observe id <$> simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (work.run before)
  simp only [StateT.run_map, simulateQ_map]
  rfl


/-- Actual source creation has its direct free realization, retaining all opaque source and platform state. -/
theorem create_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selected publicPrekey edPin mlPin keyId))).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      (beacon (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selected publicPrekey edPin mlPin keyId)).run before :=
  beacon_realized candidate _ before
    (RegistrationNativePlatformSecretWordOwnerRealization.create setup selected publicPrekey candidate edPin mlPin keyId _ _ _)

/-- Actual dynamic Init publication has its direct free realization, preserving failed writer results and full P. -/
theorem bundle_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
            (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index))).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      (beacon (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
        (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index)).run before :=
  beacon_realized candidate _ before
    (RegistrationNativePlatformSecretWordOwnerRealization.bundle setup selected publicPrekey candidate implementation index _ _ _)

/-- All four ordinary record routes retain their literal gate, advanced record effects and failed public replies before any checked material interpretation. -/
theorem record_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.record reserve query).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$> (record reserve query).run before := by
  simpa only [QueryImpl.simulateQ_compose] using record_realized candidate reserve query before

private theorem effect_source (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query))).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      ((StateT.lift (RegistrationNativeSecretWordFrontend.effect query) : M n KemSK source Platform _).run before) := by rfl

/-- Every literal current ordinary callback has its complete direct free source realization, without a known-material restriction. -/
theorem handler_source [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
    (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
    (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
    (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
    (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
    (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
    (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (query : TypedSpec.Domain) (ordinary : Ordinary query) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.realization (n := n) (KemSK := KemSK) candidate)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$> ((handler setup source selectedOwner publicPrekey reserveFrame implementation query).run before) := by
  cases query with
  | inl coin => exact effect_source candidate (.inl coin) before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_source setup source candidate selectedOwner publicPrekey edPin mlPin keyId before
    | bundle index =>
      simp only [RegistrationNativePlatformPublicFrontend.handler,handler,execute_map,StateT.run_map,simulateQ_map]
      rw [bundle_source setup source candidate selectedOwner publicPrekey implementation index before]
      simp only [Functor.map_map]
      rfl
    | accept packet => exact ordinary.elim
    | build handle application => exact ordinary.elim
    | finish index packet => exact ordinary.elim
    | hmac key bytes => rfl
    | hash bytes => exact effect_source candidate (.inr (.hash bytes)) before
    | serverSend keyId plaintext => exact record_source candidate reserveFrame (.inl (.inl (plaintext,keyId))) before
    | serverRaw raw => exact record_source candidate reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_source candidate reserveFrame (.inr (index,.inl plaintext)) before
    | beaconRaw index raw => exact record_source candidate reserveFrame (.inr (index,.inr raw)) before

end BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.bundle_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformLorIdealOrdinary.handler_source
