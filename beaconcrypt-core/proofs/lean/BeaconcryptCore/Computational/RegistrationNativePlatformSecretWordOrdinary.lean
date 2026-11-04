-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOwnerRealization
import BeaconcryptCore.Computational.RegistrationNativePlatformPublicCoinEmbedding
/-! Candidate-independent Word callbacks retain the original opaque Server references and run actual create, dynamic Init publication and terminal-gated records in one common platform state. The three material callbacks are supplied by the complete Word frontend separately. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeSecretWordInterface (Spec)
open RegistrationNativeSecretWordMessage (zero)
open PqxdhRecordLiftInterface (RecordQuery)
variable {n : Nat} {I KemSK Platform E A B : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}

abbrev State (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  RegistrationNativeSecretWordMessage.State source × Platform
abbrev M (n : Nat) (KemSK : Type) (source : RegistrationNativeMldsa.Source) (Platform : Type) :=
  StateT (State source Platform) (OracleComp (Spec n KemSK))

def evaluate (candidate : PqxdhKemIndCca.MlKemSharedSecret) : State source Platform → RegistrationNativePlatformPublicFrontend.State source Platform :=
  Prod.map (RegistrationNativeSecretWordMessage.State.eval candidate) id

def beacon (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
    (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A) : M n KemSK source Platform A := fun before =>
  (fun result => (result.1.1.1, ({ before.1 with beacons := result.1.1.2, environment := result.1.2 }, result.2))) <$>
    simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
      (((work.run before.1.beacons).run before.1.environment).run before.2)

def platform (work : StateT Platform ProbComp A) : StateT Platform (OracleComp (Spec n KemSK)) A :=
  fun previous => simulateQ (fun coin => RegistrationNativeSecretWordFrontend.effect (.inl coin)) (work.run previous)

noncomputable def record (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery) :
    M n KemSK source Platform ((PqxdhRecordLiftInterface.RecordSpec .O).Range query) := fun before =>
  match query with
  | .inl (.inl send) => do
      let result ← (Spec n KemSK).query (.inr (.inl (.inl send)))
      let result ← (RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (reserve amount))
        (fun value => value.ciphertext.length) result).run before.2
      pure (result.1, (before.1, result.2))
  | .inl (.inr raw) => (fun result => (result, before)) <$> (Spec n KemSK).query (.inr (.inl (.inr raw)))
  | .inr (index, .inl plaintext) => match before.1.beacons[index]? with
      | none => pure (none, before)
      | some owner => do
        let result ← (Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inl plaintext)))
        let result ← (RegistrationNativePlatformOrdinaryGate.gate (fun amount => platform (reserve amount))
          (fun value => value.ciphertext.length) result).run before.2
        pure (result.1, (before.1, result.2))
  | .inr (index, .inr raw) => match before.1.beacons[index]? with
      | none => pure (.None, before)
      | some owner => (fun result => (result, before)) <$>
          (Spec n KemSK).query (.inr (.inr (owner.view.worldOwner, .inr raw)))

def Ordinary : TypedSpec.Domain → Prop
  | .inr (.accept _) | .inr (.build _ _) | .inr (.finish _ _) => False
  | _ => True

noncomputable def handler (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (selectedOwner : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp)) :
    QueryImpl TypedSpec (M n KemSK source Platform)
  | .inl coin => StateT.lift (RegistrationNativeSecretWordFrontend.effect (.inl coin))
  | .inr (.create edPin mlPin keyId) => beacon
      (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selectedOwner publicPrekey edPin mlPin keyId)
  | .inr (.bundle index) => RegistrationNativePlatformPublicFrontend.bundleBytes <$>
      beacon (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
        (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selectedOwner publicPrekey index)
  | .inr (.accept _) => pure (.ok none)
  | .inr (.build _ _) => pure (.ok none)
  | .inr (.finish _ _) => pure (.ok none)
  | .inr (.hmac key bytes) => pure (setup.hmac.eval key bytes)
  | .inr (.hash bytes) => StateT.lift (RegistrationNativeSecretWordFrontend.effect (.inr (.hash bytes)))
  | .inr (.serverSend keyId plaintext) => record reserveFrame (.inl (.inl (plaintext, keyId)))
  | .inr (.serverRaw raw) => record reserveFrame (.inl (.inr raw))
  | .inr (.beaconSend index plaintext) => record reserveFrame (.inr (index, .inl plaintext))
  | .inr (.beaconRaw index raw) => record reserveFrame (.inr (index, .inr raw))

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
private theorem beacon_checked (setup : Setup base KemSK)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (work : RegistrationNativePlatformPublicOwners.M source RegistrationServerRoleBackend.State
      (RegistrationNativePlatformPublicFrontend.Base n KemSK Platform) A) (before : State source Platform)
    (independent : simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base candidate)
        (((work.run before.1.beacons).run before.1.environment).run before.2) =
      simulateQ (RegistrationNativePlatformSecretWordOwnerRealization.base zero)
        (((work.run before.1.beacons).run before.1.environment).run before.2)) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon work)).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input) ((beacon work).run before) := by
  have same := congrArg
    (simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input))
    (beacon_realized candidate work before independent)
  simpa only [RegistrationNativeSecretWordCheckedFrontend.native, QueryImpl.simulateQ_compose, simulateQ_map] using same

/-- Creation retains the whole common platform poststate and symbolic session table. -/
theorem create_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (edPin : Std.Array U8 32#usize) (mlPin : Std.Array U8 1952#usize) (keyId : U64) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selected publicPrekey edPin mlPin keyId))).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input)
        ((beacon (RegistrationNativePlatformPublicOwners.create RegistrationNativePlatformPublicFrontend.trusted setup source selected publicPrekey edPin mlPin keyId)).run before) :=
  beacon_checked setup inside candidate input _ before
    (RegistrationNativePlatformSecretWordOwnerRealization.create setup selected publicPrekey candidate edPin mlPin keyId _ _ _)

/-- Dynamic Init serialization retains every failure and the same reached platform state. -/
theorem bundle_source (setup : Setup base KemSK) (source : RegistrationNativeMldsa.Source)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (selected : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
    (implementation : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (index : Nat) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal (RegistrationNativePlatformPublicFrontend.beacon
          (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
            (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index))).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input)
        ((beacon (RegistrationNativePlatformPublicOwners.bundle RegistrationNativePlatformPublicFrontend.trusted
          (RegistrationNativePlatformPublicFrontend.writer implementation) setup source selected publicPrekey index)).run before) :=
  beacon_checked setup inside candidate input _ before
    (RegistrationNativePlatformSecretWordOwnerRealization.bundle setup selected publicPrekey candidate implementation index _ _ _)
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
/-- All ongoing record routes retain advanced sends and failed public writer results. -/
theorem record_source (setup : Setup base KemSK)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (query : RecordQuery)
    (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.record reserve query).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input)
          ((record reserve query).run before) := by
  have same := congrArg
    (simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input))
    (record_realized candidate reserve query before)
  simpa only [RegistrationNativeSecretWordCheckedFrontend.native, QueryImpl.simulateQ_compose, simulateQ_map] using same

private theorem effect_source (setup : Setup base KemSK)
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.executeLocal
          (StateT.lift (RegistrationNativePlatformPublicFrontend.effect query))).run (evaluate candidate before))) =
      Prod.map id (evaluate candidate) <$>
        simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input)
          ((StateT.lift (RegistrationNativeSecretWordFrontend.effect query) : M n KemSK source Platform _).run before) := by
  rfl
private theorem execute_map (observe : A → B)
    (work : RegistrationNativePlatformPublicFrontend.LocalM n KemSK Platform source A)
    (before : RegistrationNativePlatformPublicFrontend.State source Platform) :
    (RegistrationNativePlatformPublicFrontend.executeLocal (observe <$> work)).run before =
      Prod.map observe id <$> (RegistrationNativePlatformPublicFrontend.executeLocal work).run before := by
  change simulateQ RegistrationNativePlatformPublicFrontend.embedLocal ((observe <$> work).run before) =
    Prod.map observe id <$> simulateQ RegistrationNativePlatformPublicFrontend.embedLocal (work.run before)
  simp only [StateT.run_map, simulateQ_map]
  rfl

/-- The complete ordinary callback switch follows the actual corrected frontend, with only accept, build and finish delegated separately. -/
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
    (inside : RegistrationNativeSuffixKeyPrf.Prefix → Bool) (candidate : PqxdhKemIndCca.MlKemSharedSecret)
    (input : RegistrationNativeSecretWordMessage.Message → Option RegistrationNativeSecretWord.Key)
    (query : TypedSpec.Domain) (ordinary : Ordinary query) (before : State source Platform) :
    simulateQ (RegistrationNativeSecretWordCheckedFrontend.native (n := n) (KemSK := KemSK) setup.source inside candidate input)
      (simulateQ RegistrationNativePlatformPublicCoinEmbedding.embed
        ((RegistrationNativePlatformPublicFrontend.handler setup checks wire source sign selectedOwner selectedAccept publicPrekey
          view failure allocation reserveRegistration reservePeer reserveFrame erased helper implementation query).run (evaluate candidate before))) =
    Prod.map id (evaluate candidate) <$>
      simulateQ (RegistrationNativeSecretWordCheckedFrontend.implementation (n := n) (KemSK := KemSK) setup.source inside candidate input)
        ((handler setup source selectedOwner publicPrekey reserveFrame implementation query).run before) := by
  cases query with
  | inl coin => exact effect_source setup inside candidate input (.inl coin) before
  | inr query => cases query with
    | create edPin mlPin keyId => exact create_source setup source inside candidate input selectedOwner publicPrekey edPin mlPin keyId before
    | bundle index =>
        simp only [RegistrationNativePlatformPublicFrontend.handler, handler, execute_map,
          StateT.run_map, simulateQ_map]
        rw [bundle_source setup source inside candidate input selectedOwner publicPrekey implementation index before]
        simp only [Functor.map_map]
        rfl
    | accept packet => exact ordinary.elim
    | build handle application => exact ordinary.elim
    | finish index packet => exact ordinary.elim
    | hmac key bytes => rfl
    | hash bytes => exact effect_source setup inside candidate input (.inr (.hash bytes)) before
    | serverSend keyId plaintext => exact record_source setup inside candidate input reserveFrame (.inl (.inl (plaintext, keyId))) before
    | serverRaw raw => exact record_source setup inside candidate input reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_source setup inside candidate input reserveFrame (.inr (index, .inl plaintext)) before
    | beaconRaw index raw => exact record_source setup inside candidate input reserveFrame (.inr (index, .inr raw)) before
end BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.create_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.create_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.bundle_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.bundle_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.record_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.record_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.handler_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformSecretWordOrdinary.handler_source
