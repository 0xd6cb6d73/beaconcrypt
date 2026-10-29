-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationAuthenticationShared

/-!
The final two phases of the actual extracted Init authentication executor hash the complete retained ML keys into the shared record/authentication cache. Their accepted registration binding carries those exact fingerprints in its populated associated data. The input capability is an actual source phase; no independent initializer or desired simulation is assumed.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core PqxdhRefinement

set_option autoImplicit false

namespace BeaconcryptCore.Computational.RegistrationFingerprintExecutor

open CtxRomAuth
open BeaconcryptCore.Refinement.RegistrationInbound
open BeaconcryptCore.Refinement.SessionBinding
open RegistrationAuthenticationExecutor
open BeaconcryptCore.Refinement.RegistrationAuthenticationFlow (Event)

noncomputable def beaconPhase (before : registration.InitServerFingerprint)
    (fingerprint : Std.Array Std.U8 64#usize) : registration.InitBeaconFingerprint :=
  Classical.choose (init_server_fingerprint_exact before fingerprint)

theorem beacon_phase_exact (before : registration.InitServerFingerprint)
    (fingerprint : Std.Array Std.U8 64#usize) :
    before.resume (.Some fingerprint) = .ok (.BeaconFingerprintRequested (beaconPhase before fingerprint)) ∧
      (beaconPhase before fingerprint).state = before.state ∧
      (beaconPhase before fingerprint).registration = before.registration ∧
      (beaconPhase before fingerprint).server_pin.binding = before.state.server_pin.binding ∧
      (beaconPhase before fingerprint).server_pin.public_key = before.state.server_pin.public_key ∧
      (beaconPhase before fingerprint).server_pin.fingerprint = fingerprint :=
  Classical.choose_spec (init_server_fingerprint_exact before fingerprint)

noncomputable def accepted (before : registration.InitServerFingerprint)
    (serverFingerprint beaconFingerprint : Std.Array Std.U8 64#usize) : registration.AuthenticatedInit :=
  Classical.choose (init_beacon_fingerprint_exact (beaconPhase before serverFingerprint) beaconFingerprint)

theorem accepted_exact (before : registration.InitServerFingerprint)
    (serverFingerprint beaconFingerprint : Std.Array Std.U8 64#usize) :
    (beaconPhase before serverFingerprint).resume (.Some beaconFingerprint) =
      .ok (.Accepted (accepted before serverFingerprint beaconFingerprint)) ∧
      (accepted before serverFingerprint beaconFingerprint).registration = before.registration ∧
      (accepted before serverFingerprint beaconFingerprint).binding.server_pin.binding =
        before.state.server_pin.binding ∧
      (accepted before serverFingerprint beaconFingerprint).binding.server_pin.public_key =
        before.state.server_pin.public_key ∧
      (accepted before serverFingerprint beaconFingerprint).binding.server_pin.fingerprint = serverFingerprint ∧
      (accepted before serverFingerprint beaconFingerprint).binding.init_hash = before.state.init_hash ∧
      (accepted before serverFingerprint beaconFingerprint).binding.beacon_identity_public_key =
        before.registration.beacon_identity_public_key ∧
      (accepted before serverFingerprint beaconFingerprint).binding.beacon_fingerprint = beaconFingerprint ∧
      registrationConsistent (accepted before serverFingerprint beaconFingerprint).binding := by
  have server := beacon_phase_exact before serverFingerprint
  have beacon := Classical.choose_spec
    (init_beacon_fingerprint_exact (beaconPhase before serverFingerprint) beaconFingerprint)
  change (beaconPhase before serverFingerprint).resume (.Some beaconFingerprint) =
    .ok (.Accepted (accepted before serverFingerprint beaconFingerprint)) ∧ _ at beacon
  exact ⟨beacon.1, beacon.2.1.trans server.2.2.1,
    (congrArg (fun pin => pin.binding) beacon.2.2.1).trans server.2.2.2.1,
    (congrArg (fun pin => pin.public_key) beacon.2.2.1).trans server.2.2.2.2.1,
    (congrArg (fun pin => pin.fingerprint) beacon.2.2.1).trans server.2.2.2.2.2,
    beacon.2.2.2.1.trans (congrArg (fun state => state.init_hash) server.2.1),
    beacon.2.2.2.2.1.trans (congrArg (fun value => value.beacon_identity_public_key) server.2.2.1),
    beacon.2.2.2.2.2.1, beacon.2.2.2.2.2.2⟩

theorem execute_accepted (fuel : Nat) (value : registration.AuthenticatedInit) :
    execute fuel (.Accepted value) = pure (.ok ([], .Accepted value)) := by
  cases fuel <;> simp only [execute, step, continueWith, pure_bind]

/-- The actual executor's complete fingerprint suffix uses two actual shared-RO queries and returns the source-derived binding. -/
theorem execute_fingerprints {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (fuel : Nat) (before : registration.InitServerFingerprint)
    (state : RawCtxSharedPrimitive.SharedState Auxiliary) :
    (simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
      (execute (fuel + 2) (.ServerFingerprintRequested before))).run state = (do
        let server ← (ctxRandomOracle ((), absBytes before.state.server_pin.public_key)).run state.2
        let beacon ← (ctxRandomOracle ((), absBytes before.state.packet.mldsa_public_key)).run server.2
        let serverDigest := RegistrationAuthenticationShared.digestArray server.1
        let beaconDigest := RegistrationAuthenticationShared.digestArray beacon.1
        pure (.ok ([Event.serverFingerprint (.Some serverDigest), Event.beaconFingerprint (.Some beaconDigest)],
          .Accepted (accepted before serverDigest beaconDigest)), (state.1, beacon.2))) := by
  obtain ⟨request, _, requested, _, bytes, _⟩ := fingerprint_requests_exact before
    (beaconPhase before (RegistrationAuthenticationShared.digestArray (List.Vector.replicate 64 0)))
  simp only [execute, step, continueWith, requested, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind]
  simp only [simulateQ_pure, StateT.run_pure, bind_assoc, pure_bind]
  rw [RegistrationAuthenticationShared.hash_exact, bind_map_left, bytes]
  refine bind_congr (fun ⟨serverDigest, serverCache⟩ => ?_)
  simp only [(beacon_phase_exact before (RegistrationAuthenticationShared.digestArray serverDigest)).1,
    edge, simulateQ_bind, StateT.run_bind]
  obtain ⟨_, beaconRequest, _, beaconRequested, _, beaconBytes⟩ := fingerprint_requests_exact before
    (beaconPhase before (RegistrationAuthenticationShared.digestArray serverDigest))
  rw [(beacon_phase_exact before (RegistrationAuthenticationShared.digestArray serverDigest)).2.1]
    at beaconBytes
  simp only [beaconRequested, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure, bind_assoc, pure_bind]
  rw [RegistrationAuthenticationShared.hash_exact, bind_map_left, beaconBytes]
  refine bind_congr (fun ⟨beaconDigest, beaconCache⟩ => ?_)
  simp only [(accepted_exact before (RegistrationAuthenticationShared.digestArray serverDigest)
    (RegistrationAuthenticationShared.digestArray beaconDigest)).1, execute_accepted,
    simulateQ_pure, StateT.run_pure, pure_bind]

/-- Both fingerprint slots are readbacks of actual hash queries, together with the source binding's populated AD law. -/
def BindingCached (binding : session.RegistrationBinding) (beaconKey : Pqxdh.Bytes)
    (cache : CtxRO.QueryCache) : Prop :=
  registrationConsistent binding ∧ ∃ serverDigest beaconDigest,
    cache ((), absBytes binding.server_pin.public_key) = some serverDigest ∧
    cache ((), beaconKey) = some beaconDigest ∧
    absBytes binding.server_pin.fingerprint = serverDigest.toList ∧
    absBytes binding.beacon_fingerprint = beaconDigest.toList

theorem binding_cached_mono (binding : session.RegistrationBinding) (beaconKey : Pqxdh.Bytes)
    {before after : CtxRO.QueryCache} (extension : before ≤ after)
    (cached : BindingCached binding beaconKey before) : BindingCached binding beaconKey after := by
  obtain ⟨consistent, serverDigest, beaconDigest, serverCached, beaconCached, serverBytes, beaconBytes⟩ := cached
  exact ⟨consistent, serverDigest, beaconDigest, extension serverCached, extension beaconCached,
    serverBytes, beaconBytes⟩

/-- Every supported suffix output has source-owned metadata and both real shared-cache fingerprint receipts. -/
theorem fingerprint_receipts {Auxiliary : Type} (crypto : Pqxdh.Crypto) (verify : MldsaTranscriptAuth.Verify)
    (writer : RawCtxMixedShared.Writer)
    (kdf : QueryImpl RawCtxSharedPrimitive.KdfSpec
      (StateT (RawCtxSharedPrimitive.SharedState Auxiliary) ProbComp))
    (fuel : Nat) (before : registration.InitServerFingerprint)
    (state after : RawCtxSharedPrimitive.SharedState Auxiliary) (events : List Event)
    (authenticated : registration.AuthenticatedInit)
    (supported : (.ok (events, .Accepted authenticated), after) ∈ support
      ((simulateQ (RegistrationAuthenticationShared.implementation crypto verify writer kdf)
        (execute (fuel + 2) (.ServerFingerprintRequested before))).run state)) :
    authenticated.registration = before.registration ∧
      authenticated.binding.server_pin.binding = before.state.server_pin.binding ∧
      authenticated.binding.server_pin.public_key = before.state.server_pin.public_key ∧
      authenticated.binding.init_hash = before.state.init_hash ∧
      authenticated.binding.beacon_identity_public_key = before.registration.beacon_identity_public_key ∧
      BindingCached authenticated.binding (absBytes before.state.packet.mldsa_public_key) after.2 ∧
      after.1 = state.1 ∧ state.2 ≤ after.2 := by
  rw [execute_fingerprints, mem_support_bind_iff] at supported
  obtain ⟨⟨serverDigest, serverCache⟩, serverQueried, rest⟩ := supported
  rw [mem_support_bind_iff] at rest
  obtain ⟨⟨beaconDigest, beaconCache⟩, beaconQueried, returned⟩ := rest
  simp only [support_pure, Set.mem_singleton_iff] at returned
  have resultSame := congrArg Prod.fst returned
  have afterSame : after = (state.1, beaconCache) := congrArg Prod.snd returned
  simp only [RustM.ok.injEq, Prod.mk.injEq, registration.InitAuthentication.Accepted.injEq] at resultSame
  obtain ⟨_, authenticatedSame⟩ := resultSame
  rw [authenticatedSame, afterSame]
  have source := accepted_exact before (RegistrationAuthenticationShared.digestArray serverDigest)
    (RegistrationAuthenticationShared.digestArray beaconDigest)
  have serverCached := MldsaSharedAuthentication.query_cached (absBytes before.state.server_pin.public_key)
    state.2 (serverDigest, serverCache) serverQueried
  have beaconCached := MldsaSharedAuthentication.query_cached (absBytes before.state.packet.mldsa_public_key)
    serverCache (beaconDigest, beaconCache) beaconQueried
  refine ⟨source.2.1, source.2.2.1, source.2.2.2.1, source.2.2.2.2.2.1,
    source.2.2.2.2.2.2.1, ?_, rfl, serverCached.1.trans beaconCached.1⟩
  exact ⟨source.2.2.2.2.2.2.2.2, serverDigest, beaconDigest,
      by rw [source.2.2.2.1]; exact beaconCached.1 serverCached.2,
      beaconCached.2,
      by rw [source.2.2.2.2.1, RegistrationAuthenticationShared.digest_array_bytes],
      by rw [source.2.2.2.2.2.2.2.1, RegistrationAuthenticationShared.digest_array_bytes]⟩

/-- The associated data supplied to records contains the actual shared-cache fingerprints of both retained ML keys. -/
theorem binding_associated_data (binding : session.RegistrationBinding) (beaconKey : Pqxdh.Bytes)
    (cache : CtxRO.QueryCache) (cached : BindingCached binding beaconKey cache) :
    absBytes binding.associated_data = boundAssociatedData
      (absBytes binding.server_pin.binding.identity_public_key) (absBytes binding.beacon_identity_public_key)
      (MldsaSharedAuthentication.cacheHash cache (absBytes binding.server_pin.public_key))
      (MldsaSharedAuthentication.cacheHash cache beaconKey) := by
  obtain ⟨consistent, serverDigest, beaconDigest, serverCached, beaconCached, serverBytes, beaconBytes⟩ := cached
  rw [MldsaSharedAuthentication.cache_hash_reconstruct cache _ serverDigest serverCached,
    MldsaSharedAuthentication.cache_hash_reconstruct cache _ beaconDigest beaconCached,
    ← serverBytes, ← beaconBytes]
  exact consistent

/-- Equal native populated AD binds both ordered ML keys, unless two actual queries in the same shared cache collide. -/
theorem associated_data_key_binding (left right : session.RegistrationBinding)
    (leftBeaconKey rightBeaconKey : Pqxdh.Bytes) (cache : CtxRO.QueryCache)
    (leftCached : BindingCached left leftBeaconKey cache) (rightCached : BindingCached right rightBeaconKey cache)
    (same : absBytes left.associated_data = absBytes right.associated_data) :
    (absBytes left.server_pin.public_key = absBytes right.server_pin.public_key ∧
      leftBeaconKey = rightBeaconKey) ∨ CacheHasCollision cache := by
  obtain ⟨leftConsistent, leftServer, leftBeacon, leftServerCached, leftBeaconCached,
    leftServerBytes, leftBeaconBytes⟩ := leftCached
  obtain ⟨rightConsistent, rightServer, rightBeacon, rightServerCached, rightBeaconCached,
    rightServerBytes, rightBeaconBytes⟩ := rightCached
  rw [leftConsistent, rightConsistent] at same
  simp only [boundAssociatedData, Pqxdh.TranscriptAuth.fillAssociatedData,
    leftServerBytes, leftBeaconBytes, rightServerBytes, rightBeaconBytes] at same
  have identity_width (identity : Std.Array Std.U8 32#usize) : (absBytes identity).length = 32 := by
    simpa only [absBytes, List.length_map, Std.UScalar.ofNatCore_val_eq] using identity.property
  have baseWidths :
      ((Pqxdh.assocData (absBytes left.server_pin.binding.identity_public_key)
        (absBytes left.beacon_identity_public_key)).take 153).length =
      ((Pqxdh.assocData (absBytes right.server_pin.binding.identity_public_key)
        (absBytes right.beacon_identity_public_key)).take 153).length := by
    simp only [List.length_take, Pqxdh.assocData_length (identity_width _) (identity_width _)]
  have fields := Pqxdh.TranscriptAuth.associatedData_inj baseWidths
    (leftServer.toList_length.trans rightServer.toList_length.symm) same
  by_cases serverSame : absBytes left.server_pin.public_key = absBytes right.server_pin.public_key
  · by_cases beaconSame : leftBeaconKey = rightBeaconKey
    · exact Or.inl ⟨serverSame, beaconSame⟩
    · exact Or.inr ⟨((), leftBeaconKey), ((), rightBeaconKey), leftBeacon, rightBeacon,
        (fun equal => beaconSame (congrArg Prod.snd equal)), leftBeaconCached, rightBeaconCached,
        heq_of_eq (List.Vector.toList_injective fields.2.2)⟩
  · exact Or.inr ⟨((), absBytes left.server_pin.public_key), ((), absBytes right.server_pin.public_key),
      leftServer, rightServer, (fun equal => serverSame (congrArg Prod.snd equal)),
      leftServerCached, rightServerCached, heq_of_eq (List.Vector.toList_injective fields.2.1)⟩

end BeaconcryptCore.Computational.RegistrationFingerprintExecutor

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.beacon_phase_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.beacon_phase_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.accepted_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.accepted_exact

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_accepted

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_fingerprints' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.execute_fingerprints

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.binding_cached_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.binding_cached_mono

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.fingerprint_receipts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.fingerprint_receipts

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.binding_associated_data' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.binding_associated_data

/-- info: 'BeaconcryptCore.Computational.RegistrationFingerprintExecutor.associated_data_key_binding' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationFingerprintExecutor.associated_data_key_binding
