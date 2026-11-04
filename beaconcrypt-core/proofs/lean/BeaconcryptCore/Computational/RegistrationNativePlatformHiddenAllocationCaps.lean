-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationBuildCaps
import BeaconcryptCore.Computational.RegistrationNativePlatformSelectiveEntropyExecution
/-! Every actual callback other than create has no physical owner-append capability. The proof follows the corrected source bodies, including shared platform failures, and then closes their actual selective private backend. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativePlatformPublicFrontend
open RegistrationNativeHiddenAllocationCore (mapped simulation)
open RegistrationNativePlatformHiddenAllocationBackend (Allowed)
variable {n : Nat} {E Platform I KemSK ProviderState A : Type} {base : OracleSpec I}
private theorem every {J V : Type} {spec : OracleSpec J} (work : OracleComp spec V) :
    work.AllQueriesSatisfy (fun _ => True) := by
  induction work using OracleComp.inductionOn with
  | pure value => trivial
  | query_bind query next ih => exact ⟨trivial, ih⟩
private theorem map_apply {S V W : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (f : V → W) (work : StateT S m V) (before : S) :
    (f <$> work) before = Prod.map f id <$> work before := StateT.run_map f work before
private theorem coins_free (work : ProbComp A) :
    (simulateQ (publicCoin (n := n) (KemSK := KemSK)) work).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  apply simulation _ (fun _ => True) _ _ _ (every _)
  intro query _
  exact (allQueriesSatisfy_query_iff _ _).mpr trivial
private theorem gate_free {V : Type}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (size : V → Nat) (output : Option V) (before : Platform) :
    ((RegistrationNativePlatformOrdinaryGate.gate (fun amount => platformFull (n := n) (KemSK := KemSK) (reserve amount)) size output).run before).AllQueriesSatisfy
      (Allowed (KemSK := KemSK)) := by
  cases output with
  | none => trivial
  | some value =>
    simp only [RegistrationNativePlatformOrdinaryGate.gate, StateT.run]
    apply allQueriesSatisfy_bind (coins_free _)
    rintro ⟨result, after⟩
    cases result <;> trivial
private theorem record_free {source : RegistrationNativeMldsa.Source}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (query : PqxdhRecordLiftInterface.RecordQuery) (before : State source Platform) :
    ((record (n := n) (KemSK := KemSK) reserve query).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  rcases query with (send | raw) | ⟨owner, send | raw⟩
  · simp only [record, StateT.run, old]
    rw [allQueriesSatisfy_query_bind_iff]
    refine ⟨trivial, ?_⟩
    intro output
    simp only [bind_pure_comp]
    exact mapped _ _ _ (gate_free reserve _ output before.2)
  · simp only [record, StateT.run, old]
    exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)
  · simp only [record, StateT.run]
    split
    · trivial
    · simp only [old]
      rw [allQueriesSatisfy_query_bind_iff]
      refine ⟨trivial, ?_⟩
      intro output
      simp only [bind_pure_comp]
      exact mapped _ _ _ (gate_free reserve _ output before.2)
  · simp only [record, StateT.run]
    split
    · trivial
    · simp only [old]
      exact mapped _ _ _ ((allQueriesSatisfy_query_iff _ _).mpr trivial)
private theorem effect_free {source : RegistrationNativeMldsa.Source}
    (query : (PqxdhRecordLiftInterface.EnvEffects n).Domain)
    (safe : RegistrationNativeHiddenServerAllocationCaps.EffectAllowed query) (before : State source Platform) :
    ((executeLocal (StateT.lift (effect (KemSK := KemSK) query))).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  apply RegistrationNativePlatformHiddenAllocationLocal.embedding
  simp only [StateT.run_lift, bind_pure_comp]
  apply mapped
  exact RegistrationNativePlatformHiddenAllocationLocal.native_query false (.inr (.inl (.inr (.inr query)))) safe

variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire) (source : RegistrationNativeMldsa.Source)
variable (sign : registration.MldsaSigningRequest → ProbComp RegistrationSigningShared.SignReply)
variable (selectedOwner selectedAccept : Nat) (publicPrekey : PqxdhJointIdentity.PeerEncoding)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

/-- Every literal non-create public callback retains the no-append source capability predicate. -/
theorem frontend (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before : State source Platform)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) :
    ((handler (n := n) setup checks wire source sign selectedOwner selectedAccept publicPrekey view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query).run before).AllQueriesSatisfy (Allowed (KemSK := KemSK)) := by
  cases query with
  | inl coin => exact effect_free (.inl coin) rfl before
  | inr query => cases query with
    | create edPin mlPin keyId => exact (quiet rfl).elim
    | bundle index =>
      change (simulateQ embedLocal (_ : OracleComp (LocalSpec n KemSK) _)).AllQueriesSatisfy _
      apply RegistrationNativePlatformHiddenAllocationLocal.embedding
      simp only [beacon, StateT.run, map_apply]
      apply mapped
      apply mapped
      exact RegistrationNativePlatformHiddenAllocationLocal.bundle setup writer selectedOwner publicPrekey index _ _ _
    | accept packet =>
      change (simulateQ embedLocal ((do
        let previous ← get
        modify fun current => ({current.1 with parsedAccepts := current.1.parsedAccepts + 1}, current.2)
        serverOpen (RegistrationNativePlatformServerOpenControl.accept
          (localHandler (n := n) (KemSK := KemSK) (Platform := Platform) (decide (previous.1.parsedAccepts = selectedAccept)))
          (platform reserveRegistration) setup checks source.verify packet) : LocalM n KemSK Platform source _).run before)).AllQueriesSatisfy _
      apply RegistrationNativePlatformHiddenAllocationLocal.embedding
      simp only [StateT.run]
      apply mapped
      exact RegistrationNativePlatformHiddenAllocationLocal.accept (decide (before.1.parsedAccepts = selectedAccept)) reserveRegistration setup checks source.verify packet before.1.server before.1.environment before.2
    | build handle application =>
      apply RegistrationNativePlatformHiddenAllocationLocal.embedding
      exact RegistrationNativePlatformHiddenAllocationBuildCaps.build view failure allocation erased helper sign writer setup reservePeer handle application before
    | finish index packet =>
      apply RegistrationNativePlatformHiddenAllocationLocal.embedding
      simp only [beacon, StateT.run]
      apply mapped
      exact RegistrationNativePlatformHiddenAllocationLocal.finish setup wire index packet _ _ _
    | hmac key bytes => trivial
    | hash bytes => exact effect_free (.inr (.hash bytes)) rfl before
    | serverSend keyId plaintext => exact record_free reserveFrame (.inl (.inl (plaintext,keyId))) before
    | serverRaw raw => exact record_free reserveFrame (.inl (.inr raw)) before
    | beaconSend index plaintext => exact record_free reserveFrame (.inr (index,.inl plaintext)) before
    | beaconRaw index raw => exact record_free reserveFrame (.inr (index,.inr raw)) before

/-- Closing a non-create callback through the actual selective private backend performs no physical owner append. -/
theorem typed (credential : RegistrationNativeMldsa.Credential source)
    (seed : PqxdhJointIdentity.IdentitySeed) (scalar : PqxdhJointGapDh.ScalarBytes)
    (candidate : PqxdhKemIndCca.MlKemSharedSecret) (provider : RegistrationNativeHiddenInterpreter.Provider KemSK ProviderState)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : RegistrationNativePlatformSelectiveEntropyEnvironment.State n KemSK ProviderState Platform source)
    (quiet : RegistrationNativeRawAdapter.kind query ≠ 1) :
    ((RegistrationNativePlatformSelectiveEntropyExecution.handler setup checks wire source credential seed scalar candidate provider
      selectedOwner selectedAccept view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query).run before).AllQueriesSatisfy
      RegistrationNativeHiddenAllocationCore.WorldAllowed := by
  simp only [RegistrationNativePlatformSelectiveEntropyExecution.handler]
  apply mapped
  apply RegistrationNativePlatformHiddenAllocationBackend.program
  exact frontend setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) source (RegistrationNativeMldsa.owned source credential)
    selectedOwner selectedAccept (setup.dh.publicKey scalar) view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before.1 quiet
end BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps.frontend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps.frontend

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps.typed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformHiddenAllocationCaps.typed
