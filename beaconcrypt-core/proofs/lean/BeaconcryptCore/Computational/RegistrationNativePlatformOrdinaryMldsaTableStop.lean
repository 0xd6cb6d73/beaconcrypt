-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableGate
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache

/-! The actual dynamic-writer runtime's stopped ML experiment retains the same reached Native/private-table invariants before its public terminal writer decision. Incoming capture is unchanged at the exact same cut; no native security or desired freshness premise is introduced. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativePlatformOrdinaryMldsaTableCallback (State callback observe)
open RegistrationNativeMldsaEuf (PublicKey Forgery)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

abbrev core := RegistrationNativePlatformMldsaTableStop.core (n := n) (KemSK := KemSK) (Platform := Platform) source
abbrev Safe := RegistrationNativePlatformMldsaTableStop.Safe (n := n) (KemSK := KemSK) (Platform := Platform) source
abbrev Good := RegistrationNativePlatformMldsaTableStop.Good (n := n) (KemSK := KemSK) (Platform := Platform) source

private theorem safe_state (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (fallback : RegistrationNativeMldsa.Credential source)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (sameNative : after.1.1 = before.1.1) (samePool : after.2 = before.2)
    (safe : Safe source credential fallback before) : Safe source credential fallback after := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [RegistrationNativePlatformMldsaTableStop.core, sameNative, samePool] using safe.toSafe
  · simpa only [sameNative] using safe.pinned
  · simpa only [samePool] using safe.provenance

private theorem after_cut {Native Private : Type}
    (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : StateT ((Native × Platform) × Private) ProbComp (Option RawCtxSourceSend.Encrypted))
    (before : (Native × Platform) × Private)
    (result : Option RawCtxSourceSend.Encrypted × ((Native × Platform) × Private))
    (supported : result ∈ support ((RegistrationNativePlatformOrdinaryMldsaTableGate.after reserve work).run before)) :
    ∃ middle ∈ support (work.run before), result.2.1.1 = middle.2.1.1 ∧ result.2.2 = middle.2.2 := by
  simp only [RegistrationNativePlatformOrdinaryMldsaTableGate.after, StateT.run, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at supported
  obtain ⟨middle, called, gated, _reserved, returned⟩ := supported
  cases returned
  exact ⟨middle, called, rfl, rfl⟩

/-- Actual table startup derives every initial live-key, signing/cache, immutable-pin and birth-provenance field. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (previous : Platform) : ∃ fallback, Safe source initial.credential fallback ((initial.state, previous), started.2) :=
  RegistrationNativePlatformMldsaTableStop.initialized source setup ensureInit identityIndex serverKeyId started startup initial member previous

variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

local notation "legacy" => RegistrationNativePlatformMldsaTableCallback.callback source setup checks
  (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer
local notation "actual" => callback source setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer

private theorem prior_step (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before) (supported : result ∈ support ((legacy query).run before)) :
    Safe source credential fallback result.2 :=
  RegistrationNativePlatformMldsaTableStop.step_safe source setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation
    created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback query before result safe supported

private theorem prior_cache (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before) (supported : result ∈ support ((legacy query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativePlatformHandlerCache.table setup checks
    (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created view failure allocation
      reserveRegistration reservePeer erased helper writer source credential fallback before.2 safe.server query before.1.1 before.1.2 safe.owners inner reached

/-- Actual terminal writer failure changes only public platform state after the reached private safe state. -/
theorem step_safe (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before) (supported : result ∈ support ((actual query).run before)) :
    Safe source credential fallback result.2 := by
  rw [RegistrationNativePlatformOrdinaryMldsaTableGate.callback] at supported
  have gated (work : StateT (State (n := n) (KemSK := KemSK) (Platform := Platform) source) ProbComp (Option RawCtxSourceSend.Encrypted))
      (keeps : ∀ middle, middle ∈ support (work.run before) → Safe source credential fallback middle.2)
      (result : Option RawCtxSourceSend.Encrypted × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
      (called : result ∈ support ((RegistrationNativePlatformOrdinaryMldsaTableGate.after reserveFrame work).run before)) : Safe source credential fallback result.2 := by
    obtain ⟨middle, reached, nativeEq, poolEq⟩ := after_cut reserveFrame work before result called
    exact safe_state source credential fallback middle.2 result.2 nativeEq poolEq (keeps middle reached)
  cases query with
  | inl coin => exact prior_step source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback _ before result safe supported
  | inr query => cases query with
    | serverSend key plaintext => exact gated (legacy (.inr (.serverSend key plaintext))) (fun middle reached => prior_step source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer fallback (.inr (.serverSend key plaintext)) before middle safe reached) result supported
    | beaconSend owner plaintext => exact gated (legacy (.inr (.beaconSend owner plaintext))) (fun middle reached => prior_step source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer fallback (.inr (.beaconSend owner plaintext)) before middle safe reached) result supported
    | _ => exact prior_step source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback _ before result safe supported

/-- The actual runtime callback extends the literal shared cache, including terminal writer failure. -/
theorem cache (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before) (supported : result ∈ support ((actual query).run before)) :
    RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
  rw [RegistrationNativePlatformOrdinaryMldsaTableGate.callback] at supported
  have gated (work : StateT (State (n := n) (KemSK := KemSK) (Platform := Platform) source) ProbComp (Option RawCtxSourceSend.Encrypted))
      (keeps : ∀ middle, middle ∈ support (work.run before) →
        RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache middle.2.1.1)
      (result : Option RawCtxSourceSend.Encrypted × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
      (called : result ∈ support ((RegistrationNativePlatformOrdinaryMldsaTableGate.after reserveFrame work).run before)) :
      RegistrationNativeWorldCache.cache before.1.1 ≤ RegistrationNativeWorldCache.cache result.2.1.1 := by
    obtain ⟨middle, reached, nativeEq, _poolEq⟩ := after_cut reserveFrame work before result called
    rw [nativeEq]
    exact keeps middle reached
  cases query with
  | inl coin => exact prior_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback _ before result safe supported
  | inr query => cases query with
    | serverSend key plaintext => exact gated (legacy (.inr (.serverSend key plaintext))) (fun middle reached => prior_cache source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer fallback (.inr (.serverSend key plaintext)) before middle safe reached) result supported
    | beaconSend owner plaintext => exact gated (legacy (.inr (.beaconSend owner plaintext))) (fun middle reached => prior_cache source setup checks wire route representation created credential view failure allocation
        reserveRegistration reservePeer erased helper writer fallback (.inr (.beaconSend owner plaintext)) before middle safe reached) result supported
    | _ => exact prior_cache source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback _ before result safe supported

/-- An actual selected incoming cut is ordinary valid and fresh against that same cut's final signing prefix. -/
theorem captured (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (forgery : Forgery) (safe : Safe source credential fallback before)
    (supported : result ∈ support ((actual query).run before))
    (selected : observe source publicKey query before result.1 result.2 = some forgery) : Good source publicKey result.2 forgery := by
  rw [RegistrationNativePlatformOrdinaryMldsaTableGate.callback] at supported
  have called : result ∈ support ((legacy query).run before) := by
    cases query with
    | inl coin => exact supported
    | inr query => cases query with
      | serverSend key plaintext => cases selected
      | beaconSend owner plaintext => cases selected
      | _ => exact supported
  exact RegistrationNativePlatformMldsaTableStop.captured source setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation
    created credential view failure allocation reserveRegistration reservePeer erased helper writer publicKey fallback query before result forgery safe called selected

/-- The executable frozen corrected client returns only ordinary valid candidates fresh against its complete same-cut signing prefix. -/
theorem run_good (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (safe : Safe source credential fallback before)
    (result : Value × (State (n := n) (KemSK := KemSK) (Platform := Platform) source × Option Forgery))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (observe source publicKey) defaultReply) work).run (before, none))) :
    Safe source credential fallback result.2.1 ∧ ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery :=
  RegistrationNativeMldsaStop.freeze_property _ _ _ _ _
    (step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer fallback)
    (captured source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer publicKey fallback)
    work before none safe (by intro candidate impossible; cases impossible) result supported

/-- The initialized actual corrected frozen source derives ordinary validity and freshness without a signing-history, pin-hit or authentication premise. -/
theorem initialized_good (publicKey : PublicKey) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (State (n := n) (KemSK := KemSK) (Platform := Platform) source × Option Forgery))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
      (callback source setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer)
      (observe source publicKey) RegistrationNativeMldsaTableStop.defaultReply) work).run (((initial.state, previous), started.2), none))) :
    ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery := by
  obtain ⟨fallback, safe⟩ := initialized source setup ensureInit identityIndex serverKeyId started startup initial member previous
  exact (run_good source setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    publicKey fallback RegistrationNativeMldsaTableStop.defaultReply work ((initial.state, previous), started.2) safe result supported).2
end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.step_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.step_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.cache' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.cache

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.run_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.initialized_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryMldsaTableStop.initialized_good
