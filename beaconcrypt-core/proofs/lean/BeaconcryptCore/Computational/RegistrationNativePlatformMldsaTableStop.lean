-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCallback
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaRunChronology
import BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableCached
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace
import BeaconcryptCore.Computational.RegistrationNativeMldsaProtectedInvariant

/-! Actual corrected first-candidate stopping retains the complete native/platform state and true private signing table. The initial invariant is derived from real startup; the stored-pin receipt and successful-birth history remain explicit source state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource)
open RegistrationNativePlatformMldsaTableCallback (State callback observe)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)

def core (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) := (before.1.1, before.2)

structure Safe (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (fallback : RegistrationNativeMldsa.Credential source)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) : Prop extends
    RegistrationNativeMldsaTableStop.Safe source credential fallback (core source before) where
  pinned : RegistrationNativeServerPinRecompute.Cached before.1.1.server.pin (RegistrationNativeWorldCache.cache before.1.1)
  provenance : RegistrationNativeMldsaBirthProvenance.Provenance source before.2

/-- Actual table startup derives every initial live-key, signing/cache, immutable-pin and birth-provenance field. -/
theorem initialized (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (previous : Platform) : ∃ fallback, Safe source initial.credential fallback ((initial.state, previous), started.2) := by
  obtain ⟨fallback, good⟩ := RegistrationNativeMldsaProtectedInvariant.initialized source setup ensureInit identityIndex serverKeyId started startup initial member
  exact ⟨fallback, good.safe,
    RegistrationNativePlatformServerPinTrace.table_initialized setup source ensureInit identityIndex serverKeyId started startup initial member,
    good.provenance⟩


variable [primitive : AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential (handleSource source))
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

omit primitive in
private theorem nonsigning_of_selected (publicKey : PublicKey) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (forgery : Forgery)
    (selected : observe source publicKey query before reply after = some forgery) :
    RegistrationNativeMldsaReceiptPreservation.NonSigning query := by
  cases query with
  | inl coin => trivial
  | inr query => cases query with
    | create _ _ _ | bundle _ | build _ _ => cases selected
    | _ => trivial

def Good (publicKey : PublicKey) (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (forgery : Forgery) : Prop :=
  Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey before.2.signing) forgery

omit primitive in
private theorem evaluated {Answer : Type}
    (work : OracleComp (RegistrationNativeMldsaProgram.Spec (handleSource source)) Answer)
    (before : Pool source) (good : RegistrationNativeMldsaBirthProvenance.Provenance source before) (result : Answer × Pool source)
    (supported : result ∈ support (RegistrationNativeMldsaTableProgram.evaluate source work before)) :
    RegistrationNativeMldsaBirthProvenance.Provenance source result.2 :=
  PqxdhRecordLiftFlat.support_keep_oracle (RegistrationNativeMldsaTableProgram.handler source)
    (RegistrationNativeMldsaBirthProvenance.Provenance source)
    (fun query current previous output reached => (RegistrationNativeMldsaBirthProvenance.step source query current previous output reached).1)
    work before good result supported

private theorem step_core (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before))
    (cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject result.2.1.1)) : Safe source credential fallback result.2 := by
  simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  refine ⟨⟨?_, ?_, ?_, cached⟩, ?_, ?_⟩
  · exact RegistrationNativePlatformMldsaTableHandler.server_live source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      fallback before.2 safe.server query before.1.1 before.1.2 safe.owners inner reached
  · exact RegistrationNativePlatformMldsaTableHandler.live source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      before.2 ⟨fallback, safe.server⟩ query before.1.1 before.1.2 safe.owners inner reached
  · exact RegistrationNativePlatformMldsaRunChronology.handler source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query before.1.1 before.1.2 before.2 inner safe.aligned reached
  · exact RegistrationNativePlatformServerPinTrace.table_cached setup checks wire route representation created view failure allocation reserveRegistration reservePeer erased helper writer
      source credential fallback before.2 safe.server query before.1.1 before.1.2 safe.owners inner reached safe.pinned
  · exact evaluated source _ before.2 safe.provenance inner reached



/-- Every actual corrected callback derives all reached stopping invariants from its literal source execution. -/
theorem step_safe (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before)) : Safe source credential fallback result.2 := by
  apply step_core source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    fallback query before result safe supported
  simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, support_map] at supported
  obtain ⟨inner, reached, same⟩ := supported
  cases same
  exact RegistrationNativePlatformMldsaTableCached.cached source setup checks wire route representation created credential fallback view failure allocation
    reserveRegistration reservePeer erased helper writer query before.1.1 before.1.2 before.2 safe.server safe.owners safe.cached inner reached

/-- The actual selected incoming cut produces an ordinary valid candidate fresh against its literal same-cut final table signing prefix. -/
theorem captured (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) (Platform := Platform) source)
    (forgery : Forgery) (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query).run before))
    (selected : observe source publicKey query before result.1 result.2 = some forgery) : Good source publicKey result.2 forgery := by
  have allowed := nonsigning_of_selected source publicKey query before result.2 result.1 forgery selected
  have finalSafe := step_safe source setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer erased helper writer fallback query before result safe supported
  have frames : result.2.2 = before.2 ∧ result.2.1.1.server.world.world.2 = before.1.1.server.world.world.2 := by
    simp only [RegistrationNativePlatformMldsaTableCallback.callback, StateT.run, support_map] at supported
    obtain ⟨inner, reached, same⟩ := supported
    cases same
    exact RegistrationNativePlatformReceiptPreservation.handler source setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query allowed before.1.1 before.1.2 before.2 inner reached
  refine ⟨RegistrationNativeMldsaTrialObserver.observe_valid publicKey query before.1.1 result.2.1.1 result.1 forgery selected, ?_⟩
  rw [frames.1]
  change (RegistrationNativeMldsaTrialObserver.trial query before.1.1 result.1).bind _ = some forgery at selected
  cases reached : RegistrationNativeMldsaTrialObserver.trial query before.1.1 result.1 with
  | none => simp only [reached, Option.bind_none, reduceCtorEq] at selected
  | some trial =>
      simp only [reached, Option.bind_some] at selected
      obtain ⟨extracted, key, weak⟩ := RegistrationNativeMldsaTrialObserver.choose_sound source.verify publicKey _ trial forgery selected
      have cached : RegistrationSigningShared.Cached
          ((RegistrationNativeMldsaShared.nativeProject before.1.1).1, result.2.1.1.server.world.world.1.primitive.2) := by
        change RegistrationSigningShared.Cached (before.1.1.server.world.world.2, result.2.1.1.server.world.world.1.primitive.2)
        rw [← frames.2]
        exact finalSafe.cached
      exact RegistrationNativeMldsaCandidate.extract_fresh publicKey before.2.signing
        ((RegistrationNativeMldsaShared.nativeProject before.1.1).1, result.2.1.1.server.world.world.1.primitive.2)
        safe.aligned cached trial source.verify (RegistrationNativeMldsaTrialObserver.trial_history query before.1.1 result.1 trial reached)
        weak key forgery extracted



/-- The executable frozen corrected client returns only ordinary valid candidates fresh against its complete same-cut signing prefix. -/
theorem run_good (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State (n := n) (KemSK := KemSK) (Platform := Platform) source) (safe : Safe source credential fallback before)
    (result : Value × (State (n := n) (KemSK := KemSK) (Platform := Platform) source × Option Forgery))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
      (callback source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer)
      (observe source publicKey) defaultReply) work).run (before, none))) :
    Safe source credential fallback result.2.1 ∧ ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery :=
  RegistrationNativeMldsaStop.freeze_property _ _ _ _ _
    (step_safe source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer fallback)
    (captured source setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer publicKey fallback)
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
      (callback source setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer)
      (observe source publicKey) RegistrationNativeMldsaTableStop.defaultReply) work).run (((initial.state, previous), started.2), none))) :
    ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery := by
  obtain ⟨fallback, safe⟩ := initialized source setup ensureInit identityIndex serverKeyId started startup initial member previous
  exact (run_good source setup checks wire route representation initial.created initial.credential view failure allocation reserveRegistration reservePeer erased helper writer
    publicKey fallback RegistrationNativeMldsaTableStop.defaultReply work ((initial.state, previous), started.2) safe result supported).2
end BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.step_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.step_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.run_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.initialized_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformMldsaTableStop.initialized_good
