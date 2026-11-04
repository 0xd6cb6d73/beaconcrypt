-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeMldsaTableCallbackInvariant
import BeaconcryptCore.Computational.RegistrationNativeMldsaStop
import BeaconcryptCore.Computational.RegistrationNativeMldsaTrialObserver

/-! The online authentication candidate observer is instantiated with the actual dynamic private ML table and complete original typed callback. Reached live credentials, chronological request alignment and cached native receipts are preserved by the actual source handler. A selected candidate stops immediately and is valid/fresh against the actual final private signing prefix. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeMldsaOpaque (Pool handleSource Live)
open RegistrationNativeMldsaPoolMap (StateLive)
open RegistrationNativeMldsaChronology (Aligned)
open RegistrationNativeMldsaTableProgram (runState)
open RegistrationNativeMldsaEuf (PublicKey Forgery Valid Fresh)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι}
variable (source : RegistrationNativeMldsa.Source)
abbrev State := RegistrationNativeExperiment.State n KemSK (handleSource source) × Pool source

structure Safe (credential : RegistrationNativeMldsa.Credential (handleSource source))
    (fallback : RegistrationNativeMldsa.Credential source) (before : State (n := n) (KemSK := KemSK) source) : Prop where
  server : Live source before.2 credential fallback
  owners : StateLive source before.2 before.1
  aligned : Aligned before.2.signing (RegistrationNativeMldsaShared.nativeProject before.1).1
  cached : RegistrationSigningShared.Cached (RegistrationNativeMldsaShared.nativeProject before.1)

variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder)
variable (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit)
variable (credential : RegistrationNativeMldsa.Credential (handleSource source))

noncomputable def callback : QueryImpl RegistrationNativeRawAdapter.TypedSpec
    (StateT (State (n := n) (KemSK := KemSK) source) ProbComp) := fun query before =>
  (fun result => (result.1.1, (result.1.2, result.2))) <$>
    runState source (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query)
      before.1 before.2

def observe (publicKey : PublicKey) : RegistrationNativeMldsaStop.Observer
    (spec := RegistrationNativeRawAdapter.TypedSpec) (State := State (n := n) (KemSK := KemSK) source) (Candidate := Forgery) :=
  fun query before reply after => RegistrationNativeMldsaTrialObserver.observe source.verify publicKey query before.1 reply after.1

/-- All actual callback invariants needed at a stopping cut are derived together. -/
theorem step_safe (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) source)
    (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    Safe source credential fallback result.2 := by
  change result ∈ support ((fun inner => (inner.1.1, (inner.1.2, inner.2))) <$>
    runState source (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before.1 before.2) at supported
  rw [support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact ⟨RegistrationNativeMldsaTableHandler.server_live source setup checks wire route representation created credential fallback
      before.2 safe.server query before.1 safe.owners inner possible,
    RegistrationNativeMldsaTableHandler.live source setup checks wire route representation created credential fallback
      before.2 safe.server query before.1 safe.owners inner possible,
    RegistrationNativeMldsaRunChronology.handler source setup checks wire route representation created credential query
      before.1 before.2 inner safe.aligned possible,
    RegistrationNativeMldsaTableCallbackInvariant.cached source setup checks wire route representation created credential fallback query
      before.1 before.2 safe.server safe.owners safe.cached inner possible⟩

private theorem nonsigning_of_selected (publicKey : PublicKey) (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before after : State (n := n) (KemSK := KemSK) source)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query) (forgery : Forgery)
    (selected : observe source publicKey query before reply after = some forgery) :
    RegistrationNativeMldsaReceiptPreservation.NonSigning query := by
  cases query with
  | inl coin => trivial
  | inr query => cases query with
    | create _ _ _ | bundle _ | build _ _ => cases selected
    | _ => trivial

private theorem nonsigning_receipts (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (allowed : RegistrationNativeMldsaReceiptPreservation.NonSigning query)
    (before : State (n := n) (KemSK := KemSK) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) source)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before)) :
    result.2.2 = before.2 ∧ result.2.1.server.world.world.2 = before.1.server.world.world.2 := by
  have law : RegistrationNativeMldsaProfile.handler (n := n) setup checks wire route representation created credential query =
      RegistrationNativeMldsaProgram.liftState
        (RegistrationNativeExperiment.handler setup checks wire route representation created (handleSource source) credential query) := by
    cases query with
    | inl coin => rfl
    | inr query => cases query with
      | create _ _ _ | bundle _ | build _ _ => exact False.elim allowed
      | _ => rfl
  change result ∈ support ((fun inner => (inner.1.1, (inner.1.2, inner.2))) <$>
    runState source (RegistrationNativeMldsaProfile.handler setup checks wire route representation created credential query) before.1 before.2) at supported
  rw [law, RegistrationNativeMldsaTableProgram.run_liftState, Functor.map_map, support_map] at supported
  obtain ⟨inner, possible, same⟩ := supported
  cases same
  exact ⟨rfl, RegistrationNativeMldsaReceiptPreservation.handler setup checks wire route representation created credential
    query allowed before.1 inner possible⟩

def Good (publicKey : PublicKey) (before : State (n := n) (KemSK := KemSK) source) (forgery : Forgery) : Prop :=
  Valid source publicKey forgery ∧ Fresh (RegistrationNativeMldsaCandidate.requestsFor publicKey before.2.signing) forgery

/-- Every actual selected callback exposes a valid ordinary candidate fresh against its literal same-cut table history. -/
theorem captured (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain)
    (before : State (n := n) (KemSK := KemSK) source)
    (result : RegistrationNativeRawAdapter.TypedSpec.Range query × State (n := n) (KemSK := KemSK) source)
    (forgery : Forgery) (safe : Safe source credential fallback before)
    (supported : result ∈ support ((callback source setup checks wire route representation created credential query).run before))
    (selected : observe source publicKey query before result.1 result.2 = some forgery) :
    Good source publicKey result.2 forgery := by
  have finalSafe := step_safe source setup checks wire route representation created credential fallback query before result safe supported
  obtain ⟨poolSame, receiptsSame⟩ := nonsigning_receipts source setup checks wire route representation created credential query
    (nonsigning_of_selected source publicKey query before result.2 result.1 forgery selected) before result supported
  refine ⟨RegistrationNativeMldsaTrialObserver.observe_valid publicKey query before.1 result.2.1 result.1 forgery selected, ?_⟩
  rw [poolSame]
  change (RegistrationNativeMldsaTrialObserver.trial query before.1 result.1).bind _ = some forgery at selected
  cases reached : RegistrationNativeMldsaTrialObserver.trial query before.1 result.1 with
  | none => simp only [reached, Option.bind_none, reduceCtorEq] at selected
  | some trial =>
      simp only [reached, Option.bind_some] at selected
      obtain ⟨extracted, key, weak⟩ := RegistrationNativeMldsaTrialObserver.choose_sound source.verify publicKey _ trial forgery selected
      have cached : RegistrationSigningShared.Cached
          ((RegistrationNativeMldsaShared.nativeProject before.1).1, result.2.1.server.world.world.1.primitive.2) := by
        change RegistrationSigningShared.Cached (before.1.server.world.world.2, result.2.1.server.world.world.1.primitive.2)
        rw [← receiptsSame]
        exact finalSafe.cached
      exact RegistrationNativeMldsaCandidate.extract_fresh publicKey before.2.signing
        ((RegistrationNativeMldsaShared.nativeProject before.1).1, result.2.1.server.world.world.1.primitive.2)
        safe.aligned cached trial source.verify
        (RegistrationNativeMldsaTrialObserver.trial_history query before.1 result.1 trial reached) weak key forgery extracted

/-- The executable frozen original typed client returns only valid ordinary candidates, fresh against its actual final signing log. Its state invariants are source-derived and no callback runs after selection. -/
theorem run_good (publicKey : PublicKey) (fallback : RegistrationNativeMldsa.Credential source)
    (defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (before : State (n := n) (KemSK := KemSK) source) (safe : Safe source credential fallback before)
    (result : Value × (State (n := n) (KemSK := KemSK) source × Option Forgery))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
      (callback source setup checks wire route representation created credential) (observe source publicKey) defaultReply) work).run
        (before, none))) :
    Safe source credential fallback result.2.1 ∧ ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery :=
  RegistrationNativeMldsaStop.freeze_property _ _ _ _ _
    (step_safe source setup checks wire route representation created credential fallback)
    (captured source setup checks wire route representation created credential publicKey fallback)
    work before none safe (by intro candidate impossible; cases impossible) result supported

/-- Fixed post-stop replies are never issued to an underlying primitive; they only finish the adaptive client's pure continuation. -/
def defaultReply : (query : RegistrationNativeRawAdapter.TypedSpec.Domain) → RegistrationNativeRawAdapter.TypedSpec.Range query
  | .inl coin => (0 : Fin (coin + 1))
  | .inr (.create _ _ _) | .inr (.bundle _) | .inr (.accept _) | .inr (.build _ _) | .inr (.finish _ _) => .ok none
  | .inr (.hmac _ _) => List.Vector.replicate 64 0
  | .inr (.hash _) => List.Vector.replicate 64 0
  | .inr (.serverSend _ _) | .inr (.beaconSend _ _) => none
  | .inr (.serverRaw _) | .inr (.beaconRaw _ _) => .None

/-- Actual source startup derives every premise of the online stopping invariant, including its private and native empty signing prefixes. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1) :
    ∃ fallback, Safe source initial.credential fallback (initial.state, started.2) := by
  obtain ⟨fallback, server, owners⟩ := RegistrationNativeMldsaTableStart.initialized source setup ensureInit identityIndex
    serverKeyId started startup initial member
  refine ⟨fallback, server, owners,
    RegistrationNativeMldsaInitializedChronology.aligned source setup ensureInit identityIndex serverKeyId started startup initial member, ?_⟩
  intro receipt included
  have empty := (RegistrationNativeMldsaInitializedChronology.initialized source setup ensureInit identityIndex serverKeyId
    started startup initial member).2
  change receipt ∈ initial.state.server.world.world.2 at included
  rw [empty] at included
  cases included

/-- From the actual effectful startup, every candidate returned by the executable frozen original typed run is ordinary-valid and fresh against its complete actual signing-oracle prefix. -/
theorem initialized_good (publicKey : PublicKey) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : Std.U64)
    (started : Option (RegistrationNativeExperiment.Initial n KemSK (handleSource source)) × Pool source)
    (startup : started ∈ support (RegistrationNativeMldsaTableProgram.evaluate source
      (RegistrationNativeMldsaCreation.start setup ensureInit identityIndex serverKeyId) {}))
    (initial : RegistrationNativeExperiment.Initial n KemSK (handleSource source)) (member : initial ∈ started.1)
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (State (n := n) (KemSK := KemSK) source × Option Forgery))
    (supported : result ∈ support ((simulateQ (RegistrationNativeMldsaStop.freeze
      (callback source setup checks wire route representation initial.created initial.credential) (observe source publicKey) defaultReply) work).run
        ((initial.state, started.2), none))) :
    ∀ forgery, result.2.2 = some forgery → Good source publicKey result.2.1 forgery := by
  obtain ⟨fallback, safe⟩ := initialized source setup ensureInit identityIndex serverKeyId started startup initial member
  exact (run_good source setup checks wire route representation initial.created initial.credential publicKey fallback
    defaultReply work (initial.state, started.2) safe result supported).2

end BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop
/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.step_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.step_safe

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.run_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.run_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.initialized

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.initialized_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeMldsaTableStop.initialized_good
