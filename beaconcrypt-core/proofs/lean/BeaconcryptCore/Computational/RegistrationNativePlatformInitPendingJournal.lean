-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformBundlePhases
import BeaconcryptCore.Computational.RegistrationNativePlatformPendingFrames
import BeaconcryptCore.Computational.RegistrationNativePlatformOwnerRoster
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformPackedState
import BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal

/-! Exact initialized source histories locate every retained InitSent capability at an earlier successful source bundle in that same execution, with its actual crypto/writer cut, platform states and immutable owner metadata. The private journal is erased exactly by the generic StageTrace erasure theorem; it is not an adversary-visible interface. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePendingFrames (PendingAt)
open RegistrationNativePlatformPackedState (pack)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform

def SourceAt (coins : QueryImpl unifSpec (StateT Platform ProbComp))
    (setup : Setup base KemSK) (checks : Checks) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize))
    (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
    (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) : Prop :=
  ∃ bytes, call.query = .inr (.bundle index) ∧ HEq call.reply (.ok (some bytes) : RustM (Option Pqxdh.Bytes)) ∧
    Nonempty (RegistrationNativePlatformBundleOwnerPhase.Stored coins setup checks representation created writer index
      call.before.1 call.after.1 call.before.2 call.after.2 bytes) ∧ PendingAt call.after.1.beacons index pending oneTime

variable [primitive : AdapterSealPrimitive.Operations]
variable (coins : QueryImpl unifSpec (StateT Platform ProbComp))
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))

noncomputable def callback : QueryImpl RegistrationNativeRawAdapter.TypedSpec (StateT Whole ProbComp) :=
  fun query => pack (RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
    reserveRegistration reservePeer erased helper writer query)

local notation "impl" => callback coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  simp only [callback, pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

/-- A corrected callback inherits an exact pending capability or is its actual successful source bundle. -/
theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before))
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : PendingAt after.1.beacons index pending oneTime) :
    PendingAt before.1.beacons index pending oneTime ∨ SourceAt coins setup checks representation created writer ⟨query, before, reply, after⟩ index pending oneTime := by
  have called := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
    query before after reply supported
  by_cases allowed : RegistrationNativePendingFrames.NonBundle query
  · exact Or.inl (RegistrationNativePlatformPendingFrames.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query allowed before.1 after.1 before.2 after.2 reply called index pending oneTime present)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr command => cases command with
      | bundle target =>
        rcases RegistrationNativePlatformBundlePhases.native_pending coins setup checks representation created writer target before.1 after.1 before.2 after.2 reply
            called index pending oneTime present with old | ⟨bytes, selected, returned, receipt⟩
        · exact Or.inl old
        · subst target
          exact Or.inr ⟨bytes, rfl, heq_of_eq returned, receipt, present⟩
      | _ => exact False.elim (allowed trivial)

/-- Every retained source pending capability lies in the initial state or one earlier actual successful source bundle in the same chronological path. -/
theorem path (initial final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl initial calls final)
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : PendingAt final.1.beacons index pending oneTime) :
    PendingAt initial.1.beacons index pending oneTime ∨ ∃ call ∈ calls, SourceAt coins setup checks representation created writer call index pending oneTime := by
  revert present
  induction reached with
  | nil state => intro present; exact Or.inl present
  | cons call called rest last following ih =>
    intro present
    rcases ih present with before | ⟨earlier, member, origin⟩
    · rcases step coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        call.query call.before call.after call.reply called index pending oneTime before with old | origin
      · exact Or.inl old
      · exact Or.inr ⟨call, List.mem_cons_self, origin⟩
    · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

private theorem metadata_path (initial final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl initial calls final) : RegistrationNativeOwnerRoster.Prefix initial.1.beacons final.1.beacons := by
  induction reached with
  | nil state => exact ⟨[], (List.append_nil _).symm⟩
  | cons call called rest last following ih =>
    have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.query call.before call.after call.reply called
    obtain ⟨leading, first⟩ := RegistrationNativePlatformOwnerRoster.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 call.after.2 call.reply sourceCalled
    obtain ⟨trailing, later⟩ := ih
    exact ⟨leading ++ trailing, by rw [later, first, List.append_assoc]⟩

/-- Startup has no Beacon owner, so every later pending capability has an actual earlier source bundle and metadata-preserving suffix in this same initialized path. -/
theorem initialized_path (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl (initial.state, previous) calls final)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : final.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime) :
    ∃ call ∈ calls, SourceAt coins setup checks representation created writer call index pending oneTime ∧
      ∃ leading trailing earlier,
        calls = leading ++ call :: trailing ∧ Path impl (initial.state, previous) leading call.before ∧
        RegistrationNativeStageTrace.Executed impl call ∧ Path impl call.after trailing final ∧
        call.after.1.beacons[index]? = some earlier ∧ earlier.phase = .initSent pending oneTime ∧
        RegistrationNativeOwnerFields.metadata owner = RegistrationNativeOwnerFields.metadata earlier := by
  rcases path coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      (initial.state, previous) final calls reached index pending oneTime ⟨owner, found, phase⟩ with old | ⟨call, member, origin⟩
  · obtain ⟨earlier, previous, _phase⟩ := old
    have empty := RegistrationNativeInitPendingJournal.start_empty setup ensureInit identityIndex serverKeyId initial startup
    simp only [empty, List.getElem?_nil, reduceCtorEq] at previous
  · obtain ⟨leading, trailing, split, before, called, after⟩ := reached.member call member
    have sourceOrigin := origin
    obtain ⟨_bytes, _query, _reply, _receipt, earlier, earlierFound, earlierPhase⟩ := origin
    obtain ⟨current, currentFound, sameMetadata⟩ := RegistrationNativeOwnerRoster.lookup call.after.1.beacons final.1.beacons
      (metadata_path coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
        call.after final trailing after) index earlier earlierFound
    have currentSame := Option.some.inj (currentFound.symm.trans found)
    subst current
    exact ⟨call, member, sourceOrigin, leading, trailing, earlier, split, before, called, after, earlierFound, earlierPhase, sameMetadata⟩

private theorem cache_path (initial final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl initial calls final) : RegistrationNativeWorldCache.cache initial.1 ≤ RegistrationNativeWorldCache.cache final.1 := by
  induction reached with
  | nil state => exact le_refl _
  | cons call called rest last following ih =>
    have sourceCalled := actual coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.query call.before call.after call.reply called
    exact (RegistrationNativePlatformHandlerCache.handler coins setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.before.2 ((call.reply, call.after.1), call.after.2) sourceCalled).trans ih

omit primitive in
/-- The same actual earlier source bundle supplies the exact original tuple and cached pending digest for its own retained owner. -/
theorem source_receipt (call : Call RegistrationNativeRawAdapter.TypedSpec Whole) (index : Nat)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (origin : SourceAt coins setup checks representation created writer call index pending oneTime)
    (owner : RegistrationNativeBeaconFrontend.Owner source)
    (found : call.after.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime) :
    Nonempty (RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime (RegistrationNativeWorldCache.cache call.after.1)) := by
  obtain ⟨bytes, _query, _reply, ⟨cut⟩, _present⟩ := origin
  have sameOwner : cut.current = owner := Option.some.inj (cut.found.symm.trans found)
  cases sameOwner
  have samePhase := cut.phase.symm.trans phase
  cases samePhase
  exact RegistrationNativePlatformPendingTuple.stored coins setup checks representation created writer index call.before.1 call.after.1
    call.before.2 call.after.2 bytes cut

/-- Every actual initialized source journal derives the earlier successful bundle and its original tuple/cache receipt at the current pending owner, all in this one retained execution. -/
theorem initialized (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (previous : Platform) (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Whole × List (Call RegistrationNativeRawAdapter.TypedSpec Whole)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler impl) work).run ((initial.state, previous), [])))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : result.2.1.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime) :
    ∃ call ∈ result.2.2, SourceAt coins setup checks representation created writer call index pending oneTime ∧
      Nonempty (RegistrationNativePlatformPendingTuple.Receipt setup owner pending oneTime (RegistrationNativeWorldCache.cache result.2.1.1)) := by
  have reached := RegistrationNativeStageTrace.path impl work (initial.state, previous) result supported
  obtain ⟨call, member, origin, _leading, trailing, earlier, _split, _before, _called, after, earlierFound, earlierPhase, metadata⟩ :=
    initialized_path coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      ensureInit identityIndex serverKeyId initial startup previous result.2.1 result.2.2 reached index owner pending oneTime found phase
  obtain ⟨receipt⟩ := source_receipt coins setup checks representation created writer call index pending oneTime origin earlier earlierFound earlierPhase
  exact ⟨call, member, origin, RegistrationNativePlatformPendingTuple.transport setup earlier owner pending oneTime _ _ metadata
    (cache_path coins setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer erased helper writer
      call.after result.2.1 trailing after) receipt⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.initialized_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.source_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.source_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal.initialized
