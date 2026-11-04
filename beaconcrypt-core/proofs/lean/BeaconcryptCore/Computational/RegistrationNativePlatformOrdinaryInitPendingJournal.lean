-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformInitPendingJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryPathState
import BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryKemClientJournal
import BeaconcryptCore.Computational.RegistrationNativePlatformHandlerCache
import BeaconcryptCore.Computational.RegistrationNativePlatformServerPinTrace

/-! Every retained pending capability in the selected dynamic-writer runtime comes from an actual earlier source bundle in the same initialized execution. Dynamic established traffic preserves owner metadata and pending provenance, including failed reservations. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path Executed)
variable {n : Nat} {E Platform Value ι KemSK : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source
local notation "Whole" => Native × Platform
variable [primitive : BeaconcryptCore.Refinement.AdapterSealPrimitive.Operations]
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitive.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (BeaconcryptCore.Refinement.AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (BeaconcryptCore.Refinement.AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "impl" => RegistrationNativePlatformOrdinaryKemClientJournal.actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
attribute [local irreducible] RegistrationNativeExperiment.handler RegistrationNativePlatformSourceAccept.authenticate
  RegistrationNativePlatformSourceBuild.pin

open RegistrationNativePendingFrames (PendingAt)
open RegistrationNativePlatformInitPendingJournal (SourceAt)
local notation "coins" => RegistrationNativePlatformMldsaProgram.coins

omit primitive in
private theorem after_cut (reserve : Nat → StateT Platform ProbComp (core.result.Result Unit E))
    (work : RegistrationNativePlatformOrdinaryExperiment.M n KemSK source Platform (Option RawCtxSourceSend.Encrypted))
    (before : Native) (previous : Platform) (result : (Option RawCtxSourceSend.Encrypted × Native) × Platform)
    (supported : result ∈ support (((RegistrationNativePlatformOrdinaryExperimentRouting.after reserve work).run before).run previous)) :
    ∃ middle ∈ support ((work.run before).run previous), result.1.2 = middle.1.2 := by
  simp only [RegistrationNativePlatformOrdinaryExperimentRouting.after, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨middle, called, continued⟩ := supported
  simp only [StateT.run_lift, bind_pure_comp, StateT.run_map, support_map] at continued
  obtain ⟨gated, _reserved, same⟩ := continued
  exact ⟨middle, called, (congrArg (fun result => result.1.2) same).symm⟩

private theorem actual (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ((reply, after.1), after.2) ∈ support
      (((RegistrationNativePlatformOrdinaryExperiment.handler setup checks wire route representation created source credential view failure allocation
        reserveRegistration reservePeer reserveFrame erased helper writer query).run before.1).run before.2) := by
  simp only [RegistrationNativePlatformOrdinaryKemClientJournal.actual, RegistrationNativePlatformPackedState.pack, StateT.run, support_map] at supported
  obtain ⟨⟨⟨value, native⟩, platform⟩, called, same⟩ := supported
  cases same
  exact called

private theorem old_cut (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before)) :
    ∃ oldReply oldP, ((oldReply, after.1), oldP) ∈ support
      (((RegistrationNativePlatformExperiment.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created source credential view failure allocation
        reserveRegistration reservePeer erased helper writer query).run before.1).run before.2) := by
  have called := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before after reply supported
  rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at called
  cases query with
  | inl coin => exact ⟨reply, after.2, called⟩
  | inr command => cases command with
    | serverSend key plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | beaconSend owner plaintext =>
      obtain ⟨middle, reached, same⟩ := after_cut reserveFrame _ before.1 before.2 ((reply, after.1), after.2) called
      change after.1 = middle.1.2 at same
      exact ⟨middle.1.1, middle.2, by rw [same]; exact reached⟩
    | _ => exact ⟨reply, after.2, called⟩

/-- A selected-runtime pending capability is inherited or was produced by this actual successful source bundle. -/
theorem step (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Whole)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((impl query).run before))
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : PendingAt after.1.beacons index pending oneTime) :
    PendingAt before.1.beacons index pending oneTime ∨ SourceAt coins setup checks representation created writer ⟨query, before, reply, after⟩ index pending oneTime := by
  by_cases allowed : RegistrationNativePendingFrames.NonBundle query
  · obtain ⟨oldReply, oldP, called⟩ := old_cut setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before after reply supported
    exact Or.inl (RegistrationNativePlatformPendingFrames.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer query allowed before.1 after.1 before.2 oldP oldReply called index pending oneTime present)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr command => cases command with
      | bundle target =>
        have called := actual setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer (.inr (.bundle target)) before after reply supported
        rw [RegistrationNativePlatformOrdinaryExperimentRouting.handler_terminal] at called
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
    · rcases step setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        call.query call.before call.after call.reply called index pending oneTime before with old | origin
      · exact Or.inl old
      · exact Or.inr ⟨call, List.mem_cons_self, origin⟩
    · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

private theorem metadata_path (initial final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl initial calls final) : RegistrationNativeOwnerRoster.Prefix initial.1.beacons final.1.beacons := by
  induction reached with
  | nil state => exact ⟨[], (List.append_nil _).symm⟩
  | cons call called rest last following ih =>
    obtain ⟨oldReply, oldP, sourceCalled⟩ := old_cut setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      call.query call.before call.after call.reply called
    obtain ⟨leading, first⟩ := RegistrationNativePlatformOwnerRoster.handler coins setup checks (RegistrationNativePlatformOrdinaryExperiment.canonicalWire wire) route representation created credential view failure allocation
      reserveRegistration reservePeer erased helper writer call.query call.before.1 call.after.1 call.before.2 oldP oldReply sourceCalled
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
  rcases path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      (initial.state, previous) final calls reached index pending oneTime ⟨owner, found, phase⟩ with old | ⟨call, member, origin⟩
  · obtain ⟨earlier, previous, _phase⟩ := old
    have empty := RegistrationNativeInitPendingJournal.start_empty setup ensureInit identityIndex serverKeyId initial startup
    simp only [empty, List.getElem?_nil, reduceCtorEq] at previous
  · obtain ⟨leading, trailing, split, before, called, after⟩ := reached.member call member
    have sourceOrigin := origin
    obtain ⟨_bytes, _query, _reply, _receipt, earlier, earlierFound, earlierPhase⟩ := origin
    obtain ⟨current, currentFound, sameMetadata⟩ := RegistrationNativeOwnerRoster.lookup call.after.1.beacons final.1.beacons
      (metadata_path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
        call.after final trailing after) index earlier earlierFound
    have currentSame := Option.some.inj (currentFound.symm.trans found)
    subst current
    exact ⟨call, member, sourceOrigin, leading, trailing, earlier, split, before, called, after, earlierFound, earlierPhase, sameMetadata⟩

private theorem cache_path (initial final : Whole) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Whole))
    (reached : Path impl initial calls final) : RegistrationNativeWorldCache.cache initial.1 ≤ RegistrationNativeWorldCache.cache final.1 :=
  (RegistrationNativePlatformOrdinaryPathState.path setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer reached).1

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
    initialized_path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      ensureInit identityIndex serverKeyId initial startup previous result.2.1 result.2.2 reached index owner pending oneTime found phase
  obtain ⟨receipt⟩ := source_receipt setup checks representation created writer call index pending oneTime origin earlier earlierFound earlierPhase
  exact ⟨call, member, origin, RegistrationNativePlatformPendingTuple.transport setup earlier owner pending oneTime _ _ metadata
    (cache_path setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
      call.after result.2.1 trailing after) receipt⟩

end BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.initialized_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.source_receipt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.source_receipt

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformOrdinaryInitPendingJournal.initialized
