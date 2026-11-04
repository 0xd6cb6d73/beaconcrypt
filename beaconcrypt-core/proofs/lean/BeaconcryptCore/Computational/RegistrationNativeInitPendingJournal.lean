-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativeBundlePhases
import BeaconcryptCore.Computational.RegistrationNativeStageTrace
import BeaconcryptCore.Computational.RegistrationNativeOwnerRoster

/-! Every exact InitSent capability reached from original startup originates at an earlier successful bundle in the same complete native source journal. The receipt keeps the raw Init, one-time scalar and shared cache cut; immutable owner metadata remains attached through the later suffix. The journal is private mathematical analysis state. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeStageTrace (Call Path)
open RegistrationNativePendingFrames (PendingAt)
variable {n : Nat} {ι KemSK Value : Type} {base : OracleSpec ι} {source : RegistrationNativeMldsa.Source}
local notation "Native" => RegistrationNativeExperiment.State n KemSK source

def SourceAt (setup : Setup base KemSK) (wire : RegistrationNativeWire.Wire)
    (call : Call RegistrationNativeRawAdapter.TypedSpec Native)
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes) : Prop :=
  ∃ bytes, call.query = .inr (.bundle index) ∧ HEq call.reply (.ok (some bytes) : RustM (Option Pqxdh.Bytes)) ∧
    RegistrationNativeBundleInitReceipt.Receipt setup wire index call.before call.after bytes ∧
    PendingAt call.after.beacons index pending oneTime

/-- Every actual callback transports an exact pending capability backwards, or is its own successful bundle source. -/
theorem step (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (query : RegistrationNativeRawAdapter.TypedSpec.Domain) (before after : Native)
    (reply : RegistrationNativeRawAdapter.TypedSpec.Range query)
    (supported : (reply, after) ∈ support ((RegistrationNativeExperiment.handler setup checks wire route representation
      created source credential query).run before))
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : PendingAt after.beacons index pending oneTime) :
    PendingAt before.beacons index pending oneTime ∨ SourceAt setup wire ⟨query, before, reply, after⟩ index pending oneTime := by
  by_cases allowed : RegistrationNativePendingFrames.NonBundle query
  · exact Or.inl (RegistrationNativePendingFrames.handler setup checks wire route representation created credential
      query allowed before (reply, after) supported index pending oneTime present)
  · cases query with
    | inl coin => exact False.elim (allowed trivial)
    | inr command => cases command with
      | bundle target =>
        rcases RegistrationNativeBundlePhases.typed_pending setup checks wire route representation created credential target before after reply
            supported index pending oneTime present with old | ⟨bytes, selected, returned, receipt⟩
        · exact Or.inl old
        · subst target
          exact Or.inr ⟨bytes, rfl, heq_of_eq returned, receipt, present⟩
      | _ => exact False.elim (allowed trivial)

/-- The actual chronological path locates an existing pending capability in the initial state or at one of its own earlier successful bundle callbacks. -/
theorem path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (initial final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) initial calls final)
    (index : Nat) (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (present : PendingAt final.beacons index pending oneTime) :
    PendingAt initial.beacons index pending oneTime ∨ ∃ call ∈ calls, SourceAt setup wire call index pending oneTime := by
  revert present
  induction actual with
  | nil state => intro present; exact Or.inl present
  | cons call called rest last following ih =>
    intro present
    rcases ih present with before | ⟨earlier, member, origin⟩
    · rcases step setup checks wire route representation created credential call.query call.before call.after call.reply
        called index pending oneTime before with old | origin
      · exact Or.inl old
      · exact Or.inr ⟨call, List.mem_cons_self, origin⟩
    · exact Or.inr ⟨earlier, List.mem_cons_of_mem _ member, origin⟩

/-- Actual startup has no local Beacon slot, hence supplies no caller-created InitSent capability. -/
theorem start_empty (setup : Setup base KemSK) (ensureInit : StateT Unit ProbComp Bool)
    (identityIndex : Nat) (serverKeyId : U64) (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (supported : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId)) :
    initial.state.beacons = [] := by
  simp only [RegistrationNativeExperiment.start, mem_support_bind_iff] at supported
  obtain ⟨constructed, _constructed, continued⟩ := supported
  cases selected : constructed.1.1 with
  | none => simp only [selected, mem_support_pure_iff] at continued; cases continued
  | some created =>
    simp only [selected, mem_support_bind_iff] at continued
    obtain ⟨generated, _generated, continued⟩ := continued
    cases credential : generated.1 with
    | none => simp only [credential, mem_support_pure_iff] at continued; cases continued
    | some credential =>
      simp only [credential, mem_support_bind_iff] at continued
      obtain ⟨initialized, _initialized, returned⟩ := continued
      cases native : initialized.1 with
      | fail error | div => simp only [native, mem_support_pure_iff] at returned; cases returned
      | ok reply => cases reply with
        | none => simp only [native, mem_support_pure_iff] at returned; cases returned
        | some state =>
          simp only [native, mem_support_pure_iff, Option.some.injEq] at returned
          cases returned
          rfl


private theorem metadata_path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (created : PqxdhLiveServerConstruction.Created Unit) (credential : RegistrationNativeMldsa.Credential source)
    (initial final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation created source credential) initial calls final) :
    RegistrationNativeOwnerRoster.Prefix initial.beacons final.beacons := by
  induction actual with
  | nil state => exact ⟨[], (List.append_nil _).symm⟩
  | cons call called rest last following ih =>
    obtain ⟨leading, first⟩ := RegistrationNativeOwnerRoster.typed_prefix setup checks wire route representation created credential
      call.query call.before (call.reply, call.after) called
    obtain ⟨trailing, later⟩ := ih
    exact ⟨leading ++ trailing, by rw [later, first, List.append_assoc]⟩

/-- Every pending owner on an actual initialized source path has an earlier successful bundle in that same path, with its exact pending capability, one-time scalar, source tuple/cache receipt and immutable metadata. -/
theorem initialized_path (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (final : Native) (calls : List (Call RegistrationNativeRawAdapter.TypedSpec Native))
    (actual : Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
      initial.state calls final)
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : final.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime) :
    ∃ call ∈ calls, SourceAt setup wire call index pending oneTime ∧
      ∃ leading trailing earlier,
        calls = leading ++ call :: trailing ∧
        Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          initial.state leading call.before ∧
        RegistrationNativeStageTrace.Executed
          (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) call ∧
        Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          call.after trailing final ∧
        call.after.beacons[index]? = some earlier ∧ earlier.phase = .initSent pending oneTime ∧
        RegistrationNativeOwnerFields.metadata owner = RegistrationNativeOwnerFields.metadata earlier := by
  rcases path setup checks wire route representation initial.created initial.credential initial.state final calls actual index pending oneTime
      ⟨owner, found, phase⟩ with old | ⟨call, member, origin⟩
  · obtain ⟨earlier, previous, _phase⟩ := old
    have empty := start_empty setup ensureInit identityIndex serverKeyId initial startup
    simp only [empty, List.getElem?_nil, reduceCtorEq] at previous
  · obtain ⟨leading, trailing, split, before, called, after⟩ := actual.member call member
    have sourceOrigin := origin
    obtain ⟨_bytes, _query, _reply, _receipt, earlier, earlierFound, earlierPhase⟩ := origin
    obtain ⟨current, currentFound, sameMetadata⟩ := RegistrationNativeOwnerRoster.lookup call.after.beacons final.beacons
      (metadata_path setup checks wire route representation initial.created initial.credential call.after final trailing after)
      index earlier earlierFound
    have currentSame := Option.some.inj (currentFound.symm.trans found)
    subst current
    exact ⟨call, member, sourceOrigin, leading, trailing, earlier, split, before, called, after, earlierFound, earlierPhase, sameMetadata⟩

/-- The private original source journal derives the earlier bundle provenance directly from actual initialized adaptive execution, without an event, history or partner premise. -/
theorem initialized (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
    (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
    (ensureInit : StateT Unit ProbComp Bool) (identityIndex : Nat) (serverKeyId : U64)
    (initial : RegistrationNativeExperiment.Initial n KemSK source)
    (startup : some initial ∈ support (RegistrationNativeExperiment.start setup source ensureInit identityIndex serverKeyId))
    (work : OracleComp RegistrationNativeRawAdapter.TypedSpec Value)
    (result : Value × (Native × List (Call RegistrationNativeRawAdapter.TypedSpec Native)))
    (supported : result ∈ support ((simulateQ (RegistrationNativeStageTrace.handler
      (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)) work).run (initial.state, [])))
    (index : Nat) (owner : RegistrationNativeBeaconFrontend.Owner source)
    (pending : registration.BeaconPending) (oneTime : PqxdhJointGapDh.ScalarBytes)
    (found : result.2.1.beacons[index]? = some owner) (phase : owner.phase = .initSent pending oneTime) :
    ∃ call ∈ result.2.2, SourceAt setup wire call index pending oneTime ∧
      ∃ leading trailing earlier,
        result.2.2 = leading ++ call :: trailing ∧
        Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          initial.state leading call.before ∧
        RegistrationNativeStageTrace.Executed
          (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential) call ∧
        Path (RegistrationNativeExperiment.handler setup checks wire route representation initial.created source initial.credential)
          call.after trailing result.2.1 ∧
        call.after.beacons[index]? = some earlier ∧ earlier.phase = .initSent pending oneTime ∧
        RegistrationNativeOwnerFields.metadata owner = RegistrationNativeOwnerFields.metadata earlier :=
  initialized_path setup checks wire route representation ensureInit identityIndex serverKeyId initial startup result.2.1 result.2.2
    (RegistrationNativeStageTrace.path _ work initial.state result supported) index owner pending oneTime found phase

end BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.step

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.start_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.start_empty

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.initialized_path' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.initialized_path

/-- info: 'BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.initialized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativeInitPendingJournal.initialized
