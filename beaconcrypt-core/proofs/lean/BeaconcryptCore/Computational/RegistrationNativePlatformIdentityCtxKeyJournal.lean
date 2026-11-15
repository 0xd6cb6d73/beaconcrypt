-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxTypedKeys
import BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxSigningSource
import BeaconcryptCore.Computational.RegistrationNativeFullRegistrationJournal

/-! The actual signing-source journal retains immutable tuples from every captured owner at the same final index. The internal ownership and fresh-handle invariant starts from the literal empty owner roster. Analysis-log erasure retains every real callback reply, private source row, physical cache and P field. -/
open OracleComp OracleSpec CoreModels Aeneas beaconcrypt_core
open Aeneas.Std hiding namespace core alloc
open RustM
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal
open BeaconcryptCore.Refinement
open PqxdhServerAuthExperiment (Setup Checks)
open RegistrationNativeRawAdapter (TypedSpec)
open RegistrationNativeIdentityMetadata (keys key)
open RegistrationNativeStageTrace (Call Path Executed)
open RegistrationNativePlatformIdentityCtxMain (Full interpret)
open RegistrationNativePlatformIdentityCtxLifecycle (Owned)
open RegistrationNativePlatformIdentityCtxSigningLog (Trace)
variable {S V : Type}

abbrev Whole (n : Nat) (KemSK Platform : Type) (source : RegistrationNativeMldsa.Source) :=
  ((RegistrationNativeIdentityMain.State n KemSK source × Platform) × Trace) × RegistrationNativePlatformIdentityCtxSource.State

def drop {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
    (before : Whole n KemSK Platform source) : Full n KemSK Platform source := (before.1.1, before.2)

def owners {n : Nat} {KemSK Platform : Type} {source : RegistrationNativeMldsa.Source}
    (before : Whole n KemSK Platform source) := before.1.1.1.beacons

/-- Erasing just the signing marker restores the literal interpreted callback, including every private backend poststate. -/
theorem query_erasure (joint : PqxdhJointIdentity.Primitives)
    (frontend : QueryImpl TypedSpec (StateT S (OracleComp RegistrationNativePlatformIdentityCtxCompiler.Spec)))
    (query : TypedSpec.Domain) (before : (S × Trace) × RegistrationNativePlatformIdentityCtxSource.State) :
    (fun result => (result.1, (result.2.1.1, result.2.2))) <$>
      (RegistrationNativePlatformIdentityCtxSigningSource.typedHandler joint frontend query).run before =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (RegistrationNativePlatformIdentityCtxSource.implementation joint)
          ((frontend query).run before.1.1)).run before.2 := by
  have erased := RegistrationNativePlatformIdentityCtxSigningTrace.source_erasure joint frontend
    (TypedSpec.query query) before.1 before.2
  simp only [simulateQ_spec_query] at erased
  have mapped := congrArg (fun distribution => (fun result => (result.1.1, (result.1.2, result.2))) <$> distribution) erased
  rw [RegistrationNativePlatformIdentityCtxSigningSource.typedHandler, QueryImpl.Stateful.link_impl_apply_run]
  simpa only [Functor.map_map, Prod.map_def, id_eq, QueryImpl.Stateful.Frame.prod, PFunctor.Lens.State.fst_put, PFunctor.Lens.State.snd_put] using mapped

variable [primitives : AdapterSealPrimitive.Operations]
variable {n : Nat} {I KemSK Platform E : Type} {base : OracleSpec I} {source : RegistrationNativeMldsa.Source}
variable (setup : Setup base KemSK) (checks : Checks) (wire : RegistrationNativeWire.Wire)
variable (route : RawCtxServerRouting.SenderDecoder) (representation : RegistrationServerRoleBackend.ConvertedIdentity setup)
variable (created : PqxdhLiveServerConstruction.Created (Std.Array Std.U8 151#usize)) (credential : RegistrationNativeMldsa.Credential source)
variable (view : RegistrationNativePlatformSourceSeal.KeyView) (failure : primitives.Error)
variable (allocation : RegistrationNativePlatformSourceSeal.Allocation E (StateT Platform ProbComp))
variable (reserveRegistration reservePeer : StateT Platform ProbComp Bool)
variable (reserveFrame : Nat → StateT Platform ProbComp (core.result.Result Unit E)) (erased : commitment.CommitmentTranscript)
variable (helper : QueryImpl (AdapterRecordHelperRequestMonad.Spec E) (StateT Platform ProbComp))
variable (writer : QueryImpl (AdapterRegistrationWriterRequestMonad.Spec E) (StateT Platform ProbComp))
local notation "frontend" => RegistrationNativePlatformIdentityCtxTyped.handler setup checks wire route representation created credential view failure allocation
  reserveRegistration reservePeer reserveFrame erased helper writer
local notation "actual" => RegistrationNativePlatformIdentityCtxSigningSource.typedHandler setup.joint frontend

def Good (joint : PqxdhJointIdentity.Primitives) (before : Whole n KemSK Platform source) : Prop :=
  Owned joint (drop before) ∧ RegistrationNativeIdentityHistorySync.Distinct (owners before)

/-- Every reached logged callback projects to the same literal CTX source callback and complete private poststate. -/
theorem query_support (query : TypedSpec.Domain) (before : Whole n KemSK Platform source)
    (result : TypedSpec.Range query × Whole n KemSK Platform source)
    (reached : result ∈ support ((actual query).run before)) :
    (result.1, drop result.2) ∈ support ((interpret setup.joint (frontend query)).run (drop before)) := by
  have image := Set.mem_image_of_mem (fun result => (result.1, (result.2.1.1, result.2.2))) reached
  rw [← support_map, query_erasure] at image
  exact image

/-- Every actual signing-source callback retains all old key tuples in order. -/
theorem query_prefix (query : TypedSpec.Domain) (before : Whole n KemSK Platform source)
    (result : TypedSpec.Range query × Whole n KemSK Platform source)
    (reached : result ∈ support ((actual query).run before)) :
    keys (owners before) <+: keys (owners result.2) :=
  RegistrationNativePlatformIdentityCtxTypedKeys.handler_prefix setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer query (drop before) (result.1, drop result.2)
    (query_support setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before result reached)

/-- Actual private row ownership and distinct generated handles hold after each failed or successful callback. -/
theorem query_good (query : TypedSpec.Domain) (before : Whole n KemSK Platform source)
    (result : TypedSpec.Range query × Whole n KemSK Platform source) (prior : Good setup.joint before)
    (reached : result ∈ support ((actual query).run before)) : Good setup.joint result.2 := by
  have supported := query_support setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer query before result reached
  exact ⟨RegistrationNativePlatformIdentityCtxTyped.handler_owned setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query (drop before) (result.1, drop result.2) prior.1 supported,
    RegistrationNativePlatformIdentityCtxTypedKeys.handler_distinct setup checks wire route representation created credential view failure allocation
      reserveRegistration reservePeer reserveFrame erased helper writer query (drop before) (result.1, drop result.2) prior.1 prior.2 supported⟩

/-- Every actual source path keeps earlier immutable owner tuples at the same final indices. -/
theorem path_prefix {first last : Whole n KemSK Platform source} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    (path : Path actual first calls last) : keys (owners first) <+: keys (owners last) := by
  induction path with
  | nil => exact List.prefix_rfl
  | cons call called rest last following ih =>
    exact (query_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer call.query call.before (call.reply, call.after) called).trans ih

/-- Distinctness and private ownership are internal path invariants, with no public-key injectivity condition. -/
theorem path_good {first last : Whole n KemSK Platform source} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    (path : Path actual first calls last) (prior : Good setup.joint first) : Good setup.joint last := by
  induction path with
  | nil => exact prior
  | cons call called rest last following ih =>
    exact ih (query_good setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer call.query call.before (call.reply, call.after) prior called)

omit primitives in
private theorem prefix_at {T : Type} {first last : List T} (prefixKeys : first <+: last) (index : Nat) (value : T)
    (found : first[index]? = some value) : last[index]? = some value := by
  obtain ⟨tail, same⟩ := prefixKeys
  rw [← same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- An earlier captured owner is still present at its original final index with exactly the same credential and fixed prekey/PQ bytes. -/
theorem captured_owner {first last : Whole n KemSK Platform source} {calls : List (Call TypedSpec (Whole n KemSK Platform source))}
    (path : Path actual first calls last) (call : Call TypedSpec (Whole n KemSK Platform source)) (member : call ∈ calls)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (found : (owners call.before)[index]? = some owner) :
    ∃ finalOwner, (owners last)[index]? = some finalOwner ∧ key finalOwner = key owner := by
  obtain ⟨leading, trailing, _split, _prefixPath, called, suffixPath⟩ := path.member call member
  have complete : Path actual call.before (call :: trailing) last := .cons call called trailing last suffixPath
  have retained := path_prefix setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer complete
  have earlier : (keys (owners call.before))[index]? = some (key owner) := by
    simp only [keys, List.getElem?_map, found, Option.map_some]
  have finalFound := prefix_at retained index (key owner) earlier
  simp only [keys, List.getElem?_map] at finalFound
  cases selected : (owners last)[index]? with
  | none => simp only [selected, Option.map_none] at finalFound; cases finalFound
  | some finalOwner =>
    refine ⟨finalOwner, rfl, ?_⟩
    simpa only [selected, Option.map_some, Option.some.injEq] using finalFound

/-- Literal empty-owner initialization yields final handle distinctness for the complete full-compiler source run. -/
theorem full_distinct (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : Whole n KemSK Platform source) (empty : owners before = [])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, []))) :
    RegistrationNativeIdentityHistorySync.Distinct (owners result.2.2.1) := by
  have path := RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work before result reached
  apply (path_good setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer path ?_).2
  constructor
  · change RegistrationNativeIdentityRealization.Owned setup.joint _ (owners before)
    rw [empty]
    intro owner member
    cases member
  · simp only [RegistrationNativeIdentityHistorySync.Distinct, RegistrationNativeIdentityHistorySync.handles, empty, List.map_nil, List.nodup_nil]

/-- Every earlier captured owner in the actual full raw ledger execution has its literal immutable tuple at the same final owner index. -/
theorem full_captured (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : Whole n KemSK Platform source)
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, [])))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (member : call ∈ result.2.2.2)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (found : (owners call.before)[index]? = some owner) :
    ∃ finalOwner, (owners result.2.2.1)[index]? = some finalOwner ∧ key finalOwner = key owner :=
  captured_owner setup checks wire route representation created credential view failure allocation reserveRegistration reservePeer reserveFrame erased helper writer
    (RegistrationNativeFullRegistrationJournal.path setup.source.crypto wire serverKeyId bounds actual mode work before result reached) call member index owner found

/-- A final owner with the captured generated handle has exactly that earlier fixed tuple, without requiring distinct public keys. -/
theorem full_same_handle (serverKeyId : Std.U64) (bounds : PqxdhDeploymentInterface.FreshBounds)
    (mode : PqxdhDeploymentInterface.Mode) (work : OracleComp (RegistrationNativeInterface.ModeSpec mode) V)
    (before : Whole n KemSK Platform source) (empty : owners before = [])
    (result : V × (RegistrationNativeLedger.State × (Whole n KemSK Platform source × List (Call TypedSpec (Whole n KemSK Platform source)))))
    (reached : result ∈ support (RegistrationNativeFullCompiler.run setup.source.crypto wire serverKeyId bounds
      (RegistrationNativeStageTrace.handler actual) mode work (before, [])))
    (call : Call TypedSpec (Whole n KemSK Platform source)) (member : call ∈ result.2.2.2)
    (index : Nat) (owner : RegistrationNativeIdentityFrontend.Owner source) (found : (owners call.before)[index]? = some owner)
    (finalOwner : RegistrationNativeIdentityFrontend.Owner source) (finalMember : finalOwner ∈ owners result.2.2.1)
    (sameHandle : finalOwner.identity.handle = owner.identity.handle) : key finalOwner = key owner := by
  obtain ⟨stored, storedAt, fields⟩ := full_captured setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before result reached call member index owner found
  have unique := full_distinct setup checks wire route representation created credential view failure allocation
    reserveRegistration reservePeer reserveFrame erased helper writer serverKeyId bounds mode work before empty result reached
  have handleEq : finalOwner.identity.handle = stored.identity.handle :=
    sameHandle.trans (congrArg (fun tuple => tuple.1.handle) fields).symm
  have equal := List.inj_on_of_nodup_map unique finalMember (List.mem_of_getElem? storedAt) handleEq
  exact equal ▸ fields

end BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_erasure

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_support

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.query_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.path_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.path_prefix

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.path_good' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.path_good

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.captured_owner' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.captured_owner

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_distinct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_distinct

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_captured' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_captured

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_same_handle' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformIdentityCtxKeyJournal.full_same_handle
