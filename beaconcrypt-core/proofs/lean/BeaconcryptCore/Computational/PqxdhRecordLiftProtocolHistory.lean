-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftWorldProvenance

/-! Source control and hidden sealing history under arbitrary permitted private replies. The operational service interface remains unchanged; cryptographic byte aliases and the selected CTX stop join are separate. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory
open PqxdhRecordLiftChainState PqxdhRecordLiftChainTable PqxdhRecordLiftMaterialTable
open PqxdhRecordLiftChainCompiler PqxdhRecordLiftChainCoordinates
variable {Slot Context Plaintext SealContext Output : Type}

/-- Every permitted source opening reply preserves the complete local source certificate and send coordinate, before any private interpretation is selected. -/
theorem receive_facts (entry : LabeledKernel Slot) (target : Std.U64) (context : Context)
    (certified : Certified entry) (effect : Effect Slot Context)
    (tracked : Tracked entry context effect) (admitted : PqxdhFirstRecordReplay.Admitted entry target effect)
    (sender : FutureSendAligned effect) (attributed : EffectAttributed entry.receive_chain effect)
    (result : LabeledKernel Slot × core.option.Option Plaintext)
    (supported : result ∈ support (PqxdhRecordLiftOpaqueDrivers.receiveProgram
      (SealContext := SealContext) (Output := Output) effect)) :
    Certified result.1 ∧ ReceiveCoordinates entry result.1 := by
  generalize hdepth : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect with
  | h depth ih =>
    cases effect with
    | rejected original prior =>
      simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rw [show original = entry from tracked.1]
      exact ⟨certified, rfl, 0, by omega, by simp [advance]⟩
    | kdfRequested pending =>
      simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, mem_support_bind_iff] at supported
      obtain ⟨_, _, continued⟩ := supported
      exact ih _ (hdepth ▸ RawCtxChainReceive.normalResume_rank pending (advance pending.request 1, pending.request))
        _ (resume_tracked entry context pending pending.request tracked)
        (PqxdhFirstRecordReplay.resume_admitted entry target pending (advance pending.request 1, pending.request) admitted)
        (resume_future_send pending)
        (resume_source_attributed entry context target pending certified.2.1 tracked admitted attributed.1 attributed.2)
        continued rfl
    | openRequested pending =>
      simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, mem_support_bind_iff] at supported
      obtain ⟨reply, _, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      have coordinates := finish_coordinates entry context target pending tracked admitted reply
      have origins := receive_origins entry _ coordinates
      refine ⟨⟨?_, finish_aligned entry context target pending certified.2.1 certified.1.capacity
        tracked admitted sender reply, ?_⟩, coordinates⟩
      · cases reply with
        | none =>
            rw [PqxdhFirstRecordReplay.finish_none]
            simpa only [admitted.1] using certified.1
        | some plaintext =>
            exact (PqxdhFirstRecordReplay.finish_some entry target pending plaintext
              admitted.1 admitted.2 certified.1).2.1
      · apply (attributed_reanchor entry.receive_chain _ origins.2.1 origins.2.2 _).mpr
        apply finish_property (Attributed entry.receive_chain) pending target
          (by simpa only [admitted.1] using admitted.2) attributed.1
        cases shape : pending.prepared with
        | PreparedReceiveCachedCase cached => trivial
        | PreparedReceiveFutureCase future =>
            simp only [EffectAttributed, shape] at attributed
            exact attributed.2.1

/-- Actual source admission supplies all tracking facts; arbitrary opening replies retain source certification and the complete send coordinate. -/
theorem admitted_receive_facts (entry : LabeledKernel Slot) (target : Std.U64) (context : Context)
    (certified : Certified entry) (result : LabeledKernel Slot × core.option.Option Plaintext)
    (supported : result ∈ support (PqxdhRecordLiftOpaqueDrivers.admittedReceive
      (SealContext := SealContext) (Output := Output) entry target context)) :
    Certified result.1 ∧ ReceiveCoordinates entry result.1 :=
  receive_facts entry target context certified _ (begin_tracked entry context target)
    (PqxdhFirstRecordReplay.begin_admitted entry target context certified.1.capacity)
    (begin_future_send entry target context)
    (begin_attributed entry.receive_chain entry certified.2.2 target context) result supported

/-- The opaque source send advances its own coordinate before an arbitrary writer reply and preserves the entire certified receive side. -/
theorem send_facts (entry : LabeledKernel Slot) (context : SealContext) (certified : Certified entry)
    (start : Start Slot SealContext) (tracked : SendTracked entry context start)
    (result : LabeledKernel Slot × Option Output)
    (supported : result ∈ support (PqxdhRecordLiftOpaqueDrivers.sendProgram
      (OpenContext := Context) (Plaintext := Plaintext) start)) :
    Certified result.1 ∧ SendCoordinates entry result.1 := by
  cases start with
  | exhausted original prior =>
      simp only [PqxdhRecordLiftOpaqueDrivers.sendProgram, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rw [show original = entry from tracked.1]
      exact ⟨certified, rfl, rfl, 0, by omega, by simp [advance]⟩
  | requested pending =>
      simp only [PqxdhRecordLiftOpaqueDrivers.sendProgram, mem_support_bind_iff] at supported
      obtain ⟨_, _, reply, _, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      have aligned := send_ready_aligned entry context pending pending.request certified.2.1 tracked
      rw [send_ready_kernel entry context pending pending.request tracked] at aligned ⊢
      refine ⟨⟨?_, aligned, certified.2.2⟩, rfl, rfl, 1, le_rfl, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa only [control.RatchetState.Wf, tracked.2.2.2.2.2] using certified.1.capacity
      · simpa only [tracked.2.2.2.2.2] using certified.1.positive
      · simpa only [tracked.2.2.2.2.2, tracked.2.2.2.2.1] using certified.1.past
      · simpa only [tracked.2.2.2.2.2] using certified.1.unique

/-- Actual exhaustion admission supplies send tracking without a callback or nonwrapping assumption. -/
theorem admitted_send_facts (entry : LabeledKernel Slot) (context : SealContext)
    (certified : Certified entry) (result : LabeledKernel Slot × Option Output)
    (supported : result ∈ support (PqxdhRecordLiftOpaqueDrivers.admittedSend
      (OpenContext := Context) (Plaintext := Plaintext) entry context)) :
    Certified result.1 ∧ SendCoordinates entry result.1 :=
  send_facts entry context certified _ (send_begin_tracked entry context) result supported

variable {n : Nat}

/-- Lifting the actual local requests into the whole private interface does not introduce any source result unavailable under its original typed replies. -/
theorem local_support {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.LocalSpec n) Result) (result : Result)
    (supported : result ∈ support (simulateQ PqxdhRecordLiftProtocol.localLift client)) :
    result ∈ support client := by
  induction client using OracleComp.inductionOn generalizing result with
  | pure value => simpa only [simulateQ_pure, support_pure, Set.mem_singleton_iff] using supported
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      rw [mem_support_bind_iff]
      exact ⟨reply, mem_support_query query reply, ih reply result continued⟩

open PqxdhRecordLiftInterface
open PqxdhRecordLiftWorldCompiler (StoredKernel Owner KernelOrigin)
open PqxdhRecordLiftWorldProvenance

/-- The control-only local relation retains role orientation, actual origin tags and every prior hidden sender's nondecreasing position. -/
def KernelStep (role : Role) (before after : StoredKernel n) : Prop :=
  Oriented role after ∧ after.origin = before.origin ∧ StoredAhead before after

/-- Returning the same stored kernel preserves all local structural control facts. -/
theorem kernelStep_refl (role : Role) (stored : StoredKernel n) (oriented : Oriented role stored) :
    KernelStep role stored stored := ⟨oriented, rfl, storedAhead_refl stored⟩

/-- Every permitted opening reply preserves the installed role and tag and cannot rewind a hidden sender. Known replies stay wrapped as known kernels. -/
theorem kernel_receive (role : Role) (stored : StoredKernel n) (target : Std.U64)
    (context : RawCtxWholeOwner.OpenContext) (oriented : Oriented role stored)
    (result : StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.kernelReceive stored target context)) :
    KernelStep role stored result.1 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact ⟨trivial, rfl, by intro slot old impossible; cases impossible⟩
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have facts := admitted_receive_facts kernel target context oriented.1 inner
        (local_support _ inner member)
      have coordinates := receive_origins kernel inner.1 facts.2
      refine ⟨⟨facts.1, ⟨?_, ?_⟩, ?_, ?_⟩, rfl, ?_⟩
      · exact (congrArg (fun coordinate => coordinate.slot) coordinates.1).trans oriented.2.1.1
      · exact coordinates.2.1.trans oriented.2.1.2
      · exact (congrArg (fun coordinate => coordinate.direction) coordinates.1).trans oriented.2.2.1
      · exact coordinates.2.2.trans oriented.2.2.2
      · intro oldSlot old equal
        cases equal
        exact ⟨inner.1, rfl, by rw [coordinates.1]⟩

/-- Every permitted writer reply retains physical direction and installation origin; hidden send progress precedes the reply. -/
theorem kernel_send (role : Role) (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext)
    (oriented : Oriented role stored) (result : StoredKernel n × Option RawCtxSourceSend.Encrypted)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.kernelSend stored context)) :
    KernelStep role stored result.1 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, support_map] at supported
      obtain ⟨inner, _, rfl⟩ := supported
      exact ⟨trivial, rfl, by intro slot old impossible; cases impossible⟩
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, bind_pure_comp, support_map] at supported
      obtain ⟨inner, member, rfl⟩ := supported
      have facts := admitted_send_facts kernel context oriented.1 inner (local_support _ inner member)
      have coordinates := send_origins kernel inner.1 facts.2
      refine ⟨⟨facts.1, ⟨?_, ?_⟩, ?_, ?_⟩, rfl, ?_⟩
      · exact coordinates.2.2.1.trans oriented.2.1.1
      · exact (congrArg (fun coordinate => coordinate.slot) coordinates.1).trans oriented.2.1.2
      · exact coordinates.2.2.2.trans oriented.2.2.1
      · exact (congrArg (fun coordinate => coordinate.direction) coordinates.1).trans oriented.2.2.2
      · intro oldSlot old equal
        cases equal
        obtain ⟨count, _, advanced⟩ := facts.2.2.2
        exact ⟨inner.1, rfl, by simp only [advanced, advance]; omega⟩

/-- Empty sends retain control; every nonempty source send retains its role, tag and persistent sender progress. -/
theorem owner_send (role : Role) (sender : Std.U64) (plaintext : Pqxdh.Bytes) (owner : Owner n)
    (oriented : Oriented role owner.kernel) (result : Option RawCtxSourceSend.Encrypted × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerSend sender plaintext owner)) :
    KernelStep role owner.kernel result.2.kernel := by
  simp only [PqxdhRecordLiftProtocol.ownerSend] at supported
  split_ifs at supported with empty
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact kernelStep_refl role owner.kernel oriented
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact kernel_send role owner.kernel _ oriented inner member

/-- Parser and frame rejection retain the stored kernel; arbitrary successful or failed opening replies preserve hidden structural control. -/
theorem owner_receive (role : Role) (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes)
    (owner : Owner n) (oriented : Oriented role owner.kernel)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerReceive decode raw owner)) :
    KernelStep role owner.kernel result.2.kernel := by
  simp only [PqxdhRecordLiftProtocol.ownerReceive] at supported
  repeat' split at supported
  case h_2.isTrue =>
    simp only [bind_pure_comp, support_map] at supported
    obtain ⟨inner, member, rfl⟩ := supported
    exact kernel_receive role owner.kernel _ _ oriented inner member
  all_goals simp only [support_pure, Set.mem_singleton_iff] at supported
  all_goals subst result
  all_goals exact kernelStep_refl role owner.kernel oriented

/-- Both actual selected-owner source commands preserve the installed structural record control. -/
theorem owner_step (role : Role) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (oriented : Oriented role owner.kernel)
    (result : RawCtxMixedOwner.SourceSpec.Range query × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerStep sender decode query owner)) :
    KernelStep role owner.kernel result.2.kernel := by
  cases query with
  | inl plaintext => exact owner_send role sender plaintext owner oriented result supported
  | inr raw => exact owner_receive role decode raw owner oriented result supported

/-- A literal publication callback changes no source control and imposes no condition on private writer logs. -/
theorem owner_run (role : Role) (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64)
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (owner : Owner n) (oriented : Oriented role owner.kernel)
    (result : RawCtxMixedOwner.SourceSpec.Range query × Owner n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner)) :
    KernelStep role owner.kernel result.2.kernel := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, mem_support_bind_iff] at supported
  obtain ⟨inner, member, _, _, finished⟩ := supported
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  exact owner_step role sender decode query owner oriented inner member

/-- This structural embedding reuses predicates that read only server, owners and used-role bits. Its empty private fields are never interpreted as native secrets or a source execution. -/
def view (control : PqxdhRecordLiftProtocol.Control n) : PqxdhRecordLiftWorldCompiler.State n :=
  PqxdhRecordLiftProtocol.join control PqxdhRecordLiftProtocol.initialPrivate

def Safe (control : PqxdhRecordLiftProtocol.Control n) : Prop :=
  Roles (view control) ∧ Provenance (view control)

def Step (before after : PqxdhRecordLiftProtocol.Control n) : Prop :=
  Safe after ∧ Forward (view before) (view after)

/-- Computed origins and used-role bits determine provenance independently of all private fields. -/
theorem provenance_same (before after : PqxdhRecordLiftWorldCompiler.State n)
    (origins : PqxdhRecordLiftWorldCompiler.origins after = PqxdhRecordLiftWorldCompiler.origins before)
    (used : after.used = before.used) (good : Provenance before) : Provenance after := by
  refine ⟨?_, origins ▸ good.2⟩
  change (∀ keyId slot, (PqxdhRecordLiftWorldCompiler.origins after).peers keyId = some slot → after.used slot .server = true) ∧
    (∀ owner slot, (PqxdhRecordLiftWorldCompiler.origins after).owners owner = some slot → after.used slot .beacon = true)
  rw [origins, used]
  exact good.1

/-- Control fields outside actual stored records and used-role bits cannot alter the structural invariants or sender positions. -/
theorem step_frame (before after : PqxdhRecordLiftProtocol.Control n)
    (server : after.server = before.server) (owners : after.owners = before.owners)
    (used : after.used = before.used) (safe : Safe before) : Step before after := by
  have roles : Roles (view after) := by
    change (∀ server, after.server = some server → ∀ keyId peer, server.peers keyId = some peer → Oriented .server peer.kernel) ∧
      (∀ phase ∈ after.owners, match phase with | .inactive _ => True | .established _ kernel => Oriented .beacon kernel)
    rw [server, owners]
    exact safe.1
  exact ⟨⟨roles, provenance_same (view before) (view after) (origins_frame (view before) (view after) server owners) used safe.2⟩,
    forward_frame (view before) (view after) server owners⟩

/-- Returning the same actual control preserves its derived safety and persistent sender relation. -/
theorem step_refl (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control) : Step control control :=
  step_frame control control rfl rfl rfl safe

/-- Complete Server peer putback preserves all untouched handles, exact origin tags and derived role invariants for arbitrary local replies. -/
theorem server_store (control : PqxdhRecordLiftProtocol.Control n)
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (keyId : Std.U64) (peer : PqxdhRecordLiftWorldCompiler.Peer n) (present : server.peers keyId = some peer)
    (next : StoredKernel n) (rawAttempts : Nat) (safe : Safe control) (kernel : KernelStep .server peer.kernel next) :
    Step control { control with server := some { server with peers := Function.update server.peers keyId (some { peer with kernel := next }), rawAttempts := rawAttempts } } := by
  have roles := roles_server_store
    { view control with server := some { server with rawAttempts := rawAttempts } }
    { server with rawAttempts := rawAttempts } rfl keyId { peer with kernel := next }
    (roles_serverRaw (view control) server existing rawAttempts safe.1) kernel.1
  refine ⟨⟨roles, provenance_same (view control) _ ?_ rfl safe.2⟩, ?_⟩
  · apply congrArg₂ PqxdhRecordLiftOrigins.Origins.mk
    · funext target
      by_cases same : target = keyId
      · subst target
        simp only [view, PqxdhRecordLiftProtocol.join, existing,
          Option.bind_some, Function.update_self, present, kernel.2.1]
      · simp only [view, PqxdhRecordLiftProtocol.join, existing,
          Option.bind_some, Function.update_of_ne same]
    · rfl
  · apply forward_server_store (view control) server existing keyId { peer with kernel := next } _ rawAttempts
    intro old found
    have same := Option.some.inj (found.symm.trans present)
    subst old
    exact kernel.2.2

/-- Changing only the Server raw-attempt counter retains all physical records and provenance. -/
theorem server_raw (control : PqxdhRecordLiftProtocol.Control n)
    (server : PqxdhRecordLiftWorldCompiler.Server n) (existing : control.server = some server)
    (rawAttempts : Nat) (safe : Safe control) :
    Step control { control with server := some { server with rawAttempts := rawAttempts } } := by
  refine ⟨⟨roles_serverRaw (view control) server existing rawAttempts safe.1,
    provenance_same (view control) _ ?_ rfl safe.2⟩, forward_serverRaw (view control) server existing rawAttempts⟩
  simp only [PqxdhRecordLiftWorldCompiler.origins, view, PqxdhRecordLiftProtocol.join, existing, Option.bind_some]

/-- Beacon putback retains the actual owner index, unchanged origin tag and every earlier physical sender. -/
theorem beacon_store (control : PqxdhRecordLiftProtocol.Control n) (owner : Nat)
    (shell : BeaconShell) (stored next : StoredKernel n)
    (present : control.owners[owner]? = some (.established shell stored))
    (rawAttempts : Nat) (safe : Safe control) (kernel : KernelStep .beacon stored next) :
    Step control { control with owners := control.owners.set owner (.established shell next), ownerRaw := Function.update control.ownerRaw owner rawAttempts } := by
  refine ⟨⟨roles_owner_store (view control) owner (.established shell next) safe.1 kernel.1,
    provenance_same (view control) _ ?_ rfl safe.2⟩, ?_⟩
  · exact origins_owner_same (view control) owner (.established shell stored) (.established shell next) present kernel.2.1
  · apply forward_owner_store (view control) owner (.established shell next)
    intro oldShell oldKernel found
    have same := Option.some.inj (found.symm.trans present)
    cases same
    exact ⟨shell, next, rfl, kernel.2.2⟩

/-- Every literal Server routing, parser and selected-owner path preserves global structural control for arbitrary private replies. -/
theorem server_step (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (result : RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.serverStep decode route query control)) :
    Step control result.2 := by
  cases existing : control.server with
  | none =>
      cases query <;>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact step_refl control safe
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact step_refl control safe
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, bind_pure_comp, support_map] at supported
              obtain ⟨inner, member, rfl⟩ := supported
              exact server_store control server existing keyId peer selected inner.2.kernel inner.2.rawAttempts safe
                (owner_run .server _ server.sender decode (.inl plaintext) _
                  (safe.1.1 server existing keyId peer selected) inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact server_raw control server existing _ safe
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact server_raw control server existing _ safe
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, bind_pure_comp, support_map] at supported
                  obtain ⟨inner, member, rfl⟩ := supported
                  exact server_store control server existing keyId peer selected inner.2.kernel inner.2.rawAttempts safe
                    (owner_run .server _ server.sender decode (.inr raw) _
                      (safe.1.1 server existing keyId peer selected) inner member)

/-- Every literal Beacon routing, phase, parser and selected-owner path preserves global structural control for arbitrary private replies. -/
theorem beacon_step (decode : RawCtxReceive.FrameDecoder) (owner : Nat)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (result : RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.beaconStep decode owner query control)) :
    Step control result.2 := by
  cases selected : control.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, selected, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact step_refl control safe
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [PqxdhRecordLiftProtocol.beaconStep, selected, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact step_frame control _ rfl rfl rfl safe
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, selected, bind_pure_comp, support_map] at supported
          obtain ⟨inner, member, rfl⟩ := supported
          exact beacon_store control owner shell kernel inner.2.kernel selected inner.2.rawAttempts safe
            (owner_run .beacon _ shell.identityKeyId decode query _
              (safe.1.2 _ (List.mem_of_getElem? selected)) inner member)

/-- Private allocation returns only unit; the actual control initializer determines both the role and literal origin. -/
theorem resolve_facts (role : Role) (ref : KernelRef n) (result : StoredKernel n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.resolve role ref)) :
    Oriented role result ∧ result.origin = PqxdhRecordLiftOrigins.origin ref := by
  cases ref with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.resolve, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨trivial, rfl⟩
  | hidden slot =>
      simp only [PqxdhRecordLiftProtocol.resolve, mem_support_bind_iff] at supported
      obtain ⟨_, _, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact ⟨labeledKernel_oriented role slot, rfl⟩

/-- The structural view retains the exact used-role update and changes no hidden material. -/
theorem view_markUsed (control : PqxdhRecordLiftProtocol.Control n) (role : Role) (ref : KernelRef n) :
    view (PqxdhRecordLiftProtocol.markUsed control role ref) =
      PqxdhRecordLiftWorldCompiler.markUsed (view control) role ref := by
  cases ref <;> rfl

/-- Existing source annotation lemmas apply to control-only storage when their reply and admission equations have been derived from the actual command. -/
theorem provenance_annotate (query : (WorldSpec n).Domain) (reply : (WorldSpec n).Range query)
    (before after : PqxdhRecordLiftProtocol.Control n) (good : Provenance (view before))
    (origins : PqxdhRecordLiftWorldCompiler.origins (view after) =
      PqxdhRecordLiftOrigins.annotate query reply (PqxdhRecordLiftWorldCompiler.origins (view before)))
    (persistent : PqxdhRecordLiftWorld.UsesPersist (PqxdhRecordLiftWorldCompiler.world (view before))
      (PqxdhRecordLiftWorldCompiler.world (view after)))
    (marked : PqxdhRecordLiftOrigins.MarkedReply query reply (PqxdhRecordLiftWorldCompiler.world (view after)))
    (unused : PqxdhRecordLiftOrigins.UnusedReply query reply (PqxdhRecordLiftWorldCompiler.world (view before))) :
    Provenance (view after) := by
  change PqxdhRecordLiftOrigins.Marked (PqxdhRecordLiftWorldCompiler.world (view after), _) ∧ _
  rw [origins]
  exact ⟨PqxdhRecordLiftOrigins.annotate_marked query reply _ _ _ good.1 persistent marked,
    PqxdhRecordLiftOrigins.annotate_unique query reply _ _ good.1 good.2 unused⟩

/-- A successful actual Server install uses a vacant handle and an unused role, so arbitrary allocation behavior cannot replace a prior sender or duplicate its hidden origin. -/
theorem install_server (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (result : Bool × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installServer keyId identity ref control)) :
    Step control result.2 := by
  cases existing : control.server with
  | none =>
      simp only [PqxdhRecordLiftProtocol.installServer, existing, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact step_refl control safe
  | some server =>
      simp only [PqxdhRecordLiftProtocol.installServer, existing] at supported
      split_ifs at supported with admitted
      · simp only [bind_pure_comp, support_map] at supported
        obtain ⟨stored, member, rfl⟩ := supported
        have resolved := resolve_facts .server ref stored member
        have markedServer : (PqxdhRecordLiftProtocol.markUsed control .server ref).server = some server := by
          cases ref <;> exact existing
        have roles : Roles (view (PqxdhRecordLiftProtocol.markUsed control .server ref)) := by
          rw [view_markUsed]
          exact markUsed_roles (view control) .server ref safe.1
        refine ⟨⟨roles_server_store _ server markedServer keyId ⟨identity, stored⟩ roles resolved.1, ?_⟩, ?_⟩
        · apply provenance_annotate (.inr (.inl (.inr (.installServer keyId identity ref)))) true control _ safe.2
          · have originEq := origins_server_store (view (PqxdhRecordLiftProtocol.markUsed control .server ref))
              server markedServer keyId ⟨identity, stored⟩
            have markedOrigins : PqxdhRecordLiftWorldCompiler.origins (view (PqxdhRecordLiftProtocol.markUsed control .server ref)) =
                PqxdhRecordLiftWorldCompiler.origins (view control) := by cases ref <;> rfl
            simp only [resolved.2, markedOrigins] at originEq
            simpa only [PqxdhRecordLiftOrigins.annotate, ite_true, view, PqxdhRecordLiftProtocol.join] using originEq
          · apply marker_update_persists (view control) _ .server ref true
            cases ref <;> rfl
          · cases ref with
            | known kernel => trivial
            | hidden slot =>
                intro _
                change Function.update control.used slot (Function.update (control.used slot) .server true) slot .server = true
                simp only [Function.update_self]
          · cases ref with
            | known kernel => trivial
            | hidden slot => exact fun _ => admitted.2
        · apply forward_trans (view control) (view (PqxdhRecordLiftProtocol.markUsed control .server ref))
          · rw [view_markUsed]
            exact markUsed_forward (view control) .server ref
          · apply forward_server_store _ server markedServer keyId ⟨identity, stored⟩ _ server.rawAttempts
            intro peer present
            have impossible := present.symm.trans admitted.1
            cases impossible
      · simp only [support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact step_refl control safe

/-- A successful actual Beacon install consumes an unused role at an inactive init-sent index; it cannot reset a prior sender or duplicate a hidden origin. -/
theorem install_beacon (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (result : Bool × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.installBeacon owner shell ref control)) :
    Step control result.2 := by
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split_ifs at supported with admitted
  · simp only [bind_pure_comp, support_map] at supported
    obtain ⟨stored, member, rfl⟩ := supported
    have resolved := resolve_facts .beacon ref stored member
    have markedOwners : (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref)).owners = control.owners := by
      cases ref <;> rfl
    have roles : Roles (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref)) := by
      rw [view_markUsed]
      exact markUsed_roles (view control) .beacon ref safe.1
    change Step control { PqxdhRecordLiftProtocol.markUsed control .beacon ref with owners := control.owners.set owner (.established shell stored) }
    rw [← markedOwners]
    refine ⟨⟨roles_owner_store _ owner (.established shell stored) roles resolved.1, ?_⟩, ?_⟩
    · apply provenance_annotate (.inr (.inl (.inr (.installBeacon owner shell ref)))) true control _ safe.2
      · have bound : owner < (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref)).owners.length := by
          rw [markedOwners]
          exact (List.getElem?_eq_some_iff.mp admitted.1).1
        have originEq := origins_owner_store (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref))
          owner (.established shell stored) bound
        have markedOrigins : PqxdhRecordLiftWorldCompiler.origins (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref)) =
            PqxdhRecordLiftWorldCompiler.origins (view control) := by cases ref <;> rfl
        simp only [PqxdhRecordLiftWorldCompiler.Phase.origin, resolved.2, markedOrigins] at originEq
        simpa only [PqxdhRecordLiftOrigins.annotate, ite_true, view, PqxdhRecordLiftProtocol.join] using originEq
      · apply marker_update_persists (view control) _ .beacon ref true
        cases ref <;> rfl
      · cases ref with
        | known kernel => trivial
        | hidden slot =>
            intro _
            change Function.update control.used slot (Function.update (control.used slot) .beacon true) slot .beacon = true
            simp only [Function.update_self]
      · cases ref with
        | known kernel => trivial
        | hidden slot => exact fun _ => admitted.2
    · apply forward_trans (view control) (view (PqxdhRecordLiftProtocol.markUsed control .beacon ref))
      · rw [view_markUsed]
        exact markUsed_forward (view control) .beacon ref
      · apply forward_owner_store
        intro oldShell oldKernel present
        rw [markedOwners] at present
        have impossible := Option.some.inj (present.symm.trans admitted.1)
        cases impossible
  · simp only [support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact step_refl control safe

/-- Source Server construction introduces only caller-known peers and never resets an existing Server. -/
theorem initialize_server (created : PqxdhLiveServerConstruction.Created Unit)
    (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (result : Unit × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.initializeServer created control)) :
    Step control result.2 := by
  have source : (result.1, view result.2) ∈ support
      ((PqxdhRecordLiftWorldCompiler.initializeServer created).run (view control)) := by
    cases found : control.server <;>
      simp only [PqxdhRecordLiftProtocol.initializeServer, found, support_pure, Set.mem_singleton_iff] at supported <;>
      subst result <;>
      simp only [PqxdhRecordLiftWorldCompiler.initializeServer, StateT.run, view, PqxdhRecordLiftProtocol.join,
        found, support_pure, Set.mem_singleton_iff]
  exact ⟨⟨initialize_roles created (view control) safe.1 _ source,
    provenance_same (view control) _ (initialize_origins created (view control) _ source)
      (by cases found : control.server <;>
        simp only [PqxdhRecordLiftProtocol.initializeServer, found, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> rfl) safe.2⟩,
    initialize_forward created (view control) _ source⟩

/-- A lifted private request returns its literal reply while retaining every source control field. -/
theorem lift_control (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (control : PqxdhRecordLiftProtocol.Control n)
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) :
      PqxdhRecordLiftProtocol.Client n _).run control)) : result.2 = control := by
  change result ∈ support ((fun reply => (reply, control)) <$> ((PqxdhRecordLiftProtocol.ServiceSpec n).query query : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _)) at supported
  simp only [support_map] at supported
  obtain ⟨reply, _, rfl⟩ := supported
  rfl

/-- All frozen capability guards preserve structural safety and earlier senders under arbitrary private replies. -/
theorem capability (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (result : (CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.capability query control)) : Step control result.2 := by
  cases query with
  | installServer keyId identity ref => exact install_server keyId identity ref control safe result supported
  | installBeacon owner shell ref => exact install_beacon owner shell ref control safe result supported
  | hash bytes =>
      rw [lift_control (.hash bytes) control result supported]
      exact step_refl control safe
  | peerPresent keyId =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact step_refl control safe
  | ownerPresent owner =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact step_refl control safe
  | appendOwner sender pin phase =>
      simp only [PqxdhRecordLiftProtocol.capability, support_pure, Set.mem_singleton_iff] at supported
      subst result
      refine ⟨⟨roles_append (view control) phase safe.1, ?_⟩, forward_append (view control) phase⟩
      apply provenance_annotate (.inr (.inl (.inr (.appendOwner sender pin phase)))) control.owners.length control _ safe.2
      · exact origins_append (view control) phase
      · intro slot role marked
        exact marked
      · trivial
      · trivial
  | advanceOwner owner phase =>
      simp only [PqxdhRecordLiftProtocol.capability] at supported
      cases found : control.owners[owner]? with
      | none =>
          simp only [found, support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact step_refl control safe
      | some prior =>
          cases prior with
          | established shell kernel =>
              simp only [found, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact step_refl control safe
          | inactive before =>
              simp only [found] at supported
              split_ifs at supported with legal
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                refine ⟨⟨roles_owner_store (view control) owner (.inactive phase) safe.1 trivial,
                  provenance_same (view control) _ (origins_owner_same (view control) owner (.inactive before) (.inactive phase) found rfl) rfl safe.2⟩, ?_⟩
                apply forward_owner_store (view control) owner (.inactive phase)
                intro oldShell oldKernel present
                have impossible := Option.some.inj (present.symm.trans found)
                cases impossible
              · simp only [support_pure, Set.mem_singleton_iff] at supported
                subst result
                exact step_refl control safe

/-- Charging, environment coins and every administrative capability preserve the source control invariants independently of the private handler. -/
theorem effects (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (result : (EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.effects query).run control)) : Step control result.2 := by
  simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨charged, member, continued⟩ := supported
  have same := lift_control (.charge (effectKind query)) control charged member
  rw [same] at continued
  cases query with
  | inl coin =>
      rw [lift_control (.coin coin) control result continued]
      exact step_refl control safe
  | inr request => exact capability request control safe result continued

/-- The actual global dispatcher preserves physical role, installation uniqueness and every prior hidden sender for all permitted private service replies. -/
theorem handler (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n) (safe : Safe control)
    (result : (WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support ((PqxdhRecordLiftProtocol.handler decode route query).run control)) :
    Step control result.2 := by
  cases query with
  | inl created => exact initialize_server created control safe result supported
  | inr outer =>
      cases outer with
      | inl effect => exact effects effect control safe result supported
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact server_step decode route (.inl send) control safe result supported
              | inr raw => exact server_step decode route (.inr raw) control safe result supported
          | inr ownerQuery =>
              obtain ⟨owner, request⟩ := ownerQuery
              cases request with
              | inl plaintext => exact beacon_step decode owner (.inl plaintext) control safe result supported
              | inr raw => exact beacon_step decode owner (.inr raw) control safe result supported

/-- The actual empty control establishes roles and consumed-role provenance before any service reply is chosen. -/
theorem initial_safe : Safe (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n) :=
  ⟨initial_roles, initial_provenance⟩

/-- Every adaptive source schedule preserves the derived structural invariants for all permitted private reply paths. -/
theorem schedule {Result : Type} (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (result : Result × PqxdhRecordLiftProtocol.Control n)
    (supported : result ∈ support (PqxdhRecordLiftProtocol.schedule decode route client control)) :
    Step control result.2 := by
  induction client using OracleComp.inductionOn generalizing control result with
  | pure value =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact step_refl control safe
  | query_bind query next ih =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      have first := handler decode route query control safe inner member
      have rest := ih inner.1 inner.2 first.1 result continued
      exact ⟨rest.1, forward_trans (view control) (view inner.2) (view result.2) first.2 rest.2⟩

/-- An arbitrary private stateful interpreter can only select one of the source control's permitted reply paths. This transports control safety without a native-source correspondence premise. -/
theorem interpreted_schedule {ι : Type} {spec : OracleSpec ι} {P Result : Type}
    (service : QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp spec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (safe : Safe control) (privateState : P) (result : (Result × PqxdhRecordLiftProtocol.Control n) × P)
    (supported : result ∈ support ((simulateQ service
      (PqxdhRecordLiftProtocol.schedule decode route client control)).run privateState)) :
    Step control result.1.2 := by
  apply schedule decode route client control safe result.1
  apply support_simulateQ_run'_subset service _ privateState
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

variable {ι : Type} {targetSpec : OracleSpec ι}

/-- Proof-side instrumentation may pass its prior private trace to the interpreter. The source service ranges and replies remain unchanged, and the literal sealing coordinate is appended independently of writer success. -/
def traceService {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) →
      QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec))) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n)
      (StateT (P × List (PqxdhRecordLiftWorldCompiler.Label n)) (OracleComp targetSpec)) :=
  fun query state => do
    let result ← (service state.2 query).run state.1
    pure (result.1, (result.2, state.2 ++ sealingCoordinates query))

/-- A supported service result carries exactly the old private trace plus this actual request's sealing coordinate. -/
theorem traceService_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((traceService service query).run state)) :
    result.2.2 = state.2 ++ sealingCoordinates query := by
  simp only [traceService, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  rfl

/-- An admitted hidden source send records exactly its current coordinate once and returns the successor kernel even when the writer returns none. -/
theorem protocol_send_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (slot : PqxdhRecordLiftInterface.Slot n) (entry : PqxdhRecordLiftWorldCompiler.LabeledKernel n) (context : RawCtxSourceSend.SealContext)
    (pending : RawCtxChainSend.Kdf (PqxdhRecordLiftWorldCompiler.Label n) (PqxdhRecordLiftWorldCompiler.Label n) (PqxdhRecordLiftWorldCompiler.Label n) RawCtxSourceSend.SealContext)
    (admitted : RawCtxChainSend.normalBegin entry context = .requested pending)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.kernelSend (.hidden slot entry) context)).run state)) :
    result.1.1 = .hidden slot { entry with control := pending.committed_control, send_chain := PqxdhRecordLiftChainState.advance entry.send_chain 1 } ∧
      result.2.2 = state.2 ++ [entry.send_chain] := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  rw [admitted] at tracked
  simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
    admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure,
    bind_assoc, pure_bind] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨looked, lookupSupported, continued⟩ := supported
  rw [mem_support_bind_iff] at continued
  obtain ⟨sealed, sealSupported, finished⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  exact ⟨congrArg (StoredKernel.hidden slot)
    (PqxdhRecordLiftChainState.send_ready_kernel entry context pending pending.request tracked),
    by
      change sealed.2.2 = state.2 ++ [entry.send_chain]
      have sealTrace := traceService_trace service (.sealing (RawCtxChainSend.ready pending
        (PqxdhRecordLiftChainState.advance pending.request 1, pending.request))) looked.2 sealed sealSupported
      have lookupTrace := traceService_trace service (.lookup pending.request) state looked lookupSupported
      rw [sealTrace, lookupTrace]
      simp only [sealingCoordinates, List.append_nil, RawCtxChainSend.ready, tracked.2.2.1]⟩

/-- The full recursive opaque receive makes no sealing attempt, including cached opening, future derivation and rollback. -/
theorem receiveProgram_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (effect : PqxdhRecordLiftChainCompiler.Effect (PqxdhRecordLiftInterface.Slot n) RawCtxWholeOwner.OpenContext)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (PqxdhRecordLiftWorldCompiler.LabeledKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (simulateQ PqxdhRecordLiftProtocol.localLift
        (PqxdhRecordLiftOpaqueDrivers.receiveProgram effect))).run state)) : result.2.2 = state.2 := by
  generalize depthEq : RawCtxChainReceive.effectRank effect = depth
  induction depth using Nat.strong_induction_on generalizing effect state result with
  | h depth ih =>
      cases effect with
      | rejected entry context =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          rfl
      | openRequested pending =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
            simulateQ_pure, PqxdhRecordLiftProtocol.localLift, StateT.run_bind, StateT.run_pure] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨opened, member, finished⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at finished
          subst result
          exact (traceService_trace service (.opening pending) state opened member).trans (List.append_nil _)
      | kdfRequested pending =>
          simp only [PqxdhRecordLiftOpaqueDrivers.receiveProgram, simulateQ_bind, simulateQ_spec_query,
            PqxdhRecordLiftProtocol.localLift, StateT.run_bind] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨looked, member, continued⟩ := supported
          have unchanged := traceService_trace service (.lookup pending.request) state looked member
          exact (ih _ (depthEq ▸ RawCtxChainReceive.normalResume_rank pending
            (PqxdhRecordLiftChainState.advance pending.request 1, pending.request)) _ looked.2 result continued rfl).trans
              (unchanged.trans (List.append_nil _))

/-- Both caller-known and hidden whole-kernel receive preserve the private sealing history. -/
theorem protocol_receive_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (stored : StoredKernel n) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (StoredKernel n × core.option.Option RawCtxWholeOwner.Decrypted) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.kernelReceive stored target context)).run state)) : result.2.2 = state.2 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨opened, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact (traceService_trace service (.knownReceive kernel target context) state opened member).trans (List.append_nil _)
  | hidden slot kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelReceive, simulateQ_bind, simulateQ_pure,
        StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨opened, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact receiveProgram_trace service _ state opened member

/-- The exact source send's private log counts only hidden coordinate attempts; caller-known sends and exhausted hidden sends add none. -/
theorem protocol_kernelSend_delta {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (stored : StoredKernel n) (context : RawCtxSourceSend.SealContext) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (StoredKernel n × Option RawCtxSourceSend.Encrypted) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.kernelSend stored context)).run state)) :
    AttemptDelta stored result.1.1 state.2 result.2.2 := by
  cases stored with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.kernelSend, simulateQ_bind, simulateQ_spec_query,
        simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨sealed, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact Or.inl ((traceService_trace service (.knownSend kernel context) state sealed member).trans (List.append_nil _))
  | hidden slot entry =>
      cases admitted : RawCtxChainSend.normalBegin entry context with
      | exhausted original prior =>
          simp only [PqxdhRecordLiftProtocol.kernelSend, PqxdhRecordLiftOpaqueDrivers.admittedSend,
            admitted, PqxdhRecordLiftOpaqueDrivers.sendProgram, simulateQ_pure,
            pure_bind, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          exact Or.inl rfl
      | requested pending =>
          have actual := protocol_send_trace service slot entry context pending admitted state result supported
          exact Or.inr ⟨slot, entry,
            { entry with control := pending.committed_control, send_chain := PqxdhRecordLiftChainState.advance entry.send_chain 1 },
            rfl, actual.1, rfl, actual.2⟩

/-- Literal empty-input/parser guards and optional replies preserve the exact hidden attempt delta for one owner command. -/
theorem protocol_ownerStep_delta {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.ownerStep sender decode query owner)).run state)) :
    AttemptDelta owner.kernel result.1.2.kernel state.2 result.2.2 := by
  cases query with
  | inl plaintext =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerSend] at supported
      split_ifs at supported with empty
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        exact Or.inl rfl
      · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨sealed, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact protocol_kernelSend_delta service owner.kernel _ state sealed member
  | inr raw =>
      simp only [PqxdhRecordLiftProtocol.ownerStep, PqxdhRecordLiftProtocol.ownerReceive] at supported
      repeat' split at supported
      case h_2.isTrue =>
        simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨opened, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact Or.inl (protocol_receive_trace service owner.kernel _ _ state opened member)
      all_goals simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      all_goals subst result
      all_goals exact Or.inl rfl

/-- Publishing actual attempted frames does not add another sealing attempt to the private coordinate history. -/
theorem protocol_ownerRun_delta {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (tag : PqxdhDeploymentInterface.FrameTag) (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : Owner n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × Owner n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.ownerRun tag sender decode query owner)).run state)) :
    AttemptDelta owner.kernel result.1.2.kernel state.2 result.2.2 := by
  simp only [PqxdhRecordLiftProtocol.ownerRun, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
    StateT.run_bind, StateT.run_pure] at supported
  rw [mem_support_bind_iff] at supported
  obtain ⟨inner, member, continued⟩ := supported
  rw [mem_support_bind_iff] at continued
  obtain ⟨published, publishedMember, finished⟩ := continued
  simp only [support_pure, Set.mem_singleton_iff] at finished
  subst result
  have trace := (traceService_trace service (.publish tag) inner.2 published publishedMember).trans (List.append_nil _)
  change AttemptDelta owner.kernel inner.1.2.kernel state.2 published.2.2
  rw [trace]
  exact protocol_ownerStep_delta service sender decode query owner state inner member

variable {P : Type}

/-- The actual source Server routing program has at most one hidden attempt per request, with strict putback at its selected physical peer. -/
theorem protocol_serverStep_trace
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : RawCtxServerMixed.SourceSpec.Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (RawCtxServerMixed.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) ×
      (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.serverStep decode route query).run control)).run state)) :
    AttemptStep (view control)
      (view result.1.2) state.2 result.2.2 := by
  change result ∈ support ((simulateQ (traceService service)
    (PqxdhRecordLiftProtocol.serverStep decode route query control)).run state) at supported
  cases existing : control.server with
  | none =>
      cases query <;>
        simp only [PqxdhRecordLiftProtocol.serverStep, existing, simulateQ_pure,
          StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
        subst result <;> exact Or.inl rfl
  | some server =>
      cases query with
      | inl request =>
          obtain ⟨plaintext, keyId⟩ := request
          cases selected : server.peers keyId with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Or.inl rfl
          | some peer =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, selected,
                simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
              rw [mem_support_bind_iff] at supported
              obtain ⟨inner, member, finished⟩ := supported
              simp only [support_pure, Set.mem_singleton_iff] at finished
              subst result
              exact server_attemptStep _ _ server existing keyId peer selected inner.1.2.kernel inner.1.2.rawAttempts rfl _ _
                (protocol_ownerRun_delta service _ server.sender decode (.inl plaintext) _ state inner member)
      | inr raw =>
          cases routed : route raw with
          | none =>
              simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              exact Or.inl rfl
          | some keyId =>
              cases selected : server.peers keyId with
              | none =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected, simulateQ_pure,
                    StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
                  subst result
                  exact Or.inl rfl
              | some peer =>
                  simp only [PqxdhRecordLiftProtocol.serverStep, existing, routed, selected,
                    simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
                  rw [mem_support_bind_iff] at supported
                  obtain ⟨inner, member, finished⟩ := supported
                  simp only [support_pure, Set.mem_singleton_iff] at finished
                  subst result
                  exact server_attemptStep _ _ server existing keyId peer selected inner.1.2.kernel inner.1.2.rawAttempts rfl _ _
                    (protocol_ownerRun_delta service _ server.sender decode (.inr raw) _ state inner member)

/-- The actual Beacon program preserves the same physical owner index when recording its one possible hidden sealing attempt. -/
theorem protocol_beaconStep_trace
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (owner : Nat) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (RawCtxMixedOwner.SourceSpec.Range query × PqxdhRecordLiftProtocol.Control n) ×
      (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.beaconStep decode owner query).run control)).run state)) :
    AttemptStep (view control)
      (view result.1.2) state.2 result.2.2 := by
  change result ∈ support ((simulateQ (traceService service)
    (PqxdhRecordLiftProtocol.beaconStep decode owner query control)).run state) at supported
  cases selected : control.owners[owner]? with
  | none =>
      simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact Or.inl rfl
  | some phase =>
      cases phase with
      | inactive phase =>
          cases query <;>
            simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_pure,
              StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
            subst result <;> exact Or.inl rfl
      | established shell kernel =>
          simp only [PqxdhRecordLiftProtocol.beaconStep, selected, simulateQ_bind,
            simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
          rw [mem_support_bind_iff] at supported
          obtain ⟨inner, member, finished⟩ := supported
          simp only [support_pure, Set.mem_singleton_iff] at finished
          subst result
          exact beacon_attemptStep _ _ owner shell kernel inner.1.2.kernel selected rfl _ _
            (protocol_ownerRun_delta service _ shell.identityKeyId decode query _ state inner member)

/-- Allocating or reusing an installation seed is not a hidden record sealing attempt. -/
theorem protocol_resolve_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (role : Role) (ref : KernelRef n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : StoredKernel n × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.resolve role ref)).run state)) : result.2.2 = state.2 := by
  cases ref with
  | known kernel =>
      simp only [PqxdhRecordLiftProtocol.resolve, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | hidden slot =>
      simp only [PqxdhRecordLiftProtocol.resolve, simulateQ_bind, simulateQ_spec_query, simulateQ_pure,
        StateT.run_bind, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨allocated, member, finished⟩ := supported
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      exact (traceService_trace service (.allocate slot) state allocated member).trans (List.append_nil _)

/-- Source Server install guards and seed resolution never produce an ordinary hidden-record sealing attempt. -/
theorem protocol_installServer_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (keyId : Std.U64) (identity : RawCtxServerRouting.Identity) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.installServer keyId identity ref).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (traceService service)
    (PqxdhRecordLiftProtocol.installServer keyId identity ref control)).run state) at supported
  cases found : control.server with
  | none =>
      simp only [PqxdhRecordLiftProtocol.installServer, found, simulateQ_pure,
        StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      rfl
  | some server =>
      simp only [PqxdhRecordLiftProtocol.installServer, found] at supported
      split_ifs at supported with admitted
      · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
        rw [mem_support_bind_iff] at supported
        obtain ⟨resolved, member, finished⟩ := supported
        simp only [support_pure, Set.mem_singleton_iff] at finished
        subst result
        exact protocol_resolve_trace service .server ref state resolved member
      · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
        subst result
        rfl

/-- Source Beacon install guards and seed resolution never produce an ordinary hidden-record sealing attempt. -/
theorem protocol_installBeacon_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (owner : Nat) (shell : BeaconShell) (ref : KernelRef n)
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : (Bool × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.installBeacon owner shell ref).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (traceService service)
    (PqxdhRecordLiftProtocol.installBeacon owner shell ref control)).run state) at supported
  simp only [PqxdhRecordLiftProtocol.installBeacon] at supported
  split_ifs at supported with admitted
  · simp only [simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure] at supported
    rw [mem_support_bind_iff] at supported
    obtain ⟨resolved, member, finished⟩ := supported
    simp only [support_pure, Set.mem_singleton_iff] at finished
    subst result
    exact protocol_resolve_trace service .beacon ref state resolved member
  · simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl

/-- A lifted non-sealing private service preserves the attempt history while retaining its literal reply and the complete control state. -/
theorem protocol_lift_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) (notSealing : sealingCoordinates query = [])
    (control : PqxdhRecordLiftProtocol.Control n) (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : ((PqxdhRecordLiftProtocol.ServiceSpec n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((StateT.lift ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : PqxdhRecordLiftProtocol.Client n _).run control)).run state)) :
    result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (traceService service)
    ((fun reply => (reply, control)) <$> (PqxdhRecordLiftProtocol.ServiceSpec n).query query)).run state) at supported
  simp only [simulateQ_map, simulateQ_spec_query, StateT.run_map, support_map] at supported
  obtain ⟨inner, member, rfl⟩ := supported
  exact (traceService_trace service query state inner member).trans (by rw [notSealing, List.append_nil])

/-- Source initialization imports known records but invokes no hidden sealing service. -/
theorem protocol_initialize_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (created : PqxdhLiveServerConstruction.Created Unit) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n)) (result : (Unit × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.initializeServer created).run control)).run state)) : result.2.2 = state.2 := by
  change result ∈ support ((simulateQ (traceService service)
    (PqxdhRecordLiftProtocol.initializeServer created control)).run state) at supported
  cases found : control.server <;>
    simp only [PqxdhRecordLiftProtocol.initializeServer, found, simulateQ_pure,
      StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
    subst result <;> rfl

/-- All frozen administrative, public hash and presence capabilities preserve the ordinary hidden-record attempt history. -/
theorem protocol_capability_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (query : (CapabilitySpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : ((CapabilitySpec n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.capability query).run control)).run state)) : result.2.2 = state.2 := by
  cases query with
  | installServer keyId identity ref => exact protocol_installServer_trace service keyId identity ref control state result supported
  | installBeacon owner shell ref => exact protocol_installBeacon_trace service owner shell ref control state result supported
  | hash bytes => exact protocol_lift_trace service (.hash bytes) rfl control state result supported
  | peerPresent keyId =>
      change result ∈ support (pure (((control.server.bind fun server => server.peers keyId).isSome, control), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | ownerPresent owner =>
      change result ∈ support (pure (((control.owners[owner]?).isSome, control), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | appendOwner sender pin phase =>
      change result ∈ support (pure ((control.owners.length, { control with owners := control.owners ++ [.inactive phase] }), state)) at supported
      exact (Set.mem_singleton_iff.mp supported).symm ▸ rfl
  | advanceOwner owner phase =>
      change result ∈ support ((simulateQ (traceService service)
        (PqxdhRecordLiftProtocol.capability (.advanceOwner owner phase) control)).run state) at supported
      cases found : control.owners[owner]? with
      | none =>
          simp only [PqxdhRecordLiftProtocol.capability, found, simulateQ_pure,
            StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
          subst result
          rfl
      | some current =>
          cases current with
          | established shell kernel =>
              simp only [PqxdhRecordLiftProtocol.capability, found, simulateQ_pure,
                StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
              subst result
              rfl
          | inactive before =>
              simp only [PqxdhRecordLiftProtocol.capability, found] at supported
              split_ifs at supported with legal <;>
                simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported <;>
                subst result <;> rfl

/-- Every charged effect route preserves the attempt list, including arbitrary startup, environment and wrapper coins. -/
theorem protocol_effects_trace {P : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (query : (EnvEffects n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : ((EnvEffects n).Range query × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.effects query).run control)).run state)) : result.2.2 = state.2 := by
  cases query with
  | inl coin =>
      simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨charged, chargeMember, continued⟩ := supported
      rw [mem_support_bind_iff] at continued
      obtain ⟨sampled, sampleMember, finished⟩ := continued
      simp only [support_pure, Set.mem_singleton_iff] at finished
      subst result
      have chargedTrace := protocol_lift_trace service (.charge (effectKind (.inl coin))) rfl control state charged chargeMember
      have sampledTrace := (traceService_trace service (.coin coin) charged.2 sampled sampleMember).trans (List.append_nil _)
      exact sampledTrace.trans chargedTrace
  | inr request =>
      simp only [PqxdhRecordLiftProtocol.effects, StateT.run_bind, StateT.run_lift, simulateQ_bind,
        simulateQ_spec_query, simulateQ_pure, StateT.run_pure] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨charged, chargeMember, continued⟩ := supported
      have chargedTrace := protocol_lift_trace service (.charge (effectKind (.inr request))) rfl control state charged chargeMember
      exact (protocol_capability_trace service request charged.1.2 charged.2 result continued).trans chargedTrace

/-- Every actual global source request has the traced strict-step property, independently of private service replies. -/
theorem protocol_handler_trace
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) → QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) ×
      (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.handler decode route query).run control)).run state)) :
    AttemptStep (view control)
      (view result.1.2) state.2 result.2.2 := by
  cases query with
  | inl created => exact Or.inl (protocol_initialize_trace service created control state result supported)
  | inr outer =>
      cases outer with
      | inl effect => exact Or.inl (protocol_effects_trace service effect control state result supported)
      | inr record =>
          cases record with
          | inl serverQuery =>
              cases serverQuery with
              | inl send => exact protocol_serverStep_trace service decode route (.inl send) control state result supported
              | inr raw => exact protocol_serverStep_trace service decode route (.inr raw) control state result supported
          | inr ownerQuery =>
              obtain ⟨owner, query⟩ := ownerQuery
              cases query with
              | inl plaintext => exact protocol_beaconStep_trace service decode owner (.inl plaintext) control state result supported
              | inr raw => exact protocol_beaconStep_trace service decode owner (.inr raw) control state result supported

/-- Private history safety mentions only actual control fields and the literal attempted-seal coordinates. It imposes no invariant on private reply state. -/
def HistoryGood (control : PqxdhRecordLiftProtocol.Control n)
    (attempts : List (PqxdhRecordLiftWorldCompiler.Label n)) : Prop :=
  Safe control ∧ Past (view control) attempts ∧ attempts.Nodup

/-- Trace instrumentation can only select source replies already permitted by the unchanged service syntax. -/
theorem trace_support {Result : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) →
      QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : Result × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service) client).run state)) :
    result.1 ∈ support client := by
  apply support_simulateQ_run'_subset (traceService service) client state
  rw [StateT.run'_eq, support_map]
  exact ⟨result, supported, rfl⟩

/-- One actual request preserves distinct attempted history under any private replies, deriving safety directly from source control rather than native interpreter erasure. -/
theorem handler_history
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) →
      QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (query : (WorldSpec n).Domain) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n)) (good : HistoryGood control state.2)
    (result : ((WorldSpec n).Range query × PqxdhRecordLiftProtocol.Control n) ×
      (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      ((PqxdhRecordLiftProtocol.handler decode route query).run control)).run state)) :
    HistoryGood result.1.2 result.2.2 := by
  have controlStep := handler decode route query control good.1 result.1
    (trace_support service _ state result supported)
  have attempt := protocol_handler_trace service decode route query control state result supported
  exact ⟨controlStep.1, attemptStep_history (view control) (view result.1.2)
    good.1.1 controlStep.1.1 good.1.2 controlStep.2 state.2 result.2.2 good.2.1 good.2.2 attempt⟩

/-- The complete adaptive source schedule preserves distinct attempted history under arbitrary private service replies and arbitrary target-oracle work. -/
theorem schedule_history {Result : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) →
      QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (control : PqxdhRecordLiftProtocol.Control n)
    (state : P × List (PqxdhRecordLiftWorldCompiler.Label n)) (good : HistoryGood control state.2)
    (result : (Result × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.schedule decode route client control)).run state)) :
    HistoryGood result.1.2 result.2.2 := by
  induction client using OracleComp.inductionOn generalizing control state result with
  | pure value =>
      simp only [PqxdhRecordLiftProtocol.schedule, simulateQ_pure, StateT.run_pure,
        support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact good
  | query_bind query next ih =>
      simp only [PqxdhRecordLiftProtocol.schedule, StateT.run_bind, simulateQ_bind,
        simulateQ_spec_query] at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨inner, member, continued⟩ := supported
      exact ih inner.1.1 inner.1.2 inner.2
        (handler_history service decode route query control state good inner member) result continued

/-- The actual empty source control initializes history safety without any reachable-prefix or service correctness premise. -/
theorem initial_history : HistoryGood (PqxdhRecordLiftProtocol.initialControl : PqxdhRecordLiftProtocol.Control n) [] := by
  refine ⟨initial_safe, ?_, List.nodup_nil⟩
  intro coordinate member
  cases member

/-- Every completed typed reply path of the actual initial adaptive schedule has no repeated hidden sealing coordinate, even under changed CTX replies. Prefix freshness is proved separately below. -/
theorem initial_schedule_nodup {Result : Type}
    (service : List (PqxdhRecordLiftWorldCompiler.Label n) →
      QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT P (OracleComp targetSpec)))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) (privateState : P)
    (result : (Result × PqxdhRecordLiftProtocol.Control n) × (P × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support ((simulateQ (traceService service)
      (PqxdhRecordLiftProtocol.schedule decode route client PqxdhRecordLiftProtocol.initialControl)).run (privateState, []))) :
    result.2.2.Nodup :=
  (schedule_history service decode route client _ (privateState, []) initial_history result supported).2.2

/-- Private proof syntax attaches the prior attempted history to each unchanged source request. Its reply type is exactly the original request's reply type. -/
abbrev HistorySpec (n : Nat) : OracleSpec
    (List (PqxdhRecordLiftWorldCompiler.Label n) × PqxdhRecordLiftProtocol.Service n) :=
  fun request => (PqxdhRecordLiftProtocol.ServiceSpec n).Range request.2

/-- The trace is read only to annotate the next private query; no annotation is exposed to the source program. -/
def annotateService (past : List (PqxdhRecordLiftWorldCompiler.Label n)) :
    QueryImpl (PqxdhRecordLiftProtocol.ServiceSpec n) (StateT Unit (OracleComp (HistorySpec n))) :=
  fun query _ => do
    let reply ← (HistorySpec n).query (past, query)
    pure (reply, ())

/-- Interpret source syntax into private history annotations, retaining its complete result and its final attempted history. -/
def annotated {Result : Type} (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) :
    OracleComp (HistorySpec n) (Result × (Unit × List (PqxdhRecordLiftWorldCompiler.Label n))) :=
  (simulateQ (traceService annotateService) client).run ((), past)

/-- Each annotation records the history before the current request, including a sealing request whose optional writer reply will be absent. -/
theorem annotated_query_bind {Result : Type} (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (next : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query →
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) :
    annotated ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= next) past =
      ((liftM ((HistorySpec n).query (past, query)) : OracleComp (HistorySpec n) _) >>= fun reply =>
        annotated (next reply) (past ++ sealingCoordinates query)) := by
  simp only [annotated, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  change ((do
    let reply ← (HistorySpec n).query (past, query)
    pure (reply, ((), past ++ sealingCoordinates query))) >>= fun inner =>
      (simulateQ (traceService annotateService) (next inner.1)).run inner.2) = _
  simp only [bind_assoc, pure_bind]

/-- A terminated source program adds no attempted coordinate. -/
theorem annotated_pure {Result : Type} (result : Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) :
    annotated (pure result) past = pure (result, ((), past)) := rfl

/-- Every private source reply type is inhabited by its existing concrete constructors. This supplies syntactic continuations, not losslessness of any chosen interpreter. -/
def serviceDefault : (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain) →
    (PqxdhRecordLiftProtocol.ServiceSpec n).Range query
  | .allocate _ | .charge _ | .lookup _ | .publish _ => ()
  | .coin _ => default
  | .hash _ => default
  | .opening _ => .None
  | .sealing _ => none
  | .knownSend kernel _ => (kernel, none)
  | .knownReceive kernel _ _ => (kernel, .None)

instance historySpecInhabited (request : (HistorySpec n).Domain) : Inhabited ((HistorySpec n).Range request) :=
  ⟨serviceDefault request.2⟩

/-- Erase only the private history annotation, issuing exactly the original service request. -/
def eraseService : QueryImpl (HistorySpec n) (OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n)) :=
  fun request => (PqxdhRecordLiftProtocol.ServiceSpec n).query request.2

/-- Erasing annotations and the final ghost recovers the original source program, with all original replies and complete result intact. -/
theorem annotated_erasure {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n)) :
    Prod.fst <$> simulateQ eraseService (annotated client past) = client := by
  induction client using OracleComp.inductionOn generalizing past <;>
    simp [annotated_pure, annotated_query_bind, eraseService, map_bind, *]

/-- Every typed continuation retains the entire prior attempted history as a prefix. -/
theorem annotated_prefix {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n))
    (result : Result × (Unit × List (PqxdhRecordLiftWorldCompiler.Label n)))
    (supported : result ∈ support (annotated client past)) : past.IsPrefix result.2.2 := by
  induction client using OracleComp.inductionOn generalizing past result with
  | pure value =>
      simpa only [annotated_pure, support_pure, Set.mem_singleton_iff] using
        supported ▸ List.prefix_refl past
  | query_bind query next ih =>
      rw [annotated_query_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, _, continued⟩ := supported
      exact (List.prefix_append past (sealingCoordinates query)).trans (ih reply _ result continued)

/-- The stopped endpoint needs this fact before it answers the sealing request. All other private requests impose no attempted-seal condition. -/
def Fresh : (HistorySpec n).Domain → Prop
  | (past, .sealing pending) => pending.material ∉ past
  | _ => True

/-- Distinct final histories force the immediate post-request history to be distinct. A concrete typed continuation exists independently of any possibly stopping interpretation. -/
theorem annotated_next_nodup {Result : Type}
    (query : (PqxdhRecordLiftProtocol.ServiceSpec n).Domain)
    (next : (PqxdhRecordLiftProtocol.ServiceSpec n).Range query →
      OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n))
    (nodup : ∀ result ∈ support (annotated
      ((liftM ((PqxdhRecordLiftProtocol.ServiceSpec n).query query) : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) _) >>= next) past),
      result.2.2.Nodup) : (past ++ sealingCoordinates query).Nodup := by
  obtain ⟨result, member⟩ := support_nonempty
    (annotated (next (serviceDefault query)) (past ++ sealingCoordinates query))
  exact (annotated_prefix _ _ result member).nodup (nodup result (by
    rw [annotated_query_bind, mem_support_bind_iff]
    exact ⟨serviceDefault query, mem_support_query _ _, member⟩))

/-- Every syntactically reachable request is fresh before any endpoint reply is requested. This proof uses only typed source continuations, so it also covers a prefix at which a chosen interpreter returns an error. -/
theorem annotated_fresh {Result : Type}
    (client : OracleComp (PqxdhRecordLiftProtocol.ServiceSpec n) Result)
    (past : List (PqxdhRecordLiftWorldCompiler.Label n))
    (nodup : ∀ result ∈ support (annotated client past), result.2.2.Nodup) :
    (annotated client past).AllQueriesSatisfy Fresh := by
  induction client using OracleComp.inductionOn generalizing past with
  | pure value => exact allQueriesSatisfy_pure _ _
  | query_bind query next ih =>
      rw [annotated_query_bind, allQueriesSatisfy_query_bind_iff]
      constructor
      · have immediate := annotated_next_nodup query next past nodup
        cases query <;> try trivial
        case sealing pending =>
          exact ((List.nodup_concat _ _).mp (by
            simpa only [sealingCoordinates, ← List.concat_eq_append] using immediate)).1
      · intro reply
        apply ih reply
        intro result member
        apply nodup result
        rw [annotated_query_bind, mem_support_bind_iff]
        exact ⟨reply, mem_support_query _ _, member⟩

/-- Every reached hidden sealing request of the actual initialized adaptive source schedule is absent from its prior attempted history, before any private or possibly stopping endpoint responds. No source-reachability or cryptographic premise is supplied. -/
theorem initial_schedule_fresh {Result : Type}
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (client : OracleComp (WorldSpec n) Result) :
    (annotated (PqxdhRecordLiftProtocol.schedule decode route client
      PqxdhRecordLiftProtocol.initialControl) []).AllQueriesSatisfy Fresh :=
  annotated_fresh _ [] (fun result supported =>
    initial_schedule_nodup annotateService decode route client () result supported)

/-- The frozen environment/adversary program inherits pre-query freshness while retaining its original environment, ledger, client output and complete public control. -/
theorem program_fresh {E X Reader Response : Type} (env : Environment n E)
    (crypto : Pqxdh.Crypto) (codec : PqxdhServerAuthExperiment.Codec Reader Response)
    (route : RawCtxServerRouting.SenderDecoder) (serverKid : Std.U64)
    (bounds : PqxdhDeploymentInterface.FreshBounds) (mode : PqxdhDeploymentInterface.Mode)
    (adversary : OracleComp (PqxdhDeploymentInterface.ModeSpec mode) X) :
    (annotated (PqxdhRecordLiftProtocol.program env crypto codec route serverKid bounds mode adversary) []).AllQueriesSatisfy Fresh :=
  initial_schedule_fresh codec.frameRead route _

end BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.receive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.receive_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.admitted_receive_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.admitted_receive_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.send_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.send_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.admitted_send_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.admitted_send_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.local_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.local_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernelStep_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernelStep_refl
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernel_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernel_receive
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernel_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.kernel_send
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_send' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_send
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_receive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_receive
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_step
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.owner_run
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.provenance_same' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.provenance_same
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.step_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.step_frame
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.step_refl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.step_refl
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_store
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_raw' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_raw
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.beacon_store' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.beacon_store
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.server_step
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.beacon_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.beacon_step
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.resolve_facts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.resolve_facts
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.view_markUsed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.view_markUsed
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.provenance_annotate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.provenance_annotate
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.install_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.install_server
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.install_beacon' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.install_beacon
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initialize_server' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initialize_server
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.lift_control' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.lift_control
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.capability' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.capability
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.effects' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.effects
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.handler
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_safe' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_safe
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.schedule
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.interpreted_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.interpreted_schedule
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.traceService_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.traceService_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_send_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_send_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.receiveProgram_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.receiveProgram_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_receive_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_receive_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_kernelSend_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_kernelSend_delta
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_ownerStep_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_ownerStep_delta
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_ownerRun_delta' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_ownerRun_delta
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_serverStep_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_serverStep_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_beaconStep_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_beaconStep_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_resolve_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_resolve_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_installServer_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_installServer_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_installBeacon_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_installBeacon_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_lift_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_lift_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_initialize_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_initialize_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_capability_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_capability_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_effects_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_effects_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_handler_trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.protocol_handler_trace
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.trace_support' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.trace_support
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.handler_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.handler_history
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.schedule_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.schedule_history
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_history' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_history
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_schedule_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_schedule_nodup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_query_bind' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_query_bind
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_pure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_prefix
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_next_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_next_nodup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.annotated_fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_schedule_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.initial_schedule_fresh
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.program_fresh' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftProtocolHistory.program_fresh
