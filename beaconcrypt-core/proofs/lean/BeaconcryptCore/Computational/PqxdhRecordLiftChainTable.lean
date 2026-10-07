-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhRecordLiftChainState
import BeaconcryptCore.Computational.PqxdhRecordLiftLazyTable

/-! Persistent full76 replies interpret source coordinates through their predecessor. This operational construction does not identify real HKDF with a uniform table or prove the global evolving-chain hybrid. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhRecordLiftChainTable
open PqxdhRecordLiftChainState PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
open PqxdhSecretInputKdf

variable {Slot Context Payload : Type}

abbrev TableSpec (Slot : Type) := (Coordinate Slot →ₒ FullOutput)
abbrev Table (Slot : Type) := (TableSpec Slot).QueryCache
abbrev State (Slot : Type) := PqxdhRecordLiftLazyTable.State (TableSpec Slot)
abbrev Seeds (Slot : Type) := Slot → PqxdhRecordLiftSeed.Seed

def start (direction : Bool) : Nat := if direction then 0 else 1

def previous (coordinate : Coordinate Slot) : Coordinate Slot :=
  { coordinate with position := coordinate.position - 1 }

/-- Every interpreted coordinate is either an installed seed or the successor of a stored complete reply. -/
def Available (table : Table Slot) (coordinate : Coordinate Slot) : Prop :=
  coordinate.position = start coordinate.direction ∨
    start coordinate.direction < coordinate.position ∧
      ∃ output, table (previous coordinate) = some output

def Closed (table : Table Slot) : Prop :=
  ∀ coordinate output, table coordinate = some output → Available table coordinate

/-- The fallback makes interpretation total; availability excludes its use at every modeled reference. -/
def chain (seeds : Seeds Slot) (table : Table Slot) (coordinate : Coordinate Slot) : RatchetChain :=
  RawCtxFreshChainCut.concreteChain
    (if coordinate.position = start coordinate.direction then
      if coordinate.direction then (seeds coordinate.slot).2 else (seeds coordinate.slot).1
    else match table (previous coordinate) with
      | some output => nextChain output
      | none => ⟨List.replicate 32 0, by simp⟩)

def KernelAvailable (table : Table Slot) (kernel : Kernel Slot Payload) : Prop :=
  Available table kernel.send_chain ∧ Available table kernel.receive_chain

def PendingAvailable (table : Table Slot)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) Payload Context) : Prop :=
  KernelAvailable table pending.entry ∧ Available table pending.request

/-- Extending the persistent table preserves every previously available source chain, including byte aliases. -/
theorem chain_mono (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (coordinate : Coordinate Slot) (available : Available before coordinate) :
    chain seeds after coordinate = chain seeds before coordinate := by
  rcases available with initial | ⟨_, output, found⟩
  · simp only [chain, initial, ite_true]
  · simp only [chain, found, mono found]

/-- Cache growth preserves the operational domain of interpretation. -/
theorem available_mono (before after : Table Slot) (mono : before ≤ after)
    (coordinate : Coordinate Slot) (available : Available before coordinate) :
    Available after coordinate :=
  available.elim Or.inl (fun ⟨later, output, found⟩ => Or.inr ⟨later, output, mono found⟩)

/-- The successor's sole table predecessor is the exact original request coordinate. -/
theorem previous_advance (coordinate : Coordinate Slot) :
    previous (advance coordinate 1) = coordinate := by
  cases coordinate; simp [previous, advance]

/-- Storing a reply makes its successor available without replacing any prior chain. -/
theorem successor_available (table : Table Slot) (coordinate : Coordinate Slot)
    (available : Available table coordinate) (output : FullOutput)
    (found : table coordinate = some output) :
    Available table (advance coordinate 1) := by
  exact Or.inr ⟨Nat.lt_of_le_of_lt (available.elim Eq.ge (fun h => h.1.le))
    (Nat.lt_succ_self _), output,
    by simpa [previous, advance] using found⟩

/-- The successor chain is exactly the second32 projection of this stored full76 reply. -/
theorem successor_chain (seeds : Seeds Slot) (table : Table Slot) (coordinate : Coordinate Slot)
    (available : Available table coordinate) (output : FullOutput)
    (found : table coordinate = some output) :
    chain seeds table (advance coordinate 1) = RawCtxFreshChainCut.concreteChain (nextChain output) := by
  have later : start coordinate.direction < coordinate.position + 1 :=
    Nat.lt_of_le_of_lt (available.elim Eq.ge (fun h => h.1.le)) (Nat.lt_succ_self _)
  simp [chain, previous, advance, Nat.ne_of_gt later, found]

/-- Growing the table leaves the complete pending native request and rollback entry unchanged. -/
theorem pending_mono (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) Payload Context)
    (available : PendingAvailable before pending) :
    RawCtxChainReceive.nativeKdf (chain seeds after) (chain seeds after) pending =
      RawCtxChainReceive.nativeKdf (chain seeds before) (chain seeds before) pending := by
  simp only [RawCtxChainReceive.nativeKdf, RawCtxChainInterpretation.mapChains,
    chain_mono seeds before after mono pending.entry.send_chain available.1.1,
    chain_mono seeds before after mono pending.entry.receive_chain available.1.2,
    chain_mono seeds before after mono pending.request available.2]

/-- An actual persistent lookup realizes the complete source receive callback under the enlarged interpretation. -/
theorem receive_lookup [DecidableEq Slot] (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : PendingAvailable state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    RawCtxInterpretedReceive.normalResume
      (RawCtxChainReceive.nativeKdf (chain seeds state.1) (chain seeds state.1) pending)
      (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1)) =
      RawCtxChainReceive.nativeEffect (chain seeds result.2.1) (chain seeds result.2.1)
        (RawCtxChainReceive.normalResume pending
          (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1))) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  rw [← pending_mono seeds state.1 result.2.1 facts.2.1 pending available,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 pending.request available.2) result.1 facts.1]
  exact PqxdhRecordLiftChainState.resume_erasure (chain seeds result.2.1) pending _

/-- The same receive equality retains the full reply, table, counters and arbitrary continuation. -/
theorem receive_continuation [DecidableEq Slot] {Result : Type}
    (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : PendingAvailable state.1 pending)
    (continuation : FullOutput → RawCtxInterpretedReceive.Effect RatchetMaterial Context → State Slot → ProbComp Result) :
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (RawCtxInterpretedReceive.normalResume
        (RawCtxChainReceive.nativeKdf (chain seeds state.1) (chain seeds state.1) pending)
        (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1))) result.2) =
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1
        (RawCtxChainReceive.nativeEffect (chain seeds result.2.1) (chain seeds result.2.1)
          (RawCtxChainReceive.normalResume pending
            (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1)))) result.2) := by
  exact bind_congr_of_forall_mem_support _ fun result sampled =>
    congrArg (fun effect => continuation result.1 effect result.2)
      (receive_lookup seeds state pending available result sampled)

/-- The empty table has no invented predecessor entries. -/
theorem closed_empty : Closed (∅ : Table Slot) := by
  simp [Closed]

/-- A new reply at an available request extends the closed table without overwriting earlier replies. -/
theorem closed_record [DecidableEq Slot] (table : Table Slot) (closed : Closed table)
    (coordinate : Coordinate Slot) (available : Available table coordinate)
    (output : FullOutput) (fresh : table coordinate = none) :
    Closed (table.cacheQuery coordinate output) := by
  exact fun prior value found =>
    if same : prior = coordinate then same.symm ▸
      available_mono table _ (QueryCache.le_cacheQuery table fresh) coordinate available
    else available_mono table _ (QueryCache.le_cacheQuery table fresh) prior
      (closed prior value ((QueryCache.cacheQuery_of_ne table output same).symm.trans found))

/-- Every supported lazy lookup preserves the derived predecessor invariant. -/
theorem closed_lookup [DecidableEq Slot] (state : State Slot) (closed : Closed state.1)
    (coordinate : Coordinate Slot) (available : Available state.1 coordinate)
    (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) coordinate).run state)) :
    Closed result.2.1 := by
  cases found : state.1 coordinate with
  | some output =>
      simp only [PqxdhRecordLiftLazyTable.run_hit coordinate state output found,
        support_pure, Set.mem_singleton_iff] at sampled
      simpa only [sampled] using closed
  | none =>
      simp only [PqxdhRecordLiftLazyTable.run_miss coordinate state found, support_map] at sampled
      exact sampled.elim fun output ⟨_, equal⟩ =>
        equal ▸ closed_record state.1 closed coordinate available output found

def SendAvailable (table : Table Slot)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) Payload Context) : Prop :=
  KernelAvailable table pending.entry ∧ Available table pending.request

/-- Send table growth likewise preserves the complete actual request and both entry chains. -/
theorem send_pending_mono (seeds : Seeds Slot) (before after : Table Slot) (mono : before ≤ after)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) Payload Context)
    (available : SendAvailable before pending) :
    RawCtxChainSend.nativeKdf (chain seeds after) (chain seeds after) pending =
      RawCtxChainSend.nativeKdf (chain seeds before) (chain seeds before) pending := by
  simp only [RawCtxChainSend.nativeKdf, RawCtxChainInterpretation.mapChains,
    chain_mono seeds before after mono pending.entry.send_chain available.1.1,
    chain_mono seeds before after mono pending.entry.receive_chain available.1.2,
    chain_mono seeds before after mono pending.request available.2]

/-- The same complete table reply realizes actual source send advancement before sealing. -/
theorem send_lookup [DecidableEq Slot] (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : SendAvailable state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    RawCtxInterpretedSend.resume
      (RawCtxChainSend.nativeKdf (chain seeds state.1) (chain seeds state.1) pending)
      (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1))) =
      RawCtxChainSend.nativeSeal (chain seeds result.2.1) (chain seeds result.2.1) <$>
        RawCtxChainSend.resume pending
          (ok (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1))) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  rw [← send_pending_mono seeds state.1 result.2.1 facts.2.1 pending available,
    RawCtxFreshChainCut.decoded_parts,
    ← successor_chain seeds result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 pending.request available.2) result.1 facts.1]
  simpa only [RawCtxMaterialInterpretation.rust_map_ok] using
    RawCtxChainSend.native_resume (chain seeds result.2.1) (chain seeds result.2.1) pending
      (ok (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1)))

/-- Actual failed opening restores only the source kernel; every sampled coordinate survives arbitrary adaptive table work. -/
theorem rollback_lookup [DecidableEq Slot] {Plaintext Result : Type}
    (entry : Kernel Slot RatchetMaterial) (context : Context)
    (opening : RawCtxInterpretedOpening.Opening (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (tracked : Tracked entry context (.openRequested opening))
    (coordinate : Coordinate Slot) (state : State Slot) (first : FullOutput × State Slot)
    (sampled : first ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) coordinate).run state))
    (program : OracleComp (TableSpec Slot) Result) (last : Result × State Slot)
    (continued : last ∈ support ((simulateQ PqxdhRecordLiftLazyTable.impl program).run first.2)) :
    (PqxdhRecordLiftLazyTable.withCaller coordinate).run
      ((RawCtxChainReceive.normalFinish opening (.None : core.option.Option Plaintext)).1, last.2) =
      pure (first.1, (entry, (last.2.1,
        ⟨last.2.2.lookups + 1, last.2.2.draws⟩))) := by
  rw [PqxdhRecordLiftChainState.failed_open entry context opening tracked]
  exact PqxdhRecordLiftLazyTable.rollback_after_adaptive entry entry coordinate state first sampled program last continued

def EffectAvailable (table : Table Slot) :
    RawCtxChainReceive.Effect (Coordinate Slot) (Coordinate Slot) Payload Context → Prop
  | .rejected entry _ => KernelAvailable table entry
  | .kdfRequested pending => PendingAvailable table pending
  | .openRequested opening => KernelAvailable table opening.entry ∧
      match opening.prepared with
      | .PreparedReceiveCachedCase _ => True
      | .PreparedReceiveFutureCase pending => Available table pending.final_receive_chain

/-- Every actual cached, rejected or future admission starts with available chain references. -/
theorem begin_available (table : Table Slot) (entry : Kernel Slot Payload)
    (available : KernelAvailable table entry) (target : Std.U64) (context : Context) :
    EffectAvailable table (RawCtxChainReceive.normalBegin entry target context) := by
  have run := RawCtxChainReceive.normalBegin_exact entry target context
  generalize RawCtxChainReceive.normalBegin entry target context = effect at run ⊢
  repeat' first | (unfold RawCtxChainReceive.beginReceive at run) |
    (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectAvailable, PendingAvailable, KernelAvailable, available.1, available.2, and_self]

/-- Source skip, target and rejection branches retain the available entry and supplied successor. -/
theorem resume_available (table : Table Slot)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) Payload Context)
    (available : PendingAvailable table pending)
    (successor : Available table (advance pending.request 1)) (value : Payload) :
    EffectAvailable table (RawCtxChainReceive.normalResume pending (advance pending.request 1, value)) := by
  have run := RawCtxChainReceive.normalResume_exact pending (advance pending.request 1, value)
  generalize RawCtxChainReceive.normalResume pending (advance pending.request 1, value) = effect at run ⊢
  repeat' first | (unfold RawCtxChainReceive.resume at run) |
    (obtain ⟨_, _, run⟩ := PqxdhFirstRecordReplay.rust_bind_ok run) | split at run
  all_goals cases RustM.ok.inj run
  all_goals simp only [EffectAvailable, PendingAvailable, KernelAvailable,
    available.1.1, available.1.2, true_and]
  all_goals cases RustM.ok.inj (show ok (advance pending.request 1, value) = ok _ from by assumption)
  all_goals exact successor

/-- The actual receive lookup preserves both the closed table and every reference in its complete next effect. -/
theorem receive_lookup_available [DecidableEq Slot] (state : State Slot) (closed : Closed state.1)
    (pending : RawCtxChainReceive.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : PendingAvailable state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    Closed result.2.1 ∧ EffectAvailable result.2.1
      (RawCtxChainReceive.normalResume pending
        (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1))) := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  have afterPending : PendingAvailable result.2.1 pending :=
    ⟨⟨available_mono state.1 result.2.1 facts.2.1 _ available.1.1,
      available_mono state.1 result.2.1 facts.2.1 _ available.1.2⟩,
      available_mono state.1 result.2.1 facts.2.1 _ available.2⟩
  exact ⟨closed_lookup state closed pending.request available.2 result sampled,
    resume_available result.2.1 pending afterPending
      (successor_available result.2.1 pending.request afterPending.2 result.1 facts.1) _⟩

/-- Both source seed kernels start entirely within the table interpretation domain. -/
theorem seeds_available (table : Table Slot) (slot : Slot) :
    (∃ kernel, serverLabels slot = ok kernel ∧ KernelAvailable table kernel) ∧
      (∃ kernel, beaconLabels slot = ok kernel ∧ KernelAvailable table kernel) := by
  refine ⟨⟨_, rfl, ?_⟩, ⟨_, rfl, ?_⟩⟩
  all_goals exact ⟨Or.inl rfl, Or.inl rfl⟩

/-- This constructed interpretation discharges both seed bindings against the complete production kernels. -/
theorem seeds_erasure (seeds : Seeds Slot) (table : Table Slot) (slot : Slot) :
    (erase (chain seeds table) <$> serverLabels slot = PqxdhRecordLiftSeed.serverKernel (seeds slot)) ∧
      (erase (chain seeds table) <$> beaconLabels slot = PqxdhRecordLiftSeed.beaconKernel (seeds slot)) := by
  exact ⟨server_seed_erasure slot (seeds slot) (chain seeds table) rfl rfl,
    beacon_seed_erasure slot (seeds slot) (chain seeds table) rfl rfl⟩

def StartAvailable (table : Table Slot) :
    RawCtxChainSend.Start (Coordinate Slot) (Coordinate Slot) Payload Context → Prop
  | .exhausted entry _ => KernelAvailable table entry
  | .requested pending => SendAvailable table pending

/-- Actual send admission obtains an available request from the same source entry. -/
theorem send_begin_available (table : Table Slot) (entry : Kernel Slot Payload)
    (available : KernelAvailable table entry) (context : Context) :
    StartAvailable table (RawCtxChainSend.normalBegin entry context) := by
  have tracked := PqxdhRecordLiftChainState.send_begin_tracked entry context
  cases shape : RawCtxChainSend.normalBegin entry context <;>
    simp_all [StartAvailable, SendAvailable, SendTracked, KernelAvailable]

/-- Actual send lookup retains a closed table and available chains in the entire advanced kernel. -/
theorem send_lookup_available [DecidableEq Slot] (state : State Slot) (closed : Closed state.1)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : SendAvailable state.1 pending) (result : FullOutput × State Slot)
    (sampled : result ∈ support ((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state)) :
    Closed result.2.1 ∧ KernelAvailable result.2.1
      (RawCtxChainSend.ready pending
        (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1))).advanced := by
  have facts := PqxdhRecordLiftLazyTable.step_facts pending.request state result sampled
  exact ⟨closed_lookup state closed pending.request available.2 result sampled,
    successor_available result.2.1 pending.request
      (available_mono state.1 result.2.1 facts.2.1 _ available.2) result.1 facts.1,
    available_mono state.1 result.2.1 facts.2.1 _ available.1.2⟩

/-- Send realization also retains its complete RustM result, full reply and persistent state under every continuation. -/
theorem send_continuation [DecidableEq Slot] {Result : Type}
    (seeds : Seeds Slot) (state : State Slot)
    (pending : RawCtxChainSend.Kdf (Coordinate Slot) (Coordinate Slot) RatchetMaterial Context)
    (available : SendAvailable state.1 pending)
    (continuation : FullOutput → RustM (RawCtxInterpretedSend.Seal RatchetMaterial Context) → State Slot → ProbComp Result) :
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1 (RawCtxInterpretedSend.resume
        (RawCtxChainSend.nativeKdf (chain seeds state.1) (chain seeds state.1) pending)
        (ok (RawCtxInterpretedReceive.decodeResponse (RawCtxKdfRequestTable.fullResponse result.1)))) result.2) =
    (((PqxdhRecordLiftLazyTable.impl (spec := TableSpec Slot) pending.request).run state) >>= fun result =>
      continuation result.1
        (RawCtxChainSend.nativeSeal (chain seeds result.2.1) (chain seeds result.2.1) <$>
          RawCtxChainSend.resume pending
            (ok (advance pending.request 1, RawCtxFreshChainCut.concreteMaterial (material result.1)))) result.2) := by
  exact bind_congr_of_forall_mem_support _ fun result sampled =>
    congrArg (fun effect => continuation result.1 effect result.2)
      (send_lookup seeds state pending available result sampled)

end BeaconcryptCore.Computational.PqxdhRecordLiftChainTable

/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.chain_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.chain_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.available_mono' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.available_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.previous_advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.previous_advance
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.successor_available' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.successor_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.successor_chain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.successor_chain
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.pending_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.pending_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_continuation
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_empty
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_record' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_record
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.closed_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_pending_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_pending_mono
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.rollback_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.rollback_lookup
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.begin_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.begin_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.resume_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.resume_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_lookup_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.receive_lookup_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.seeds_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.seeds_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.seeds_erasure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.seeds_erasure
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_begin_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_begin_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_lookup_available' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_lookup_available
/-- info: 'BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_continuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhRecordLiftChainTable.send_continuation
