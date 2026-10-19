import BeaconcryptCore.Computational.RawCtxMixedOwner

/-!
# Native Beacon lifecycle and established send/raw field wiring

All five source phase variants and their private fields are retained. Only the established variant admits record operations. Its actual outer identity_key_kid supplies the encoded sender; the extracted control accessor supplies target and expected sender; the stored 153-byte array supplies associated data. No equality between the outer identifier and control.assigned_key_id is assumed.

One whole owner and the same actual primitive interpreter implement sends and raw receives. Complete source/program equalities retain every optional reply and all primitive effects. Raw API attempts, including inactive rejection, have a separate ghost counter; native role fields contain no such counter. Adaptive send/raw calls preserve every non-ratchet phase field, including inactive private keys, with the actual five source callback caps and no new scheduling loss.

This is the normal-return functional representation of the native role dispatch, using already checked source helpers. It does not prove native enum/key/array or slot memory layout, compiler/runtime/allocator behavior, registration phase transitions or correct initialization, persistence, concurrency or crashes. The frame decoder and primitive handler retain their explicit interfaces. Source normalizers are analysis functions, not extracted executable runtime code.

Client coins, registration, reveals, snapshots and multi-owner/network scheduling need additional interfaces. The actual API optional plaintext is not necessarily public network observation; unknown-target disclosure requires explicit freshness or declassification. No primitive security, source-key independence or global symbolic/computational conclusion follows from these operational equalities.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false

namespace BeaconcryptCore.Computational.RawCtxBeaconLifecycle

/-- The native role variants retain every private field; primitive key-pair representations remain parameters. -/
inductive Phase (DhPair KemPair Kernel : Type) where
  | fresh (control : pqxdh.BeaconFresh) (prekey : DhPair) (kem : KemPair)
  | freshWithCoins (control : pqxdh.BeaconFresh) (prekey oneTime : DhPair) (kem : KemPair)
  | initSent (control : pqxdh.BeaconInitSent) (prekey oneTime : DhPair) (kem : KemPair)
  | established (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize) (kernel : Kernel)
  | aborted (control : pqxdh.BeaconAborted)

/-- Actual outer identity and route fields are distinct from the established control's assigned identifier. -/
structure Beacon (Identity DhPair KemPair : Type) where
  identity : Identity
  identityKeyId : Std.U64
  serverIdentity : Array Std.U8 32#usize
  phase : Phase DhPair KemPair ConcreteRatchetKernel

/-- Count every outer raw API attempt without making that counter native role state. -/
structure State (Identity DhPair KemPair : Type) where
  beacon : Beacon Identity DhPair KemPair
  rawAttempts : Nat

/-- Read the exact established pinned server accessor, without an assigned-ID equality premise. -/
theorem target_exact (control : pqxdh.BeaconEstablished) :
    control.server_key_id = ok control.server_binding.identity_key_id := by
  rfl

/-- The owner receives the stored associated data and both directions of the same kernel. -/
def selected {Identity DhPair KemPair : Type} (state : State Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (kernel : ConcreteRatchetKernel) : RawCtxWholeOwner.OwnerState Unit :=
  ⟨⟨kernel, control.server_binding.identity_key_id, PqxdhRefinement.absBytes associatedData, ()⟩, state.rawAttempts⟩

/-- Reinstall only the whole returned kernel; all native outer/control/AD fields remain the original fields. -/
def reinstall {Identity DhPair KemPair : Type} (state : State Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (owner : RawCtxWholeOwner.OwnerState Unit) : State Identity DhPair KemPair :=
  ⟨{ state.beacon with phase := .established control associatedData owner.owner.kernel }, owner.rawAttempts⟩

/-- An inactive role returns its actual API rejection; raw attempts are counted before lifecycle rejection. -/
def rejected {Identity DhPair KemPair : Type} (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State Identity DhPair KemPair) : RawCtxMixedOwner.SourceSpec.Range query × State Identity DhPair KemPair :=
  match query with
  | .inl _ => (none, state)
  | .inr _ => (.None, { state with rawAttempts := state.rawAttempts + 1 })

/-- Established calls use actual outer sender, control target/pin and stored AD; all other variants retain their full state. -/
noncomputable def beaconImpl {Identity DhPair KemPair : Type} (decode : RawCtxReceive.FrameDecoder) :
    QueryImpl RawCtxMixedOwner.SourceSpec
      (StateT (State Identity DhPair KemPair) (OracleComp RawCtxMixedOwner.NativeSpec)) :=
  fun query state =>
    let sender := state.beacon.identityKeyId
    match state.beacon.phase with
    | .established control associatedData kernel => do
        let result ← (RawCtxMixedOwner.ownerImpl sender decode query).run
          (selected state control associatedData kernel)
        pure (result.1, reinstall state control associatedData result.2)
    | _ => pure (rejected query state)

/-- Source role admission is exactly the established variant, with no cryptographic or freshness premise. -/
def Established {DhPair KemPair : Type} : Phase DhPair KemPair ConcreteRatchetKernel → Prop
  | .established _ _ _ => True
  | _ => False

/-- Every non-established phase rejects before any primitive callback and retains every private/native field. -/
theorem inactive {Identity DhPair KemPair : Type} (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Identity DhPair KemPair)
    (hinactive : ¬ Established state.beacon.phase) :
    (beaconImpl decode query).run state = pure (rejected query state) := by
  unfold beaconImpl StateT.run
  cases hphase : state.beacon.phase <;> simp_all [Established]

/-- Established owner fields are the actual source target, stored 153-byte AD, whole kernel and current attempt count. -/
theorem selected_fields {Identity DhPair KemPair : Type} (state : State Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (kernel : ConcreteRatchetKernel) :
    let owner := selected state control associatedData kernel
    owner.owner.expectedSender = control.server_binding.identity_key_id ∧
      owner.owner.associatedData = PqxdhRefinement.absBytes associatedData ∧
      owner.owner.associatedData.length = 153 ∧ owner.owner.kernel = kernel ∧
      owner.rawAttempts = state.rawAttempts := by
  simp [selected, PqxdhRefinement.absBytes_length]

/-- Exact source established dispatch retains actual outer sender and publishes the returned kernel before reply. -/
theorem established {Identity DhPair KemPair : Type} (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (kernel : ConcreteRatchetKernel)
    (hphase : state.beacon.phase = .established control associatedData kernel) :
    (beaconImpl decode query).run state = (do
      let result ← (RawCtxMixedOwner.ownerImpl state.beacon.identityKeyId decode query).run
        (selected state control associatedData kernel)
      pure (result.1, reinstall state control associatedData result.2)) := by
  simp only [beaconImpl, StateT.run, hphase]

/-- Only the returned whole kernel and ghost attempt count can change during established publication. -/
theorem reinstall_fields {Identity DhPair KemPair : Type} (state : State Identity DhPair KemPair)
    (control : pqxdh.BeaconEstablished) (associatedData : Array Std.U8 153#usize)
    (owner : RawCtxWholeOwner.OwnerState Unit) :
    let result := reinstall state control associatedData owner
    result.beacon.identity = state.beacon.identity ∧
      result.beacon.identityKeyId = state.beacon.identityKeyId ∧
      result.beacon.serverIdentity = state.beacon.serverIdentity ∧
      result.beacon.phase = .established control associatedData owner.owner.kernel ∧
      result.rawAttempts = owner.rawAttempts := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Source entry rejection or actual dispatch has the existing per-service bounds, including inactive raw attempts. -/
theorem step_bound {Identity DhPair KemPair : Type} (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (state : State Identity DhPair KemPair)
    (kind : RawCtxMixedOwner.CallKind) :
    ((beaconImpl decode query).run state).IsQueryBoundP
      (fun request => RawCtxMixedOwner.callKind request = kind)
      (match query with
       | .inl _ => RawCtxMixedOwner.sendCost kind
       | .inr _ => RawCtxMixedOwner.receiveCost kind) := by
  cases hphase : state.beacon.phase
  all_goals simp only [beaconImpl, StateT.run, hphase, isQueryBoundP_pure, bind_pure_comp, isQueryBoundP_map_iff]
  cases query with
  | inl plaintext => exact RawCtxMixedOwner.send_bounds _ _ _ _ _
  | inr raw => exact RawCtxMixedOwner.receive_bounds _ _ _ _ _

/-- Interpret the established role through the actual source send/raw wrappers, retaining the same entire primitive state. -/
noncomputable def sourceImpl {Identity DhPair KemPair PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) : QueryImpl RawCtxMixedOwner.SourceSpec
      (StateT (State Identity DhPair KemPair × PrimitiveState) (OracleComp base)) :=
  fun query state =>
    let sender := state.1.beacon.identityKeyId
    match state.1.beacon.phase with
    | .established control associatedData kernel => do
        let result ← (RawCtxMixedOwner.sourceImpl impl sender decode query).run
          (selected state.1 control associatedData kernel, state.2)
        pure (result.1, (reinstall state.1 control associatedData result.2.1, result.2.2))
    | _ => pure ((rejected query state.1).1, ((rejected query state.1).2, state.2))

/-- One established dispatch has complete state-pair equality with the supplied actual source interpreter. -/
theorem selected_interpretation {PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (query : RawCtxMixedOwner.SourceSpec.Domain) (owner : RawCtxWholeOwner.OwnerState Unit)
    (primitive : PrimitiveState) :
    (simulateQ impl ((RawCtxMixedOwner.ownerImpl sender decode query).run owner)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        ((RawCtxMixedOwner.sourceImpl impl sender decode query).run (owner, primitive)) := by
  simpa [OracleSpec.query] using RawCtxMixedOwner.schedule_interpretation impl sender decode
    (RawCtxMixedOwner.SourceSpec.query query) owner primitive

/-- Complete native role interpretation preserves every actual optional reply and all owner/primitive effects. -/
theorem beacon_interpretation {Identity DhPair KemPair PrimitiveState : Type} {ι : Type}
    {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) :
    (impl.mapStateTBase (beaconImpl (Identity := Identity) (DhPair := DhPair) (KemPair := KemPair) decode)).flattenStateT =
      sourceImpl impl decode := by
  funext query state
  change (fun result => (result.1.1, (result.1.2, result.2))) <$>
      (simulateQ impl ((beaconImpl decode query).run state.1)).run state.2 =
    (sourceImpl impl decode query).run state
  cases hphase : state.1.beacon.phase
  case established control associatedData kernel =>
    rw [established decode query state.1 control associatedData kernel hphase]
    simp only [bind_pure_comp, simulateQ_map, StateT.run_map, Functor.map_map]
    rw [selected_interpretation]
    simp only [sourceImpl, StateT.run, hphase, Functor.map_map, bind_pure_comp]
  all_goals rw [inactive decode query state.1 (by simp [Established, hphase])]
  all_goals simp only [simulateQ_pure, StateT.run_pure, map_pure]
  all_goals simp only [sourceImpl, StateT.run, hphase]

/-- Arbitrary adaptive send/raw scheduling retains the entire Beacon and actual primitive state, up to tuple reassociation only. -/
theorem schedule_interpretation {Identity DhPair KemPair PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (state : State Identity DhPair KemPair) (primitive : PrimitiveState) :
    (simulateQ impl ((simulateQ (beaconImpl decode) client).run state)).run primitive =
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (sourceImpl impl decode) client).run (state, primitive) := by
  rw [simulateQ_mapStateTBase_run_eq_map_flattenStateT, beacon_interpretation]

/-- All outer attempts remain in their service budgets, including lifecycle rejection, arbitrary replies and adaptive stopping. -/
theorem schedule_bound {Identity DhPair KemPair Result : Type}
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Identity DhPair KemPair) (kind : RawCtxMixedOwner.CallKind) :
    ((simulateQ (beaconImpl decode) client).run state).IsQueryBoundP
      (fun query => RawCtxMixedOwner.callKind query = kind)
      (RawCtxMixedOwner.sendCost kind * qSend + RawCtxMixedOwner.receiveCost kind * qRaw) := by
  induction client using OracleComp.inductionOn generalizing qSend qRaw state with
  | pure value => trivial
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hSend hRaw
      rw [simulateQ_query_bind, StateT.run_bind]
      cases query with
      | inl plaintext =>
          simp only [Sum.isLeft, Sum.isRight, Bool.false_eq_true, not_true_eq_false, false_or, ↓reduceIte] at hSend hRaw
          apply (isQueryBoundP_bind (step_bound decode (.inl plaintext) state kind)
            (fun result _ => ih result.1 (qSend - 1) qRaw (hSend.2 result.1)
              (hRaw.2 result.1) result.2)).mono
          cases kind <;> simp only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost] <;> omega
      | inr raw =>
          simp only [Sum.isLeft, Sum.isRight, Bool.false_eq_true, not_true_eq_false, false_or, ↓reduceIte] at hSend hRaw
          apply (isQueryBoundP_bind (step_bound decode (.inr raw) state kind)
            (fun result _ => ih result.1 qSend (qRaw - 1) (hSend.2 result.1)
              (hRaw.2 result.1) result.2)).mono
          cases kind <;> simp only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost] <;> omega

/-- All five actual source callback caps carry through the full Beacon lifecycle boundary. -/
theorem schedule_bounds {Identity DhPair KemPair Result : Type}
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qSend qRaw : Nat)
    (hSend : client.IsQueryBoundP (fun query => query.isLeft = true) qSend)
    (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Identity DhPair KemPair) :
    let program := (simulateQ (beaconImpl decode) client).run state
    program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .kdf) (qSend + 51 * qRaw) ∧
      program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .sealing) qSend ∧
      program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .opening) qRaw ∧
      program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .hash) (qSend + qRaw) ∧
      program.IsQueryBoundP (fun query => RawCtxMixedOwner.callKind query = .writer) qSend := by
  simpa only [RawCtxMixedOwner.sendCost, RawCtxMixedOwner.receiveCost,
    Nat.one_mul, Nat.zero_mul, Nat.add_zero, Nat.zero_add] using
    And.intro (schedule_bound decode client qSend qRaw hSend hRaw state .kdf)
      (And.intro (schedule_bound decode client qSend qRaw hSend hRaw state .sealing)
        (And.intro (schedule_bound decode client qSend qRaw hSend hRaw state .opening)
          (And.intro (schedule_bound decode client qSend qRaw hSend hRaw state .hash)
            (schedule_bound decode client qSend qRaw hSend hRaw state .writer))))

/-- Retain all role fields, including private inactive material, while omitting only the established ratchet. -/
def phaseFields {DhPair KemPair : Type} : Phase DhPair KemPair ConcreteRatchetKernel → Phase DhPair KemPair Unit
  | .fresh control prekey kem => .fresh control prekey kem
  | .freshWithCoins control prekey oneTime kem => .freshWithCoins control prekey oneTime kem
  | .initSent control prekey oneTime kem => .initSent control prekey oneTime kem
  | .established control associatedData _ => .established control associatedData ()
  | .aborted control => .aborted control

def retained {Identity DhPair KemPair : Type} (state : State Identity DhPair KemPair) :=
  (state.beacon.identity, state.beacon.identityKeyId, state.beacon.serverIdentity, phaseFields state.beacon.phase)

/-- Every actual source call retains all role/identity fields and counts each raw attempt exactly once. -/
theorem source_step {Identity DhPair KemPair PrimitiveState : Type} {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (state : State Identity DhPair KemPair × PrimitiveState)
    (result : RawCtxMixedOwner.SourceSpec.Range query × (State Identity DhPair KemPair × PrimitiveState))
    (supported : result ∈ support ((sourceImpl impl decode query).run state)) :
    result.2.1.rawAttempts = state.1.rawAttempts + (if query.isRight then 1 else 0) ∧
      retained result.2.1 = retained state.1 := by
  cases hphase : state.1.beacon.phase
  all_goals simp only [sourceImpl, StateT.run, hphase, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at supported
  case established control associatedData kernel =>
    obtain ⟨inner, hinner, rfl⟩ := supported
    have hstep := RawCtxMixedOwner.source_step impl state.1.beacon.identityKeyId decode query
      (selected state.1 control associatedData kernel, state.2) inner hinner
    simpa only [reinstall, retained, hphase, phaseFields, and_true, selected] using hstep.1
  all_goals subst result
  all_goals cases query <;> simp [rejected, retained]

/-- Complete adaptive source scheduling preserves every retained native/private role field and all actual raw-attempt counts. -/
theorem source_schedule {Identity DhPair KemPair PrimitiveState Result : Type}
    {ι : Type} {base : OracleSpec ι}
    (impl : QueryImpl RawCtxMixedOwner.NativeSpec (StateT PrimitiveState (OracleComp base)))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (qRaw : Nat) (hRaw : client.IsQueryBoundP (fun query => query.isRight = true) qRaw)
    (state : State Identity DhPair KemPair × PrimitiveState)
    (result : Result × (State Identity DhPair KemPair × PrimitiveState))
    (supported : result ∈ support ((simulateQ (sourceImpl impl decode) client).run state)) :
    result.2.1.rawAttempts ≤ state.1.rawAttempts + qRaw ∧ retained result.2.1 = retained state.1 := by
  induction client using OracleComp.inductionOn generalizing qRaw state result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at supported
      subst result
      exact ⟨Nat.le_add_right _ _, rfl⟩
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at hRaw
      rw [simulateQ_query_bind, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨step, hstep, htail⟩ := supported
      have hlocal := source_step impl decode query state step hstep
      have rest := ih step.1 _ (hRaw.2 step.1) step.2 result htail
      refine ⟨?_, rest.2.trans hlocal.2⟩
      by_cases right : query.isRight = true
      · simp only [right, ite_true] at hlocal rest
        have positive : 0 < qRaw := hRaw.1.resolve_left (not_not.mpr right)
        omega
      · simp only [right, Bool.false_eq_true, ite_false, Nat.add_zero] at hlocal rest
        omega

end BeaconcryptCore.Computational.RawCtxBeaconLifecycle

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.target_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.target_exact

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.inactive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.inactive

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.selected_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.selected_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.established' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.established

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.reinstall_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.reinstall_fields

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.step_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.step_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.selected_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.selected_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.beacon_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.beacon_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_interpretation

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_bound

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.schedule_bounds

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.source_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.source_step

/--
info: 'BeaconcryptCore.Computational.RawCtxBeaconLifecycle.source_schedule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxBeaconLifecycle.source_schedule
