import BeaconcryptCore.Computational.PqxdhInitialOriginPost

/-!
The actual first Beacon receive retains its literal initializer return before any ratchet advancement. A private attempted-initializer receipt contains that kernel and the same prepared source response, including later failures. Erasure recovers the existing origin-marked program, so its Boolean coordinate gate and every protocol operation remain unchanged. This receipt is an analysis annotation, not an executable observer interface or a proof that kernel bytes identify a session.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFinishReceipt
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared PqxdhInitialGenericBeacon
variable {Kernel Origin I D K X Response Shared : Type}

structure Receipt (Kernel Response Shared : Type) where
  prepared : Prepared Response Shared
  initial : Kernel

abbrev Result (Kernel Origin I D K Response Shared : Type) :=
  PqxdhInitialFinishOrigin.Result Kernel Origin I D K × Option (Receipt Kernel Response Shared)

def successful (result : Result Kernel Origin I D K Response Shared) : Option (Receipt Kernel Response Shared) :=
  if result.1.1.1.isSome then result.2 else none

section Effects
variable {m : Type → Type*} [Monad m]

noncomputable def prepared (mark : Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K)
    (pending : Prepared Response Shared) : m (Result Kernel Origin I D K Response Shared) := do
  let kernel ← initial pending.root
  match kernel with
  | none => pure ((finish control state none, none), none)
  | some kernel => do
      let staged ← afterInitial calls application decode pending kernel
      let result := finish control state staged
      pure (PqxdhInitialFinishOrigin.tag (mark pending.root) result,
        some ⟨pending, kernel⟩)

noncomputable def owner (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) : m (Result Kernel Origin I D K Response Shared) :=
  match state.beacon.phase with
  | .initSent control prekey oneTime kem => do
      let pending ← simulateQ pre (PqxdhBeaconPhase2Shared.prepare control state.beacon.identity prekey oneTime kem raw)
      match pending with
      | none => pure ((finish control state none, none), none)
      | some pending => prepared mark calls application initial decode control state pending
  | _ => pure (((none, state), none), none)

variable [LawfulMonad m]

/-- Erasing the receipt retains the exact original initializer, getter, raw receive and origin-tagged publication, in their source order. -/
theorem prepared_erase (mark : Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K)
    (pending : Prepared Response Shared) :
    Prod.fst <$> prepared mark calls application initial decode control state pending =
      (fun staged => PqxdhInitialFinishOrigin.tag (mark pending.root) (finish control state staged)) <$>
        PqxdhInitialGenericBeacon.tail calls application initial decode pending := by
  simp only [prepared, PqxdhInitialGenericBeacon.tail, map_bind]
  apply bind_congr
  intro kernel
  cases kernel
  · simp only [map_pure, PqxdhInitialFinishOrigin.tag, finish, Option.map_none]
  · simp only [bind_pure_comp, Functor.map_map]

/-- Erasing only the new receipt recovers the existing origin-marked owner, including failed and inactive attempts and every original private callback effect. -/
theorem owner_erase (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) :
    Prod.fst <$> owner mark pre calls application initial decode raw state =
      PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw state := by
  unfold owner PqxdhInitialFinishOrigin.owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [map_bind]
    apply bind_congr
    intro pending
    cases pending with
    | none => simp only [map_pure]
    | some pending =>
        rw [prepared_erase]
        simp only [bind_pure_comp]
  all_goals simp only [map_pure]

end Effects

/-- Every actual successful initializer return is recorded before the complete subsequent receive result is considered, including a later rejection or failed publication. -/
theorem prepared_records {State : Type} (mark : Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (entry : BeaconState Kernel I D K)
    (pending : Prepared Response Shared) (kernel : Kernel) (before atInitial after : State)
    (staged : Option (Staged Kernel))
    (initialized : (some kernel, atInitial) ∈ support ((initial pending.root).run before))
    (completed : (staged, after) ∈ support ((afterInitial calls application decode pending kernel).run atInitial)) :
    ((PqxdhInitialFinishOrigin.tag (mark pending.root) (finish control entry staged), some ⟨pending, kernel⟩), after) ∈
      support ((prepared mark calls application initial decode control entry pending).run before) := by
  simp only [prepared, StateT.run_bind, mem_support_bind_iff]
  refine ⟨(some kernel, atInitial), initialized, ?_⟩
  simp only [StateT.run_bind, mem_support_bind_iff]
  exact ⟨(staged, after), completed, by simp only [StateT.run_pure, mem_support_pure_iff]⟩

/-- Every receipt identifies the actual optional initializer return and its complete subsequent getter/raw-receive execution, retaining all intermediate and final private states. -/
theorem prepared_origin {State : Type} (mark : Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (entry : BeaconState Kernel I D K)
    (pending : Prepared Response Shared) (before : State)
    (result : Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((prepared mark calls application initial decode control entry pending).run before))
    (receipt : Receipt Kernel Response Shared) (recorded : result.1.2 = some receipt) :
    ∃ (afterInitialState : State) (staged : Option (Staged Kernel)),
      receipt.prepared = pending ∧
      (some receipt.initial, afterInitialState) ∈ support ((initial pending.root).run before) ∧
      (staged, result.2) ∈ support ((afterInitial calls application decode pending receipt.initial).run afterInitialState) ∧
      result.1.1 = PqxdhInitialFinishOrigin.tag (mark pending.root) (finish control entry staged) := by
  unfold prepared at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨initialized, reached, rest⟩ := supported
  cases kernelFound : initialized.1 with
  | none =>
      simp only [kernelFound, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      cases recorded
  | some kernel =>
      simp only [kernelFound, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, tailReached, final⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at final
      subst result
      cases Option.some.inj recorded
      exact ⟨initialized.2, staged.1, rfl, by simpa only [← kernelFound] using reached, tailReached, rfl⟩

/-- A receipt in the complete native-shaped finish comes from its own successful preparation and literal initializer kernel before the getter and first raw receive advance it. -/
theorem owner_origin {State : Type} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((owner mark pre calls application initial decode raw entry).run before))
    (receipt : Receipt Kernel Response Shared) (recorded : result.1.2 = some receipt) :
    ∃ control prekey oneTime kem, ∃ (atPrepared atInitial : State) (staged : Option (Staged Kernel)),
      entry.beacon.phase = .initSent control prekey oneTime kem ∧
      (some receipt.prepared, atPrepared) ∈ support ((simulateQ pre
        (PqxdhBeaconPhase2Shared.prepare control entry.beacon.identity prekey oneTime kem raw)).run before) ∧
      (some receipt.initial, atInitial) ∈ support ((initial receipt.prepared.root).run atPrepared) ∧
      (staged, result.2) ∈ support ((afterInitial calls application decode receipt.prepared receipt.initial).run atInitial) ∧
      result.1.1 = PqxdhInitialFinishOrigin.tag (mark receipt.prepared.root) (finish control entry staged) := by
  unfold owner at supported
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨preparedResult, reached, rest⟩ := supported
    cases preparedFound : preparedResult.1 with
    | none =>
        simp only [preparedFound, StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        cases recorded
    | some pending =>
        simp only [preparedFound] at rest
        obtain ⟨atInitial, staged, same, initialized, completed, exactResult⟩ :=
          prepared_origin mark calls application initial decode control entry pending preparedResult.2 result rest receipt recorded
        subst pending
        exact ⟨control, prekey, oneTime, kem, preparedResult.2, atInitial, staged, rfl,
          by simpa only [← preparedFound] using reached, initialized, completed, exactResult⟩
  all_goals
    simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    cases recorded

private theorem prepared_initialized {State : Type} (mark : Secrets Shared → Origin)
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (control : pqxdh.BeaconInitSent) (entry : BeaconState Kernel I D K)
    (pending : Prepared Response Shared) (before : State)
    (result : Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((prepared mark calls application initial decode control entry pending).run before)) :
    result.1.1.1.1.isSome = true → result.1.2.isSome = true := by
  unfold prepared at supported
  simp only [StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨initialized, _, rest⟩ := supported
  cases kernelFound : initialized.1 with
  | none =>
      simp only [kernelFound, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      intro impossible
      cases impossible
  | some kernel =>
      simp only [kernelFound, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, _, final⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at final
      subst result
      exact fun _ => rfl

private theorem owner_initialized {State : Type} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((owner mark pre calls application initial decode raw entry).run before)) :
    result.1.1.1.1.isSome = true → result.1.2.isSome = true := by
  unfold owner at supported
  cases phase : entry.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [phase, StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨preparedResult, _, rest⟩ := supported
    cases preparedFound : preparedResult.1 with
    | none =>
        simp only [preparedFound, StateT.run_pure, mem_support_pure_iff] at rest
        subst result
        intro impossible
        cases impossible
    | some pending =>
        exact prepared_initialized mark calls application initial decode control entry pending preparedResult.2 result
          (by simpa only [preparedFound] using rest)
  all_goals
    simp only [phase, StateT.run_pure, mem_support_pure_iff] at supported
    subst result
    intro impossible
    cases impossible

/-- Filtering the attempted-initializer receipt for installation succeeds exactly when this same original finish publishes its application reply. Failed attempts retain only their private attempted-initializer evidence. -/
theorem published {State : Type} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : Result Kernel Origin I D K Response Shared × State)
    (supported : result ∈ support ((owner mark pre calls application initial decode raw entry).run before)) :
    (successful result.1).isSome = result.1.1.1.1.isSome := by
  cases success : result.1.1.1.1.isSome
  · simp only [successful, success, Bool.false_eq_true, ite_false, Option.isSome_none]
  · simpa only [successful, success, ite_true] using
      owner_initialized mark pre calls application initial decode raw entry before result supported success

/-- Private receipt bookkeeping preserves every original source query-class allowance exactly; no initializer or continuation work is declared free. -/
theorem queries {ι : Type} {spec : OracleSpec ι} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (calls : RawCtxChainOwner.Calls Kernel (OracleComp spec)) (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (initial : Secrets Shared → OracleComp spec (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K)
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    (owner mark pre calls application initial decode raw state).IsQueryBoundP predicate budget ↔
      (PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw state).IsQueryBoundP predicate budget := by
  rw [← owner_erase mark pre calls application initial decode raw state]
  exact (isQueryBoundP_map_iff _ _ _).symm

def roots (receipt : Receipt (PqxdhInitialPendingPost.KernelOf RatchetChain) Response Shared) :
    RatchetChain × RatchetChain :=
  (receipt.initial.send_chain, receipt.initial.receive_chain)

end BeaconcryptCore.Computational.PqxdhInitialFinishReceipt

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.owner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.owner_erase

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.owner_origin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.owner_origin

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.published' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.published

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.queries' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.queries

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_records' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishReceipt.prepared_records
