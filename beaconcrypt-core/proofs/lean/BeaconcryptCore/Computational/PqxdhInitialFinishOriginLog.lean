import BeaconcryptCore.Computational.PqxdhInitialFinishOrigin

/-!
The initializer-origin marker is written at the actual initializer callback, before the first raw receive can reach a selected private derivation. Every other callback lifts past this private marker. Successful owner publication attaches the recorded marker; the original client receives only its original optional application reply. This realizes the finish transcript with an explicit pre-cut state field rather than reconstructing a forgotten secret or selecting an inverse of a continuation.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared PqxdhInitialGenericBeacon
variable {Kernel Origin I D K X Response Shared Metadata : Type}
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

def calls (original : RawCtxChainOwner.Calls Kernel m) : RawCtxChainOwner.Calls Kernel (StateT (Option Origin) m) where
  receive := fun entry number context => liftM (original.receive entry number context)
  send := fun entry context => liftM (original.send entry context)

def initial (mark : Secrets Shared → Origin) (original : Secrets Shared → m (Option Kernel))
    (secrets : Secrets Shared) : StateT (Option Origin) m (Option Kernel) :=
  fun _ => (fun kernel => (kernel, some (mark secrets))) <$> original secrets

private theorem raw_lift (original : RawCtxChainOwner.Calls Kernel m)
    (decode : RawCtxReceive.FrameDecoder) (raw : Pqxdh.Bytes) (entry : RawCtxChainOwner.State Kernel Metadata)
    (saved : Option Origin) :
    (((RawCtxChainOwner.rawReceive (calls original) decode raw).run entry).run saved) =
      (fun result => (result, saved)) <$> (RawCtxChainOwner.rawReceive original decode raw).run entry := by
  simp only [RawCtxChainOwner.rawReceive, StateT.run]
  by_cases empty : raw.isEmpty = true
  · simp [empty]; rfl
  · simp only [empty, Bool.false_eq_true, if_false]
    cases decoded : decode raw with
    | none => simp only [map_pure]; rfl
    | some frame =>
      by_cases valid : RawCtxReceive.ValidFrame entry.expectedSender entry.associatedData frame
      · simp only [valid, if_true, calls, bind_pure_comp]
        change ((RawCtxChainOwner.publish entry <$> (StateT.lift (original.receive entry.kernel frame.sequence ⟨raw, frame, entry.associatedData⟩) : StateT (Option Origin) m _)).run saved) = _
        simp only [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map]
      · simp [valid]; rfl

private theorem after_lift (original : RawCtxChainOwner.Calls Kernel m)
    (application : Response → m (Option Pqxdh.Bytes)) (decode : RawCtxReceive.FrameDecoder)
    (pending : Prepared Response Shared) (kernel : Kernel) (saved : Option Origin) :
    (afterInitial (calls original) (fun reply => StateT.lift (application reply)) decode pending kernel).run saved =
      (fun result => (result, saved)) <$> afterInitial original application decode pending kernel := by
  simp only [afterInitial, StateT.run_bind, StateT.run_lift, bind_assoc, pure_bind, map_bind]
  apply bind_congr
  intro raw
  cases raw with
  | none => simp only [StateT.run_pure, map_pure]
  | some raw =>
    simp only [bind_pure_comp, StateT.run_map, raw_lift, Functor.map_map]

/-- The actual initializer records its marker before the first receive, and the complete remaining tail preserves that marker on every optional outcome. -/
theorem tail_logged (mark : Secrets Shared → Origin) (original : RawCtxChainOwner.Calls Kernel m)
    (application : Response → m (Option Pqxdh.Bytes)) (originalInitial : Secrets Shared → m (Option Kernel))
    (decode : RawCtxReceive.FrameDecoder) (pending : Prepared Response Shared) (saved : Option Origin) :
    (tail (calls original) (fun reply => StateT.lift (application reply))
      (initial mark originalInitial) decode pending).run saved =
      (fun result => (result, some (mark pending.root))) <$>
        tail original application originalInitial decode pending := by
  simp only [PqxdhInitialGenericBeacon.tail, StateT.run_bind, map_bind]
  change ((fun kernel => (kernel, some (mark pending.root))) <$> originalInitial pending.root >>= _) = _
  simp only [bind_map_left]
  apply bind_congr
  intro kernel
  cases kernel with
  | none => simp only [StateT.run_pure, map_pure]
  | some kernel => exact after_lift original application decode pending kernel _

def published (result : (Option Pqxdh.Bytes × BeaconState Kernel I D K) × Option Origin) :
    PqxdhInitialFinishOrigin.Result Kernel Origin I D K :=
  (result.1, if result.1.1.isSome then result.2 else none)

private theorem lifted_run {Value : Type} (work : m Value) (saved : Option Origin) :
    (liftM work : StateT (Option Origin) m Value).run saved =
      (fun value => (value, saved)) <$> work := by
  change (StateT.lift work).run saved = _
  simp only [StateT.run_lift, bind_pure_comp]

/-- Recording the initializer marker before the cut and retaining it through the source finish realizes exactly the successful-installation transcript. -/
theorem owner_logged (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (original : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (originalInitial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) (saved : Option Origin) :
    published <$> (PqxdhInitialGenericBeacon.owner (pre.liftTarget (StateT (Option Origin) m))
      (calls original) (fun reply => StateT.lift (application reply))
      (initial mark originalInitial) decode raw state).run saved =
    PqxdhInitialFinishOrigin.owner mark pre original application originalInitial decode raw state := by
  unfold PqxdhInitialGenericBeacon.owner PqxdhInitialFinishOrigin.owner
  cases phase : state.beacon.phase
  case initSent control prekey oneTime kem =>
    simp only [StateT.run_bind, simulateQ_liftTarget, lifted_run, bind_map_left, map_bind]
    apply bind_congr
    intro prepared
    cases prepared with
    | none => simp only [StateT.run_pure, map_pure]; rfl
    | some prepared =>
      simp only [StateT.run_bind, tail_logged, bind_map_left, StateT.run_pure, map_bind, map_pure]
      apply bind_congr
      intro staged
      apply congrArg pure
      unfold published PqxdhInitialFinishOrigin.tag
      cases (finish control state staged).1 <;> rfl
  all_goals simp only [StateT.run_pure, map_pure]; rfl

/-- Erasing the private marker recovers the original complete finish, including preparation, all optional failures, the first receive and publication. -/
theorem owner_erase (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (original : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (originalInitial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) (saved : Option Origin) :
    Prod.fst <$> (PqxdhInitialGenericBeacon.owner (pre.liftTarget (StateT (Option Origin) m))
      (calls original) (fun reply => StateT.lift (application reply))
      (initial mark originalInitial) decode raw state).run saved =
    PqxdhInitialGenericBeacon.owner pre original application originalInitial decode raw state := by
  have equality := congrArg (fun work => Prod.fst <$> work)
    (owner_logged mark pre original application originalInitial decode raw state saved)
  rw [PqxdhInitialFinishOrigin.erase] at equality
  simpa only [Functor.map_map, published] using equality

/-- The explicit origin log preserves every syntactic oracle-class budget of the actual source finish. -/
theorem owner_query_bound {ι : Type} {spec : OracleSpec ι} (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (OracleComp spec))
    (original : RawCtxChainOwner.Calls Kernel (OracleComp spec))
    (application : Response → OracleComp spec (Option Pqxdh.Bytes))
    (originalInitial : Secrets Shared → OracleComp spec (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) (saved : Option Origin)
    (predicate : spec.Domain → Prop) [DecidablePred predicate] (budget : Nat) :
    ((PqxdhInitialGenericBeacon.owner (pre.liftTarget (StateT (Option Origin) (OracleComp spec)))
      (calls original) (fun reply => StateT.lift (application reply))
      (initial mark originalInitial) decode raw state).run saved).IsQueryBoundP predicate budget ↔
    (PqxdhInitialGenericBeacon.owner pre original application originalInitial decode raw state).IsQueryBoundP predicate budget := by
  rw [← owner_erase mark pre original application originalInitial decode raw state saved]
  exact (isQueryBoundP_map_iff _ _ _).symm

end BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.tail_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.tail_logged
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_logged' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_logged
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_erase
/-- info: 'BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_query_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialFinishOriginLog.owner_query_bound
