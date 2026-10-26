import BeaconcryptCore.Computational.PqxdhServerAuthBeaconFactor

/-! Exact sequence-one receive settlement at the initial Beacon state, with arbitrary chain and material types. The selected target key is consumed without being placed in a skipped slot. The theorem applies to the source input sequence one; a caller must retain the actual reply/frame provenance before using the Beacon registration gate to establish that input. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening

/-- The source initializer with arbitrary chain and material types. -/
def initial {Send Receive Material : Type} (send : Send) (receive : Receive) : RefinedRatchet Send Receive Material :=
  { control := ⟨0#u64, 0#u64, ⟨Std.Array.repeat 50#usize 0#u64, 0#u8⟩⟩
    send_chain := send
    receive_chain := receive
    receive_slots := Std.Array.repeat 50#usize .None }

/-- This is exactly the extracted zero-counter constructor. -/
theorem initial_new {Send Receive Material : Type} (send : Send) (receive : Receive) :
    RefinedRatchet.new Material send receive = ok (initial send receive) := rfl

/-- The single derivation request of the exact sequence-one initial receive. -/
def requested {Send Receive Material Context : Type} (send : Send) (receive : Receive) (context : Context) :
    RawCtxChainReceive.Kdf Send Receive Material Context :=
  ⟨initial send receive, context, 1#u64, (initial (Material := Material) send receive).control,
    Std.Array.repeat 50#usize .None, 0#u8, 0#u8, 1#u8, receive⟩

/-- The extracted initial receive takes precisely one derivation, with no skipped slot. -/
theorem begin_one {Send Receive Material Context : Type} (send : Send) (receive : Receive) (context : Context) :
    RawCtxChainReceive.normalBegin (initial (Material := Material) send receive) 1#u64 context =
      .kdfRequested (requested send receive context) := by
  have exactRun := RawCtxChainReceive.normalBegin_exact (initial (Material := Material) send receive) 1#u64 context
  obtain ⟨derivations, planned, count⟩ := control.plan_receive_until_accept
    (initial (Material := Material) send receive).control 1#u64 (by simp [initial]) (by simp [initial])
  simp only [initial] at count
  have one : derivations = 1#u64 := by scalar_tac
  have noSkip : refined_receive_slots_are_empty (initial (Material := Material) send receive) 0#u8 0#u8 = ok true := by
    rw [refined_receive_slots_are_empty, refined_receive_slots_are_empty_loop, loop.eq_def]
    simp [refined_receive_slots_are_empty_loop.body]
  have source : RawCtxChainReceive.beginReceive (initial (Material := Material) send receive) 1#u64 context =
      ok (.kdfRequested (requested send receive context)) := by
    simp only [RawCtxChainReceive.beginReceive, planned, one, bind_tc_ok]
    simp only [show (1#u64 = 0#u64) = False from by decide, ite_false,
      show (1#u64 - 1#u64 : RustM Std.U64) = ok 0#u64 from rfl,
      bind_tc_ok, show (0#u64 > control.RATCHET_MAX_GAP) = False from by decide,
      show (initial (Material := Material) send receive).control.receive_cache_len = ok 0#u8 from rfl, lift,
      show UScalar.cast .U8 0#u64 = 0#u8 from rfl, show UScalar.cast .U8 1#u64 = 1#u8 from rfl]
    rw [noSkip]
    rfl
  exact RustM.ok.inj (exactRun.symm.trans source)

/-- The validated target is uncached; all staged slots remain empty. -/
def targetPending {Send Receive Material : Type} (send : Send) (receive next : Receive)
    (material : Material) : PendingReceive Receive Material :=
  ⟨{ (initial (Material := Material) send receive).control with receive_sequence := 1#u64 },
    next, Std.Array.repeat 50#usize .None, 1#u64, material, 0#u8, 0#u8⟩

/-- The source sequence-one opening retains no skipped material in its pending state. -/
def opening {Send Receive Material Context : Type} (send : Send) (receive next : Receive)
    (material : Material) (context : Context) : RawCtxInterpretedOpening.Opening Send Receive Material Context :=
  ⟨initial send receive, context, .PreparedReceiveFutureCase (targetPending send receive next material)⟩

/-- Every typed first derivation resumes to the exact uncached target opening. -/
theorem resume_one {Send Receive Material Context : Type} (send : Send) (receive next : Receive)
    (material : Material) (context : Context) :
    RawCtxChainReceive.normalResume (requested send receive context) (next, material) =
      .openRequested (opening send receive next material context) := by
  have exactRun := RawCtxChainReceive.normalResume_exact (requested send receive context) (next, material)
  have valid : pending_receive_is_valid (initial send receive) (targetPending send receive next material) 1#u64 = ok true := by
    apply pending_receive_is_valid_true <;> simp [initial, targetPending]
    · rw [control.lookup_receive_key_unfold, control.lookup_receive_key_loop, loop.eq_def]
      simp [control.lookup_receive_key_loop.body, lift]
    all_goals
      intro i below
      change (List.replicate 50 (none : Option (CachedReceiveKey Material)))[i]?.getD default = none
      simp only [List.getElem?_replicate, below, ite_true, Option.getD_some]
  have source : RawCtxChainReceive.resume (requested send receive context) (ok (next, material)) =
      ok (.openRequested (opening send receive next material context)) := by
    simp only [RawCtxChainReceive.resume, requested,
      show (1#u8 = 0#u8) = False from by decide, ite_false, ite_true,
      show control.advance_receive_target (initial (Material := Material) send receive).control =
        ok ⟨{ (initial (Material := Material) send receive).control with receive_sequence := 1#u64 },
          .Some 1#u64⟩ from rfl, bind_tc_ok]
    simp only [targetPending] at valid
    simp only [valid, bind_tc_ok, ite_true]
    rfl
  exact RustM.ok.inj (exactRun.symm.trans source)

/-- Successful sequence-one publication advances the receive counter and stores no material. -/
def published {Send Receive Material : Type} (send : Send) (next : Receive) : RefinedRatchet Send Receive Material :=
  { initial send next with control :=
    { (initial (Material := Material) send next).control with receive_sequence := 1#u64 } }

/-- Exact extracted publication retains all empty slots and consumes the uncached target. -/
theorem publish_one {Send Receive Material : Type} (send : Send) (receive next : Receive) (material : Material) :
    publish_future_receive (initial send receive) (targetPending send receive next material) =
      ok (published send next) := by
  obtain ⟨result, actual, controlEq, sendEq, receiveEq, slots⟩ := publish_future_receive_exact
    (initial send receive) (targetPending send receive next material) (by simp [targetPending])
  have same : result = published send next := by
    rcases result with ⟨control, sending, receiving, slotsOut⟩
    simp only [targetPending, initial, published] at *
    congr
    apply Subtype.ext
    apply List.ext_getElem
    · exact slotsOut.property.trans (Std.Array.repeat 50#usize (core.option.Option.None : core.option.Option (CachedReceiveKey Material))).property.symm
    · intro i first second
      have slotEq := slots i (by simpa [slotsOut.property] using first)
      simpa only [ite_self, _root_.getElem!_pos slotsOut.val i first,
        _root_.getElem!_pos (Std.Array.repeat 50#usize (core.option.Option.None : core.option.Option (CachedReceiveKey Material))).val i second] using slotEq
  exact actual.trans (congrArg RustM.ok same)

/-- The exact optional reply selects source rollback or the material-free published state. -/
theorem finish_one {Send Receive Material Context Plaintext : Type} (send : Send) (receive next : Receive)
    (material : Material) (context : Context) (reply : core.option.Option Plaintext) :
    RawCtxChainReceive.normalFinish (opening send receive next material context) reply =
      ((match reply with | .None => initial send receive | .Some _ => published send next), reply) := by
  apply RustM.ok.inj
  rw [← RawCtxChainReceive.normalFinish_exact]
  cases reply with
  | none => rfl
  | some plaintext => simp only [RawCtxInterpretedOpening.finish, opening, publish_one, bind_tc_ok]

/-- The complete sequence-one source driver calls one derivation and one opening, keeping both arbitrary callback effects and the challenger's actual optional plaintext. -/
theorem execute_one {Send Receive Material Context Plaintext : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (native : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) m)
    (send : Send) (receive : Receive) (context : Context) :
    simulateQ native (RawCtxChainReceive.execute (initial send receive) 1#u64 context) = (do
      let step ← native (.inl receive)
      let reply ← native (.inr (opening send receive step.1 step.2 context))
      pure ((match reply with | .None => initial send receive | .Some _ => published send step.1), reply)) := by
  simp only [RawCtxChainReceive.execute, begin_one, RawCtxChainReceive.program,
    simulateQ_bind, simulateQ_spec_query]
  refine bind_congr fun step => ?_
  rcases step with ⟨next, material⟩
  simp only [resume_one, RawCtxChainReceive.program, simulateQ_bind, simulateQ_spec_query,
    simulateQ_pure, finish_one]
  refine bind_congr fun reply => ?_
  cases reply <;> rfl

/-- Empty initial slots contain no material under any interpretation. -/
theorem initial_map {Send Receive Material Value : Type} (interpret : Material → Value)
    (send : Send) (receive : Receive) :
    RawCtxMaterialInterpretation.mapRefined interpret (initial send receive) = initial send receive := by
  rfl

/-- Successful sequence-one slots contain no material under any interpretation. -/
theorem published_map {Send Receive Material Value : Type} (interpret : Material → Value)
    (send : Send) (next : Receive) :
    RawCtxMaterialInterpretation.mapRefined interpret (published send next) = published send next := by
  rfl

/-- The complete sequence-one result is independent of its material interpretation. The identical callback execution and every monadic effect are still retained. -/
theorem execute_one_material {Send Receive Material Value Context Plaintext : Type}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (native : QueryImpl (RawCtxChainReceive.ReceiveSpec Send Receive Material Context Plaintext) m)
    (first second : Material → Value) (send : Send) (receive : Receive) (context : Context) :
    Prod.map (RawCtxMaterialInterpretation.mapRefined first) id <$>
        simulateQ native (RawCtxChainReceive.execute (initial send receive) 1#u64 context) =
      Prod.map (RawCtxMaterialInterpretation.mapRefined second) id <$>
        simulateQ native (RawCtxChainReceive.execute (initial send receive) 1#u64 context) := by
  rw [execute_one]
  simp only [map_bind, map_pure]
  refine bind_congr fun step => bind_congr fun reply => ?_
  cases reply <;> simp only [Prod.map_def, initial_map, published_map]

end BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening

/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.initial_new' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.initial_new
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.begin_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.begin_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.resume_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.resume_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.publish_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.publish_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.finish_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.finish_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.execute_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.execute_one
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.initial_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.initial_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.published_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.published_map
/-- info: 'BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.execute_one_material' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhServerAuthBeaconFirstOpening.execute_one_material
