-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotControl
/-! A computable analysis observer records only opaque slot IDs, public handles and successful installation ordinals. It forwards every original query/reply once, keeps failures literal, and reconstructs the free controller's final slot map without exposing a root, key, kernel, seed, chain state or cache. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
open PqxdhRecordLiftInterface (WorldSpec Slot Role)
open PqxdhDeploymentInterface (Handle)
open PqxdhRecordLiftProtocol (Control ServiceSpec)
open PqxdhRecordLiftOrigins (Origins annotate origin)
variable {n : Nat} {A : Type}

structure Receipt (n : Nat) where
  role : Role
  handle : Handle
  slot : Option (Slot n)

structure State (n : Nat) where
  origins : Origins n
  installs : List (Receipt n)

def initial : State n := ⟨PqxdhRecordLiftOrigins.empty,[]⟩

def next (request : (WorldSpec n).Domain) (reply : (WorldSpec n).Range request) (before : State n) : State n :=
  ⟨annotate request reply before.origins,match request with
    | .inr (.inl (.inr (.installServer keyId _ ref))) =>
        if @Eq Bool reply true then before.installs++[⟨.server,.peer keyId,origin ref⟩] else before.installs
    | .inr (.inl (.inr (.installBeacon owner _ ref))) =>
        if @Eq Bool reply true then before.installs++[⟨.beacon,.owner owner,origin ref⟩] else before.installs
    | _ => before.installs⟩

def handler : QueryImpl (WorldSpec n) (StateT (State n) (OracleComp (WorldSpec n))) := fun request before =>
  (fun reply => (reply,next request reply before)) <$> (WorldSpec n).query request

def program (work : OracleComp (WorldSpec n) A) (before : State n := initial) : OracleComp (WorldSpec n) (A × State n) :=
  (simulateQ handler work).run before

def slots (before : State n) : Handle → Option (Slot n)
  | .peer keyId => before.origins.peers keyId
  | .owner owner => before.origins.owners owner

/-- Every observed request/reply erases to exactly one original request, without changing any returned value or optional failure. -/
theorem query_erase (request : (WorldSpec n).Domain) (before : State n) :
    Prod.fst <$> (handler request).run before = (WorldSpec n).query request := by
  simp only [handler,StateT.run,Functor.map_map,id_map']

/-- The full adaptive observer erases to the original World tree, including all failed send and source reservation histories. -/
theorem program_erase (work : OracleComp (WorldSpec n) A) (before : State n) :
    Prod.fst <$> program work before=work := by
  unfold program
  induction work using OracleComp.inductionOn generalizing before with
  | pure value => simp only [simulateQ_pure,StateT.run_pure,map_pure]
  | query_bind request continuation ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind]
    simp only [handler,StateT.run,bind_map_left,map_bind]
    apply bind_congr
    intro reply
    exact ih reply _

/-- Opaque slot instrumentation makes no extra primitive, platform coin or record call. -/
theorem program_bound (predicate : (WorldSpec n).Domain → Prop) [DecidablePred predicate]
    (work : OracleComp (WorldSpec n) A) (count : Nat) (bounded : work.IsQueryBoundP predicate count) (before : State n) :
    (program work before).IsQueryBoundP predicate count := by
  apply bounded.simulateQ_run_of_step
  · intro request counted current
    simp [handler,StateT.run,isQueryBoundP_map_iff,isQueryBoundP_query_iff,counted]
  · intro request uncounted current
    simp [handler,StateT.run,isQueryBoundP_map_iff,isQueryBoundP_query_iff,uncounted]

noncomputable def controlled (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder) :
    QueryImpl (WorldSpec n) (StateT (State n × Control n) (OracleComp (ServiceSpec n))) :=
  QueryImpl.Stateful.link handler (PqxdhRecordLiftProtocol.handler decode route)

/-- Every interpreted observed request derives its next slot projection from actual source control and the literal reply. No initial slot-map conclusion is assumed. -/
theorem query_origins (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (request : (WorldSpec n).Domain) (before : State n × Control n)
    (prior : before.1.origins=RegistrationNativePlatformRecordSlotControl.origins before.2)
    (result : (WorldSpec n).Range request × (State n × Control n))
    (supported : result ∈ support ((controlled decode route request).run before)) :
    result.2.1.origins=RegistrationNativePlatformRecordSlotControl.origins result.2.2 := by
  simp only [controlled,QueryImpl.Stateful.link,QueryImpl.Stateful.linkWith,StateT.mk,
    QueryImpl.Stateful.Frame.prod,QueryImpl.Stateful.Frame.linkReshape,
    PFunctor.Lens.State.fst,PFunctor.Lens.State.snd,handler,StateT.run,
    simulateQ_map,simulateQ_spec_query,support_map] at supported
  obtain ⟨raw,called,rfl⟩ := supported
  change raw ∈ support (((fun reply => (reply,next request reply before.1)) <$>
    PqxdhRecordLiftProtocol.handler decode route request).run before.2) at called
  rw [StateT.run_map,support_map] at called
  obtain ⟨actual,original,rfl⟩ := called
  change annotate request actual.1 before.1.origins=RegistrationNativePlatformRecordSlotControl.origins actual.2
  rw [prior]
  exact (RegistrationNativePlatformRecordSlotControl.query decode route request before.2 actual original).symm

/-- Full adaptive controller execution retains every private-independent slot receipt and gives exactly its final actual slot projection. -/
theorem program_origins (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (before : State n × Control n)
    (prior : before.1.origins=RegistrationNativePlatformRecordSlotControl.origins before.2)
    (result : A × (State n × Control n))
    (supported : result ∈ support ((simulateQ (controlled decode route) work).run before)) :
    result.2.1.origins=RegistrationNativePlatformRecordSlotControl.origins result.2.2 := by
  induction work using OracleComp.inductionOn generalizing before result with
  | pure value =>
    simp only [simulateQ_pure,StateT.run_pure,mem_support_pure_iff] at supported
    cases supported
    exact prior
  | query_bind request continuation ih =>
    rw [simulateQ_bind,simulateQ_spec_query,StateT.run_bind,mem_support_bind_iff] at supported
    obtain ⟨middle,called,continued⟩ := supported
    exact ih middle.1 middle.2 (query_origins decode route request before prior middle called) result continued

/-- The analysis projection exposes only opaque IDs, and agrees with the actual handle-slot map whenever the derived origin equation holds. -/
theorem slots_of_origins (ghost : State n) (control : Control n)
    (same : ghost.origins=RegistrationNativePlatformRecordSlotControl.origins control) :
    slots ghost=PqxdhRecordLiftIdeal.handleSlot control := by
  funext handle
  cases handle <;> simp only [slots,same] <;> rfl

/-- Every persistent interpreter retains its complete original poststate when the ghost is erased. This includes arbitrary physical CTX state and common platform state. -/
theorem interpreted_erase {I S : Type} {spec : OracleSpec I}
    (implementation : QueryImpl (WorldSpec n) (StateT S (OracleComp spec)))
    (work : OracleComp (WorldSpec n) A) (ghost : State n) (before : S) :
    (fun result => (result.1.1,result.2)) <$>
      (simulateQ implementation (program work ghost)).run before =
        (simulateQ implementation work).run before := by
  have erased := congrArg (fun tree => (simulateQ implementation tree).run before) (program_erase work ghost)
  simpa only [simulateQ_map,StateT.run_map] using erased

/-- Linked execution keeps the complete source ghost and full controller, with only their product association changed. -/
theorem controlled_source (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (ghost : State n) (before : Control n) :
    (simulateQ (controlled decode route) work).run (ghost,before) =
      (fun result => (result.1.1,(result.1.2,result.2))) <$>
        (simulateQ (PqxdhRecordLiftProtocol.handler decode route) (program work ghost)).run before := by
  exact QueryImpl.Stateful.simulateQ_link_run handler (PqxdhRecordLiftProtocol.handler decode route) work ghost before

/-- Source support alone identifies the complete final opaque slot map; the successful-install receipt list remains in the same result. -/
theorem protocol_slots (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (ghost : State n) (before : Control n)
    (prior : ghost.origins=RegistrationNativePlatformRecordSlotControl.origins before)
    (result : (A × State n) × Control n)
    (supported : result ∈ support ((simulateQ (PqxdhRecordLiftProtocol.handler decode route) (program work ghost)).run before)) :
    slots result.1.2=PqxdhRecordLiftIdeal.handleSlot result.2 := by
  have mapped : (result.1.1,(result.1.2,result.2)) ∈ support
      ((simulateQ (controlled decode route) work).run (ghost,before)) := by
    rw [controlled_source,support_map]
    exact ⟨result,supported,rfl⟩
  exact slots_of_origins result.1.2 result.2 (program_origins decode route work (ghost,before) prior _ mapped)

/-- Any real or ideal private record service preserves the derived ghost-slot projection and its entire reached private state. -/
theorem interpreted_slots {S : Type} (service : QueryImpl (ServiceSpec n) (StateT S ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (route : RawCtxServerRouting.SenderDecoder)
    (work : OracleComp (WorldSpec n) A) (ghost : State n) (before : Control n)
    (prior : ghost.origins=RegistrationNativePlatformRecordSlotControl.origins before) (privateBefore : S)
    (result : ((A × State n) × Control n) × S)
    (supported : result ∈ support ((simulateQ service
      ((simulateQ (PqxdhRecordLiftProtocol.handler decode route) (program work ghost)).run before)).run privateBefore)) :
    slots result.1.1.2=PqxdhRecordLiftIdeal.handleSlot result.1.2 := by
  apply protocol_slots decode route work ghost before prior result.1
  apply OracleComp.support_simulateQ_run'_subset service _ privateBefore
  rw [StateT.run'_eq,support_map]
  exact Set.mem_image_of_mem Prod.fst supported

end BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost
/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.query_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.query_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_bound

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.query_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.query_origins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.program_origins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.slots_of_origins' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.slots_of_origins

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.interpreted_erase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.interpreted_erase

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.controlled_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.controlled_source

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.protocol_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.protocol_slots

/-- info: 'BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.interpreted_slots' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RegistrationNativePlatformRecordSlotGhost.interpreted_slots
