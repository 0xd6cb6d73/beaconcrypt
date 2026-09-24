import BeaconcryptCore.Computational.PqxdhInitialSelectedOrigin
import BeaconcryptCore.Computational.RawCtxGenericFamilyLive

/-!
The actual Beacon Phase2 attempt consumes InitSent even on failure. An established or aborted owner cannot initialize again; ordinary record operations keep that terminal registration state. These source occurrence facts are independent of byte equality between different owners' roots or keys. Stable private KEM ownership is a separate consuming boundary.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization
open RawCtxGenericRoleStorage PqxdhBeaconPhase2Shared PqxdhInitialGenericBeacon
variable {Kernel I D K X Response Shared Origin : Type}

def Closed (state : BeaconState Kernel I D K) : Prop :=
  match state.beacon.phase with
  | .established _ _ _ | .aborted _ => True
  | _ => False

/-- Every original Phase2 finish is terminal, including failed preparation, opening, binding or pin checks. -/
theorem finish_closed (control : pqxdh.BeaconInitSent) (state : BeaconState Kernel I D K)
    (staged : Option (Staged Kernel)) : Closed (finish control state staged).2 := by
  cases staged with
  | none => trivial
  | some staged =>
      simp only [finish]
      split
      · trivial
      · split <;> trivial

/-- A terminal source owner rejects every later Phase2 call before preparation, initialization or opening, retaining its complete state. -/
theorem owner_closed {m : Type → Type*} [Monad m]
    (mark : Secrets Shared → Origin) (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) (closed : Closed state) :
    PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw state = pure ((none, state), none) := by
  cases phase : state.beacon.phase <;> simp_all only [Closed]
  all_goals simp only [PqxdhInitialFinishOrigin.owner, phase]

/-- Support in the actual active Phase2 execution makes the same returned owner terminal; every optional failure is included. -/
theorem attempt_closed {State : Type}
    (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (control : pqxdh.BeaconInitSent)
    (prekey oneTime : D) (kem : K) (phase : entry.beacon.phase = .initSent control prekey oneTime kem)
    (before : State) (result : PqxdhInitialFinishOrigin.Result Kernel Origin I D K × State)
    (supported : result ∈ support ((PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw entry).run before)) :
    Closed result.1.1.2 := by
  simp only [PqxdhInitialFinishOrigin.owner, phase, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨prepared, _, rest⟩ := supported
  cases found : prepared.1 with
  | none =>
      simp only [found, StateT.run_pure, mem_support_pure_iff] at rest
      subst result
      exact finish_closed control entry none
  | some pending =>
      simp only [found, StateT.run_bind, mem_support_bind_iff] at rest
      obtain ⟨staged, _, returned⟩ := rest
      simp only [StateT.run_pure, mem_support_pure_iff] at returned
      subst result
      exact finish_closed control entry staged.1

/-- Every successful installation marker comes with the same terminal returned owner, rather than an independently chosen successful witness. -/
theorem marker_closed {State : Type}
    (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : BeaconState Kernel I D K) (before : State)
    (result : PqxdhInitialFinishOrigin.Result Kernel Origin I D K × State)
    (supported : result ∈ support ((PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw entry).run before))
    (origin : Origin) (recorded : result.1.2 = some origin) : Closed result.1.1.2 := by
  obtain ⟨control, prekey, oneTime, kem, prepared, atTail, staged, phase, _, _, _, _, _⟩ :=
    PqxdhInitialFinishOrigin.origin mark pre calls application initial decode raw entry before result supported origin recorded
  exact attempt_closed mark pre calls application initial decode raw entry control prekey oneTime kem phase before result supported

/-- The original record frontend retains a terminal registration phase through every send, receive, rejection and callback outcome. -/
theorem record_closed {State : Type}
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (query : RawCtxMixedOwner.SourceSpec.Domain)
    (entry : BeaconState Kernel I D K) (closed : Closed entry) (before : State)
    (result : (RawCtxMixedOwner.SourceSpec.Range query × BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((RawCtxGenericBeacon.impl calls decode query).run entry).run before)) :
    Closed result.1.2 := by
  cases phase : entry.beacon.phase <;> simp_all only [Closed]
  case established control ad kernel =>
    rw [RawCtxGenericBeacon.established calls decode query entry control ad kernel phase] at supported
    simp only [StateT.run_bind, mem_support_bind_iff] at supported
    obtain ⟨reply, _, returned⟩ := supported
    simp only [StateT.run_pure, mem_support_pure_iff] at returned
    subst result
    trivial
  case aborted control =>
    cases query <;> simp [RawCtxGenericBeacon.impl, StateT.run, phase, RawCtxGenericBeacon.rejected] at supported
    all_goals subst result; simp only [phase]

/-- The entire adaptive Beacon record schedule preserves terminal registration state while retaining every optional result and primitive effect. -/
theorem record_schedule_closed {State Result : Type}
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (decode : RawCtxReceive.FrameDecoder) (client : OracleComp RawCtxMixedOwner.SourceSpec Result)
    (entry : BeaconState Kernel I D K) (closed : Closed entry) (before : State)
    (result : (Result × BeaconState Kernel I D K) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericBeacon.impl calls decode) client).run entry).run before)) :
    Closed result.1.2 := by
  induction client using OracleComp.inductionOn generalizing entry before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact closed
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support ((((RawCtxGenericBeacon.impl calls decode query).run entry).run before) >>= fun reply =>
        ((simulateQ (RawCtxGenericBeacon.impl calls decode) (next reply.1.1)).run reply.1.2).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1.1 reply.1.2 (record_closed calls decode query entry closed before reply head) reply.2 result tail

/-- Every original family request preserves the selected Beacon's terminal phase, including calls to other owners and public primitive services. -/
theorem family_closed {State M P : Type} {S B : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolRoles.SourceSpec S B).Domain)
    (entry : RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) (selected : Fin B)
    (closed : Closed (entry.2 selected)) (before : State)
    (result : ((RawCtxProtocolRoles.SourceSpec S B).Range query × RawCtxGenericRoleFamily.Roles Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode query).run entry).run before)) :
    Closed (result.1.2.2 selected) := by
  rcases query with ⟨index, request⟩ | (⟨index, request⟩ | request)
  case inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.1, (Function.update entry.1 index reply.1.2, entry.2)), reply.2)) <$>
      ((RawCtxGenericServer.serverImpl calls sender route decode request).run (entry.1 index)).run before) at supported
    rw [support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact closed
  case inr.inl =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1.1, (entry.1, Function.update entry.2 index reply.1.2)), reply.2)) <$>
      ((RawCtxGenericBeacon.impl calls decode request).run (entry.2 index)).run before) at supported
    rw [support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    by_cases same : selected = index
    · subst selected
      simpa only [Function.update_self] using record_closed calls decode request (entry.2 index) closed before reply reached
    · simpa only [Function.update_of_ne same] using closed
  case inr.inr =>
    simp only [RawCtxGenericFamilyFrontend.impl, StateT.run, bind_pure_comp] at supported
    change result ∈ support ((fun reply => ((reply.1, entry), reply.2)) <$> (publicCalls request).run before) at supported
    rw [support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact closed

/-- Original live read replies and their history notes cannot reopen a terminal registration; all family requests retain the same property. -/
theorem live_closed {State M P : Type} {S B : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (selected : Fin B)
    (closed : Closed (entry.1.2 selected)) (before : State)
    (result : ((RawCtxProtocolReveals.SourceSpec S B).Range query × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run before)) :
    Closed (result.1.2.1.2 selected) := by
  cases query with
  | inl request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support ((fun reply => ((reply.1.1, (reply.1.2, RawCtxProtocolReveals.tick entry.2)), reply.2)) <$>
        ((RawCtxGenericFamilyFrontend.impl calls publicCalls sender route decode request).run entry.1).run before) at supported
      rw [support_map] at supported
      obtain ⟨reply, reached, rfl⟩ := supported
      exact family_closed calls publicCalls sender route decode request entry.1 selected closed before reply reached
  | inr request =>
      simp only [RawCtxGenericFamilyLive.impl, StateT.run, bind_pure_comp] at supported
      change result ∈ support ((fun reply => ((reply.1, (entry.1, RawCtxProtocolReveals.note ⟨request, reply.1⟩ entry.2)), reply.2)) <$>
        (reader (request, RawCtxGenericRoleFamily.selectedKernel (RawCtxGenericFamilyRead.requestOwner request) entry.1)).run before) at supported
      rw [support_map] at supported
      obtain ⟨reply, _, rfl⟩ := supported
      exact closed

/-- An arbitrary adaptive original live-family schedule cannot reopen a closed Beacon, including reads, other owners and public evaluations. -/
theorem live_schedule_closed {State M P Result : Type} {S B : Nat}
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B) (selected : Fin B)
    (closed : Closed (entry.1.2 selected)) (before : State)
    (result : (Result × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) client).run entry).run before)) :
    Closed (result.1.2.1.2 selected) := by
  induction client using OracleComp.inductionOn generalizing entry before result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact closed
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query] at supported
      change result ∈ support ((((RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode query).run entry).run before) >>= fun reply =>
        ((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) (next reply.1.1)).run reply.1.2).run reply.2) at supported
      rw [mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1.1 reply.1.2 (live_closed calls publicCalls reader sender route decode query entry selected closed before reply head) reply.2 result tail

/-- After the actual first installation and any original live-family continuation, a second finish at that same owner is exactly the rejected pure call with complete owner state retained. This does not identify owners through equal key bytes. -/
theorem no_second_after_live {State M P Result : Type} {S B : Nat}
    (mark : Secrets Shared → Origin)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT State ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT State ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (raw laterRaw : Pqxdh.Bytes) (entry : RawCtxGenericFamilyLive.State Kernel M P I D K S B)
    (selected : Fin B) (before : State)
    (first : PqxdhInitialFinishOrigin.Result Kernel Origin I D K × State)
    (firstSupported : first ∈ support ((PqxdhInitialFinishOrigin.owner mark pre calls application initial decode raw (entry.1.2 selected)).run before))
    (origin : Origin) (recorded : first.1.2 = some origin)
    (client : OracleComp (RawCtxProtocolReveals.SourceSpec S B) Result)
    (result : (Result × RawCtxGenericFamilyLive.State Kernel M P I D K S B) × State)
    (supported : result ∈ support (((simulateQ (RawCtxGenericFamilyLive.impl calls publicCalls reader sender route decode) client).run
      ((entry.1.1, Function.update entry.1.2 selected first.1.1.2), entry.2)).run first.2)) :
    PqxdhInitialFinishOrigin.owner mark pre calls application initial decode laterRaw (result.1.2.1.2 selected) =
      pure ((none, result.1.2.1.2 selected), none) := by
  apply owner_closed
  apply live_schedule_closed calls publicCalls reader sender route decode client
    ((entry.1.1, Function.update entry.1.2 selected first.1.1.2), entry.2) selected _ first.2 result supported
  simpa only [Function.update_self] using
    marker_closed mark pre calls application initial decode raw (entry.1.2 selected) before first firstSupported origin recorded

/-- The original uninstrumented finish also rejects a terminal owner exactly, without consulting any primitive callback. -/
theorem original_closed {m : Type → Type*} [Monad m]
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (calls : RawCtxChainOwner.Calls Kernel m) (application : Response → m (Option Pqxdh.Bytes))
    (initial : Secrets Shared → m (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (state : BeaconState Kernel I D K) (closed : Closed state) :
    PqxdhInitialGenericBeacon.owner pre calls application initial decode raw state = pure (none, state) := by
  cases phase : state.beacon.phase <;> simp_all only [Closed]
  all_goals simp only [PqxdhInitialGenericBeacon.owner, phase]

end BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.finish_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.finish_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.owner_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.owner_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.attempt_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.attempt_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.marker_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.marker_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.record_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.record_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.record_schedule_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.record_schedule_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.family_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.family_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.live_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.live_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.live_schedule_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.live_schedule_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.no_second_after_live' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.no_second_after_live

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.original_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization.original_closed
