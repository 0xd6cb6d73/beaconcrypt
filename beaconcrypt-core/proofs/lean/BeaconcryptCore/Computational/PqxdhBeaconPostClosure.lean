import BeaconcryptCore.Computational.PqxdhBeaconSingleInitialization
import BeaconcryptCore.Computational.PqxdhInitialGenericPost

/-!
The existing complete post-registration interface preserves a Beacon's terminal registration phase under arbitrary interleaved live-family, selector and Beacon-finish requests. The owner used below is the literal original finish, and the records service is the literal original generic live-family wrapper. Only callback effects reside in their existing private state; no callback receives or replaces the complete role family. This is an operational lifetime result, not a cryptographic owner-injectivity or nonce theorem.
-/
open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhBeaconPostClosure
open PqxdhBeaconSingleInitialization PqxdhBeaconPhase2Shared
variable {Kernel M P I D K X Response Shared A N Result : Type} {S B : Nat}

/-- The exact source records wrapper preserves closure alongside all registration controls, consumed identifiers, primitive state and live history. -/
theorem records_closed
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (query : (RawCtxProtocolReveals.SourceSpec S B).Domain)
    (entry : PqxdhInitialGenericProtocol.State Kernel M P I D K A S B) (selected : Fin B)
    (closed : Closed (entry.roles.1.2 selected))
    (result : (RawCtxProtocolReveals.SourceSpec S B).Range query × PqxdhInitialGenericProtocol.State Kernel M P I D K A S B)
    (supported : result ∈ support ((PqxdhInitialGenericRecords.records calls publicCalls reader sender route decode query).run entry)) :
    Closed (result.2.roles.1.2 selected) := by
  simp only [PqxdhInitialGenericRecords.records, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨reply, reached, rfl⟩ := supported
  exact live_closed calls publicCalls reader sender route decode query entry.roles selected closed entry.primitive reply reached

/-- A successful original uninstrumented finish closes its exact returned owner and retains its actual shared poststate. -/
theorem successful_closed {State : Type}
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT State ProbComp))
    (calls : RawCtxChainOwner.Calls Kernel (StateT State ProbComp))
    (application : Response → StateT State ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT State ProbComp (Option Kernel)) (decode : RawCtxReceive.FrameDecoder)
    (raw : Pqxdh.Bytes) (entry : RawCtxGenericRoleStorage.BeaconState Kernel I D K) (before : State)
    (result : (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K) × State)
    (supported : result ∈ support ((PqxdhInitialGenericBeacon.owner pre calls application initial decode raw entry).run before))
    (success : result.1.1.isSome = true) : Closed result.1.2 := by
  have erased := congrArg (fun work : StateT State ProbComp _ => work.run before)
    (PqxdhInitialFinishOrigin.erase (fun _ => ()) pre calls application initial decode raw entry)
  rw [← erased, StateT.run_map, support_map] at supported
  obtain ⟨finished, reached, rfl⟩ := supported
  have present := (PqxdhInitialFinishOrigin.published (fun _ => ()) pre calls application initial decode raw entry before finished reached).trans success
  obtain ⟨origin, recorded⟩ := Option.isSome_iff_exists.mp present
  exact marker_closed (fun _ => ()) pre calls application initial decode raw entry before finished reached origin recorded

section Post
variable {ι : Type} {extra : OracleSpec ι}
variable
    (calls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (publicCalls : QueryImpl RawCtxServerServices.PublicSpec (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec Kernel S B) (StateT (RawCtxSharedPrimitive.SharedState A) ProbComp))
    (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
    (selector : QueryImpl extra (StateT N ProbComp))
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (StateT (RawCtxSharedPrimitive.SharedState A × N) ProbComp))
    (finishCalls : RawCtxChainOwner.Calls Kernel (StateT (RawCtxSharedPrimitive.SharedState A × N) ProbComp))
    (application : Response → StateT (RawCtxSharedPrimitive.SharedState A × N) ProbComp (Option Pqxdh.Bytes))
    (initial : Secrets Shared → StateT (RawCtxSharedPrimitive.SharedState A × N) ProbComp (Option Kernel))

/-- This is the existing source post dispatcher instantiated by its original records wrapper and original uninstrumented Beacon finish. -/
noncomputable def post : QueryImpl (PqxdhInitialGenericPost.Spec extra S B)
    (StateT (PqxdhInitialGenericPost.State Kernel M P I D K A N S B) ProbComp) :=
  PqxdhInitialGenericPost.post (PqxdhInitialGenericRecords.records calls publicCalls reader sender route decode)
    selector (PqxdhInitialGenericBeacon.owner pre finishCalls application initial decode)

set_option backward.isDefEq.respectTransparency false in
/-- Any original post request preserves the selected terminal Beacon, including repeated finish attempts and selector calls with arbitrary effects on their private state. -/
theorem step_closed (query : (PqxdhInitialGenericPost.Spec extra S B).Domain)
    (entry : PqxdhInitialGenericPost.State Kernel M P I D K A N S B) (selected : Fin B)
    (closed : Closed (entry.1.roles.1.2 selected))
    (result : (PqxdhInitialGenericPost.Spec extra S B).Range query × PqxdhInitialGenericPost.State Kernel M P I D K A N S B)
    (supported : result ∈ support ((post calls publicCalls reader sender route decode selector pre finishCalls application initial query).run entry)) :
    Closed (result.2.1.roles.1.2 selected) := by
  rcases query with (query | query) | ⟨index, raw⟩
  case inl.inl =>
    simp only [post, PqxdhInitialGenericPost.post, StateT.run, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    exact records_closed calls publicCalls reader sender route decode query entry.1 selected closed reply reached
  case inl.inr =>
    simp only [post, PqxdhInitialGenericPost.post, StateT.run, support_map] at supported
    obtain ⟨reply, _, rfl⟩ := supported
    exact closed
  case inr =>
    simp only [post, PqxdhInitialGenericPost.post, StateT.run, support_map] at supported
    obtain ⟨reply, reached, rfl⟩ := supported
    by_cases same : selected = index
    · subst selected
      rw [original_closed pre finishCalls application initial decode raw (entry.1.roles.1.2 index) closed] at reached
      change reply ∈ support (pure ((none, entry.1.roles.1.2 index), (entry.1.primitive, entry.2))) at reached
      simp only [mem_support_pure_iff] at reached
      subst reply
      simpa only [PqxdhInitialGenericPost.installed, PqxdhInitialGenericProtocol.finishInstall, Function.update_self] using closed
    · simpa only [PqxdhInitialGenericPost.installed, PqxdhInitialGenericProtocol.finishInstall, Function.update_of_ne same] using closed

/-- The original adaptive post scheduler may interleave arbitrary live, selector and finish calls; a previously terminal owner remains terminal in every supported result. -/
theorem schedule_closed (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (entry : PqxdhInitialGenericPost.State Kernel M P I D K A N S B) (selected : Fin B)
    (closed : Closed (entry.1.roles.1.2 selected))
    (result : Result × PqxdhInitialGenericPost.State Kernel M P I D K A N S B)
    (supported : result ∈ support ((simulateQ (post calls publicCalls reader sender route decode selector pre finishCalls application initial) client).run entry)) :
    Closed (result.2.1.roles.1.2 selected) := by
  induction client using OracleComp.inductionOn generalizing entry result with
  | pure value =>
      simp only [simulateQ_pure, StateT.run_pure, mem_support_pure_iff] at supported
      subst result
      exact closed
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at supported
      obtain ⟨reply, head, tail⟩ := supported
      exact ih reply.1 reply.2
        (step_closed calls publicCalls reader sender route decode selector pre finishCalls application initial query entry selected closed reply head)
        result tail

/-- The same actual successful finish cannot be followed by a second installation at that Beacon after any original adaptive post schedule. The intervening schedule includes attempts at every Beacon and arbitrary selector work. -/
theorem no_second (raw laterRaw : Pqxdh.Bytes)
    (entry : PqxdhInitialGenericPost.State Kernel M P I D K A N S B) (selected : Fin B)
    (first : (Option Pqxdh.Bytes × RawCtxGenericRoleStorage.BeaconState Kernel I D K) ×
      (RawCtxSharedPrimitive.SharedState A × N))
    (firstSupported : first ∈ support ((PqxdhInitialGenericBeacon.owner pre finishCalls application initial decode raw
      (entry.1.roles.1.2 selected)).run (entry.1.primitive, entry.2)))
    (success : first.1.1.isSome = true)
    (client : OracleComp (PqxdhInitialGenericPost.Spec extra S B) Result)
    (result : Result × PqxdhInitialGenericPost.State Kernel M P I D K A N S B)
    (supported : result ∈ support ((simulateQ (post calls publicCalls reader sender route decode selector pre finishCalls application initial) client).run
      (PqxdhInitialGenericPost.installed selected entry first).2)) :
    PqxdhInitialGenericBeacon.owner pre finishCalls application initial decode laterRaw (result.2.1.roles.1.2 selected) =
      pure (none, result.2.1.roles.1.2 selected) := by
  apply original_closed
  apply schedule_closed calls publicCalls reader sender route decode selector pre finishCalls application initial client
    (PqxdhInitialGenericPost.installed selected entry first).2 selected _ result supported
  simpa only [PqxdhInitialGenericPost.installed, PqxdhInitialGenericProtocol.finishInstall, Function.update_self] using
    successful_closed pre finishCalls application initial decode raw (entry.1.roles.1.2 selected)
      (entry.1.primitive, entry.2) first firstSupported success

end Post

end BeaconcryptCore.Computational.PqxdhBeaconPostClosure

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPostClosure.records_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPostClosure.records_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPostClosure.successful_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPostClosure.successful_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPostClosure.step_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPostClosure.step_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPostClosure.schedule_closed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPostClosure.schedule_closed

/-- info: 'BeaconcryptCore.Computational.PqxdhBeaconPostClosure.no_second' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhBeaconPostClosure.no_second
