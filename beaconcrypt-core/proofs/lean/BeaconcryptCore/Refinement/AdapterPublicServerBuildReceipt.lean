-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Refinement.AdapterPublicServerRecordReceipt
import BeaconcryptCore.Computational.RegistrationServerCompletionSnapshot
open CoreModels Aeneas OracleComp OracleSpec
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
/-! Every successful actual enclosing Server builder reaches its actual reserved-map first-record continuation with the original moved token binding and rollback control. The proof follows the literal pin, preflight, occupancy and reservation cuts; it retains the reached full external poststates. -/
namespace BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt
open AdapterPublicWrapperRustT (RustT)
open AdapterPublicWrapperRequestMonad
open AdapterPublicServerBuildBody (Server Reply)
open AdapterRecordRequestMonad (liftRust)
open BeaconcryptCore.Computational
variable {State A B : Type}

private theorem bind_success (work : RustT (StateT State ProbComp) A)
    (next : A → RustT (StateT State ProbComp) B) (value : B) (before after : State)
    (supported : (.ok value, after) ∈ support (((work >>= next).run).run before)) :
    ∃ input middle, (.ok input, middle) ∈ support ((work.run).run before) ∧
      (.ok value, after) ∈ support (((next input).run).run middle) := by
  simp only [RustT.run_bind, StateT.run_bind, mem_support_bind_iff] at supported
  obtain ⟨⟨reply, middle⟩, reached, continued⟩ := supported
  cases reply with
  | fail error | div => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, reduceCtorEq, false_and] at continued
  | ok input => exact ⟨input, middle, reached, continued⟩

variable [material : PublicWrapperPlatform.Material] [platform : PublicWrapperPlatform.Platform]
variable [ed : AdapterInitEdPrimitive.Operations] [PublicWrapperPlatform.Allocator]
variable [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations]
variable [localOps : LocalOperations (RustT (StateT State ProbComp))]
variable [crypto : CryptoOperations (RustT (StateT State ProbComp))]
variable [containers : ContainerOperations (RustT (StateT State ProbComp))]
variable [children : ChildOperations (RustT (StateT State ProbComp))]

omit [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] localOps crypto containers children in
private theorem checked_success (self : Server) (work : RustM (core.result.Result A pqxdh.ServerState))
    (next : A → RustT (StateT State ProbComp) Reply)
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.checked self work next).run).run before)) :
    ∃ input, work = .ok (.Ok input) ∧
      (.ok (.Some response, current), after) ∈ support (((next input).run).run before) := by
  rw [AdapterPublicServerRecord.checked] at supported
  cases work with
  | fail error | div => simp only [AdapterPublicServerRecord.resumeResult, StateT.run_pure,
      support_pure, Set.mem_singleton_iff, Prod.mk.injEq, reduceCtorEq, false_and] at supported
  | ok result => cases result with
    | Err previous => simp only [AdapterPublicServerRecord.resumeResult, StateT.run_pure,
        support_pure, Set.mem_singleton_iff, Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at supported
    | Ok input => exact ⟨input, rfl, supported⟩

omit material platform ed localOps crypto containers children [PublicWrapperPlatform.Allocator] [PublicWrapperPlatform.LocalOperations] [PublicWrapperPlatform.ContainerOperations] in
theorem lookup_fields (control : pqxdh.ServerState) (pin : session.ServerAuthenticationPin)
    (token : peer.ConsumedRegistration) (application : Slice U8) (lookup : peer.CompletionLookup)
    (began : peer.begin_completion_lookup control pin token application = .ok (.Ok lookup)) :
    lookup.control = control ∧ lookup.pin = pin ∧ lookup.registration = token ∧ lookup.application = application := by
  obtain ⟨next, actual⟩ := BeaconcryptCore.PanicFreedom.server_next_key_id_ok control
  cases next with
  | Err error => simp only [peer.begin_completion_lookup, actual, bind_tc_ok, RustM.ok.injEq, reduceCtorEq] at began
  | Ok identifier =>
    simp only [peer.begin_completion_lookup, actual, bind_tc_ok, RustM.ok.injEq, core.result.Result.Ok.injEq] at began
    cases began
    exact ⟨rfl, rfl, rfl, rfl⟩

omit crypto in
theorem reserved (self : Server) (initial : registration.ServerInitialKdf)
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.reserved (m := StateT State ProbComp) self initial).run).run before)) :
    ∃ known middle,
      (.ok (.Ok (), known), middle) ∈ support
        (((containers.mapReserve core.U64.Insts.CoreCmpEq core.U64.Insts.CoreHashHash
          beaconcrypt_public_request.collections.KeyedHasher.Insts.CoreHashBuildHasherSipHasher13
          hashbrown.alloc.inner.Global.Insts.HashbrownAllocInnerAllocator self.known_ids 1#usize).run).run before) ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) { self with known_ids := known } initial).run).run middle) := by
  unfold AdapterPublicServerBuildBody.reserved at supported
  obtain ⟨⟨allocation, known⟩, middle, reached, continued⟩ := bind_success _ _ _ _ _ supported
  cases allocation with
  | Err error => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
  | Ok unitValue => cases unitValue; exact ⟨known, middle, reached, continued⟩

omit crypto in
theorem lookup (self : Server) (pending : peer.CompletionLookup) (plaintext : Slice U8)
    (response : beaconcrypt_public_wrapper.server.RegResponse) (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.lookup (m := StateT State ProbComp) self pending plaintext).run).run before)) :
    ∃ occupied initial middle,
      pending.resume occupied = .ok (.Ok initial) ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.reserved (m := StateT State ProbComp) self initial).run).run middle) := by
  unfold AdapterPublicServerBuildBody.lookup at supported
  obtain ⟨identifier, s1, _requested, continued⟩ := bind_success _ _ _ _ _ supported
  obtain ⟨size, s2, _sized, continued⟩ := bind_success _ _ _ _ _ continued
  obtain ⟨admitted, s3, _preflight, continued⟩ := bind_success _ _ _ _ _ continued
  cases admitted with
  | none => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
  | some length =>
    obtain ⟨occupied, s4, _present, continued⟩ := bind_success _ _ _ _ _ continued
    obtain ⟨initial, resumed, reached⟩ := checked_success self _ _ response current s4 after continued
    exact ⟨occupied, initial, s4, resumed, reached⟩

theorem build (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (response : beaconcrypt_public_wrapper.server.RegResponse)
    (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((AdapterPublicServerBuildBody.build (m := StateT State ProbComp) self token data).run).run before)) :
    ∃ initial known middle,
      initial.binding = token.registration.agreement.binding ∧ initial.candidate.previous_state = self.control ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) { self with known_ids := known } initial).run).run middle) := by
  unfold AdapterPublicServerBuildBody.build at supported
  obtain ⟨application, s1, _normalized, continued⟩ := bind_success _ _ _ _ _ supported
  obtain ⟨plaintext, s2, _bytes, continued⟩ := bind_success _ _ _ _ _ continued
  obtain ⟨pin, s3, _pinned, continued⟩ := bind_success _ _ _ _ _ continued
  cases pin with
  | none => simp only [RustT.run_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff,
      Prod.mk.injEq, RustM.ok.injEq, reduceCtorEq, false_and] at continued
  | some pin =>
    obtain ⟨pending, began, continued⟩ := checked_success self _ _ response current s3 after continued
    obtain ⟨occupied, initial, s4, resumed, continued⟩ := lookup self pending plaintext response current s3 after continued
    obtain ⟨known, middle, _reserved, recorded⟩ := reserved self initial response current s4 after continued
    have fields := lookup_fields self.control pin token.registration plaintext pending began
    have started : registration.begin_server_completion self.control pin
        (if occupied then .Occupied else .Available) token.registration.agreement plaintext = .ok (.Ok initial) := by
      cases occupied <;> simpa only [PeerOwnership.completion_lookup_resume, fields.1, fields.2.1,
        fields.2.2.1, fields.2.2.2] using resumed
    refine ⟨initial, known, middle, RegistrationServerRecordExecutor.initial_binding _ _ _ _ _ _ started, ?_, recorded⟩
    have previous := RegistrationServerCompletionSnapshot.initial self.control pin
      (if occupied then .Occupied else .Available) token.registration.agreement plaintext
    rw [started] at previous
    exact previous (.Ok initial) rfl
theorem actual (self : Server) (token : beaconcrypt_public_wrapper.server.RegistrationOutput)
    (data : core.option.Option (Slice U8)) (response : beaconcrypt_public_wrapper.server.RegResponse)
    (current : Server) (before after : State)
    (supported : (.ok (.Some response, current), after) ∈ support
      (((beaconcrypt_public_request.server.Server.Insts.BeaconcryptServerProviderServer.build_registration_response
        (m := RustT (StateT State ProbComp)) self token data).run).run before)) :
    ∃ initial known middle,
      initial.binding = token.registration.agreement.binding ∧ initial.candidate.previous_state = self.control ∧
      (.ok (.Some response, current), after) ∈ support
        (((AdapterPublicServerBuildBody.record (m := StateT State ProbComp) { self with known_ids := known } initial).run).run middle) := by
  rw [AdapterPublicServerBuildBody.source] at supported
  exact build self token data response current before after supported

end BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.lookup_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.lookup_fields

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.reserved' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.reserved

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.lookup

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.build

/-- info: 'BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.actual' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Refinement.AdapterPublicServerBuildReceipt.actual
