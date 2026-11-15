-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.CborRecordWorldCursor

/-! Administrative World operations expose exactly the initialization and successful installation data used by the public cursor shell. Hidden initialization counters are derived from the actual source constructors. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.CborRecordWorldCursorAdmin
open PqxdhRecordLiftInterface
open CborRecordWorldClient (Shell initialSequence)
open CborRecordWorldCursor
variable {n : Nat}

/-- Resolving a hidden kernel leaves existing record control unchanged and gives the public deterministic source counter. -/
theorem resolve_cursor (role : Role) (ref : KernelRef n) (state : PqxdhRecordLiftWorld.State n)
    (result : ConcreteRatchetKernel × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.resolve role ref).run state)) :
    result.2.server = state.server ∧ result.2.owners = state.owners ∧
      result.1.refined.control.send_sequence.val = initialSequence role ref := by
  cases ref with
  | known kernel =>
    simp only [PqxdhRecordLiftWorld.resolve, StateT.run] at supported
    subst result
    exact ⟨rfl, rfl, rfl⟩
  | hidden slot =>
    obtain ⟨seed, kernelEq, _, _, _, serverEq, ownersEq, _⟩ :=
      PqxdhRecordLiftWorld.resolve_hidden_facts role slot state result supported
    refine ⟨serverEq, ownersEq, ?_⟩
    rw [kernelEq]
    have erased := PqxdhRecordLiftWorldCompiler.labeledKernel_erasure (fun _ => seed) ∅ role slot
    rw [← erased]
    rfl

private theorem shell_ext (left right : Shell)
    (server : left.server = right.server) (owners : left.owners = right.owners) : left = right := by
  cases left
  cases right
  cases server
  cases owners
  rfl

private theorem server_ext (left right : CborRecordWorldClient.Server)
    (sender : left.sender = right.sender) (peers : left.peers = right.peers) : left = right := by
  cases left
  cases right
  cases sender
  cases peers
  rfl

/-- Every probabilistic primitive operation retains the whole public cursor shell. -/
theorem sampled_shell {Result : Type} (work : ProbComp Result) (state : PqxdhRecordLiftWorld.State n)
    (result : Result × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.sampled work).run state)) :
    worldShell result.2 = worldShell state := by
  simp only [PqxdhRecordLiftWorld.sampled, StateT.run, bind_pure_comp, support_map] at supported
  obtain ⟨inner, reached, rfl⟩ := supported
  rfl

/-- A successful Server installation updates only its selected public cursor, and a refusal updates none. -/
theorem install_server_shell (keyId : Std.U64) (binding : PeerBinding) (ref : KernelRef n)
    (state : PqxdhRecordLiftWorld.State n) (result : Bool × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installServer keyId binding ref).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (.inr (.inl (.inr (.installServer keyId binding ref))))
      result.1 (worldShell state) := by
  cases existing : state.server with
  | none =>
    simp only [PqxdhRecordLiftWorld.installServer, StateT.run, existing, mem_support_pure_iff] at supported
    subst result
    rfl
  | some server =>
    by_cases admitted : server.records.server.peers keyId = none ∧ PqxdhRecordLiftWorld.Unused state .server ref
    · simp only [PqxdhRecordLiftWorld.installServer, StateT.run, existing, ite_eq_left admitted,
        bind_pure_comp, support_map] at supported
      obtain ⟨resolved, reached, rfl⟩ := supported
      obtain ⟨serverEq, ownersEq, counterEq⟩ := resolve_cursor .server ref state resolved reached
      apply shell_ext
      · simp only [worldShell, CborRecordWorldClient.next, ite_true, existing,
          PqxdhRecordLiftWorld.markUsed, Option.map_some]
        cases ref
        all_goals congr 1; apply server_ext; rfl
        all_goals funext other; by_cases same : other = keyId
        all_goals simp only [Function.update_apply, same, ite_true, ite_false, Option.map_some]
        all_goals exact congrArg some counterEq
      · cases ref <;> simp only [worldShell, CborRecordWorldClient.next, ite_true,
          PqxdhRecordLiftWorld.markUsed, ownersEq]
    · simp only [PqxdhRecordLiftWorld.installServer, StateT.run, existing, ite_eq_right admitted,
        mem_support_pure_iff] at supported
      subst result
      rfl

/-- Beacon installation exposes only the supplied sender metadata and deterministic initial sequence. -/
theorem install_beacon_shell (owner : Nat) (metadata : BeaconShell) (ref : KernelRef n)
    (state : PqxdhRecordLiftWorld.State n) (result : Bool × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.installBeacon owner metadata ref).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (.inr (.inl (.inr (.installBeacon owner metadata ref))))
      result.1 (worldShell state) := by
  by_cases admitted : PqxdhRecordLiftWorld.BeaconReady state owner ∧ PqxdhRecordLiftWorld.Unused state .beacon ref
  · simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ite_eq_left admitted,
      bind_pure_comp, support_map] at supported
    obtain ⟨resolved, reached, rfl⟩ := supported
    obtain ⟨serverEq, ownersEq, counterEq⟩ := resolve_cursor .beacon ref state resolved reached
    apply shell_ext
    · cases ref <;> simp only [worldShell, CborRecordWorldClient.next, ite_true,
        PqxdhRecordLiftWorld.markUsed, serverEq]
    · funext other
      have existing := admitted.1
      change state.owners[owner]? = some (.inactive .initSent) at existing
      have within := (List.getElem?_eq_some_iff.mp existing).1
      cases ref <;> simp only [worldShell, CborRecordWorldClient.next, ite_true, PqxdhRecordLiftWorld.markUsed]
      all_goals by_cases same : other = owner
      all_goals first
        | (subst other; simp only [List.getElem?_set_self within, Option.bind_some, Function.update_self]; rw [counterEq])
        | simp only [List.getElem?_set_ne (Ne.symm same), Function.update_of_ne same]
  · simp only [PqxdhRecordLiftWorld.installBeacon, StateT.run, ite_eq_right admitted,
      mem_support_pure_iff] at supported
    subst result
    rfl

private theorem inactive_set_shell (state : PqxdhRecordLiftWorld.State n) (owner : Nat)
    (before after : InactivePhase) (found : state.owners[owner]? = some (.inactive before)) :
    worldShell { state with owners := state.owners.set owner (.inactive after) } = worldShell state := by
  apply shell_ext
  · rfl
  · funext other
    by_cases same : other = owner
    · subst other
      simp only [worldShell, List.getElem?_set_self (List.getElem?_eq_some_iff.mp found).1,
        found, Option.bind_some]
    · simp only [worldShell, List.getElem?_set_ne (Ne.symm same)]

private theorem inactive_append_shell (state : PqxdhRecordLiftWorld.State n) (phase : InactivePhase) :
    worldShell { state with owners := state.owners ++ [.inactive phase] } = worldShell state := by
  apply shell_ext
  · rfl
  · funext owner
    by_cases within : owner < state.owners.length
    · simp only [worldShell, List.getElem?_append_left within]
    · have beyond : state.owners.length ≤ owner := by omega
      have absent : state.owners[owner]? = none := List.getElem?_eq_none_iff.mpr beyond
      simp only [worldShell, List.getElem?_append_right beyond, absent, Option.bind_none]
      cases offset : owner - state.owners.length <;> simp

/-- Actual public effects preserve cursors except for the two explicitly successful installations. -/
theorem capability_shell (query : (CapabilitySpec n).Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : (CapabilitySpec n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.capability query).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (.inr (.inl (.inr query))) result.1 (worldShell state) := by
  cases query with
  | peerPresent keyId =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, mem_support_pure_iff] at supported
    subst result
    rfl
  | ownerPresent owner =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, mem_support_pure_iff] at supported
    subst result
    rfl
  | installServer keyId binding ref => exact install_server_shell keyId binding ref state result supported
  | installBeacon owner metadata ref => exact install_beacon_shell owner metadata ref state result supported
  | appendOwner sender pin phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, mem_support_pure_iff] at supported
    subst result
    exact inactive_append_shell state phase
  | advanceOwner owner phase =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run] at supported
    split at supported
    · rename_i before found
      split at supported
      · simp only [mem_support_pure_iff] at supported
        subst result
        exact inactive_set_shell state owner before phase found
      · simp only [mem_support_pure_iff] at supported
        subst result
        rfl
    · simp only [mem_support_pure_iff] at supported
      subst result
      rfl
  | hash bytes =>
    simp only [PqxdhRecordLiftWorld.capability, StateT.run, bind_pure_comp, support_map] at supported
    obtain ⟨inner, reached, rfl⟩ := supported
    exact sampled_shell ((CtxRomAuth.ctxRandomOracle ((), bytes)).run state.primitive.2) state inner reached

/-- Effect accounting changes only instrumentation, while registration's public cursor transition is retained. -/
theorem effects_shell (query : (EnvEffects n).Domain) (state : PqxdhRecordLiftWorld.State n)
    (result : (EnvEffects n).Range query × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.effects query).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (.inr (.inl query)) result.1 (worldShell state) := by
  cases query with
  | inl coin =>
    exact sampled_shell (unifSpec.query coin : ProbComp _) (PqxdhRecordLiftWorld.chargeEffect (.inl coin) state) result supported
  | inr request =>
    exact capability_shell request (PqxdhRecordLiftWorld.chargeEffect (.inr request) state) result supported

/-- The actual first initialization and duplicate refusal agree with public constructor metadata. -/
theorem initialize_shell (created : PqxdhLiveServerConstruction.Created (Std.Array U8 151#usize)) (state : PqxdhRecordLiftWorld.State n)
    (result : Unit × PqxdhRecordLiftWorld.State n)
    (supported : result ∈ support ((PqxdhRecordLiftWorld.initializeServer created).run state)) :
    worldShell result.2 = CborRecordWorldClient.next (n := n) (.inl created) result.1 (worldShell state) := by
  cases existing : state.server with
  | some server =>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, existing, mem_support_pure_iff] at supported
    subst result
    simp only [worldShell, CborRecordWorldClient.next, existing, Option.map_some]
  | none =>
    simp only [PqxdhRecordLiftWorld.initializeServer, StateT.run, existing, mem_support_pure_iff] at supported
    subst result
    simp only [worldShell, CborRecordWorldClient.next, PqxdhRecordLiftWorld.importedServer,
      existing, Option.map_none, Option.map_some, Option.map_map]
    rfl

end BeaconcryptCore.Computational.CborRecordWorldCursorAdmin

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.resolve_cursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.resolve_cursor

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.sampled_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.sampled_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.install_server_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.install_server_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.install_beacon_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.install_beacon_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.capability_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.capability_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.effects_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.effects_shell

/-- info: 'BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.initialize_shell' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.CborRecordWorldCursorAdmin.initialize_shell
