-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentCompileRegistration

/-! One step of the CE-3 compile lemma. The compiled handler, run under the source14 native handler on the product of the compiled program's local state and the source14 state, is related to the native deployment handler by the projection `merge`. For every command, under a simulation invariant, merging after the compiled step gives exactly the native step from the merged state (`step_merge`). The invariant consists of facts about the source14 state and the compiled program's public log: the Server key ID is the public one, every local copy refers to an installed peer or an established owner, the log counts every created owner, and every installed peer and established owner is publicly reconstructible from the log. Preservation of the invariant is a separate obligation. -/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhDeploymentCompileStep
open PqxdhServerAuthExperiment PqxdhServerAuthNative PqxdhJointIdentity
open PqxdhDeploymentCompile (Kernel Local merge compileImpl)
open PqxdhDeploymentInterface (Spec)
open PqxdhDeploymentCompileRegistration (Installed Copied)
variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-- The compiled handler under the source14 native handler, on the product of local and source14 state. -/
noncomputable def compiledImpl (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) :
    QueryImpl Spec (StateT (Local × PqxdhRegistrationSchedule.State KemSK) ProbComp) :=
  ((PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed).mapStateTBase
    (compileImpl setup codec route)).flattenStateT

/-- One compiled step is the compiled command run under the source14 native handler, reassociated. -/
theorem compiledImpl_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (compiledImpl setup codec checks route serverSeed query).run (copies, native) =
      (fun result => (result.1.1, (result.1.2, result.2))) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          ((compileImpl setup codec route query).run copies)).run native := rfl

/-- The simulation invariant of the compile lemma. -/
structure Inv (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) : Prop where
  keyId : native.shared.2.server.identityKeyId = setup.serverKeyId
  installed : Installed copies native.shared.2
  serverVisible : ∀ kid peer, native.shared.2.server.server.peers kid = some peer →
    PqxdhDeploymentCompile.peerView codec copies.log kid = some (native.shared.2.server.server.identity, peer.identity)
  count : copies.log.owners.length = native.owners.length
  copied : Copied copies native
  beaconVisible : ∀ index owner control associatedData kernel, native.owners[index]? = some owner →
    owner.beacon.phase = .established control associatedData kernel →
    PqxdhDeploymentCompile.ownerView codec copies.log index = some (owner.beacon.identityKeyId, control, associatedData)

/-- Merging ignores the public log. -/
theorem merge_log (copies : Local) (log : PqxdhDeploymentCompile.Log) (native : PqxdhRegistrationSchedule.State KemSK) :
    merge { copies with log := log } native = merge copies native := rfl

/-- A forwarded registration command with logged reply, run under the source14 native handler. -/
theorem forwardLogged_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (command : PqxdhDeploymentInterface.Command)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → PqxdhDeploymentInterface.CommandSpec command)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((PqxdhDeploymentCompile.forwardLogged request command reply).run copies)).run native =
      (fun result => ((reply result.1, { copies with log := PqxdhDeploymentCompile.logReply copies.log command (reply result.1) }),
        result.2)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native := by
  show (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      (PqxdhDeploymentCompile.forwardLogged request command reply copies)).run native = _
  simp only [PqxdhDeploymentCompile.forwardLogged, PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map,
    simulateQ_spec_query, StateT.run_map]
  rfl

/-- A forwarded command without a logged reply, run under the source14 native handler. -/
theorem forward_run (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request) (copies : Local)
    (native : PqxdhRegistrationSchedule.State KemSK) :
    (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
      ((StateT.lift (PqxdhDeploymentCompile.forward (KemSK := KemSK) request) : StateT Local _ _).run copies)).run native =
      (fun result => ((result.1, copies), result.2)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native := by
  simp only [PqxdhDeploymentCompile.forward, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query,
    StateT.run_map]
  rfl

/-- The native deployment handler on a registration command is the source14 handler on the native part. -/
theorem onNative_run {Result : Type} (work : PqxdhRegistrationSchedule.Game KemSK Result)
    (state : PqxdhDeploymentNative.State KemSK) :
    (PqxdhDeploymentNative.onNative work).run state =
      (fun result => (result.1, { state with native := result.2 })) <$> work.run state.native := rfl

/-- A registration command that commutes with merging gives the native step after merging. -/
theorem registration_step {Result : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response)
    (checks : Checks) (serverSeed : IdentitySeed) (request : PqxdhRegistrationSchedule.Request)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (updated : Local)
    (reply : PqxdhRegistrationSchedule.QuerySpec request → Result) (same : merge (KemSK := KemSK) updated = merge copies)
    (commutes : (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run (merge copies native).native =
      (fun result => (result.1, (merge copies result.2).native)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native) :
    (fun result => (reply result.1, merge updated result.2)) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run native =
      (fun result => (reply result.1, { merge copies native with native := result.2 })) <$>
        (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr request)).run (merge copies native).native := by
  rw [commutes, Functor.map_map, same]
  rfl

/-- One step of the compile lemma: under the invariant, merging after the compiled step is the native step from the merged state. -/
theorem step_merge (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed) (query : Spec.Domain)
    (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK) (inv : Inv setup codec copies native) :
    Prod.map id (fun state : Local × PqxdhRegistrationSchedule.State KemSK => merge state.1 state.2) <$>
        (compiledImpl setup codec checks route serverSeed query).run (copies, native) =
      (PqxdhDeploymentNative.handler setup codec checks route serverSeed query).run (merge copies native) := by
  rw [compiledImpl_run, Functor.map_map]
  rcases query with coin | command
  · simp only [compileImpl, StateT.run_lift, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
      Functor.map_map, PqxdhDeploymentNative.handler]
    rfl
  · cases command with
    | create pin keyId =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        cases parsed : PqxdhDeploymentInterface.parsePin pin with
        | none =>
            change (fun result => _) <$> (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
              (pure (none, copies) : OracleComp (PqxdhDeploymentRecordCache.SourceSpec KemSK) _)).run native = _
            simp only [simulateQ_pure, StateT.run_pure, map_pure]
            rfl
        | some word =>
            change (fun result => _) <$> (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
              (PqxdhDeploymentCompile.forward (.create word keyId) >>= fun index => pure (some index, _))).run native =
              (some <$> PqxdhDeploymentNative.onNative
                (PqxdhRegistrationSchedule.handler setup codec checks serverSeed (.inr (.create word keyId)))).run
                (merge copies native)
            simp only [PqxdhDeploymentCompile.forward, bind_pure_comp, simulateQ_map, simulateQ_spec_query, StateT.run_map,
              Functor.map_map, StateT.run_map, onNative_run,
              PqxdhDeploymentCompileRegistration.create_merge setup codec checks serverSeed copies native word keyId]
            rfl
    | bundle index =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forwardLogged_run, onNative_run, PqxdhDeploymentCompileRegistration.bundle_merge setup codec checks serverSeed
          copies native index inv.copied, Functor.map_map, Functor.map_map]
        rfl
    | accept raw =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forwardLogged_run, onNative_run, PqxdhDeploymentCompileRegistration.shared_merge setup codec checks serverSeed
          copies native _ trivial inv.installed, Functor.map_map, Functor.map_map]
        rfl
    | build session payload =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forwardLogged_run, onNative_run, PqxdhDeploymentCompileRegistration.shared_merge setup codec checks serverSeed
          copies native _ trivial inv.installed, Functor.map_map, Functor.map_map]
        rfl
    | finish index raw =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forwardLogged_run, onNative_run, PqxdhDeploymentCompileRegistration.finish_merge setup codec checks serverSeed
          copies native index raw inv.copied, Functor.map_map, Functor.map_map]
        rfl
    | hmac key message =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forward_run, onNative_run, PqxdhDeploymentCompileRegistration.shared_merge setup codec checks serverSeed
          copies native _ trivial inv.installed, Functor.map_map, Functor.map_map]
        rfl
    | hash bytes =>
        simp only [compileImpl, PqxdhDeploymentNative.handler]
        rw [forward_run, onNative_run, PqxdhDeploymentCompileRegistration.shared_merge setup codec checks serverSeed
          copies native _ trivial inv.installed, Functor.map_map, Functor.map_map]
        rfl
    | serverSend kid plaintext =>
        exact PqxdhDeploymentCompileRecords.server_record setup codec checks route serverSeed (.inl (plaintext, kid)) copies native inv.keyId
          inv.installed inv.serverVisible
    | serverRaw raw =>
        exact PqxdhDeploymentCompileRecords.server_record setup codec checks route serverSeed (.inr raw) copies native inv.keyId
          inv.installed inv.serverVisible
    | beaconSend index plaintext =>
        exact PqxdhDeploymentCompileRecords.beacon_record setup codec checks serverSeed index (.inl plaintext) copies native inv.count
          inv.copied inv.beaconVisible
    | beaconRaw index raw =>
        exact PqxdhDeploymentCompileRecords.beacon_record setup codec checks serverSeed index (.inr raw) copies native inv.count
          inv.copied inv.beaconVisible

/-- The compile simulation for any invariant that implies `Inv` and is preserved by every compiled step: the compiled program run under the source14 native handler, merged at the end, has exactly the distribution of the native deployment run from the merged start state, jointly with the adversary's output. -/
theorem compile_simulation {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (Good : Local → PqxdhRegistrationSchedule.State KemSK → Prop)
    (sound : ∀ copies native, Good copies native → Inv setup codec copies native)
    (preserved : ∀ query copies native, Good copies native →
      ∀ result ∈ support ((compiledImpl setup codec checks route serverSeed query).run (copies, native)),
        Good result.2.1 result.2.2)
    (adversary : OracleComp Spec X) (copies : Local) (native : PqxdhRegistrationSchedule.State KemSK)
    (start : Good copies native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          ((simulateQ (compileImpl setup codec route) adversary).run copies)).run native =
      (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) adversary).run
        (merge copies native) := by
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT, Functor.map_map]
  have simulated := OracleComp.map_run_simulateQ_eq_of_query_map_eq_inv'
    (compiledImpl setup codec checks route serverSeed) (PqxdhDeploymentNative.handler setup codec checks route serverSeed)
    (fun state => Good state.1 state.2) (fun state => merge state.1 state.2)
    (fun query state good result supported => preserved query state.1 state.2 good result supported)
    (fun query state good => step_merge setup codec checks route serverSeed query state.1 state.2
      (sound state.1 state.2 good))
    adversary (copies, native) start
  rw [← simulated]
  rfl

/-- The compiled program from the empty local state: under a preserved invariant that holds at the start, merging its final local state into the final source14 state gives exactly the native deployment run, which starts with zero raw-attempt counters. -/
theorem compile_run {X : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (route : RawCtxServerRouting.SenderDecoder) (serverSeed : IdentitySeed)
    (Good : Local → PqxdhRegistrationSchedule.State KemSK → Prop)
    (sound : ∀ copies native, Good copies native → Inv setup codec copies native)
    (preserved : ∀ query copies native, Good copies native →
      ∀ result ∈ support ((compiledImpl setup codec checks route serverSeed query).run (copies, native)),
        Good result.2.1 result.2.2)
    (adversary : OracleComp Spec X) (native : PqxdhRegistrationSchedule.State KemSK)
    (start : Good Local.empty native) :
    (fun result => (result.1.1, merge result.1.2 result.2)) <$>
        (simulateQ (PqxdhRegistrationJointRevealSchedule.native setup codec checks serverSeed)
          (PqxdhDeploymentCompile.compile setup codec route adversary)).run native =
      (simulateQ (PqxdhDeploymentNative.handler setup codec checks route serverSeed) adversary).run
        ⟨native, 0, fun _ => 0⟩ := by
  rw [← PqxdhDeploymentCompile.merge_empty]
  exact compile_simulation setup codec checks route serverSeed Good sound preserved adversary Local.empty native start

end BeaconcryptCore.Computational.PqxdhDeploymentCompileStep

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compiledImpl_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compiledImpl_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.merge_log' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.merge_log

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.forwardLogged_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.forwardLogged_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.forward_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.forward_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.onNative_run' does not depend on any axioms -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.onNative_run

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.registration_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.registration_step

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.step_merge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.step_merge

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compile_simulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compile_simulation

/-- info: 'BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compile_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentCompileStep.compile_run
