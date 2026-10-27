-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealPostItem

/-!
# Item 2's per-request steps against the middle execution: the projection and the native requests (CE-11b, unit U6, second part)

Item 2's side of the post-challenge simulation (`PqxdhDeploymentIdealPostSim.sim_option`) needs, for every request of the middle source handler (`PqxdhDeploymentIdealPostSource.sourceMid`), that item 2's two layers answer it from item 2's view of the middle state without stopping and end in item 2's view of the middle's poststate. This module fixes that view and proves the first steps.

- `encodeMid`: item 2's view of a middle state: the encoded owners of the annotated source state (`PqxdhRegistrationJointGeneratedFinish.encodeState`), the skeleton state (the game state without analysis observers and the mark with the value of its coordinates in the two-slot table, `skelMarks`), and the service state (the router state of the annotated pools without transcripts, `PqxdhDeploymentIdealPoolSource.routerOf`, the public table cache of the shared native state, the allocator and the table). `upperE` and `lowerE` are item 2's two layers with the erasures of `PqxdhDeploymentIdealPostItem`, and `StepAt` is the per-request obligation (`sim_option`'s `step` at this view).
- Helpers: `lowerE_native` (the erased service layers act on native skeleton steps as the table layers, from a view without router transcripts, `encodeMid_erased`), `upperE_run` (from a view without game observers, `encodeMid_clean`), `tableLayer_direct` (a direct read is answered by the public table).
- The native requests: the BLAKE2b request (`step_hash`, with `upperLayer_hash`), the Server kernel reveal (`step_reveal`, with `upperLayer_reveal`) and the coin request (`step_coin`, with `upperLayer_coin`).

These are program equalities. They charge nothing and make no security claim.
-/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption coinLift clean)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer upperLayer eraseService)
open PqxdhDeploymentIdealPostSource (Mid sourceMid)
open PqxdhDeploymentIdealPostItem (cleanSkel cleanUpper)
open PqxdhDeploymentIdealParams (Target Params)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Item 2's view of the middle state -/

/-- The mark of the middle state with the value of its coordinates in the two-slot table. -/
def skelMarks (m : Mid KemSK) : Option (ℕ × Output) :=
  m.backend.2.2.marks.bind fun mark =>
    (PqxdhRegistrationJointKemSecondEntry.cacheOf (m.backend.2.1, m.backend.1) mark.2).map fun value => (mark.1, value)

/-- Item 2's view of the middle state: the encoded owners, the skeleton state (the game state without analysis observers and the mark with its value), and the service state (the router state of the annotated pools without transcripts, the public table cache, the allocator and the two-slot table). -/
def encodeMid (setup : Setup baseSpec KemSK) (m : Mid KemSK) :
    (List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) × ServiceState KemSK :=
  (((PqxdhRegistrationJointGeneratedFinish.encodeState setup m.joint).owners, (clean m.joint.shared.2, skelMarks m)),
    (PqxdhRegistrationJointKemObserverFree.eraseJoint (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
      (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))))

section Layers
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Item 2's upper layers with the skeleton's game observers erased, at the cut's Server and target. -/
noncomputable abbrev upperE :=
  PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpper
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
      p.challenge (factoredServices setup codec checks))

/-- Item 2's service layers with the router transcripts erased, at the challenger's draws. -/
noncomputable abbrev lowerE :=
  PqxdhRegistrationJointKemObserverFree.eraseOptionImpl eraseService
    (serviceLayer setup t.kem p.chosen p.others p.challenge)

/-- One request of the middle source handler is answered by item 2's two layers from item 2's view of the middle state, without stopping, with item 2's view of the middle's poststate. -/
def StepAt (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain) (m : Mid KemSK) : Prop :=
  ((simulateQ (lowerE setup t p) ((upperE setup codec checks t p created query).run (encodeMid setup m).1)).run).run
      (encodeMid setup m).2 =
    (fun result => (some (result.1, (encodeMid setup result.2).1), (encodeMid setup result.2).2)) <$>
      (sourceMid setup codec route checks t p created query).run m

end Layers

/-! ### Helpers -/

section Helpers
variable (setup : Setup baseSpec KemSK) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- On a native skeleton step, the erased service layers act as the table layers from a service state without router transcripts. -/
theorem lowerE_native {α : Type} (work : OracleComp (SkelSpec Output) α) (state : ServiceState KemSK)
    (erased : eraseService state = state) :
    ((simulateQ (lowerE setup t p) (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) work)).run).run state =
      (fun result => (some result.1, (state.1, result.2))) <$> (simulateQ tableLayer work).run state.2 := by
  have run := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen p.others p.challenge)
    (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    (simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) work) state
  rw [erased] at run
  rw [← run, PqxdhDeploymentIdealPostItem.service_native, Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  have first : PqxdhRegistrationJointKemObserverFree.eraseJoint state.1 = state.1 := congrArg Prod.fst erased
  simp only [Prod.map, id_eq, eraseService, first]

/-- Item 2's view of a middle state has no router transcripts. -/
theorem encodeMid_erased (m : Mid KemSK) : eraseService (encodeMid setup m).2 = (encodeMid setup m).2 := rfl

/-- Item 2's view of a middle state has no game observers. -/
theorem encodeMid_clean (m : Mid KemSK) : cleanUpper (encodeMid setup m).1 = (encodeMid setup m).1 := rfl

end Helpers

/-! ### The native requests -/

section NativeSteps
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The upper layers with erased game observers, from a view without them, are the upper layers with the observers of the poststate erased. -/
theorem upperE_run (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output)
    (clean : cleanUpper state = state) :
    (upperE setup codec checks t p created query).run state =
      Prod.map id cleanUpper <$> (upperLayer setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks) query).run state := by
  change Prod.map id cleanUpper <$> _ = _
  rw [clean]

/-- The upper layers on the BLAKE2b request: the skeleton's native hash on its game state. -/
theorem upperLayer_hash (bytes : Pqxdh.Bytes)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.hash bytes)))).run state =
      (fun result => (result.1, (state.1, result.2))) <$> simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.gameStep (V := Output)
          (PqxdhRegistrationJointKemPostSkeleton.hashGame bytes)).run state.2) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run ((fun a => (a, state.1)) <$>
    PqxdhRegistrationJointKemPostSkeleton.liftT (V := Output)
      (PqxdhRegistrationJointKemPostSkeleton.gameStep (PqxdhRegistrationJointKemPostSkeleton.hashGame bytes))) state.2 = _
  rw [StateT.run_map, Functor.map_map]
  rfl

/-- The BLAKE2b request. -/
theorem step_hash (bytes : Pqxdh.Bytes) (m : Mid KemSK) :
    StepAt setup codec route checks t p created (.inl (.inr (.hash bytes))) m := by
  unfold StepAt
  rw [upperE_run setup codec checks t p created _ _ (encodeMid_clean setup m), upperLayer_hash, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map, lowerE_native setup t p _ _ (encodeMid_erased setup m),
    PqxdhRegistrationJointKemPostSkeleton.gameStep_run, simulateQ_map, StateT.run_map,
    PqxdhDeploymentIdealPostItem.tableLayer_lift]
  simp only [Functor.map_map]
  change _ = _ <$> ((fun r => (r.1, { m with joint := r.2 })) <$>
    ((fun r => (r.1, { m.joint with shared := r.2 })) <$>
      PqxdhServerAuthNative.nativeHash (KemSK := KemSK) bytes m.joint.shared))
  simp only [PqxdhServerAuthNative.nativeHash, PqxdhRegistrationJointKemPostSkeleton.hashGame, StateT.run,
    Functor.map_map]
  rfl

/-- The upper layers on the Server kernel reveal: the skeleton's native reveal on its game state. -/
theorem upperLayer_reveal (keyId : Std.U64)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inr (.reveal keyId)))).run state =
      (fun result => (result.1, (state.1, result.2))) <$> simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK)))
        ((PqxdhRegistrationJointKemPostSkeleton.gameStep (V := Output)
          (fun game => pure (PqxdhServerAuthExperiment.revealKernel keyId game, game))).run state.2) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run ((fun a => (a, state.1)) <$>
    PqxdhRegistrationJointKemPostSkeleton.liftT (V := Output)
      (PqxdhRegistrationJointKemPostSkeleton.gameStep
        (fun game => pure (PqxdhServerAuthExperiment.revealKernel keyId game, game)))) state.2 = _
  rw [StateT.run_map, Functor.map_map]
  rfl

/-- The Server kernel reveal. -/
theorem step_reveal (keyId : Std.U64) (m : Mid KemSK) :
    StepAt setup codec route checks t p created (.inl (.inr (.reveal keyId))) m := by
  unfold StepAt
  rw [upperE_run setup codec checks t p created _ _ (encodeMid_clean setup m), upperLayer_reveal, Functor.map_map,
    simulateQ_map, OptionT.run_map, StateT.run_map, lowerE_native setup t p _ _ (encodeMid_erased setup m),
    PqxdhRegistrationJointKemPostSkeleton.gameStep_run, simulateQ_map, StateT.run_map,
    PqxdhDeploymentIdealPostItem.tableLayer_lift]
  simp only [Functor.map_map]
  rfl

/-- The upper layers on a coin: the coin channel of the exposed encapsulation interface, with the state kept. -/
theorem upperLayer_coin (coin : unifSpec.Domain)
    (state : List PqxdhRegistrationJointGeneratedFinish.EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inl (.inl coin))).run state =
      (fun reply => (reply, state)) <$> ((Enc KemSK + TSpec Output).query (.inl (.inl (.inr (.inl coin)))) :
        OracleComp (Enc KemSK + TSpec Output) _) := by
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client,
    PqxdhRegistrationJointServiceSchedule.handler]
  simp only [PqxdhRegistrationJointKemPostSkeleton.liftGrouped, StateT.run, StateT.lift, bind_pure_comp,
    simulateQ_map, simulateQ_spec_query, PqxdhRegistrationJointKemPostSkeleton.groupedLift,
    PqxdhRegistrationJointKemPostSkeleton.skelImpl, PqxdhRegistrationJointKemPostSkeleton.encLift]
  rfl

/-- The coin request. -/
theorem step_coin (coin : unifSpec.Domain) (m : Mid KemSK) :
    StepAt setup codec route checks t p created (.inl (.inl coin)) m := by
  unfold StepAt
  rw [upperE_run setup codec checks t p created _ _ (encodeMid_clean setup m), upperLayer_coin, Functor.map_map,
    simulateQ_map, simulateQ_spec_query, OptionT.run_map, StateT.run_map]
  have lowered : ((lowerE setup t p (.inl (.inl (.inr (.inl coin))))).run).run (encodeMid setup m).2 =
      (fun reply => (some reply, (encodeMid setup m).2)) <$> (unifSpec.query coin : ProbComp _) := by
    change Prod.map id eraseService <$> ((serviceLayer setup t.kem p.chosen p.others p.challenge
      (.inl (.inl (.inr (.inl coin))))).run).run (eraseService (encodeMid setup m).2) = _
    rw [encodeMid_erased, PqxdhDeploymentIdealPostItem.service_coin, Functor.map_map]
    rfl
  rw [lowered, Functor.map_map]
  rfl

/-- A direct table read is answered by item 2's public table, keeping the slot state. -/
theorem tableLayer_direct (point : Pqxdh.Bytes) (state : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    (tableLayer (.inr (.inr point))).run state =
      (fun result => (result.1, (result.2, state.2))) <$> (PqxdhSecretInputKdf.HmacOracle.randomOracle point).run state.1 := by
  simp only [tableLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemEntryFactor.publicLocalV]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl
    (D := PqxdhCorrelatedExtractFamily.Message) (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
    (OracleComp.liftComp ((PqxdhSecretInputKdf.HmacOracle.randomOracle point).run state.1)
      (PqxdhRegistrationJointKemEntryFactor.EntrySpec Output))).run state.2 = _
  rw [PqxdhDeploymentIdealCut.slotImpl_lift, Functor.map_map]

end NativeSteps

end BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.lowerE_native' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.lowerE_native

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.encodeMid_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.encodeMid_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.encodeMid_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.encodeMid_clean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperE_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperE_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_hash' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_hash

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_reveal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_reveal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_reveal

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.upperLayer_coin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_coin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.step_coin

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.tableLayer_direct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealPostSteps.tableLayer_direct
