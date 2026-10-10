-- SPDX-License-Identifier: 0BSD
import BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterMid

/-! LQ-F upstream, unit B2: item 2's side of the middle run of the later second compile lemma (the logged counterpart of CE-11b unit U6's `PqxdhDeploymentIdealPostSteps`, `PqxdhDeploymentIdealPostRequests`, `PqxdhDeploymentIdealPostServer`, `PqxdhDeploymentIdealPostInvariant`, `PqxdhDeploymentIdealPostItem` and `PqxdhDeploymentIdealPostItemRun`). On an active cut, item 2's logged post-challenge phase (`PqxdhDeploymentIdealLaterBranch.itemPostL`) resumes the Server's selected raw accept and runs the tagged logged continuation through its post-challenge layers: the logged grouped client of unit D1 over the logged skeleton, then the service layers. This module shows that the whole phase is the logged middle run of `PqxdhDeploymentIdealLaterMid` (`itemPost_middleL`), so that item 2's side and the CE side of the active branch become functions of one run.

- Item 2's logged layers and view: `upperLayerL` (the logged grouped client over the logged skeleton), `cleanUpperL`, `upperEL`, the logged views `encodeMidCL` and `encodeMidL` (CE-11b's views with the log beside the owners) and the per-request obligations `StepAtCL` and `StepAtL`; `skelImplL_lift`, `upperLayerL_inl`, `stepAtCL_of_stepAtL` and `stepAtCL_of_stepAtC` (every CE-11b per-request step of a source14 request other than a raw accept lifts to the logged view, whatever the log).
- The requests that the classical middle run does not issue or answers differently: the Server read (`upperLayerL_read`, `step_serverRead`: both sides reveal the Server's identity slot of the same pool), a raw accept other than the selected one (`upperLayerL_accept`, `prefix_chainL`, `orderedL_bound`, `acceptSource_run`, `step_acceptL`, `step_acceptCL`: the logged skeleton accept is the logged annotated accept, with the logged scalar appended to the log on both sides), and an identity field read of the terminal reads (`lowerE_poolL`, `upperLayer_identity`, `step_identity`, `step_identityCL`: the identity-pool reveal of the owner's slot through the post-challenge router holds the owner's seed, `PqxdhRegistrationJointLiveRead.entry_source`; `lowerE_poolL` is CE-11b's `lowerE_pool` with identity reveals allowed, through `PqxdhDeploymentIdealLaterPool.stopped_programL`).
- The simulation: `AllowedL` (every logged request but a KEM field read), `CostlyL` (the creations), `roomL`, `ItemInvL` (CE-11b's `ItemInv` of the middle state), `step_allL`, `keep_allL` and `item_simL` (`PqxdhDeploymentIdealPostSim.sim_option`), and `simulate_keeps` (the support form of the preservation obligation).
- The logged skeleton with both erasures: `ghostFree_acceptStepL`, `skelImplL_ghostFree`, `upperLayerL_neverRead`, `skelResumeL_upper`, `itemPostL_active`, `itemPostL_erased` and `itemPostL_clean`; then `itemPost_middleL`, through CE-11b's `resume_clean`, `resume_accept`, `lowerEC_run`, `acceptAfter_keeps` and `itemInv_after`.

Premises: item 2's facts at the pool at the cut (`PoolOwned`, a prefix KEM pool, the owner positions), the constructed Server's public identity, the selected PQ key, and a continuation with only simulated logged requests and at most the room's number of creations. These are program equalities and support facts. They charge nothing and make no security claim. -/

open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc

set_option autoImplicit false

namespace BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps
open PqxdhServerAuthExperiment (Setup Codec Checks)
open PqxdhKemIndCca (MlKem768PublicKey MlKem768Ciphertext)
open PqxdhRegistrationJointKemPostSkeleton (Enc TSpec SkelSpec SkelState fwd fwdOption coinLift clean)
open PqxdhDeploymentIdealLaterMid (MidL sourceMidL sourceMidL_inl)
open PqxdhRegistrationJointKemEntryFactor (Output factoredServices)
open PqxdhDeploymentIdealPostSim (SlotState ServiceState tableLayer serviceLayer upperLayer eraseService)
open PqxdhDeploymentIdealPostSource (Mid sourceMid realMid bumpSource)
open PqxdhDeploymentIdealPostItem (cleanSkel cleanUpper)
open PqxdhDeploymentIdealPostHidden (StepAtC encodeMidC lowerEC)
open PqxdhDeploymentIdealParams (Target Params)
open PqxdhDeploymentLaterServerSource (Log)
open PqxdhRegistrationJointGeneratedFinish (EncodedEntry)
open PqxdhDeploymentLaterServerItemTargets (skelImplL groupedClientL GSpecL)

variable {ι : Type} {baseSpec : OracleSpec ι} {KemSK Reader Response : Type}

/-! ### Item 2's logged upper layers and view -/

/-- Item 2's logged upper layers: the logged grouped client over the logged skeleton, flattened. -/
noncomputable def upperLayerL {V : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)
    (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    QueryImpl (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (StateT ((List EncodedEntry × Log) × SkelState KemSK V) (OracleComp (Enc KemSK + TSpec V))) :=
  ((skelImplL setup codec checks identityIndex publicIdentity services).mapStateTBase
    (groupedClientL setup codec selected challenge identityIndex)).flattenStateT

/-- Erasing the skeleton's game observers in the logged upper state. -/
def cleanUpperL {V : Type} (state : (List EncodedEntry × Log) × SkelState KemSK V) :
    (List EncodedEntry × Log) × SkelState KemSK V :=
  (state.1, cleanSkel state.2)

section View
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Item 2's logged upper layers with the game observers erased. -/
noncomputable abbrev upperEL :=
  PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpperL
    (upperLayerL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
      p.challenge (factoredServices setup codec checks))

/-- Item 2's view of a logged middle state: the classical view without table counters, with the log beside the owners. -/
def encodeMidCL (s : MidL KemSK) :
    ((List EncodedEntry × Log) × SkelState KemSK Output) × ServiceState KemSK :=
  ((((encodeMidC setup s.1).1.1, s.2), (encodeMidC setup s.1).1.2), (encodeMidC setup s.1).2)

/-- The per-request obligation at the logged view. -/
def StepAtCL (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (s : MidL KemSK) : Prop :=
  ((simulateQ (lowerEC setup t p) ((upperEL setup codec checks t p created query).run (encodeMidCL setup s).1)).run).run
      (encodeMidCL setup s).2 =
    (fun result => (some (result.1, (encodeMidCL setup result.2).1), (encodeMidCL setup result.2).2)) <$>
      (sourceMidL setup codec route checks t p created query).run s

/-- The logged skeleton on classical requests lifted to the logged grouped interface is the classical skeleton. -/
theorem skelImplL_lift {V α : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (work : OracleComp (PqxdhRegistrationJointKemPostSkeleton.GSpec KemSK Response) α) :
    simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _)) work) =
      simulateQ (PqxdhRegistrationJointKemPostSkeleton.skelImpl setup codec checks identityIndex publicIdentity services)
        work := by
  induction work using OracleComp.inductionOn with
  | pure value => simp
  | query_bind query next ih =>
      simp only [simulateQ_bind, simulateQ_spec_query, ih]
      rfl

/-- The logged upper layers on a source14 request other than a raw accept are the classical upper layers with the log kept. -/
theorem upperLayerL_inl {V : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (selected : ℕ) (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw)))
    (state : (List EncodedEntry × Log) × SkelState KemSK V) :
    (upperLayerL setup codec checks identityIndex publicIdentity selected challenge services (.inl query)).run state =
      (fun result => (result.1, ((result.2.1, state.1.2), result.2.2))) <$>
        (upperLayer setup codec checks identityIndex publicIdentity selected challenge services query).run
          (state.1.1, state.2) := by
  have client : (groupedClientL (Response := Response) setup codec selected challenge identityIndex (.inl query)).run
      state.1 = (fun result => (result.1, (result.2, state.1.2))) <$>
        simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
          ((PqxdhRegistrationJointKemPostSkeleton.groupedClient setup codec selected challenge query).run state.1.1) :=
    PqxdhDeploymentLaterServerItemTargets.groupedClientL_inl setup codec selected challenge identityIndex query other
      state.1
  simp only [upperLayerL, upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk]
  rw [client, simulateQ_map, StateT.run_map, skelImplL_lift, Functor.map_map, Functor.map_map]

/-- Item 2's view of a logged middle state with the table counters kept (the classical `encodeMid`), with the log beside the owners. -/
def encodeMidL (s : MidL KemSK) :
    ((List EncodedEntry × Log) × SkelState KemSK Output) × ServiceState KemSK :=
  ((((PqxdhDeploymentIdealPostSteps.encodeMid setup s.1).1.1, s.2), (PqxdhDeploymentIdealPostSteps.encodeMid setup s.1).1.2),
    (PqxdhDeploymentIdealPostSteps.encodeMid setup s.1).2)

/-- The per-request obligation at the logged view with the table counters kept. -/
def StepAtL (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (s : MidL KemSK) : Prop :=
  ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p)
      ((upperEL setup codec checks t p created query).run (encodeMidL setup s).1)).run).run (encodeMidL setup s).2 =
    (fun result => (some (result.1, (encodeMidL setup result.2).1), (encodeMidL setup result.2).2)) <$>
      (sourceMidL setup codec route checks t p created query).run s

/-- Every step at the logged view with the table counters is a step at the logged view without them. -/
theorem stepAtCL_of_stepAtL (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (s : MidL KemSK)
    (step : StepAtL setup codec route checks t p created query s) :
    StepAtCL setup codec route checks t p created query s := by
  unfold StepAtL at step
  unfold StepAtCL
  have counted := PqxdhRegistrationJointKemObserverFree.run_eraseOption PqxdhDeploymentIdealPostHidden.eraseServiceC
    PqxdhDeploymentIdealPostHidden.eraseServiceC_idem _
    (PqxdhDeploymentIdealPostHidden.serviceLayer_neverReadC setup t.kem p.chosen p.others p.challenge)
    ((upperEL setup codec checks t p created query).run (encodeMidL setup s).1) (encodeMidL setup s).2
  have erased := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    _ (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    ((upperEL setup codec checks t p created query).run (encodeMidL setup s).1) (encodeMidL setup s).2
  rw [show eraseService (encodeMidL setup s).2 = (encodeMidL setup s).2 from rfl] at erased
  change _ = ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p) _).run).run (encodeMidL setup s).2 at erased
  change ((simulateQ (lowerEC setup t p) ((upperEL setup codec checks t p created query).run
    (encodeMidL setup s).1)).run).run (PqxdhDeploymentIdealPostHidden.eraseServiceC (encodeMidL setup s).2) = _
  have key := congrArg (fun work => Prod.map id PqxdhDeploymentIdealPostHidden.eraseServiceC <$> work) erased
  have comp : ∀ {α : Type} (result : α × ServiceState KemSK),
      Prod.map id PqxdhDeploymentIdealPostHidden.eraseServiceC (Prod.map id eraseService result) =
        Prod.map id PqxdhDeploymentIdealPostHidden.eraseServiceC result :=
    fun result => by simp only [Prod.map, id_eq, PqxdhDeploymentIdealPostHidden.eraseServiceC_eraseService]
  simp only [Functor.map_map, comp] at key
  rw [← counted, key, step, Functor.map_map]
  rfl

end View


section Lift
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Every step at the classical view without table counters, of a source14 request other than a raw accept, is a step at the logged view, whatever the log. -/
theorem stepAtCL_of_stepAtC (query : (PqxdhRegistrationJointRevealSchedule.Spec KemSK).Domain)
    (other : ∀ raw, query ≠ .inl (.inr (.accept raw))) (m : Mid KemSK) (log : Log)
    (step : StepAtC setup codec route checks t p created query m) :
    StepAtCL setup codec route checks t p created (.inl query) (m, log) := by
  unfold StepAtC at step
  unfold StepAtCL
  have upper : (upperEL setup codec checks t p created (.inl query)).run (encodeMidCL setup (m, log)).1 =
      (fun result => (result.1, ((result.2.1, log), result.2.2))) <$>
        (PqxdhDeploymentIdealPostSteps.upperE setup codec checks t p created query).run (encodeMidC setup m).1 := by
    change Prod.map id cleanUpperL <$> (upperLayerL setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks) (.inl query)).run
          (cleanUpperL (encodeMidCL setup (m, log)).1) =
      _ <$> (Prod.map id cleanUpper <$> (upperLayer setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks) query).run
          (cleanUpper (encodeMidC setup m).1))
    rw [upperLayerL_inl setup codec checks _ _ _ _ _ query other, Functor.map_map, Functor.map_map]
    rfl
  rw [upper, simulateQ_map, OptionT.run_map, StateT.run_map, sourceMidL_inl setup codec route checks t p created query
    other m log, show (encodeMidCL setup (m, log)).2 = (encodeMidC setup m).2 from rfl, step, Functor.map_map,
    Functor.map_map]
  refine congrArg (fun f => f <$> _) (funext fun result => ?_)
  rfl

end Lift

section Read
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

theorem upperLayerL_read {V : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (selected : ℕ) (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (state : (List EncodedEntry × Log) × SkelState KemSK V) :
    (upperLayerL setup codec checks identityIndex publicIdentity selected challenge services (.inr ())).run state =
      (fun reply => ((reply, state.1.2), state)) <$>
        PqxdhRegistrationJointKemPostSkeleton.encLift (V := V) (.inl (.inl (.inr (.reveal identityIndex)))) := by
  have inner : simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
      (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
        (PqxdhRegistrationJointKemPostSkeleton.groupedPoolLift (Response := Response)
          (.inl (.inr (.reveal identityIndex))))) =
      fun s => (fun reply => (reply, s)) <$>
        PqxdhRegistrationJointKemPostSkeleton.encLift (V := V) (.inl (.inl (.inr (.reveal identityIndex)))) := by
    rw [skelImplL_lift, PqxdhRegistrationJointKemPostSkeleton.groupedPoolLift, simulateQ_spec_query]
    rfl
  change (fun x => (x.1.1, (x.1.2, x.2))) <$> StateT.run ((fun seed => ((seed, state.1.2), state.1)) <$>
    simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
      (simulateQ (fun q => ((GSpecL KemSK Response).query (.inl q) : OracleComp (GSpecL KemSK Response) _))
        (PqxdhRegistrationJointKemPostSkeleton.groupedPoolLift (Response := Response)
          (.inl (.inr (.reveal identityIndex)))))) state.2 = _
  rw [StateT.run_map, inner]
  simp only [StateT.run, Functor.map_map]

/-- The Server read: item 2's logged grouped client reveals the Server's identity slot through the post-challenge router, as the logged source's read on the middle state does. -/
theorem step_serverRead (m : Mid KemSK) (log : Log) :
    StepAtCL setup codec route checks t p created (.inr ()) (m, log) := by
  rfl

end Read

section Accept
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The logged upper layers on a raw accept: the logged skeleton accept, with its logged scalar appended to the log. -/
theorem upperLayerL_accept {V : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (selected : ℕ) (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response)
    (raw : Pqxdh.Bytes) (state : (List EncodedEntry × Log) × SkelState KemSK V) :
    (upperLayerL setup codec checks identityIndex publicIdentity selected challenge services
        (.inl (.inl (.inr (.accept raw))))).run state =
      (fun result => (result.1.1, ((state.1.1, state.1.2 ++ [result.1.2]), result.2))) <$>
        (PqxdhDeploymentLaterServerItemTargets.acceptStepL setup codec checks identityIndex publicIdentity raw).run
          state.2 := by
  change (fun x => (x.1.1, (x.1.2, x.2))) <$> StateT.run (simulateQ (skelImplL setup codec checks identityIndex
    publicIdentity services) ((fun answer => (answer.1, (state.1.1, state.1.2 ++ [answer.2]))) <$>
      ((GSpecL KemSK Response).query (.inr raw) : OracleComp (GSpecL KemSK Response) _))) state.2 = _
  rw [simulateQ_map, simulateQ_spec_query, StateT.run_map, Functor.map_map]
  rfl

/-- The exposed logged collector, run by the actual encapsulator and the actual private services, is item 2's annotated logged collector, when the Server's identity slot holds its seed (the logged form of `PqxdhDeploymentIdealPostServer.prefix_chain`). -/
theorem prefix_chainL (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes)
    (pool : PqxdhRegistrationJointPreparation.Pool KemSK) (consumed : List Pqxdh.Bytes)
    (owned : pool.1.seeds[identityIndex]? = some seed) :
    (simulateQ (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem)
        (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
          ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run consumed))).run pool =
      (fun result => ((result.1, result.2.2), result.2.1)) <$>
        (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (PqxdhServerAuthExperiment.serverAux setup codec checks))
          (PqxdhDeploymentLaterServerSource.collectLogged (Reader := Reader) raw)).run (pool, consumed) := by
  rw [PqxdhDeploymentLaterServerCommands.ordered, PqxdhRegistrationJointKemSourceSuffix.handler,
    QueryImpl.simulateQ_compose, PqxdhRegistrationJointKemEncapsulation.prefix_program]
  have chain := PqxdhRegistrationJointOpenBackend.prefix_program setup codec checks
    (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex)
      (PqxdhDeploymentLaterServerSource.collectLogged (Reader := Reader) raw)) (pool, consumed)
  rw [PqxdhRegistrationJointServerPrefix.program_source setup (PqxdhServerAuthExperiment.serverAux setup codec checks)
    seed identityIndex _ (pool, consumed) owned] at chain
  rw [← chain]
  simp only [PqxdhRegistrationJointOpenBackend.run, Functor.map_map]
  exact (id_map _).symm

/-- The exposed logged collector, under the actual encapsulator, has the private-request bound of the classical raw prefix in every non-uniform pool class: one static DH request and nothing else (`PqxdhRegistrationJointOpenCosts.prefix_bound` through `collectLogged_fst`). -/
theorem orderedL_bound (identityIndex : ℕ) (raw : Pqxdh.Bytes) (consumed : List Pqxdh.Bytes)
    (kind : PqxdhRegistrationJointServiceCosts.Kind) (nonuniform : kind ≠ .uniform) :
    (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
        ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks identityIndex raw).run consumed)).IsQueryBoundP
      (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = kind)
      (if kind = .staticDh then 1 else 0) := by
  rw [PqxdhDeploymentLaterServerCommands.ordered, PqxdhRegistrationJointKemSourceSuffix.handler,
    QueryImpl.simulateQ_compose, PqxdhRegistrationJointKemEncapsulation.prefix_program]
  have mapped : (fun result => (result.1.1, result.2)) <$>
      (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
        (simulateQ (PqxdhRegistrationJointServerPrefix.compiler identityIndex)
          (PqxdhDeploymentLaterServerSource.collectLogged (Reader := Reader) raw))).run consumed =
      (simulateQ (PqxdhRegistrationJointOpenBackend.prefixImpl setup codec checks)
        (PqxdhRegistrationJointServerPrefix.clientPrefix (Reader := Reader) identityIndex raw)).run consumed := by
    rw [PqxdhRegistrationJointServerPrefix.clientPrefix, ← PqxdhDeploymentLaterServerSource.collectLogged_fst,
      simulateQ_map, simulateQ_map, StateT.run_map]
  have bound := PqxdhRegistrationJointOpenCosts.prefix_bound (KemSK := KemSK) setup codec checks identityIndex raw
    consumed kind nonuniform
  rw [← mapped, isQueryBoundP_map_iff] at bound
  exact bound

/-- The logged annotated source accept: the annotated logged collector on the private pools and the consumed list, then the accept tail on the native state captured before it, with the logged scalar returned beside the reply. -/
theorem acceptSource_run (seed : PqxdhJointIdentity.IdentitySeed) (identityIndex : ℕ) (raw : Pqxdh.Bytes)
    (state : PqxdhRegistrationJointSchedule.State KemSK) :
    (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks
      seed identityIndex raw)).run state =
      (simulateQ (PqxdhRegistrationJointServerPrefix.annotated setup.joint seed identityIndex
          (PqxdhServerAuthExperiment.serverAux setup codec checks))
          (PqxdhDeploymentLaterServerSource.collectLogged (Reader := Reader) raw)).run
          (state.pool, state.shared.2.server.consumed) >>= fun prepared =>
        (fun result => ((result.1, prepared.1.2), { state with pool := prepared.2.1, shared := result.2 })) <$>
          (PqxdhRegistrationJointServerAccept.tail setup (setup.joint.publicKeys seed) state.shared.2
            (prepared.1.1, prepared.2.2)).run state.shared := by
  show PqxdhRegistrationJointServerSchedule.onBackend _ state = _
  simp only [PqxdhRegistrationJointServerSchedule.onBackend, PqxdhDeploymentLaterServerSource.acceptSource]
  rw [StateT.run_bind]
  change _ <$> ((pure (state.shared.2, (state.pool, state.shared)) : ProbComp _) >>= _) = _
  rw [pure_bind, StateT.run_bind]
  simp only [PqxdhDeploymentLaterServerSource.sourcePrepare, StateT.run, bind_map_left, map_bind]
  refine bind_congr fun prepared => ?_
  change _ <$> (StateT.run (PqxdhRegistrationJointFinish.onNative _ >>= _) (prepared.2.1, state.shared)) = _
  rw [StateT.run_bind]
  simp only [PqxdhRegistrationJointFinish.onNative, StateT.run, bind_map_left, map_bind]
  rw [map_eq_bind_pure_comp]
  refine bind_congr fun answer => ?_
  rfl

/-- A raw accept (never the selected one in the middle run): the logged skeleton accept through item 2's layers (its logged collector through the actual encapsulator and the post-challenge router, its tail through the table layers) is the logged annotated source accept on the middle state, with the accept counter advanced and the logged scalar appended to the log on both sides. It needs the Server's identity slot to hold its seed, the constructed Server's public identity to be that of its seed, and a prefix KEM pool. -/
theorem step_acceptL (raw : Pqxdh.Bytes) (m : Mid KemSK) (log : Log)
    (owned : m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAtL setup codec route checks t p created (.inl (.inl (.inr (.accept raw)))) (m, log) := by
  unfold StepAtL
  have upper : (upperEL setup codec checks t p created (.inl (.inl (.inr (.accept raw))))).run
      (encodeMidL setup (m, log)).1 =
      (fun result => (result.1.1, ((((PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.1, log ++ [result.1.2])),
        cleanSkel result.2))) <$>
        (PqxdhDeploymentLaterServerItemTargets.acceptStepL setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity raw).run (PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.2 := by
    change Prod.map id cleanUpperL <$> (upperLayerL setup codec checks created.server.server.metadata.identityIndex
        created.publicIdentity t.kem.val p.challenge (factoredServices setup codec checks)
          (.inl (.inl (.inr (.accept raw))))).run (cleanUpperL (encodeMidL setup (m, log)).1) = _
    rw [upperLayerL_accept, Functor.map_map]
    rfl
  have middle : (sourceMidL setup codec route checks t p created (.inl (.inl (.inr (.accept raw))))).run (m, log) =
      (fun result => (result.1.1, ((⟨result.2, bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) m.backend,
        m.seeds⟩ : Mid KemSK), log ++ [result.1.2]))) <$>
        (PqxdhRegistrationJointServerSchedule.onBackend (PqxdhDeploymentLaterServerSource.acceptSource setup codec checks
          created.seed created.server.server.metadata.identityIndex raw)).run m.joint := by
    change _ <$> (_ <$> _) = _
    rw [Functor.map_map]
  rw [upper, simulateQ_map, OptionT.run_map, StateT.run_map, middle, acceptSource_run]
  have noCreate : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks created.server.server.metadata.identityIndex
        raw).run m.joint.shared.2.server.consumed)).IsQueryBoundP
        (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) 0 := by
    refine (isQueryBoundP_congr_pred (fun query => ?_)).mpr (by
      simpa using orderedL_bound (Reader := Reader) setup codec checks created.server.server.metadata.identityIndex raw
        m.joint.shared.2.server.consumed .kemCreate (by decide))
    rw [PqxdhDeploymentIdealPoolSource.isCreate_class]
  have noReveal : (simulateQ (PqxdhRegistrationJointKemEncapsulation.actual setup)
      ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks created.server.server.metadata.identityIndex
        raw).run m.joint.shared.2.server.consumed)).IsQueryBoundP
        (fun query => PqxdhRegistrationJointServiceCosts.poolClass (KemSK := KemSK) query = .other) 0 := by
    simpa using orderedL_bound (Reader := Reader) setup codec checks created.server.server.metadata.identityIndex raw
      m.joint.shared.2.server.consumed .other (by decide)
  have fresh := PqxdhDeploymentIdealPostRequests.fresh_of_noDecaps t.kem.val p.challenge _ (by
    simpa using orderedL_bound (Reader := Reader) setup codec checks created.server.server.metadata.identityIndex raw
      m.joint.shared.2.server.consumed .decapsulate (by decide))
  have stepT : (PqxdhDeploymentLaterServerItemTargets.acceptStepL (V := Output) setup codec checks
      created.server.server.metadata.identityIndex created.publicIdentity raw).run
        (PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.2 =
      ((fun result => (result, (PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.2)) <$>
        simulateQ (PqxdhRegistrationJointKemPostSkeleton.encLift (V := Output))
          ((PqxdhDeploymentLaterServerCommands.ordered setup codec checks created.server.server.metadata.identityIndex
            raw).run m.joint.shared.2.server.consumed)) >>= fun result =>
        (fun reply => ((reply.1, result.1.1.2), reply.2)) <$>
          (PqxdhRegistrationJointKemPostSkeleton.liftT (PqxdhRegistrationJointKemPostSkeleton.acceptTail setup
            created.publicIdentity (clean m.joint.shared.2) (result.1.1.1, result.1.2))).run result.2 := by
    simp only [PqxdhDeploymentLaterServerItemTargets.acceptStepL, StateT.run_bind]
    change (pure _ >>= _) = _
    rw [pure_bind]
    refine bind_congr fun result => ?_
    rw [map_eq_bind_pure_comp]
    rfl
  rw [stepT, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, simulateQ_map, OptionT.run_map,
    StateT.run_map]
  rw [show (encodeMidL setup (m, log)).2 = (PqxdhRegistrationJointKemObserverFree.eraseJoint
      (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
      (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) from rfl,
    PqxdhDeploymentIdealPostServer.lowerE_enc setup t p _ noCreate noReveal fresh m.joint.pool.1 m.joint.pool.2
      prefixed,
    prefix_chainL setup codec checks created.seed _ raw (m.joint.pool.1, m.joint.pool.2) _ owned]
  simp only [Functor.map_map, bind_map_left, map_bind, Prod.mk.eta]
  refine bind_congr fun prepared => ?_
  rw [identity] at *
  have native := PqxdhDeploymentIdealPostSteps.lowerE_native setup t p
    ((PqxdhRegistrationJointKemPostSkeleton.acceptTail setup (setup.joint.publicKeys created.seed)
      (clean m.joint.shared.2) (prepared.1.1, prepared.2.2)).run (PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.2)
    (PqxdhRegistrationJointKemObserverFree.eraseJoint (prepared.2.1.1, PqxdhDeploymentIdealPoolSource.routerOf
      prepared.2.1.2), (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1)))
    (by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
  simp only [Option.map_some, Option.elim_some]
  rw [simulateQ_map, OptionT.run_map, StateT.run_map]
  rw [show ∀ (work : PqxdhRegistrationJointKemPostSkeleton.NGame KemSK Output (Option ℕ)) (s : SkelState KemSK Output),
      (PqxdhRegistrationJointKemPostSkeleton.liftT work).run s =
        simulateQ (fwd (T := TSpec Output) (coinLift (KemSK := KemSK))) (work.run s) from fun _ _ => rfl, native,
    show (PqxdhDeploymentIdealPostSteps.encodeMid setup m).1.2 =
      (clean m.joint.shared.2, PqxdhDeploymentIdealPostSteps.skelMarks m) from rfl,
    PqxdhDeploymentIdealPostServer.splitT_tail setup _ m.joint.shared.2 (prepared.1.1, prepared.2.2) m.joint.shared
      (PqxdhDeploymentIdealPostSteps.skelMarks m) (m.backend.2.1, m.backend.1)]
  simp only [Functor.map_map]
  rfl

/-- A raw accept at the logged view without table counters (`step_acceptL`). -/
theorem step_acceptCL (raw : Pqxdh.Bytes) (m : Mid KemSK) (log : Log)
    (owned : m.joint.pool.1.seeds[created.server.server.metadata.identityIndex]? = some created.seed)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAtCL setup codec route checks t p created (.inl (.inl (.inr (.accept raw)))) (m, log) :=
  stepAtCL_of_stepAtL setup codec route checks t p created _ _
    (step_acceptL setup codec route checks t p created raw m log owned identity prefixed)

end Accept

/-! ### Identity field reads -/

section Identity
open PqxdhDeploymentIdealPostSteps (StepAt encodeMid lowerE)
open PqxdhDeploymentIdealPostRequests (poolUp challengeDecaps)

/-- A private-service program sent by the skeleton, with at most `qCreate` KEM creations within the challenger's pool, no KEM reveal and no decapsulation of the selected challenge ciphertext, runs through item 2's erased service layers from the erased router state of a prefix pool as its run under the reserved services, without stopping (`PqxdhDeploymentIdealPostRequests.lowerE_pool` with identity reveals allowed, through `PqxdhDeploymentIdealLaterPool.stopped_programL`). -/
theorem lowerE_poolL (setup : Setup baseSpec KemSK) {count : ℕ} (t : Target count) (p : Params KemSK count) {α : Type}
    (client : OracleComp (PqxdhLiveKemBirth.Spec KemSK) α) (qCreate : ℕ)
    (bounded : client.IsQueryBoundP (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK)) qCreate)
    (noReveal : client.IsQueryBoundP
      (fun query => PqxdhDeploymentIdealLaterPool.kemReveal (KemSK := KemSK) query = true) 0)
    (fresh : client.IsQueryBoundP (fun query => challengeDecaps (KemSK := KemSK) t.kem.val p.challenge query = true) 0)
    (joint : PqxdhDynamicIdentityPool.SourceState) (pool : PqxdhLiveKemBirth.Pool KemSK)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) pool)
    (room : pool.keys.length + qCreate ≤ (p.pool t).length)
    (tables : PqxdhSecretInputKdf.HmacOracle.QueryCache × SlotState) :
    ((simulateQ (lowerE setup t p) (simulateQ poolUp client)).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables) =
      (fun result => (some result.1, (PqxdhRegistrationJointKemObserverFree.eraseJoint
          (result.2.1, PqxdhDeploymentIdealPoolSource.routerOf result.2.2), tables))) <$>
        (simulateQ (PqxdhDeploymentIdealPoolSource.reservedAt setup (p.pool t)) client).run (joint, pool) := by
  have run := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen p.others p.challenge)
    (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen p.others p.challenge)
    (simulateQ poolUp client) ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)
  change ((simulateQ (lowerE setup t p) (simulateQ poolUp client)).run).run
    (eraseService ((joint, PqxdhDeploymentIdealPoolSource.routerOf pool), tables)) = _
  rw [← run, PqxdhDeploymentIdealPostRequests.service_poolProgram]
  have reservation : PqxdhDynamicKemRouter.selectedReservation t.kem p.chosen.1 p.others =
      PqxdhDynamicKemRouter.redact t.kem.val (p.pool t) := by
    rw [PqxdhDeploymentIdealParams.pool_eq, PqxdhDynamicKemRouter.selected_reservation]
  have present : (p.pool t)[t.kem.val]? = some (p.chosen.1, p.chosen.2) := PqxdhDeploymentIdealParams.pool_kem t p
  simp only [PqxdhDeploymentIdealPostRequests.postRouter, reservation]
  rw [PqxdhDeploymentIdealPostRequests.jointProgram_fresh setup.baseImpl setup.kem setup.joint t.kem.val (p.pool t)
      p.chosen.1 p.chosen.2 present p.challenge _ client fresh,
    PqxdhDeploymentIdealLaterPool.stopped_programL setup t.kem.val (p.pool t) client qCreate bounded noReveal joint pool
      prefixed room]
  simp only [Functor.map_map]
  rfl

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- The upper layers on an identity field read: the identity-pool reveal of the encoded owner's identity slot, sent to the exposed encapsulation interface, with the upper state kept; an absent owner reads nothing. -/
theorem upperLayer_identity (address : ℕ)
    (state : List EncodedEntry × SkelState KemSK Output) :
    (upperLayer setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks) (.inr (address, .identity))).run state =
      match state.1[address]? with
      | none => pure (none, state)
      | some entry => (fun value => (value, state)) <$>
          simulateQ poolUp (PqxdhRegistrationJointLiveRead.entryClient (KemSK := KemSK) .identity entry) := by
  rcases state with ⟨owners, skel⟩
  simp only [upperLayer, QueryImpl.flattenStateT, QueryImpl.mapStateTBase, StateT.run_mk,
    PqxdhRegistrationJointKemPostSkeleton.groupedClient, PqxdhRegistrationJointRevealSchedule.client]
  change (fun x => (x.1.1, x.1.2, x.2)) <$> StateT.run (simulateQ _
    (simulateQ PqxdhRegistrationJointKemPostSkeleton.groupedLift
      (PqxdhRegistrationJointLiveRead.clientStep (Response := Response) (address, .identity) owners))) skel = _
  rcases found : owners[address]? with _ | entry
  · simp [PqxdhRegistrationJointLiveRead.clientStep, found]
  · simp only [PqxdhRegistrationJointLiveRead.clientStep, found, simulateQ_map, StateT.run_map,
      PqxdhDeploymentIdealPostRequests.skel_pool, Functor.map_map]
    rfl

/-- An identity field read at a middle state with item 2's ownership of the annotated state and a prefix KEM pool: item 2's layers reveal the owner's identity slot through the post-challenge router, which holds the owner's identity seed, as the middle source handler's annotated read does (`PqxdhRegistrationJointLiveRead.entry_source`). -/
theorem step_identity (address : ℕ) (m : Mid KemSK)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex m.joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAt setup codec route checks t p created (.inr (address, .identity)) m := by
  unfold StepAt
  rw [PqxdhDeploymentIdealPostSteps.upperE_run setup codec checks t p created _ _
      (PqxdhDeploymentIdealPostSteps.encodeMid_clean setup m), upperLayer_identity]
  change _ = _ <$> ((fun r => (r.1, ({ m with joint := r.2, backend := m.backend } : Mid KemSK))) <$>
    (pure (PqxdhRegistrationJointLiveRead.sourceStep (address, .identity) m.joint) : ProbComp _))
  rw [map_pure, map_pure]
  have encoded : (encodeMid setup m).1.1[address]? =
      (m.joint.owners[address]?).map (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup) := by
    simp [encodeMid, PqxdhRegistrationJointGeneratedFinish.encodeState, List.getElem?_map]
  rw [encoded]
  rcases found : m.joint.owners[address]? with _ | entry
  · simp only [Option.map_none, map_pure, simulateQ_pure, OptionT.run_pure, StateT.run_pure,
      PqxdhRegistrationJointLiveRead.sourceStep, found]
    rfl
  · simp only [Option.map_some, PqxdhRegistrationJointLiveRead.sourceStep, found]
    have single : ∀ (q : (PqxdhLiveKemBirth.Spec KemSK).Domain → Prop) [DecidablePred q],
        ¬ q (.inl (.inr (.reveal (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry).2.2.beacon.identity.1))) →
        (PqxdhRegistrationJointLiveRead.entryClient (KemSK := KemSK) .identity
          (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry)).IsQueryBoundP q 0 := by
      intro q _ outside
      exact (isQueryBoundP_map_iff _ _ _).mpr ((isQueryBoundP_query_iff _ _ _).mpr fun inside => absurd inside outside)
    have noCreate := single (PqxdhLiveKemReservation.IsCreate (KemSK := KemSK))
      (by simp [PqxdhLiveKemReservation.IsCreate])
    have entryOwned : PqxdhRegistrationJointOwnership.Owned m.joint.pool entry :=
      owned.1.1 entry (List.mem_of_getElem? found)
    have lowered := lowerE_poolL setup t p (PqxdhRegistrationJointLiveRead.entryClient (KemSK := KemSK) .identity
      (PqxdhRegistrationJointGeneratedFinish.encodeEntry setup entry)) 0 noCreate
      (single _ (by simp [PqxdhDeploymentIdealLaterPool.kemReveal]))
      (single _ (by simp [challengeDecaps])) m.joint.pool.1 m.joint.pool.2 prefixed (by
        have length := congrArg List.length prefixed
        rw [List.length_take] at length
        omega) (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))
    rw [PqxdhDeploymentIdealPool.simulateQ_congr_none (PqxdhDeploymentIdealPoolSource.reservedAt setup (p.pool t))
      (PqxdhLiveKemBirth.impl setup.baseImpl setup.joint setup.kem) _
      (PqxdhDeploymentIdealPoolSource.reserved_agree setup (p.pool t)) _ noCreate, Prod.mk.eta,
      PqxdhRegistrationJointLiveRead.entry_source setup .identity entry m.joint.pool entryOwned, map_pure] at lowered
    simp only [simulateQ_map, OptionT.run_map, StateT.run_map]
    rw [show (encodeMid setup m).2 = (PqxdhRegistrationJointKemObserverFree.eraseJoint
        (m.joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf m.joint.pool.2),
        (m.joint.shared.1.cache, (m.backend.2.1, m.backend.1))) from rfl, lowered]
    simp only [map_pure]
    rfl

/-- An identity field read at the logged view without table counters (`step_identity`). -/
theorem step_identityCL (address : ℕ) (m : Mid KemSK) (log : Log)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex m.joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) m.joint.pool.2) :
    StepAtCL setup codec route checks t p created (.inl (.inr (address, .identity))) (m, log) :=
  stepAtCL_of_stepAtC setup codec route checks t p created _ (fun _ same => by cases same) m log
    (PqxdhDeploymentIdealPostHidden.stepAtC_of_stepAt setup codec route checks t p created _ m
      (step_identity setup codec route checks t p created address m owned prefixed))

end Identity

/-! ### Item 2's invariant and the simulation of the logged middle run -/

section Invariant
open PqxdhDeploymentIdealPostInvariant (Allowed Costly room ItemInv)
open PqxdhRegistrationJointRevealCosts (sourceKind)

/-- The logged source requests that item 2's side simulates: every request but a KEM field read (identity field reads and the Server read included). -/
def AllowedL : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop
  | .inl query => sourceKind (KemSK := KemSK) query ≠ .inr 1
  | .inr _ => True

/-- Deciding the simulated logged requests. -/
instance : DecidablePred (AllowedL (KemSK := KemSK)) := fun query => by
  rcases query with query | read
  · unfold AllowedL
    infer_instance
  · unfold AllowedL
    infer_instance

/-- The costly logged requests: the creations. -/
def CostlyL : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain → Prop
  | .inl query => Costly (KemSK := KemSK) query
  | .inr _ => False

/-- Deciding the costly logged requests. -/
instance : DecidablePred (CostlyL (KemSK := KemSK)) := fun query => by
  rcases query with query | read
  · unfold CostlyL
    infer_instance
  · unfold CostlyL
    infer_instance

/-- The room for creations at a logged middle state: CE-11b's room of the middle state. -/
def roomL {count : ℕ} (t : Target count) (p : Params KemSK count) (s : MidL KemSK) : ℕ :=
  room t p s.1

/-- Item 2's invariant at a logged middle state: CE-11b's `ItemInv` of the middle state (the log is free). -/
def ItemInvL {count : ℕ} (created : PqxdhLiveServerConstruction.Created Unit) (t : Target count)
    (p : Params KemSK count) (s : MidL KemSK) : Prop :=
  ItemInv created t p s.1

variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)
  (created : PqxdhLiveServerConstruction.Created Unit)

/-- Every simulated logged request at a logged middle state with item 2's invariant, with room for a creation: item 2's logged layers answer it from item 2's logged view without table counters as the logged middle source handler does. A raw accept by `step_acceptCL`, an identity field read by `step_identityCL`, the Server read by `step_serverRead`, every other source14 request by CE-11b's `PqxdhDeploymentIdealPostInvariant.step_all` with the log kept. -/
theorem step_allL (identity : created.publicIdentity = setup.joint.publicKeys created.seed)
    (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (s : MidL KemSK) (inv : ItemInvL created t p s)
    (allowed : AllowedL query) (fits : CostlyL query → 0 < roomL t p s) :
    StepAtCL setup codec route checks t p created query s := by
  obtain ⟨m, log⟩ := s
  rcases query with query | read
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      exact step_acceptCL setup codec route checks t p created raw m log inv.owned.1.2 identity inv.prefixed
    · have other : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => accept ⟨raw, same⟩
      by_cases identityRead : ∃ address, query = .inr (address, .identity)
      · obtain ⟨address, rfl⟩ := identityRead
        exact step_identityCL setup codec route checks t p created address m log inv.owned inv.prefixed
      · have notIdentity : sourceKind (KemSK := KemSK) query ≠ .inr 0 := by
          rcases query with (coin | request) | ⟨address, field⟩
          · simp [sourceKind]
          · simp [sourceKind]
          · cases field
            · exact absurd ⟨address, rfl⟩ identityRead
            all_goals simp [sourceKind, PqxdhRegistrationJointRevealCosts.fieldIndex]
        exact stepAtCL_of_stepAtC setup codec route checks t p created query other m log
          (PqxdhDeploymentIdealPostInvariant.step_all setup codec route checks t p created identity query m inv
            ⟨notIdentity, allowed⟩ fits)
  · exact step_serverRead setup codec route checks t p created m log

/-- Every simulated logged middle step keeps item 2's invariant, with one unit of room used exactly by a creation: a raw accept (never the selected one) and every other source14 request by CE-11b's `PqxdhDeploymentIdealPostInvariant.keep_all`, the Server read changes only the identity pool's transcript. -/
theorem keep_allL (query : (PqxdhDeploymentLaterServerSource.Spec KemSK).Domain) (s : MidL KemSK)
    (inv : ItemInvL created t p s) (fits : CostlyL query → 0 < roomL t p s)
    (result : (PqxdhDeploymentLaterServerSource.Spec KemSK).Range query × MidL KemSK)
    (member : result ∈ support ((sourceMidL setup codec route checks t p created query).run s)) :
    ItemInvL created t p result.2 ∧ roomL t p s ≤ roomL t p result.2 + (if CostlyL query then 1 else 0) := by
  obtain ⟨m, log⟩ := s
  rcases query with query | read
  · by_cases accept : ∃ raw, query = .inl (.inr (.accept raw))
    · obtain ⟨raw, rfl⟩ := accept
      have real : (sourceMid setup codec route checks t p created (.inl (.inr (.accept raw)))).run m =
          (realMid setup codec checks t p created (.inl (.inr (.accept raw)))).run m := by
        change (if m.backend.2.2.accepts = t.accept then _ else _) = _
        exact ite_eq_right_of_eq_false _ _ (eq_false (Nat.ne_of_gt inv.done))
      have projected : (result.1, result.2.1) ∈ support
          ((sourceMid setup codec route checks t p created (.inl (.inr (.accept raw)))).run m) := by
        rw [real]
        change _ ∈ support ((fun r => (r.1, (⟨r.2, bumpSource (KemSK := KemSK) (.inl (.inr (.accept raw))) m.backend,
          m.seeds⟩ : Mid KemSK))) <$>
            (PqxdhRegistrationJointServerSchedule.source setup codec checks created.seed
              created.server.server.metadata.identityIndex (.inl (.inr (.accept raw)))).run m.joint)
        rw [← PqxdhDeploymentLaterServerSource.query_projection setup codec checks created.seed
          created.server.server.metadata.identityIndex (.inl (.inr (.accept raw))) m.joint log, Functor.map_map,
          support_map]
        change result ∈ support (_ <$> _) at member
        rw [support_map] at member
        obtain ⟨r, rMember, rfl⟩ := member
        exact ⟨r, rMember, rfl⟩
      exact PqxdhDeploymentIdealPostInvariant.keep_all setup codec route checks t p created _ m inv fits _ projected
    · have other : ∀ raw, query ≠ .inl (.inr (.accept raw)) := fun raw same => accept ⟨raw, same⟩
      rw [sourceMidL_inl setup codec route checks t p created query other m log, support_map] at member
      obtain ⟨inner, innerMember, rfl⟩ := member
      exact PqxdhDeploymentIdealPostInvariant.keep_all setup codec route checks t p created query m inv fits inner
        innerMember
  · rw [PqxdhDeploymentIdealLaterMid.serverRead_mid, support_pure] at member
    subst member
    refine ⟨⟨⟨⟨fun entry mem => PqxdhRegistrationJointOwnership.owned_slots _ _ entry rfl rfl (inv.owned.1.1 entry mem),
      inv.owned.1.2⟩, inv.owned.2⟩, inv.prefixed, inv.indexed, inv.active, inv.done, inv.good, inv.stored⟩, ?_⟩
    simp [roomL, room, CostlyL]

/-- Item 2's logged layers on a logged program with only simulated requests and at most the room's number of creations, from item 2's logged view without table counters of a logged middle state with item 2's invariant, run without stopping as the projection of the program's logged middle run (`PqxdhDeploymentIdealPostSim.sim_option` with `step_allL` and `keep_allL`). It needs the constructed Server's public identity to be its seed's. -/
theorem item_simL (identity : created.publicIdentity = setup.joint.publicKeys created.seed) {α : Type}
    (work : OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) α)
    (onlyAllowed : work.IsQueryBoundP (fun query => ¬ AllowedL (KemSK := KemSK) query) 0) (budget : ℕ)
    (bounded : work.IsQueryBoundP (CostlyL (KemSK := KemSK)) budget) (s : MidL KemSK) (fits : budget ≤ roomL t p s)
    (holds : ItemInvL created t p s) :
    ((simulateQ (lowerEC setup t p) ((simulateQ (upperEL setup codec checks t p created) work).run
        (encodeMidCL setup s).1)).run).run (encodeMidCL setup s).2 =
      (fun result => (some (result.1, (encodeMidCL setup result.2).1), (encodeMidCL setup result.2).2)) <$>
        (simulateQ (sourceMidL setup codec route checks t p created) work).run s :=
  PqxdhDeploymentIdealPostSim.sim_option (upperEL setup codec checks t p created) (lowerEC setup t p)
    (sourceMidL setup codec route checks t p created) (encodeMidCL setup) (ItemInvL created t p) AllowedL CostlyL
    (roomL t p)
    (fun query state holds allowed fits => step_allL setup codec route checks t p created identity query state holds
      allowed fits)
    (fun query state holds _ fits => keep_allL setup codec route checks t p created query state holds fits)
    work onlyAllowed budget bounded s fits holds

end Invariant

/-! ### Item 2's logged post-challenge phase with both erasures -/

section Skeleton
open PqxdhDeploymentIdealPostItem (GhostFree ghostFree_bind ghostFree_pure ghostFree_liftT ghostFree_acceptTail)
open PqxdhRegistrationJointKemPostSkeleton (skelDecide)
variable {V : Type} (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (checks : Checks)

/-- The logged raw accept of the skeleton (`PqxdhDeploymentLaterServerItemTargets.acceptStepL`) never reads the analysis observers of its game state. -/
theorem ghostFree_acceptStepL (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (raw : Pqxdh.Bytes) :
    GhostFree (PqxdhDeploymentLaterServerItemTargets.acceptStepL (V := V) setup codec checks identityIndex
      publicIdentity raw) := by
  unfold PqxdhDeploymentLaterServerItemTargets.acceptStepL
  refine ghostFree_bind _ _ (fun state => rfl) fun before => ghostFree_bind _ _ (fun state => ?_) fun collected =>
    ghostFree_bind _ _ (ghostFree_liftT _ (ghostFree_acceptTail setup _ _ _)) fun reply => ghostFree_pure _
  simp only [StateT.run, Functor.map_map]
  rfl

/-- The logged skeleton never reads the analysis observers of its game state. -/
theorem skelImplL_ghostFree (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) (query : (GSpecL KemSK Response).Domain) :
    GhostFree (skelImplL setup codec checks identityIndex publicIdentity services query) := by
  rcases query with query | raw
  · exact PqxdhDeploymentIdealPostItem.skelImpl_ghostFree setup codec checks identityIndex publicIdentity services query
  · exact ghostFree_acceptStepL setup codec checks identityIndex publicIdentity raw

/-- Item 2's logged upper layers never read the analysis observers of the skeleton's game state. -/
theorem upperLayerL_neverRead (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    PqxdhRegistrationJointKemObserverFree.NeverRead cleanUpperL
      (upperLayerL setup codec checks identityIndex publicIdentity selected challenge services) := by
  intro query state
  have erased : ∀ sk : SkelState KemSK V, Prod.map id cleanSkel <$>
      (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run sk =
      (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanSkel
        (skelImplL setup codec checks identityIndex publicIdentity services))
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run (cleanSkel sk) :=
    fun sk => PqxdhRegistrationJointKemObserverFree.run_erase cleanSkel PqxdhDeploymentIdealPostItem.cleanSkel_idem _
      (fun query state => skelImplL_ghostFree setup codec checks identityIndex publicIdentity services query state) _ sk
  have left := erased state.2
  have right := erased (cleanSkel state.2)
  rw [PqxdhDeploymentIdealPostItem.cleanSkel_idem] at right
  change Prod.map id cleanUpperL <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run state.2) =
    Prod.map id cleanUpperL <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run (cleanSkel state.2))
  have mapped : ∀ sk : SkelState KemSK V, Prod.map id cleanUpperL <$> ((fun r => (r.1.1, (r.1.2, r.2))) <$>
      (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run sk) =
      (fun r => (r.1.1, (r.1.2, r.2))) <$> (Prod.map id cleanSkel <$>
      (simulateQ (skelImplL setup codec checks identityIndex publicIdentity services)
        ((groupedClientL setup codec selected challenge identityIndex query).run state.1)).run sk) := by
    intro sk
    simp only [Functor.map_map]
    rfl
  rw [mapped, mapped, left, right]

/-- The logged skeleton's resumed client: the Server's private resumption on the native layer, then the tagged logged client through `upperLayerL` from the encoded owners with the log at the cut extended by the selected accept's ephemeral, and the skeleton state after the resumption. -/
theorem skelResumeL_upper {X R : Type} (identityIndex : ℕ) (publicIdentity : PqxdhJointIdentity.PublicIdentity)
    (observe : X × PqxdhRegistrationJointAcceptCutTag.Tag → R) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (game : PqxdhServerAuthExperiment.GameState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK) X) (selected : ℕ)
    (challenge : MlKem768Ciphertext) (services : PqxdhRegistrationJointKemPostSkeleton.Services V Response) :
    PqxdhDeploymentLaterServerItemTargets.skelResumeL setup codec checks identityIndex publicIdentity observe raw value
        ephemeral consumed game owners log next selected challenge services =
      (simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac game.sessions services)
          (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks identityIndex publicIdentity raw value ephemeral
            (PqxdhAcceptedRegistration.ciphertextArray challenge) .challenge game consumed)).run (game, none) >>=
        fun answer => (fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (upperLayerL setup codec checks identityIndex publicIdentity selected challenge services)
            (PqxdhDeploymentLaterServerCut.tagged observe raw next answer.1)).run
              ((owners, log ++ [some ephemeral.secret]), answer.2) := by
  unfold PqxdhDeploymentLaterServerItemTargets.skelResumeL upperLayerL
  refine bind_congr fun answer => ?_
  rw [OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]

variable {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- Item 2's logged post-challenge phase (`PqxdhDeploymentIdealLaterBranch.itemPostL`) on a pending prechallenge context whose verified PQ key is the selected one is the logged skeleton's resumed client run through the one optional service layer, from the erased router state of the context, the context's table cache and the empty slot state, followed by the skeleton's decision (`PqxdhDeploymentIdealPostSim.itemPost_active` for the logged skeleton). -/
theorem itemPostL_active {A Out : Type}
    (decision : Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local)) → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local))))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealLaterBranch.itemPostL (Reader := Reader) setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners log next)) state after) =
      skelDecide <$> ((simulateQ (serviceLayer setup t.kem p.chosen others p.challenge)
        (PqxdhDeploymentLaterServerItemTargets.skelResumeL setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed
          native.2 owners log next t.kem.val p.challenge (factoredServices setup codec checks))).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
          (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  have table : ∀ {β : Type} (work : OracleComp (SkelSpec Output) β) (cache : PqxdhSecretInputKdf.HmacOracle.QueryCache)
      (slots : SlotState),
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl (D := PqxdhCorrelatedExtractFamily.Message)
        (PqxdhRegistrationJointKemSecondEntry.tableService (n := 2)))
          ((simulateQ (PqxdhRegistrationJointKemEntryFactor.publicLocalV Output) work).run' cache)).run' slots =
        (simulateQ tableLayer work).run' (cache, slots) := by
    intro β work cache slots
    simp only [StateT.run'_eq, simulateQ_map, StateT.run_map,
      OracleComp.simulateQ_mapStateTBase_run_eq_map_flattenStateT]
    simp only [Functor.map_map]
    rfl
  unfold PqxdhDeploymentIdealLaterBranch.itemPostL
  simp only [PqxdhDeploymentLaterServerItemTargets.postSkelL, matched, ↓reduceIte,
    PqxdhDeploymentLaterServerItemTargets.cacheOfL]
  rw [table, simulateQ_map, StateT.run'_eq, StateT.run_map, ← QueryImpl.simulateQ_compose,
    ← QueryImpl.simulateQ_compose (fwdOption (T := TSpec Output) _), PqxdhDeploymentIdealPostSim.optionLower_run]
  simp only [Functor.map_map]
  rfl

/-- Item 2's logged post-challenge phase on an active context, with the router transcripts erased after every step (`PqxdhDeploymentIdealPostSim.itemPost_erased` for the logged skeleton). -/
theorem itemPostL_erased {A Out : Type}
    (decision : Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local)) → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local))))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealLaterBranch.itemPostL (Reader := Reader) setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners log next)) state after) =
      skelDecide <$> ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl eraseService
          (serviceLayer setup t.kem p.chosen others p.challenge))
        (PqxdhDeploymentLaterServerItemTargets.skelResumeL setup codec checks created.server.server.metadata.identityIndex
          created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed
          native.2 owners log next t.kem.val p.challenge (factoredServices setup codec checks))).run).run
        (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
          (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [itemPostL_active setup codec checks t p decision created others raw value matched ephemeral consumed native owners
    log next state after]
  have erased := PqxdhRegistrationJointKemObserverFree.run_eraseOption eraseService
    (fun state => by simp only [eraseService, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem, id_eq])
    (serviceLayer setup t.kem p.chosen others p.challenge)
    (PqxdhDeploymentIdealPostSim.serviceLayer_neverRead setup t.kem p.chosen others p.challenge)
    (PqxdhDeploymentLaterServerItemTargets.skelResumeL setup codec checks created.server.server.metadata.identityIndex
      created.publicIdentity (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw value ephemeral consumed
      native.2 owners log next t.kem.val p.challenge (factoredServices setup codec checks))
    (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)))
  have same : eraseService (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
      (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) =
      (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
        (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := rfl
  rw [same] at erased
  rw [← erased, Functor.map_map]
  rfl

/-- Item 2's logged post-challenge phase on an active context: the Server's private resumption, then the tagged logged client through the upper layers that erase the analysis observers of the skeleton's game state, from the encoded owners with the log at the cut extended by the selected accept's ephemeral and the skeleton state of the resumption with those observers erased, all through the service layers that erase the router transcripts, followed by the skeleton's decision (`PqxdhDeploymentIdealPostItem.itemPost_clean` for the logged skeleton). -/
theorem itemPostL_clean {A Out : Type}
    (decision : Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local)) → Bool)
    (created : PqxdhRegistrationJointServerBirth.ClientCreated Unit) (others : Fin count → MlKem768PublicKey × KemSK)
    (raw : Pqxdh.Bytes) (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (native : PqxdhServerAuthNative.NativeState KemSK) (owners : List EncodedEntry) (log : Log)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local))))
    (state : PqxdhDynamicKemJointSource.State KemSK) (after : A) :
    PqxdhDeploymentIdealLaterBranch.itemPostL (Reader := Reader) setup codec checks t p decision
        (.ready created others (some (.pending raw value ephemeral consumed native owners log next)) state after) =
      skelDecide <$>
        ((simulateQ (PqxdhRegistrationJointKemObserverFree.eraseOptionImpl eraseService
          (serviceLayer setup t.kem p.chosen others p.challenge))
          ((simulateQ (PqxdhRegistrationJointKemPostSkeleton.resumeImpl setup.hmac native.2.sessions
              (factoredServices setup codec checks))
            (PqxdhRegistrationJointKemOpaqueResume.resume setup codec checks created.server.server.metadata.identityIndex
              created.publicIdentity raw value ephemeral (PqxdhAcceptedRegistration.ciphertextArray p.challenge)
              .challenge native.2 consumed)).run (native.2, none) >>= fun answer =>
            (fun result => ((result.1, result.2.1), result.2.2)) <$>
              (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpperL
                (upperLayerL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
                  t.kem.val p.challenge (factoredServices setup codec checks)))
                (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
                  answer.1)).run ((owners, log ++ [some ephemeral.secret]), cleanSkel answer.2))).run).run
          (PqxdhRegistrationJointKemObserverFree.eraseJoint state,
            (native.1.cache, (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) := by
  rw [itemPostL_erased setup codec checks t p decision created others raw value matched ephemeral consumed native owners
    log next state after, skelResumeL_upper]
  have inner : ∀ answer : Option ℕ × SkelState KemSK Output,
      (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (PqxdhRegistrationJointKemObserverFree.eraseImpl cleanUpperL
          (upperLayerL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
            p.challenge (factoredServices setup codec checks)))
          (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            answer.1)).run ((owners, log ++ [some ephemeral.secret]), cleanSkel answer.2) =
      (fun result : (Bool × (List EncodedEntry × Log)) × SkelState KemSK Output => (result.1, cleanSkel result.2)) <$>
        ((fun result => ((result.1, result.2.1), result.2.2)) <$>
          (simulateQ (upperLayerL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity
            t.kem.val p.challenge (factoredServices setup codec checks))
            (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
              answer.1)).run ((owners, log ++ [some ephemeral.secret]), answer.2)) := by
    intro answer
    have erased := PqxdhRegistrationJointKemObserverFree.run_erase cleanUpperL (fun _ => rfl)
      (upperLayerL setup codec checks created.server.server.metadata.identityIndex created.publicIdentity t.kem.val
        p.challenge (factoredServices setup codec checks))
      (upperLayerL_neverRead setup codec checks _ _ _ _ _)
      (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next answer.1)
      ((owners, log ++ [some ephemeral.secret]), answer.2)
    change _ = _ <$> (_ <$> _)
    rw [show ((owners, log ++ [some ephemeral.secret]), cleanSkel answer.2) =
      cleanUpperL ((owners, log ++ [some ephemeral.secret]), answer.2) from rfl, ← erased]
    simp only [Functor.map_map]
    rfl
  simp only [inner, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind, map_bind]
  refine bind_congr fun reached => ?_
  rcases reached with ⟨_ | answer, after⟩
  · rfl
  · simp only [Option.elim, simulateQ_map, OptionT.run_map, StateT.run_map, Functor.map_map]
    refine congrArg (fun f => f <$> _) (funext fun reached => ?_)
    rcases reached with ⟨_ | result, after⟩ <;> rfl

end Skeleton

/-! ### Item 2's logged post-challenge phase as the logged middle run -/

section Item
open PqxdhDeploymentIdealPostItemRun (afterSelected)
open PqxdhDeploymentIdealPostAccept (marksOf)
variable (setup : Setup baseSpec KemSK) (codec : Codec Reader Response) (route : RawCtxServerRouting.SenderDecoder)
  (checks : Checks) {count : ℕ} (t : Target count) (p : Params KemSK count)

/-- Item 2's logged post-challenge phase on an active cut (a pending logged context whose verified PQ key is the selected one) is the logged middle run: the ideal registration's steps after encapsulation through the allocator from the empty allocator and table, then the tagged logged continuation under the logged middle source handler from the middle state after the selected accept (CE-11b's `PqxdhDeploymentIdealPostItemRun.afterSelected`) with the log at the cut extended by the selected accept's ephemeral, read off as its output (`PqxdhDeploymentIdealPostItemRun.itemPost_middle` over the logged source, with `item_simL`). It needs item 2's facts at the pool at the cut, the constructed Server's public identity, and a continuation with only simulated logged requests and at most the room's number of creations. -/
theorem itemPost_middleL {A Out : Type}
    (decision : Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local)) → Bool)
    (created : PqxdhLiveServerConstruction.Created Unit)
    (identity : created.publicIdentity = setup.joint.publicKeys created.seed) (raw : Pqxdh.Bytes)
    (value : PqxdhServerRootPreparation.Verified Reader) (matched : value.keys.pqKey = p.chosen.1)
    (ephemeral : PqxdhServerRootPreparation.Ephemeral PqxdhJointGapDh.ScalarBytes) (consumed : List Pqxdh.Bytes)
    (logged : Option PqxdhJointGapDh.ScalarBytes) (joint : PqxdhRegistrationJointSchedule.State KemSK) (log : Log)
    (owned : PqxdhDeploymentIdealPoolSource.PoolOwned created.seed created.server.server.metadata.identityIndex joint)
    (prefixed : PqxdhDeploymentIdealPoolSource.PoolPrefix (p.pool t) joint.pool.2)
    (indexed : PqxdhDeploymentIdealCut.PoolIndexed joint)
    (next : Option ℕ → OracleComp (PqxdhDeploymentLaterServerSource.Spec KemSK)
      (Out × (PqxdhDeploymentSecrecy.Ledger × (PqxdhDeploymentLater.Snap × PqxdhDeploymentCompile.Local))))
    (onlyAllowed : ∀ answer, (next answer).IsQueryBoundP (fun query => ¬ AllowedL (KemSK := KemSK) query) 0)
    (budget : ℕ) (bounded : ∀ answer, (next answer).IsQueryBoundP (CostlyL (KemSK := KemSK)) budget)
    (fits : budget ≤ (p.pool t).length - joint.pool.2.keys.length) (after : A) :
    PqxdhDeploymentIdealLaterBranch.itemPostL (Reader := Reader) setup codec checks t p decision
        (.ready (PqxdhRegistrationJointServerBirth.encode created) p.others
          (some (.pending raw value ephemeral consumed joint.shared
            (PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners log next))
          (joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2) after) =
      (simulateQ (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService)
          ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value ephemeral consumed
            logged).run joint.shared)).run
          (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial) >>= fun w =>
        (fun result => result.1) <$> (simulateQ (sourceMidL setup codec route checks t p created)
          (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            w.1.1.1.1)).run (afterSelected t joint w, log ++ [some ephemeral.secret]) := by
  rw [itemPostL_clean setup codec checks t p decision _ p.others raw value matched ephemeral consumed joint.shared _ log
    next _ after]
  have counts : (PqxdhRegistrationJointKemObserverFree.eraseJoint (joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial))) =
      PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2),
        (joint.shared.1.cache, ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState)))) :=
    rfl
  rw [counts]
  have toC : ∀ work : OracleComp (Enc KemSK + TSpec Output) ((Bool × (List EncodedEntry × Log)) ×
        SkelState KemSK Output),
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (PqxdhDeploymentIdealPostSteps.lowerE setup t p)
        work).run).run (PqxdhDeploymentIdealPostSim.eraseService ((joint.pool.1,
          PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
            ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
              PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) =
      PqxdhRegistrationJointKemPostSkeleton.skelDecide <$> ((simulateQ (lowerEC setup t p) work).run).run
        (PqxdhDeploymentIdealPostHidden.eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2),
          (joint.shared.1.cache, ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc :
            PqxdhRegistrationJointKemSecondEntry.Alloc PqxdhCorrelatedExtractFamily.Message 2),
            (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))) := by
    intro work
    rw [PqxdhDeploymentIdealPostFinish.lowerEC_run, Functor.map_map]
    rfl
  rw [toC]
  refine Eq.trans (congrArg (fun work => PqxdhRegistrationJointKemPostSkeleton.skelDecide <$>
    ((simulateQ (lowerEC setup t p) work).run).run (PqxdhDeploymentIdealPostHidden.eraseServiceC ((joint.pool.1,
      PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2), (joint.shared.1.cache,
        ((PqxdhRegistrationJointKemSecondEntry.emptyAlloc : PqxdhRegistrationJointKemSecondEntry.Alloc
          PqxdhCorrelatedExtractFamily.Message 2), (PqxdhRecordLiftLazyTable.initial : PqxdhDeploymentIdealSteps.TableState))))))
    (PqxdhDeploymentIdealPostItemRun.bind_clean _ _ (PqxdhDeploymentIdealPostAccept.resume_clean setup codec checks
      (factoredServices setup codec checks)
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex
      (PqxdhRegistrationJointServerBirth.encode created).publicIdentity raw value ephemeral
      (PqxdhAcceptedRegistration.ciphertextArray p.challenge) joint.shared.2 consumed none)
      (fun answer skel => (fun result => ((result.1, result.2.1), result.2.2)) <$>
        (simulateQ (upperEL setup codec checks t p created)
          (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next
            answer)).run (((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners,
              log ++ [some ephemeral.secret]), skel)))) ?_
  rw [show (PqxdhRegistrationJointServerBirth.encode created).publicIdentity = setup.joint.publicKeys created.seed
      from identity, simulateQ_bind, OptionT.run_bind, Option.elimM, StateT.run_bind,
    PqxdhDeploymentIdealPostAccept.resume_accept setup codec checks t p created.seed
      (PqxdhRegistrationJointServerBirth.encode created).server.server.metadata.identityIndex raw value ephemeral consumed
      logged joint.shared joint.pool.1 joint.pool.2 prefixed owned.1.2 _
      PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide),
    bind_map_left, map_bind]
  refine bind_congr_of_forall_mem_support _ fun w member => ?_
  have produced : w.1 ∈ support ((PqxdhDeploymentIdealActive.acceptAfter setup codec checks created.seed p.challenge value
      ephemeral consumed logged).run joint.shared) := by
    apply OracleComp.support_simulateQ_run'_subset
      (PqxdhRegistrationJointKemSecondEntry.slotImpl PqxdhDeploymentSeedSplit.tableService) _
      (PqxdhRegistrationJointKemSecondEntry.emptyAlloc, PqxdhRecordLiftLazyTable.initial)
    rw [StateT.run'_eq, support_map]
    exact ⟨w, member, rfl⟩
  have active := (PqxdhDeploymentIdealPostMark.acceptAfter_mark setup codec checks created.seed p.challenge value ephemeral
    consumed logged joint.shared w.1 produced).1
  obtain ⟨good, stored⟩ := PqxdhDeploymentIdealPostItemRun.acceptAfter_keeps setup codec checks p created.seed value
    ephemeral consumed logged joint.shared _ PqxdhRegistrationJointKemSecondEntry.slotGood_empty (by decide) w member
  have holds := PqxdhDeploymentIdealPostItemRun.itemInv_after t p created joint owned prefixed indexed w active good stored
  have encodeAfter : encodeMidCL setup (afterSelected t joint w, log ++ [some ephemeral.secret]) =
      ((((PqxdhRegistrationJointGeneratedFinish.encodeState setup joint).owners, log ++ [some ephemeral.secret]),
        (clean w.1.2.2, marksOf w.1.1.2.2 w.2)),
        PqxdhDeploymentIdealPostHidden.eraseServiceC ((joint.pool.1, PqxdhDeploymentIdealPoolSource.routerOf joint.pool.2),
          (w.1.2.1.cache, w.2))) := by
    simp only [encodeMidCL, encodeMidC, PqxdhDeploymentIdealPostSteps.encodeMid,
      PqxdhDeploymentIdealPostHidden.eraseServiceC, Prod.map, PqxdhRegistrationJointKemObserverFree.eraseJoint_idem]
    rfl
  have sim := item_simL setup codec route checks t p created identity
    (PqxdhDeploymentLaterServerCut.tagged (PqxdhRegistrationJointAcceptCutTag.decideTag decision) raw next w.1.1.1.1)
    (by unfold PqxdhDeploymentLaterServerCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (onlyAllowed _))
    budget
    (by unfold PqxdhDeploymentLaterServerCut.tagged; exact (OracleComp.isQueryBoundP_map_iff _ _ _).mpr (bounded _))
    (afterSelected t joint w, log ++ [some ephemeral.secret]) fits holds
  rw [encodeAfter] at sim
  simp only [Option.elim_some, simulateQ_map, OptionT.run_map, StateT.run_map]
  rw [show cleanSkel (clean w.1.2.2, marksOf w.1.1.2.2 w.2) = (clean w.1.2.2, marksOf w.1.1.2.2 w.2) from rfl, sim,
    Functor.map_map, Functor.map_map]
  rfl

end Item

/-! ### Reachability of a budget-indexed invariant -/

/-- A stateful handler whose every allowed step keeps an invariant and uses one unit of room exactly on a costly request keeps the invariant on every reached state of a program with only allowed requests and at most the room's number of costly requests (the support form of `PqxdhDeploymentIdealPostSim.sim_option`'s preservation obligation). -/
theorem simulate_keeps {ι' S α : Type} {spec : OracleSpec ι'} (middle : QueryImpl spec (StateT S ProbComp))
    (inv : S → Prop) (allowed costly : ι' → Prop) [DecidablePred allowed] [DecidablePred costly] (room : S → ℕ)
    (keep : ∀ query state, inv state → allowed query → (costly query → 0 < room state) →
      ∀ result ∈ support ((middle query).run state), inv result.2 ∧
        room state ≤ room result.2 + (if costly query then 1 else 0))
    (work : OracleComp spec α) (onlyAllowed : work.IsQueryBoundP (fun query => ¬ allowed query) 0) (budget : ℕ)
    (bounded : work.IsQueryBoundP costly budget) (state : S) (fits : budget ≤ room state) (holds : inv state) :
    ∀ result ∈ support ((simulateQ middle work).run state), inv result.2 := by
  induction work using OracleComp.inductionOn generalizing budget state with
  | pure value =>
      intro result member
      simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
      subst member
      exact holds
  | query_bind query next ih =>
      rw [isQueryBoundP_query_bind_iff] at bounded onlyAllowed
      obtain ⟨allowedCost, rest⟩ := bounded
      obtain ⟨first, restOnly⟩ := onlyAllowed
      have isAllowed : allowed query := by
        rcases first with free | impossible
        · exact not_not.mp free
        · omega
      have available : costly query → 0 < room state := by
        intro isCostly
        rcases allowedCost with free | positive
        · exact absurd isCostly free
        · omega
      intro result member
      simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff] at member
      obtain ⟨step, stepMember, member⟩ := member
      obtain ⟨stepInv, stepRoom⟩ := keep query state holds isAllowed available step stepMember
      have nextOnly := restOnly step.1
      simp only [isAllowed, not_true_eq_false, ite_false] at nextOnly
      by_cases isCostly : costly query
      · have nextBound := rest step.1
        simp only [isCostly, ite_true] at nextBound stepRoom
        exact ih step.1 nextOnly (budget - 1) nextBound step.2 (by omega) stepInv result member
      · have nextBound := rest step.1
        simp only [isCostly, ite_false] at nextBound stepRoom
        exact ih step.1 nextOnly budget nextBound step.2 (by omega) stepInv result member

end BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps

-- Axiom guards (generated)

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelImplL_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelImplL_lift

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_inl' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_inl

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.stepAtCL_of_stepAtL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.stepAtCL_of_stepAtL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.stepAtCL_of_stepAtC' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.stepAtCL_of_stepAtC

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_read' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_read

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_serverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_serverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_accept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_accept

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.prefix_chainL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.prefix_chainL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.orderedL_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.orderedL_bound

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.acceptSource_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.acceptSource_run

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_acceptL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_acceptL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_acceptCL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_acceptCL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.lowerE_poolL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.lowerE_poolL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayer_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayer_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_identity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_identity

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_identityCL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_identityCL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_allL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.step_allL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.keep_allL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.keep_allL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.item_simL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.item_simL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.ghostFree_acceptStepL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.ghostFree_acceptStepL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelImplL_ghostFree' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelImplL_ghostFree

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_neverRead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.upperLayerL_neverRead

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelResumeL_upper' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.skelResumeL_upper

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_active' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_active

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_erased' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_erased

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_clean' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPostL_clean

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPost_middleL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.itemPost_middleL

/--
info: 'BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.simulate_keeps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhDeploymentIdealLaterSteps.simulate_keeps
