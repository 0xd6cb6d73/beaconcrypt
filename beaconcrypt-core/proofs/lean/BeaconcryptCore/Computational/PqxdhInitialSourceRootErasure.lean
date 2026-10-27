import BeaconcryptCore.Computational.PqxdhInitialSourceExperiment

/-!
The complete source chain experiment consumes the supplied64-byte initializer response, not its erased earlier root. This is proved for the entire source run and original final publication/freshness event, including all repeated initializer requests and the full private state. The input root remains available only to the separate initializer audit used after the initializer comparison.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure
open PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhCorrelatedExpand PqxdhCorrelatedExtractFamily
open PqxdhInitialBeaconAmbient PqxdhInitialSourceExperiment
variable {ι M P I D K X Response A N : Type} {extra : OracleSpec ι} {S B : Nat}

/-- The source initializer's complete optional kernel and cache effects are independent of its private audit root. -/
theorem initial_root_unused (source : FixedHkdfSha512NoSaltSource) (selectedMessage : Message)
    (left right : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (secrets : PqxdhBeaconPhase2Shared.Secrets PqxdhPhase2DecapsulationRouting.Shared) :
    (Prod.snd <$> PqxdhInitialNativeInitializer.initial (A := A) (N := N) source selectedMessage left response64 secrets) =
      (Prod.snd <$> PqxdhInitialNativeInitializer.initial source selectedMessage right response64 secrets) := by
  funext ambient cache
  change ((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selectedMessage left response64 secrets).run ambient).run cache =
    ((Prod.snd <$> PqxdhInitialNativeInitializer.initial source selectedMessage right response64 secrets).run ambient).run cache
  simp only [StateT.run_map]
  exact (PqxdhInitialNativeInitializer.initial_erase source selectedMessage left response64 secrets ambient cache).trans
    (PqxdhInitialNativeInitializer.initial_erase source selectedMessage right response64 secrets ambient cache).symm

/-- Both actual directional roots come from the same supplied64 response, regardless of the erased input root. -/
theorem root_unused (source : FixedHkdfSha512NoSaltSource) (left right : RootOutput)
    (response64 : PqxdhInitialRootLabelService.Response) (selected : RawCtxProtocolReveals.Owner S B) :
    root source left response64 selected = root source right response64 selected := by
  cases selected with
  | server _ _ => rfl
  | beacon _ =>
    exact congrArg (fun kernel : ConcreteRatchetKernel => RawCtxSelectedQueryTrace.rootVector kernel.refined.send_chain)
      (PqxdhInitialNativeInitializer.kernel_input_unused left right response64)

/-- Every actual future initializer keeps the same optional kernel and all external state after erasing the earlier root. -/
theorem external_root_unused (source : FixedHkdfSha512NoSaltSource) (selectedMessage : Message)
    (left right : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
    (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
      (Ambient A N RootOracle.QueryCache)) :
    PqxdhInitialOriginFinishPath.withInitial source selectedMessage left response64 other =
      PqxdhInitialOriginFinishPath.withInitial source selectedMessage right response64 other := by
  funext query
  rcases query with query | (reply | (secrets | (query | query)))
  · rfl
  · rfl
  · exact initial_root_unused source selectedMessage left right response64 secrets
  · rfl
  · rfl

variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (selectedMessage : Message) (left right : RootOutput) (response64 : PqxdhInitialRootLabelService.Response)
  (other : QueryImpl (PqxdhInitialNativeLog.External extra RatchetChain I D K X Response PqxdhPhase2DecapsulationRouting.Shared)
    (Ambient A N RootOracle.QueryCache))
  (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder) (decode : RawCtxReceive.FrameDecoder)
  (index : Fin S) (metadata : P) (ready : PqxdhPrivateAcceptedRoot.Ready)
  (post : RustM (Option PqxdhServerRegistrationPublication.Response) → OracleComp (PqxdhInitialGenericPost.Spec extra S B) Bool)
  (before : PqxdhInitialOriginPostPath.Front M P I D K S B)
  (selected : RawCtxProtocolReveals.Owner S B)
  (shared : RawCtxSharedPrimitive.SharedState A) (privateState : N) (cache : RootOracle.QueryCache)

/-- The full original adaptive source run is root-erased, retaining all final fields rather than only its final decision. -/
theorem run_root_unused (stage : Nat) :
    run source writer selectedMessage left response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage =
    run source writer selectedMessage right response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage := by
  simp only [run_source, root_unused source left right response64 selected,
    external_root_unused source selectedMessage left right response64 other]

/-- The same original publication and byte-lineage freshness decision is root-erased in every chain stage. -/
theorem game_root_unused (number : Std.U64) (ancestors disclosed : List RatchetChain) (stage : Nat) :
    game source writer selectedMessage left response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache stage =
    game source writer selectedMessage right response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache stage := by
  rw [game, game, root_unused source left right response64 selected,
    run_root_unused source writer selectedMessage left right response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage]

/-- The supplied initializer also removes the Ready root field from the original builder and its complete adaptive continuation. -/
theorem run_ready_root_unused (replacement : RootOutput) (stage : Nat) :
    run source writer selectedMessage left response64 other sender route decode index metadata { ready with root := replacement } post before
      selected shared privateState cache stage =
    run source writer selectedMessage left response64 other sender route decode index metadata ready post before
      selected shared privateState cache stage := rfl

/-- The original source publication and full byte freshness event retain the same decision after erasing the unused Ready root. -/
theorem game_ready_root_unused (replacement : RootOutput) (number : Std.U64) (ancestors disclosed : List RatchetChain) (stage : Nat) :
    game source writer selectedMessage left response64 other sender route decode index metadata { ready with root := replacement } post before
      selected number ancestors disclosed shared privateState cache stage =
    game source writer selectedMessage left response64 other sender route decode index metadata ready post before
      selected number ancestors disclosed shared privateState cache stage := rfl

end BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.initial_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.initial_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.external_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.external_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.run_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.run_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.game_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.game_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.run_ready_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.run_ready_root_unused

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.game_ready_root_unused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialSourceRootErasure.game_ready_root_unused
