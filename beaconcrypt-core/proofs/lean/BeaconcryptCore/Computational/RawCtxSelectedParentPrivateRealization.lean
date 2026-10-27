import BeaconcryptCore.Computational.RawCtxSelectedParentPrivatePatch
import BeaconcryptCore.Computational.RawCtxSelectedParentPrivate

/-!
Private alias-consistent routing realizes the exact patched native table. The common public interface is the real fixed-source function, including at a guessed selected input. The explicit parent-address collision remains a separate event to charge. These equalities preserve the original full pending program and all optional/shared effects; the routing interpreter may know the mathematical target, while the stopped source program does not.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization
open RawCtxSelectedParentCalls RawCtxSelectedParentOwner RawCtxSelectedParentEntry RawCtxSelectedParentTable RawCtxSelectedChain
open RawCtxSelectedParentPrivatePatch
open PqxdhJointKdf PqxdhJointKdfGame PqxdhSecretInputKdf PqxdhFullSecretInputKdf

/-- Private known aliases and hidden requests use the same arbitrary child response; parent retries and every public/read/open/seal effect retain the same original behavior. -/
theorem handler_patch {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (reader : RawCtxSelectedLiveTrace.Reader) (view : RawCtxSelectedParentLive.View)
    (separate : targetAddress target ≠ entry.address) :
    RawCtxSelectedParentLive.handler (Auxiliary := Auxiliary) source writer (privatePatch prior target output) entry output reader view =
      RawCtxSelectedParentPrivate.handler source writer prior entry output reader view target := by
  funext query
  rcases query with ((slot | opening) | ((slot | sealing) | (coins | (hash | viewQuery)))) | read
  · cases slot with
    | hidden =>
      rw [RawCtxSelectedParentPrivate.hidden_receive]
      rfl
    | known chain =>
      rw [RawCtxSelectedParentPrivate.known_receive]
      exact congrArg pure (step_patch prior entry target output separate (.known chain))
  · simp [RawCtxSelectedParentPrivate.handler, RawCtxSelectedAliasCoupling.routed,
      RawCtxSelectedParentPrivate.alternate, RawCtxSelectedParentLive.handler, RawCtxSelectedParentSource.labelReceive]
  · cases slot with
    | hidden =>
      rw [RawCtxSelectedParentPrivate.hidden_send]
      rfl
    | known chain =>
      rw [RawCtxSelectedParentPrivate.known_send]
      exact congrArg pure (step_patch prior entry target output separate (.known chain))
  · simp [RawCtxSelectedParentPrivate.handler, RawCtxSelectedAliasCoupling.routed,
      RawCtxSelectedParentPrivate.alternate, RawCtxSelectedParentLive.handler, RawCtxSelectedParentSource.labelSend]
  · simp [RawCtxSelectedParentPrivate.handler, RawCtxSelectedAliasCoupling.routed,
      RawCtxSelectedParentPrivate.alternate, RawCtxSelectedParentLive.handler]
  · simp [RawCtxSelectedParentPrivate.handler, RawCtxSelectedAliasCoupling.routed,
      RawCtxSelectedParentPrivate.alternate, RawCtxSelectedParentLive.handler]
  · rw [RawCtxSelectedParentPrivate.public_real]
    rfl
  · rw [RawCtxSelectedParentPrivate.read_same]
    rfl

noncomputable def realView (source : FixedHkdfSha512NoSaltSource) : RawCtxSelectedParentLive.View :=
  fun query => query.project (productionStream source.crypto query.address)

/-- The original full pending handler erases only pending payloads, retaining actual source public HKDF at every input. -/
theorem live_real {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (output : FullOutput) (reader : RawCtxSelectedLiveTrace.Reader) :
    RawCtxSelectedParentCompiler.live (Auxiliary := Auxiliary) source writer prior entry (RawCtxKdfRequestTable.fullResponse output) reader =
      RawCtxSelectedParentLive.handler source writer prior entry output reader (realView source) ∘ₛ RawCtxPendingLiveQueries.erase := by
  funext query
  rcases query with ((pending | opening) | ((pending | sealing) | (coins | (hash | viewQuery)))) | read
  all_goals simp only [RawCtxSelectedParentCompiler.live, RawCtxGenericLiveRead.handler,
    RawCtxSelectedParentCompiler.pending, QueryImpl.compose, RawCtxPendingLiveQueries.erase,
    RawCtxPendingOwnerQueries.erase]
  all_goals rfl

/-- The actual pending source interpreter with a private patch is exactly the private-only consistent handler; public evaluations remain real. -/
theorem live_patch {Auxiliary : Type}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
    (prior : Prior) (entry : Entry) (target : RootOutput) (output : FullOutput)
    (reader : RawCtxSelectedLiveTrace.Reader) (separate : targetAddress target ≠ entry.address) :
    RawCtxSelectedParentCompiler.live (Auxiliary := Auxiliary) source writer (privatePatch prior target output) entry
        (RawCtxKdfRequestTable.fullResponse output) reader =
      RawCtxSelectedParentPrivate.handler source writer prior entry output reader (realView source) target ∘ₛ
        RawCtxPendingLiveQueries.erase := by
  rw [live_real, handler_patch source writer prior entry target output reader (realView source) separate]

/-- The concrete native one-owner tail with an arbitrary private child replacement realizes the same material-only source program under exact private alias routing and real public HKDF. -/
theorem native_cut {Metadata Auxiliary Result : Type} {serverCount beaconCount : Nat}
    (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer) (prior : Prior)
    (sender : Std.U64) (decode : RawCtxReceive.FrameDecoder)
    (owner : RawCtxProtocolReveals.Owner serverCount beaconCount)
    (context : RawCtxSelectedParentContext.Context Metadata Result serverCount beaconCount)
    (parentOutput childOutput : FullOutput)
    (separate : targetAddress (PqxdhOrderedChainHybrids.nextChain parentOutput) ≠ RawCtxSelectedParentContext.address context) :
    RawCtxSelectedParentContext.native (Auxiliary := Auxiliary) source writer
      (privatePatch prior (PqxdhOrderedChainHybrids.nextChain parentOutput) childOutput) sender decode owner context parentOutput =
      Prod.map id (RawCtxSelectedParentLiveSource.project (PqxdhOrderedChainHybrids.nextChain parentOutput)) <$>
        simulateQ (RawCtxSelectedParentPrivate.handler source writer prior
          (fromOutput (RawCtxSelectedParentContext.address context) parentOutput) childOutput
          (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain parentOutput)))
          (realView source) (PqxdhOrderedChainHybrids.nextChain parentOutput))
          (simulateQ RawCtxPendingLiveQueries.erase
            (RawCtxSelectedParentContext.stopped sender decode owner context (PqxdhOrderedChainHybrids.material parentOutput))) := by
  rw [RawCtxSelectedParentPrivatePatch.native_cut source writer prior sender decode owner context parentOutput childOutput separate,
    live_patch source writer prior (fromOutput (RawCtxSelectedParentContext.address context) parentOutput)
      (PqxdhOrderedChainHybrids.nextChain parentOutput) childOutput
      (RawCtxSelectedLiveTrace.nativeReader (RawCtxFreshChainCut.concreteChain (PqxdhOrderedChainHybrids.nextChain parentOutput))) separate]
  apply congrArg (Functor.map (Prod.map id (RawCtxSelectedParentLiveSource.project (PqxdhOrderedChainHybrids.nextChain parentOutput))))
  exact QueryImpl.simulateQ_compose _ _ _

end BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.handler_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.handler_patch

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.live_real' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.live_real

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.live_patch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.live_patch

/-- info: 'BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.native_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxSelectedParentPrivateRealization.native_cut
