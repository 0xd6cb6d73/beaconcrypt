import BeaconcryptCore.Computational.PqxdhInitialParentPost

/-!
The concrete full post descriptor receives its original full76 reply and preserves its entire native continuation. The material-only stopped continuation uses the checked retained-parent interpretation and the same later initializer service, represented by known returned kernels. Complete private state, selectors, Beacon first-receive publication and original LIVE history are preserved; native read interpretation here is an operational comparison that precedes reveal masking.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialParentContext
open PqxdhInitialPendingPost PqxdhInitialPostContext PqxdhInitialParentPost
open RawCtxSelectedParentCalls RawCtxSelectedParentEntry RawCtxSelectedFamilyContext
open RawCtxGenericRoleStorage RawCtxGenericRoleFamily PqxdhJointKdfGame PqxdhSecretInputKdf
open PqxdhInitialBeaconAmbient PqxdhFullSecretInputKdf PqxdhOrderedChainHybrids
variable {ι M P I D K X Response Shared Result A N C : Type} {extra : OracleSpec ι} {S B : Nat}

noncomputable def reply (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (output : FullOutput) :
    (Base extra RatchetChain I D K X Response Shared S B).Range
      (PqxdhInitialPostContext.frame sender route decode context).1 :=
  match context with
  | .record _ _ _ inner => RawCtxSelectedFamilyNativeContext.reply sender route decode inner output
  | .finish _ _ _ candidate _ inner =>
      RawCtxSelectedFamilyNativeContext.ownerReply candidate.server_binding.identity_key_id decode inner output

/-- The exact first receive publication and original history tick commute with the full private kernel map. -/
theorem finish_map (target : RootOutput) (index : Fin B) (before : LabelFront M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State (KernelOf RawCtxSelectedChain.Slot) Unit) :
    finishResult index (mapFront (nativeKernel target) before) control candidate
      (Prod.map id (RawCtxSelectedParentOwner.mapOwner target) result) =
      Prod.map id (mapFront (nativeKernel target)) (finishResult index before control candidate result) := by
  simp only [finishResult, Prod.map_def, id_eq, RawCtxSelectedParentOwner.mapOwner, RawCtxGenericOwnerMap.mapOwner]
  rw [PqxdhInitialGenericBeacon.opening_map]
  change ((PqxdhInitialGenericBeacon.finish control (mapBeacon (nativeKernel target) (before.roles.1.2 index))
    (Option.map (PqxdhInitialGenericBeacon.mapStaged (nativeKernel target))
      (PqxdhInitialGenericBeacon.afterOpening candidate result.2.kernel result.1))).1,
    install index (mapFront (nativeKernel target) before)
      (PqxdhInitialGenericBeacon.finish control (mapBeacon (nativeKernel target) (before.roles.1.2 index))
        (Option.map (PqxdhInitialGenericBeacon.mapStaged (nativeKernel target))
          (PqxdhInitialGenericBeacon.afterOpening candidate result.2.kernel result.1))).2) = _
  rw [PqxdhInitialGenericBeacon.finish_map]
  exact congrArg (fun state => (_, state)) (install_map (nativeKernel target) index before _)

section Services
variable (source : FixedHkdfSha512NoSaltSource) (writer : RawCtxMixedShared.Writer)
  (prior : RawCtxSelectedParentTable.Prior)
  (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
  (application : Response → Ambient A N C (Option Pqxdh.Bytes))
  (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf RatchetChain)))
  (selector : QueryImpl extra (Ambient A N C))
  (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Ambient A N C))

/-- The owner portion of the full post service is exactly the same native pending source interpreter, with all ambient state retained. -/
theorem native_primitive (entry : Entry) (target : RootOutput) :
    nativeHandler source writer prior entry target pre application initial selector aux ∘ₛ
      primitiveForward (S := S) (B := B) =
    nativePrimitive (A := A) (N := N) (C := C) source writer prior entry target := by
  funext query
  simp [QueryImpl.compose, primitiveForward, nativeHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler]

/-- The label owner portion forwards every original pending effect to the same retained-parent source service. -/
theorem label_primitive (entry : Entry) (target : RootOutput) (response : RatchetKdfResponse) :
    labelHandler source writer prior entry target pre application initial selector aux response ∘ₛ
      primitiveForward (S := S) (B := B) =
    labelPrimitive (A := A) (N := N) (C := C) source writer prior entry response := by
  funext query
  simp [QueryImpl.compose, primitiveForward, labelHandler, handler, OracleSpec.query,
    RawCtxPendingFamilyLiveQueries.handler]

/-- The actual full post frame, including future registrations, equals its material-only stopped source continuation after private native interpretation. -/
theorem frame_cut (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (output : FullOutput) :
    simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialPostContext.frame sender route decode context).2 (reply sender route decode context output)) =
    Prod.map id (mapFront (nativeKernel (nextChain output))) <$> simulateQ
      (labelHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialPostContext.address context) output) (nextChain output)))
      (PqxdhInitialPostContext.stopped sender route decode context (material output)) := by
  cases context with
  | finish index before control candidate outside inner =>
    simp only [PqxdhInitialPostContext.frame, reply, PqxdhInitialPostContext.address,
      PqxdhInitialPostContext.stopped, simulateQ_bind, ← QueryImpl.simulateQ_compose,
      native_primitive, label_primitive]
    unfold nativePrimitive labelPrimitive
    rw [simulate_lift, simulate_lift, RawCtxSelectedFamilyNativeContext.owner_cut, lift_map]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro result
    have finished := finish_map (nextChain output) index (knownFront before) control candidate result
    rw [known_front] at finished
    rw [finished]
    exact PqxdhInitialParentPost.program source writer prior (fromOutput (ownerAddress inner) output)
      (nextChain output) pre application initial selector aux sender route decode _ _
  | record request before outside inner =>
    simp only [PqxdhInitialPostContext.frame, reply, PqxdhInitialPostContext.address,
      PqxdhInitialPostContext.stopped, simulateQ_bind, ← QueryImpl.simulateQ_compose,
      native_live, label_live, simulate_lift]
    rw [RawCtxSelectedFamilyNativeContext.frame_cut, lift_map]
    simp only [bind_map_left, map_bind]
    apply bind_congr
    intro result
    exact PqxdhInitialParentPost.program source writer prior (fromOutput (RawCtxSelectedFamilyContext.address inner) output)
      (nextChain output) pre application initial selector aux sender route decode (outside result.1)
      { knownFront before with roles := result.2 }

/-- Evaluation preserves the entire shared primitive state, private interpreter and root cache after the full stopped source continuation. -/
theorem frame_run (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : PqxdhInitialPostContext.Context extra M P I D K Result S B)
    (output : FullOutput) (state : RawCtxSharedPrimitive.SharedState A × N) (cache : C) :
    ((simulateQ (nativeHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
      (nextChain output) pre application initial selector aux)
      ((PqxdhInitialPostContext.frame sender route decode context).2 (reply sender route decode context output))).run state).run cache =
    (fun result => ((Prod.map id (mapFront (nativeKernel (nextChain output))) result.1.1, result.1.2), result.2)) <$>
      ((simulateQ (labelHandler source writer prior (fromOutput (PqxdhInitialPostContext.address context) output)
        (nextChain output) pre application initial selector aux
        (childResponse prior (fromOutput (PqxdhInitialPostContext.address context) output) (nextChain output)))
      (PqxdhInitialPostContext.stopped sender route decode context (material output))).run state).run cache := by
  rw [frame_cut]
  rfl

end Services
end BeaconcryptCore.Computational.PqxdhInitialParentContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentContext.finish_map' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentContext.finish_map

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentContext.native_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentContext.native_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentContext.label_primitive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentContext.label_primitive

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentContext.frame_cut' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentContext.frame_cut

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialParentContext.frame_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialParentContext.frame_run
