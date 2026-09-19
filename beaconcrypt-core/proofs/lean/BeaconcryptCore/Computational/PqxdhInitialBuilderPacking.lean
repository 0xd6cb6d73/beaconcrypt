import BeaconcryptCore.Computational.PqxdhInitialBuilderAmbient
import BeaconcryptCore.Computational.PqxdhInitialPendingAmbient
import BeaconcryptCore.Computational.PqxdhInitialGenericProtocolBuilder

/-!
The actual first-send builder uses the same explicit pending callbacks and complete ambient state as the following post schedule. Its frontend reinstallation is proved equal to the original protocol builder's reinstallation for ordinary, failed and divergent Rust results. Original shared effects are retained even on failure; the private identity state and root cache remain in the interpreter.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderPacking
open PqxdhInitialBeaconAmbient PqxdhInitialPendingPost
variable {ι Chain M P I D K X Response Shared A N C : Type} {extra : OracleSpec ι} {S B : Nat}

section Callbacks
variable {m : Type → Type} [Monad m] [LawfulMonad m]
variable
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) m)
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) m)
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) m)
    (application : Response → m (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → m (Option (KernelOf Chain)))
    (selector : QueryImpl extra m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)

/-- The explicit full post interpreter forwards the exact pending receive/send calls without consulting unrelated callbacks. -/
theorem calls_handler :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (handler primitive reader pre application initial selector aux) calls =
      RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls := by
  have forward : handler primitive reader pre application initial selector aux ∘ₛ primitiveForward = primitive := by
    funext query
    simp [QueryImpl.compose, primitiveForward, handler, OracleSpec.query, RawCtxPendingFamilyLiveQueries.handler]
  simp only [calls, RawCtxGenericOwnerInterpretation.interpretedCalls, ← QueryImpl.simulateQ_compose, forward]

/-- The explicit full post interpreter forwards the original auxiliary builder callback and all its effects. -/
theorem aux_handler : handler primitive reader pre application initial selector aux ∘ₛ auxForward = aux := by
  funext query
  simp [QueryImpl.compose, auxForward, handler, OracleSpec.query]
end Callbacks

/-- Generic source calls commute with the complete ambient lift, including both original optional receive and send results. -/
theorem calls_lift (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (Base A)) :
    RawCtxGenericOwnerInterpretation.interpretedCalls
      (fun query => PqxdhInitialBeaconAmbient.lift (N := N) (C := C) (primitive query)) RawCtxPendingOwnerQueries.calls =
      liftCalls (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls) := by
  simp only [RawCtxGenericOwnerInterpretation.interpretedCalls, liftCalls, simulate_lift]

/-- Every actual first-send builder branch has the original full protocol state after reversible frontend packing. -/
theorem build
    (primitive : QueryImpl (RawCtxPendingOwnerQueries.Spec Chain) (Base A))
    (reader : QueryImpl (RawCtxGenericFamilyRead.ReadSpec (KernelOf Chain) S B) (Ambient A N C))
    (pre : QueryImpl (PqxdhBeaconPhase2Shared.Spec I D K X Response Shared) (Ambient A N C))
    (application : Response → Ambient A N C (Option Pqxdh.Bytes))
    (initial : PqxdhBeaconPhase2Shared.Secrets Shared → Ambient A N C (Option (KernelOf Chain)))
    (selector : QueryImpl extra (Ambient A N C))
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec (Base A))
    (source : PqxdhJointKdfGame.FixedHkdfSha512NoSaltSource)
    (kernel : RustM (KernelOf Chain)) (sender : M → Std.U64) (index : Fin S) (metadata : P)
    (ready : PqxdhPrivateAcceptedRoot.Ready) (before : PqxdhInitialPostPacking.Full Chain M P I D K A N S B) :
    (fun result => (result.1.1, PqxdhInitialPostPacking.pack (result.1.2, result.2))) <$>
      (simulateQ (handler (fun query => PqxdhInitialBeaconAmbient.lift (primitive query))
        reader pre application initial selector (fun query => PqxdhInitialBeaconAmbient.lift (aux query)))
        ((PqxdhInitialPendingBuilder.build source kernel sender index metadata ready).run before.1)).run before.2 =
      (fun cache => (fun result => ((result.1, (result.2, before.2.2)), cache)) <$>
        (PqxdhInitialGenericProtocolBuilder.build source
          (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls)
          aux kernel sender index metadata ready).run (PqxdhInitialPostPacking.pack before).1) := by
  rw [PqxdhInitialPendingBuilder.build_interpretation]
  funext cache
  simp only [Functor.map, StateT.map, StateT.run, PqxdhInitialPendingBuilder.interpretedBuild, calls_handler, aux_handler, calls_lift,
    PqxdhInitialBuilderAmbient.ready_lift]
  let current := PqxdhInitialPendingBuilder.consume index ready before.1
  let input := PqxdhInitialPendingBuilder.selected sender index current
  let execution := (PqxdhInitialGenericBuilder.readyBuild source
    (RawCtxGenericOwnerInterpretation.interpretedCalls primitive RawCtxPendingOwnerQueries.calls) aux kernel
    ⟨input.server.identity, input.identityKeyId⟩ ready metadata input).run before.2.1
  change (fun x => ((x.1.1.1, PqxdhInitialPostPacking.pack (x.1.1.2, x.1.2)), x.2)) <$>
    ((fun x => ((PqxdhInitialPendingBuilder.reinstall index current x.1.1, x.1.2), x.2)) <$>
      ((fun x => ((x.1, (x.2, before.2.2)), cache)) <$> execution)) =
    (fun x => ((x.1, (x.2, before.2.2)), cache)) <$>
      (PqxdhInitialGenericProtocol.reinstall index (PqxdhInitialPostPacking.pack (current, before.2)).1 <$> execution)
  simp only [Functor.map_map]
  apply congrArg (fun f => f <$> execution)
  funext result
  rcases result with ⟨result, shared⟩
  cases result <;> rfl

end BeaconcryptCore.Computational.PqxdhInitialBuilderPacking

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.calls_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.calls_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.aux_handler' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.aux_handler

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.calls_lift' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.calls_lift

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderPacking.build
