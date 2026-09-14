import BeaconcryptCore.Computational.RawCtxPendingOwnerQueries
import BeaconcryptCore.Computational.RawCtxGenericFamilyFrontend

/-!
The original interpreted receive and send programs are compiled through the native adapters into any native backend monad. Their concrete Calls reconstruct precisely the original complete source kernel and optional output, with no callback-realization premise. Every mutable backend effect remains in the same monad, including private KDF table, cursor, caches and instrumentation.

This operational construction may therefore be used before a selected cut with a dynamically changing selective interpreter. It does not assume the prefix uses a fixed retained table. It introduces no primitive, uniform-input, freshness, success or key-independence premise. The family frontend and pending compiler must still connect this exact call construction to their complete original source program.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxGenericNativeCalls
open RawCtxPendingOwnerQueries

noncomputable def calls {m : Type → Type*} [Monad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) : RawCtxChainOwner.Calls (Kernel RatchetChain) m :=
  { receive := fun entry target context =>
      simulateQ (((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter) ∘ₛ
        RawCtxInterpretedReceive.nativeAdapter) (RawCtxInterpretedReceive.receive entry target context)
    send := fun entry context =>
      simulateQ (((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) ∘ₛ
        RawCtxInterpretedSend.nativeAdapter) (RawCtxInterpretedSend.send entry context) }

/-- Any native interpreter realizes the complete source receive, retaining all mutable primitive effects and optional replies. -/
theorem receive_realized {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (entry : Kernel RatchetChain)
    (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ ((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter)
      (RawCtxOwnerOracle.receive ⟨entry⟩ target context) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> (calls native).receive entry target context := by
  rw [RawCtxInterpretedReceive.receive_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

/-- Any native interpreter realizes the source send including failed sealing and its complete advanced state. -/
theorem send_realized {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (entry : Kernel RatchetChain)
    (context : RawCtxSourceSend.SealContext) :
    simulateQ ((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter)
      (RawCtxSourceSend.send ⟨entry⟩ context) =
      (fun result => (ConcreteRatchetKernel.mk result.1, result.2)) <$> (calls native).send entry context := by
  rw [RawCtxInterpretedSend.send_native, simulateQ_map, ← QueryImpl.simulateQ_compose]
  rfl

end BeaconcryptCore.Computational.RawCtxGenericNativeCalls

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericNativeCalls.receive_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericNativeCalls.receive_realized

/-- info: 'BeaconcryptCore.Computational.RawCtxGenericNativeCalls.send_realized' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxGenericNativeCalls.send_realized

