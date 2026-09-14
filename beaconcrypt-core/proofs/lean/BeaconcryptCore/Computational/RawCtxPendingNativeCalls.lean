import BeaconcryptCore.Computational.RawCtxGenericNativeCalls
import BeaconcryptCore.Computational.RawCtxGenericOwnerInterpretation

/-!
The private pending source compiler executes the actual native receive/send adapters in any lawful backend monad. Each original KDF query retains its real request and complete decoded reply; the enriched pending payload is erased only at that callback. Opening, sealing and public operations preserve all backend state. This supports mutable private tables and cursors without fixing their values before the execution or postulating call-realization equations.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
open OracleComp OracleSpec
set_option autoImplicit false
namespace BeaconcryptCore.Computational.RawCtxPendingNativeCalls
open RawCtxPendingOwnerQueries RawCtxChainInterpretation

noncomputable def receive {m : Type → Type*} [Monad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) :=
  (((native ∘ₛ RawCtxMixedOwner.receiveAdapter) ∘ₛ RawCtxWholeOwner.adapter) ∘ₛ RawCtxInterpretedReceive.nativeAdapter)

noncomputable def send {m : Type → Type*} [Monad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) :=
  (((native ∘ₛ RawCtxMixedOwner.sendAdapter) ∘ₛ RawCtxSourceSend.adapter) ∘ₛ RawCtxInterpretedSend.nativeAdapter)

noncomputable def original {m : Type → Type*} [Monad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m) :
    QueryImpl (OriginalSpec RatchetChain) m
  | .inl (.inl chain) => receive native (.inl (RawCtxChainSend.nativeRequest chain))
  | .inl (.inr pending) => receive native (.inr (mapOpeningChains id id pending))
  | .inr (.inl (.inl chain)) => send native (.inl (RawCtxChainSend.nativeRequest chain))
  | .inr (.inl (.inr pending)) => send native (.inr (RawCtxChainSend.nativeSeal id id pending))
  | .inr (.inr request) => publicCalls request

noncomputable def pending {m : Type → Type*} [Monad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m) :=
  original native publicCalls ∘ₛ erase

private theorem kernel_id (kernel : Kernel RatchetChain) : mapChains id id kernel = kernel := by
  cases kernel
  rfl

/-- The complete pending receive call is the original native call under the same arbitrary mutable backend. -/
theorem receive_call {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (kernel : Kernel RatchetChain) (target : Std.U64) (context : RawCtxWholeOwner.OpenContext) :
    simulateQ (pending native publicCalls) (RawCtxPendingOwnerQueries.calls.receive kernel target context) =
      (RawCtxGenericNativeCalls.calls native).receive kernel target context := by
  rw [pending, QueryImpl.simulateQ_compose, RawCtxPendingOwnerQueries.receive_call]
  simp only [originalCalls, ← QueryImpl.simulateQ_compose]
  have actual := RawCtxChainReceive.execute_native id id
    (original native publicCalls ∘ₛ originalReceive) (receive native)
    (fun request => by simp [QueryImpl.compose, originalReceive, original, OracleSpec.query])
    (fun opening => by simp [QueryImpl.compose, originalReceive, original, OracleSpec.query])
    kernel target context
  have mapped : (fun result : Kernel RatchetChain × core.option.Option RawCtxWholeOwner.Decrypted =>
      (mapChains id id result.1, result.2)) = id := by
    funext result
    rw [kernel_id]
    rfl
  rw [mapped, kernel_id] at actual
  simpa only [Functor.map_id, id_eq, receive, RawCtxGenericNativeCalls.calls] using actual.symm

/-- The pending send preserves the actual advanced kernel and optional seal under the same mutable backend. -/
theorem send_call {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m)
    (kernel : Kernel RatchetChain) (context : RawCtxSourceSend.SealContext) :
    simulateQ (pending native publicCalls) (RawCtxPendingOwnerQueries.calls.send kernel context) =
      (RawCtxGenericNativeCalls.calls native).send kernel context := by
  rw [pending, QueryImpl.simulateQ_compose, RawCtxPendingOwnerQueries.send_call]
  simp only [originalCalls, ← QueryImpl.simulateQ_compose]
  have actual := RawCtxChainSend.execute_native id id
    (original native publicCalls ∘ₛ originalSend) (send native)
    (fun request => by simp [QueryImpl.compose, originalSend, original, OracleSpec.query])
    (fun sealing => by simp [QueryImpl.compose, originalSend, original, OracleSpec.query])
    kernel context
  have mapped : (fun result : Kernel RatchetChain × Option RawCtxSourceSend.Encrypted =>
      (mapChains id id result.1, result.2)) = id := by
    funext result
    rw [kernel_id]
    rfl
  rw [mapped, kernel_id] at actual
  simpa only [Functor.map_id, id_eq, send, RawCtxGenericNativeCalls.calls] using actual.symm

/-- Both interpreted pending callbacks form exactly the original native call record; no realization premise is supplied. -/
theorem calls_interpretation {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m) :
    RawCtxGenericOwnerInterpretation.interpretedCalls (pending native publicCalls)
      RawCtxPendingOwnerQueries.calls = RawCtxGenericNativeCalls.calls native := by
  exact congrArg₂ RawCtxChainOwner.Calls.mk
    (funext fun kernel => funext fun target => funext fun context => receive_call native publicCalls kernel target context)
    (funext fun kernel => funext fun context => send_call native publicCalls kernel context)

/-- Every public query retains its actual callback and every state effect under the same mutable interpreter. -/
theorem public_interpretation {m : Type → Type*} [Monad m] [LawfulMonad m]
    (native : QueryImpl RawCtxMixedOwner.NativeSpec m) (publicCalls : QueryImpl RawCtxServerServices.PublicSpec m) :
    (fun request => simulateQ (pending native publicCalls) (RawCtxPendingOwnerQueries.publicForward request)) =
      publicCalls := by
  funext request
  simp [pending, QueryImpl.compose, RawCtxPendingOwnerQueries.publicForward, erase, original, OracleSpec.query]

end BeaconcryptCore.Computational.RawCtxPendingNativeCalls

/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCalls.receive_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCalls.receive_call
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCalls.send_call' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCalls.send_call
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCalls.calls_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCalls.calls_interpretation
/-- info: 'BeaconcryptCore.Computational.RawCtxPendingNativeCalls.public_interpretation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.RawCtxPendingNativeCalls.public_interpretation
