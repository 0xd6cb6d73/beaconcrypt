import BeaconcryptCore.Computational.PqxdhInitialForwardPost
import BeaconcryptCore.Computational.PqxdhInitialPendingBuilder

/-!
The first Server send has a concrete source descriptor before its KDF response. It retains the original current protocol state, authenticated plaintext, candidate, metadata, pending send and complete original post client. The stopped tail uses only material, keeps the new chain as a private label, performs the same erase/write/publication and continues the full schedule. No arbitrary continuation over unavailable chain bytes is stored.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialBuilderContext
open PqxdhInitialPendingPost PqxdhInitialPostContext
variable {ι Chain Kernel M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev BuildResult := RustM (Option PqxdhServerRegistrationPublication.Response)

noncomputable def afterSend {m : Type → Type} [Monad m]
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (metadata : P) (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes))
    (result : Kernel × Option RawCtxSourceSend.Encrypted) :
    m (Option PqxdhServerRegistrationPublication.Response ×
      PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) := do
  let _ ← aux (.erase authenticated)
  match result.2 with
  | none => pure (none, state)
  | some encrypted => do
      let serialized ← aux (.write (PqxdhServerRegistrationPublication.responseFields candidate encrypted))
      match serialized with
      | none => pure (none, state)
      | some serialized => pure (some ⟨serialized, candidate.key_id⟩,
          PqxdhInitialGenericPublication.publish state candidate result.1 metadata)

/-- The exact first send precedes the original erase, serialization and peer publication, including every optional failure. -/
theorem after_factor {m : Type → Type} [Monad m] [LawfulMonad m]
    (calls : RawCtxChainOwner.Calls Kernel m)
    (aux : QueryImpl PqxdhServerRegistrationPublication.AuxSpec m)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes)
    (kernel : Kernel) (metadata : P)
    (state : PqxdhInitialGenericPublication.State Kernel M P (List Pqxdh.Bytes)) :
    PqxdhInitialGenericPublication.afterInitialization calls aux candidate authenticated kernel metadata state =
      (calls.send kernel (PqxdhServerRegistrationPublication.firstContext candidate authenticated) >>=
        afterSend aux candidate authenticated metadata state) := rfl

structure Builder (extra : OracleSpec ι) (M P I D K Result : Type) (S B : Nat) where
  index : Fin S
  before : NativeFront M P I D K S B
  metadata : P
  candidate : pqxdh.ServerRegistrationCandidate
  authenticated : Pqxdh.Bytes
  pending : RawCtxChainSend.Kdf RatchetChain RatchetChain RatchetMaterial RawCtxSourceSend.SealContext
  outside : BuildResult → OracleComp (PostSpec extra S B) Result

abbrev Context (extra : OracleSpec ι) (M P I D K Result : Type) (S B : Nat) :=
  PqxdhInitialPostContext.Context extra M P I D K Result S B ⊕ Builder extra M P I D K Result S B

noncomputable def complete (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (index : Fin S) (before : Front Chain M P I D K S B)
    (candidate : pqxdh.ServerRegistrationCandidate) (authenticated : Pqxdh.Bytes) (metadata : P)
    (outside : BuildResult → OracleComp (PostSpec extra S B) Result)
    (result : KernelOf Chain × Option RawCtxSourceSend.Encrypted) :
    OracleComp (Base extra Chain I D K X Response Shared S B) (Result × Front Chain M P I D K S B) := do
  let published ← afterSend auxForward candidate authenticated metadata
    (PqxdhInitialPendingBuilder.selected sender index before) result
  let installed := PqxdhInitialPendingBuilder.reinstall index before (.ok published)
  (simulateQ (compiler sender route decode) (outside installed.1)).run installed.2

noncomputable def builderFrame (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Builder extra M P I D K Result S B) :
    PqxdhInitialPostContext.Frame extra M P I D K X Response Shared Result S B :=
  ⟨.inl (.inl (.inr (.inl (.inl context.pending)))), fun reply => do
    let ready := RawCtxChainSend.ready context.pending reply
    let sealed ← (Base extra RatchetChain I D K X Response Shared S B).query (.inl (.inl (.inr (.inl (.inr ready)))))
    complete sender route decode context.index context.before context.candidate context.authenticated
      context.metadata context.outside (ready.advanced, sealed)⟩

noncomputable def frame (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) : Context extra M P I D K Result S B →
    PqxdhInitialPostContext.Frame extra M P I D K X Response Shared Result S B
  | .inl context => PqxdhInitialPostContext.frame sender route decode context
  | .inr context => builderFrame sender route decode context

noncomputable def stopped (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context extra M P I D K Result S B)
    (material : PqxdhOrderedChainHybrids.Material) :
    OracleComp (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B)
      (Result × LabelFront M P I D K S B) :=
  match context with
  | .inl context => PqxdhInitialPostContext.stopped sender route decode context material
  | .inr context => do
      let ready := RawCtxSelectedPendingCut.sendStop context.pending material
      let sealed ← (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B).query
        (.inl (.inl (.inr (.inl (.inr ready)))))
      complete sender route decode context.index (knownFront context.before) context.candidate
        context.authenticated context.metadata context.outside (ready.advanced, sealed)

def address : Context extra M P I D K Result S B → PqxdhJointKdf.JointKdfAddress
  | .inl context => PqxdhInitialPostContext.address context
  | .inr context => RawCtxSelectedPendingCut.requestAddress context.pending.request

/-- The outer source descriptor retains the same complete original address whether the cut is in the first builder or any later post operation. -/
theorem frame_address (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context extra M P I D K Result S B) :
    PqxdhInitialPostContext.queryAddress (extra := extra)
      (frame (X := X) (Response := Response) (Shared := Shared) sender route decode context).1 = some (address context) := by
  cases context with
  | inl context => exact PqxdhInitialPostContext.frame_address sender route decode context
  | inr context => rfl

end BeaconcryptCore.Computational.PqxdhInitialBuilderContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderContext.after_factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderContext.after_factor

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialBuilderContext.frame_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialBuilderContext.frame_address
