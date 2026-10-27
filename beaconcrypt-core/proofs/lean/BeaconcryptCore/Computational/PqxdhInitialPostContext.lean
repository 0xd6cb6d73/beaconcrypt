import BeaconcryptCore.Computational.PqxdhInitialPendingPost
import BeaconcryptCore.Computational.RawCtxForwardLive

/-!
A stopped source descriptor retains the original full post client rather than restricting the remaining schedule to established-family traffic. Record descriptors retain the exact inner family context. Finish descriptors retain the original staged first raw receive and finish publication. The material-only representation marks only the new chain hidden; every saved pre-draw kernel is represented as known and every later preparation, initializer and selector remains an explicit source query.
-/
open OracleComp OracleSpec CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM beaconcrypt_core ratchet ratchet.refined ratchet.concrete
set_option autoImplicit false
namespace BeaconcryptCore.Computational.PqxdhInitialPostContext
open PqxdhInitialPendingPost RawCtxSelectedFamilyContext
variable {ι M P I D K X Response Shared Result : Type} {extra : OracleSpec ι} {S B : Nat}

abbrev PostSpec (extra : OracleSpec ι) (S B : Nat) := PqxdhInitialGenericPost.Spec extra S B
abbrev Base (extra : OracleSpec ι) (Chain I D K X Response Shared : Type) (S B : Nat) :=
  PqxdhInitialPendingPost.Spec extra Chain I D K X Response Shared S B
abbrev NativeFront (M P I D K : Type) (S B : Nat) := Front RatchetChain M P I D K S B
abbrev LabelFront (M P I D K : Type) (S B : Nat) := Front RawCtxSelectedChain.Slot M P I D K S B

inductive Context (extra : OracleSpec ι) (M P I D K Result : Type) (S B : Nat) : Type where
  | record (request : (RawCtxProtocolReveals.SourceSpec S B).Domain)
      (before : NativeFront M P I D K S B)
      (outside : (RawCtxProtocolReveals.SourceSpec S B).Range request → OracleComp (PostSpec extra S B) Result)
      (inner : RawCtxSelectedFamilyContext.Context M P I D K
        ((RawCtxProtocolReveals.SourceSpec S B).Range request) S B)
  | finish (index : Fin B) (before : NativeFront M P I D K S B)
      (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
      (outside : Option Pqxdh.Bytes → OracleComp (PostSpec extra S B) Result)
      (inner : OwnerContext Unit (core.option.Option RawCtxWholeOwner.Decrypted))

abbrev Frame (extra : OracleSpec ι) (M P I D K X Response Shared Result : Type) (S B : Nat) :=
  RawCtxForwardAnnotation.Frame (Base extra RatchetChain I D K X Response Shared S B)
    (Result × NativeFront M P I D K S B)

def knownFront (before : NativeFront M P I D K S B) : LabelFront M P I D K S B :=
  ⟨(RawCtxGenericRoleFamily.mapRoles knownKernel before.roles.1, before.roles.2), before.controls, before.consumed⟩

noncomputable def finishResult {Chain : Type} (index : Fin B) (before : Front Chain M P I D K S B)
    (control : pqxdh.BeaconInitSent) (candidate : pqxdh.BeaconRegistrationCandidate)
    (result : core.option.Option RawCtxWholeOwner.Decrypted × RawCtxChainOwner.State (KernelOf Chain) Unit) :
    Option Pqxdh.Bytes × Front Chain M P I D K S B :=
  let staged := PqxdhInitialGenericBeacon.afterOpening candidate result.2.kernel result.1
  let published := PqxdhInitialGenericBeacon.finish control (before.roles.1.2 index) staged
  (published.1, PqxdhInitialPendingPost.install index before published.2)

noncomputable def frame (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) :
    Context extra M P I D K Result S B → Frame extra M P I D K X Response Shared Result S B
  | .record _ before outside inner =>
      let saved := RawCtxSelectedFamilyContext.frame sender route decode inner
      ⟨.inl saved.1, fun reply => do
        let result ← simulateQ liveForward (saved.2 reply)
        (simulateQ (compiler sender route decode) (outside result.1)).run { before with roles := result.2 }⟩
  | .finish index before control candidate outside inner =>
      let saved := ownerFrame candidate.server_binding.identity_key_id decode inner
      ⟨.inl (.inl saved.1), fun reply => do
        let result ← simulateQ primitiveForward (saved.2 reply)
        let finished := finishResult index before control candidate result
        (simulateQ (compiler sender route decode) (outside finished.1)).run finished.2⟩

noncomputable def stopped (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context extra M P I D K Result S B)
    (material : PqxdhOrderedChainHybrids.Material) :
    OracleComp (Base extra RawCtxSelectedChain.Slot I D K X Response Shared S B)
      (Result × LabelFront M P I D K S B) :=
  match context with
  | .record _ before outside inner => do
      let result ← simulateQ liveForward (RawCtxSelectedFamilyContext.stopped sender route decode inner material)
      (simulateQ (compiler sender route decode) (outside result.1)).run { knownFront before with roles := result.2 }
  | .finish index before control candidate outside inner => do
      let result ← simulateQ primitiveForward (ownerStopped candidate.server_binding.identity_key_id decode inner material)
      let finished := finishResult index (knownFront before) control candidate result
      (simulateQ (compiler sender route decode) (outside finished.1)).run finished.2

def address : Context extra M P I D K Result S B → PqxdhJointKdf.JointKdfAddress
  | .record _ _ _ inner => RawCtxSelectedFamilyContext.address inner
  | .finish _ _ _ _ _ inner => ownerAddress inner

def queryAddress : (Base extra RatchetChain I D K X Response Shared S B).Domain →
    Option PqxdhJointKdf.JointKdfAddress
  | .inl query => RawCtxSelectedFamilyContext.queryAddress query
  | .inr _ => none

/-- Each carried outer descriptor names exactly the actual private input in its complete source continuation. -/
theorem frame_address (sender : M → Std.U64) (route : RawCtxServerRouting.SenderDecoder)
    (decode : RawCtxReceive.FrameDecoder) (context : Context extra M P I D K Result S B) :
    queryAddress (extra := extra) (frame (X := X) (Response := Response) (Shared := Shared) sender route decode context).1 =
      some (address context) := by
  cases context with
  | record request before outside inner =>
      exact RawCtxSelectedFamilyContext.frame_address sender route decode inner
  | finish index before control candidate outside inner => cases inner <;> rfl

end BeaconcryptCore.Computational.PqxdhInitialPostContext

/-- info: 'BeaconcryptCore.Computational.PqxdhInitialPostContext.frame_address' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BeaconcryptCore.Computational.PqxdhInitialPostContext.frame_address
